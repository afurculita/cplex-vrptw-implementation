"""The ``VRPTW.mod`` formulation written with the docplex Python API.

The model is the classic three-index (vehicle, from, to) formulation with
big-M time propagation constraints (Solomon & Desrosiers 1988; Toth & Vigo,
*Vehicle Routing*, ch. 5).  It mirrors ``VRPTW.mod`` constraint by constraint
so the two can be validated against each other.

Requires ``docplex`` and a CPLEX engine (``pip install cplex docplex``; the
Community Edition from PyPI is limited to 1000 variables/constraints, which
is enough for the sample instance).
"""

from __future__ import annotations

from dataclasses import dataclass
from typing import Any

from vrptw.data import Instance
from vrptw.verify import Route, Solution


@dataclass
class BuiltModel:
    model: Any  # docplex.mp.model.Model
    x: dict[tuple[int, int, int], Any]  # arc variables, only for allowed arcs
    s: dict[tuple[int, int], Any]  # start-of-service variables
    instance: Instance


def build_model(inst: Instance, symmetry_breaking: bool = True, name: str | None = None) -> BuiltModel:
    """Build the MIP.  Arc variables exist only for arcs allowed by the data."""
    from docplex.mp.model import Model

    K = range(1, inst.vehicles + 1)
    N = inst.nodes
    C = inst.customers
    depot, end = inst.depot, inst.end_depot
    arcs = [(i, j) for i in N for j in N if inst.arc_allowed(i, j)]

    m = Model(name=name or f"VRPTW-{inst.name}")
    x = m.binary_var_dict(((k, i, j) for k in K for i, j in arcs), name="x")
    s = m.continuous_var_dict(
        ((k, i) for k in K for i in N),
        lb=lambda ki: inst.ready[ki[1]],  # time windows as variable bounds
        ub=lambda ki: inst.due[ki[1]],
        name="s",
    )

    def out_arcs(k: int, i: int):
        return (x[k, i, j] for j in N if (k, i, j) in x)

    def in_arcs(k: int, j: int):
        return (x[k, i, j] for i in N if (k, i, j) in x)

    m.minimize(m.sum(inst.distance[i][j] * x[k, i, j] for k in K for i, j in arcs))

    # Each customer is served exactly once, by exactly one vehicle.
    for i in C:
        m.add_constraint(m.sum(x[k, i, j] for k in K for j in N if (k, i, j) in x) == 1, f"serve_{i}")
    # Vehicle capacity.
    for k in K:
        m.add_constraint(
            m.sum(inst.demand[i] * x[k, i, j] for i in C for j in N if (k, i, j) in x) <= inst.capacity,
            f"capacity_{k}",
        )
    # Every vehicle leaves the depot once (possibly straight to the end depot = idle).
    for k in K:
        m.add_constraint(m.sum(out_arcs(k, depot)) == 1, f"leave_depot_{k}")
    # Flow conservation at customers.
    for k in K:
        for h in C:
            m.add_constraint(m.sum(in_arcs(k, h)) == m.sum(out_arcs(k, h)), f"flow_{k}_{h}")
    # Every vehicle ends at the end depot once.
    for k in K:
        m.add_constraint(m.sum(in_arcs(k, end)) == 1, f"return_depot_{k}")
    # Time propagation with the tightest valid big-M per arc.
    for k in K:
        for i, j in arcs:
            big_m = inst.big_m(i, j)
            m.add_constraint(s[k, i] + inst.time[i][j] - big_m * (1 - x[k, i, j]) <= s[k, j], f"time_{k}_{i}_{j}")
    # Identical vehicles: break symmetry by forcing idle vehicles to have the
    # highest indices (vehicle k idle => vehicle k + 1 idle).
    if symmetry_breaking and (depot, end) in [(a, b) for a, b in arcs]:
        for k in K:
            if k + 1 in K:
                m.add_constraint(x[k, depot, end] <= x[k + 1, depot, end], f"symmetry_{k}")
    return BuiltModel(model=m, x=x, s=s, instance=inst)


def extract_routes(built: BuiltModel, solution: Any) -> list[Route]:
    """Follow the selected arcs of each vehicle from the depot to the end depot."""
    inst = built.instance
    routes: list[Route] = []
    for k in range(1, inst.vehicles + 1):
        succ = {i: j for (kk, i, j), var in built.x.items() if kk == k and solution.get_value(var) > 0.5}
        route: list[int] = []
        node = inst.depot
        while node != inst.end_depot:
            node = succ[node]
            if node != inst.end_depot:
                route.append(node)
            if len(route) > inst.n:
                raise RuntimeError("cycle detected while extracting routes")
        routes.append(tuple(route))
    return routes


def solve(
    inst: Instance,
    time_limit: float | None = None,
    log_output: bool = False,
    symmetry_breaking: bool = True,
) -> Solution | None:
    """Solve an instance to optimality. Returns ``None`` if it is infeasible."""
    built = build_model(inst, symmetry_breaking=symmetry_breaking)
    if time_limit is not None:
        built.model.set_time_limit(time_limit)
    sol = built.model.solve(log_output=log_output)
    if sol is None:
        return None
    routes = extract_routes(built, sol)
    return Solution(routes=tuple(routes), distance=round(sol.objective_value, 6))
