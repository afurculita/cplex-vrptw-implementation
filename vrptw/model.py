"""The VRPTW formulations written with the docplex Python API.

Two formulations are available, both with the tightest per-arc big-M, arc
variables only for time-compatible arcs and the fleet-size cut
``vehicles >= ceil(total demand / capacity)``:

* ``three-index`` mirrors ``VRPTW.mod``: ``x[k, i, j]`` per vehicle, with
  symmetry breaking for the identical vehicles;
* ``two-index`` mirrors ``VRPTW2.mod``: ``x[i, j]`` shared by all vehicles,
  with Miller-Tucker-Zemlin style load variables for the capacity.  It has
  ``v`` times fewer variables and no vehicle symmetry.

The objective is either the total distance or, following the Solomon
benchmark convention, lexicographically the number of vehicles and then the
distance (``objective="lex"``, solved with CPLEX's static multi-objective).

Requires ``docplex`` and a CPLEX engine (``pip install cplex docplex``).
"""

from __future__ import annotations

import math
from dataclasses import dataclass
from typing import Any, Literal

from vrptw.data import Instance
from vrptw.heuristic import construct
from vrptw.preprocess import tighten_time_windows
from vrptw.verify import Route, Solution, route_distance, route_schedule

Formulation = Literal["three-index", "two-index"]
Objective = Literal["distance", "lex"]


@dataclass
class BuiltModel:
    model: Any  # docplex.mp.model.Model
    x: dict[tuple, Any]  # arc variables: (k, i, j) for three-index, (i, j) for two-index
    s: dict[tuple, Any]  # start-of-service variables: (k, i) or (i,)
    u: dict[int, Any]  # load variables (two-index only)
    instance: Instance
    formulation: Formulation
    total_distance: Any
    vehicles_used: Any


def build_model(
    inst: Instance,
    formulation: Formulation = "three-index",
    objective: Objective = "distance",
    symmetry_breaking: bool = True,
    capacity_cut: bool = True,
    name: str | None = None,
) -> BuiltModel:
    """Build the MIP for ``inst`` (whose time windows should already be tightened)."""
    from docplex.mp.model import Model

    m = Model(name=name or f"VRPTW-{inst.name}")
    if formulation == "three-index":
        built = _three_index(m, inst, symmetry_breaking)
    elif formulation == "two-index":
        built = _two_index(m, inst)
    else:
        raise ValueError(f"unknown formulation {formulation!r}")

    if capacity_cut:
        min_vehicles = math.ceil(sum(inst.demand[i] for i in inst.customers) / inst.capacity)
        m.add_constraint(built.vehicles_used >= min_vehicles, "min_vehicles")

    if objective == "distance":
        m.minimize(built.total_distance)
    elif objective == "lex":
        m.minimize_static_lex([built.vehicles_used, built.total_distance], objnames=["vehicles", "distance"])
    else:
        raise ValueError(f"unknown objective {objective!r}")
    return built


def _three_index(m: Any, inst: Instance, symmetry_breaking: bool) -> BuiltModel:
    K = range(1, inst.vehicles + 1)
    N, C = inst.nodes, inst.customers
    depot, end = inst.depot, inst.end_depot
    arcs = [(i, j) for i in N for j in N if inst.arc_allowed(i, j)]

    x = m.binary_var_dict(((k, i, j) for k in K for i, j in arcs), name="x")
    s = m.continuous_var_dict(
        ((k, i) for k in K for i in N),
        lb=lambda ki: inst.ready[ki[1]],
        ub=lambda ki: inst.due[ki[1]],
        name="s",
    )

    def out_arcs(k: int, i: int):
        return (x[k, i, j] for j in N if (k, i, j) in x)

    def in_arcs(k: int, j: int):
        return (x[k, i, j] for i in N if (k, i, j) in x)

    for i in C:  # each customer is served exactly once
        m.add_constraint(m.sum(x[k, i, j] for k in K for j in N if (k, i, j) in x) == 1, f"serve_{i}")
    for k in K:
        m.add_constraint(
            m.sum(inst.demand[i] * x[k, i, j] for i in C for j in N if (k, i, j) in x) <= inst.capacity,
            f"capacity_{k}",
        )
        m.add_constraint(m.sum(out_arcs(k, depot)) == 1, f"leave_depot_{k}")
        m.add_constraint(m.sum(in_arcs(k, end)) == 1, f"return_depot_{k}")
        for h in C:
            m.add_constraint(m.sum(in_arcs(k, h)) == m.sum(out_arcs(k, h)), f"flow_{k}_{h}")
        for i, j in arcs:
            m.add_constraint(
                s[k, i] + inst.time[i][j] - inst.big_m(i, j) * (1 - x[k, i, j]) <= s[k, j], f"time_{k}_{i}_{j}"
            )
    if symmetry_breaking and inst.arc_allowed(depot, end):
        for k in K:  # idle vehicles take the highest indices
            if k + 1 in K:
                m.add_constraint(x[k, depot, end] <= x[k + 1, depot, end], f"symmetry_{k}")

    total_distance = m.sum(inst.distance[i][j] * x[k, i, j] for k in K for i, j in arcs)
    vehicles_used = m.sum(x[k, depot, j] for k in K for j in C if (k, depot, j) in x)
    return BuiltModel(m, x, s, {}, inst, "three-index", total_distance, vehicles_used)


def _two_index(m: Any, inst: Instance) -> BuiltModel:
    N, C = inst.nodes, inst.customers
    depot, end = inst.depot, inst.end_depot
    arcs = [(i, j) for i in N for j in N if inst.arc_allowed(i, j) and (i, j) != (depot, end)]

    x = m.binary_var_dict(arcs, name="x")
    s = m.continuous_var_dict(((i,) for i in N), lb=lambda i: inst.ready[i[0]], ub=lambda i: inst.due[i[0]], name="s")
    u = m.continuous_var_dict(C, lb=lambda i: inst.demand[i], ub=inst.capacity, name="u")

    for j in C:
        m.add_constraint(m.sum(x[i, j] for i in N if (i, j) in x) == 1, f"arrive_{j}")
        m.add_constraint(m.sum(x[j, i] for i in N if (j, i) in x) == 1, f"leave_{j}")
    vehicles_used = m.sum(x[depot, j] for j in C if (depot, j) in x)
    m.add_constraint(vehicles_used <= inst.vehicles, "fleet")
    for i, j in arcs:
        m.add_constraint(s[i,] + inst.time[i][j] - inst.big_m(i, j) * (1 - x[i, j]) <= s[j,], f"time_{i}_{j}")
        if i in C and j in C:  # load propagation (Miller-Tucker-Zemlin)
            m.add_constraint(u[i] + inst.demand[j] - inst.capacity * (1 - x[i, j]) <= u[j], f"load_{i}_{j}")

    total_distance = m.sum(inst.distance[i][j] * x[i, j] for i, j in arcs)
    return BuiltModel(m, x, s, u, inst, "two-index", total_distance, vehicles_used)


def extract_routes(built: BuiltModel, solution: Any) -> list[Route]:
    """Follow the selected arcs from the depot to the end depot."""
    inst = built.instance
    chosen = {key for key, var in built.x.items() if solution.get_value(var) > 0.5}
    routes: list[Route] = []
    if built.formulation == "three-index":
        for k in range(1, inst.vehicles + 1):
            succ = {i: j for (kk, i, j) in chosen if kk == k}
            routes.append(_follow(inst, succ, succ[inst.depot]))
    else:
        succ = {i: j for (i, j) in chosen if i != inst.depot}
        starts = sorted(j for (i, j) in chosen if i == inst.depot)
        routes = [_follow(inst, succ, j) for j in starts]
        routes += [() for _ in range(inst.vehicles - len(routes))]
    return routes


def _follow(inst: Instance, succ: dict[int, int], node: int) -> Route:
    route: list[int] = []
    while node != inst.end_depot:
        route.append(node)
        if len(route) > inst.n:
            raise RuntimeError("cycle detected while extracting routes")
        node = succ[node]
    return tuple(route)


def arc_variables(built: BuiltModel) -> dict[tuple[int, int], list[Any]]:
    """Group the arc variables by arc (summing over vehicles in the three-index model)."""
    grouped: dict[tuple[int, int], list[Any]] = {}
    for key, var in built.x.items():
        i, j = key[-2], key[-1]
        grouped.setdefault((i, j), []).append(var)
    return grouped


def add_warm_start(built: BuiltModel, solution: Solution) -> None:
    """Pass a feasible solution to CPLEX as a MIP start."""
    inst = built.instance
    start = built.model.new_solution()
    routes = [r for r in solution.routes if r]
    if built.formulation == "three-index":
        for k in range(1, inst.vehicles + 1):
            route = routes[k - 1] if k - 1 < len(routes) else ()
            nodes = (inst.depot, *route, inst.end_depot)
            for a, b in zip(nodes, nodes[1:], strict=False):
                start.add_var_value(built.x[k, a, b], 1)
            times = route_schedule(inst, route)
            if times is not None:
                for node, t in zip(nodes, times, strict=True):
                    start.add_var_value(built.s[k, node], t)
    else:
        for route in routes:
            nodes = (inst.depot, *route, inst.end_depot)
            for a, b in zip(nodes, nodes[1:], strict=False):
                start.add_var_value(built.x[a, b], 1)
            times = route_schedule(inst, route)
            load = 0
            for node, t in zip(nodes, times or [], strict=False):
                if node in inst.customers:
                    load += inst.demand[node]
                    start.add_var_value(built.u[node], load)
                    start.add_var_value(built.s[node,], t)
    built.model.add_mip_start(start)


def solve(
    inst: Instance,
    formulation: Formulation = "three-index",
    objective: Objective = "distance",
    time_limit: float | None = None,
    mip_gap: float | None = None,
    preprocess: bool = True,
    warm_start: bool = True,
    symmetry_breaking: bool = True,
    capacity_cut: bool = True,
    cuts: bool = False,
    log_output: bool = False,
    stats: dict | None = None,
) -> Solution | None:
    """Solve ``inst``. Returns ``None`` when the instance is infeasible.

    With ``cuts=True`` rounded capacity cuts and 2-path cuts are separated
    in a CPLEX callback (see :mod:`vrptw.cuts`).  ``stats``, if given, is
    filled with solve statistics (nodes, cuts, ...).  The returned distance is
    recomputed from the routes on the original instance, so it is exact
    regardless of preprocessing and objective.
    """
    work = tighten_time_windows(inst) if preprocess else inst
    built = build_model(work, formulation, objective, symmetry_breaking, capacity_cut)
    if time_limit is not None:
        built.model.set_time_limit(time_limit)
    if mip_gap is not None:
        built.model.parameters.mip.tolerances.mipgap = mip_gap
    if warm_start:
        heuristic = construct(work)
        if heuristic is not None:
            add_warm_start(built, heuristic)
    callback = None
    if cuts:
        from vrptw.cuts import install

        callback = install(built.model, work, arc_variables(built))
    sol = built.model.solve(log_output=log_output)
    if stats is not None:
        details = sol.solve_details if sol is not None else built.model.solve_details
        nodes, gap = details.nb_nodes_processed, details.mip_relative_gap
        stats.update(
            status=details.status,
            nodes=nodes if isinstance(nodes, int) else None,  # not reported for multi-objective solves
            time=round(details.time, 3),
            gap=gap if isinstance(gap, float) and gap < 1e6 else None,
            cuts=callback.cuts_added if callback else 0,
            callback_calls=callback.calls if callback else 0,
        )
    if sol is None:
        return None
    routes = tuple(extract_routes(built, sol))
    return Solution(routes=routes, distance=round(sum(route_distance(inst, r) for r in routes), 6))
