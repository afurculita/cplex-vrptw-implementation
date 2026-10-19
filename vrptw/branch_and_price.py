"""Branch-and-price for the VRPTW (set-partitioning master, ESPPRC pricing).

Master problem (LP relaxation, solved with CPLEX through the ``cplex`` API so
columns can be added incrementally)::

    min  sum_r c_r lambda_r
    s.t. sum_r a_ir lambda_r = 1       for every customer i
         sum_r lambda_r      <= v
         lambda_r >= 0

Columns are feasible elementary routes.  New columns come from the pricing
problem in :mod:`vrptw.pricing`.  Branching is done on arc flows
``x_ij = sum_r a_ijr lambda_r``: one child forbids the arc, the other forces
it by forbidding every competing arc.  Columns incompatible with a node's
decisions get an upper bound of zero at that node.  An artificial column
covering all customers at a prohibitive cost keeps every node's LP feasible.
"""

from __future__ import annotations

import heapq
import math
import time as _time
from dataclasses import dataclass, field

from vrptw.data import Instance
from vrptw.heuristic import construct
from vrptw.preprocess import tighten_time_windows
from vrptw.pricing import price
from vrptw.verify import Route, Solution, route_distance, route_schedule

Arc = tuple[int, int]


@dataclass
class BPResult:
    solution: Solution | None
    lower_bound: float
    status: str  # "optimal", "time_limit", "node_limit" or "infeasible"
    nodes: int = 0
    columns: int = 0
    pricing_rounds: int = 0
    root_bound: float = math.nan

    @property
    def upper_bound(self) -> float:
        return self.solution.distance if self.solution else math.inf


def _route_arcs(inst: Instance, route: Route) -> tuple[Arc, ...]:
    nodes = (inst.depot, *route, inst.end_depot)
    return tuple(zip(nodes, nodes[1:], strict=False))


class Master:
    """The restricted master LP, kept in a ``cplex.Cplex`` object."""

    def __init__(self, inst: Instance, big_cost: float):
        import cplex

        self.inst = inst
        self.cpx = cplex.Cplex()
        for stream in (self.cpx.set_log_stream, self.cpx.set_results_stream, self.cpx.set_warning_stream):
            stream(None)
        self.cpx.objective.set_sense(self.cpx.objective.sense.minimize)
        self.customer_rows = {c: f"cover_{c}" for c in inst.customers}
        self.cpx.linear_constraints.add(
            lin_expr=[cplex.SparsePair([], []) for _ in inst.customers],
            senses="E" * inst.n,
            rhs=[1.0] * inst.n,
            names=list(self.customer_rows.values()),
        )
        self.cpx.linear_constraints.add(
            lin_expr=[cplex.SparsePair([], [])], senses="L", rhs=[float(inst.vehicles)], names=["fleet"]
        )
        self.routes: list[Route | None] = []
        self.arcs: list[frozenset[Arc]] = []
        self.index: dict[Route, int] = {}
        # artificial column: covers everybody, uses one vehicle, costs a fortune
        self._add(None, big_cost, list(inst.customers))

    def _add(self, route: Route | None, cost: float, covered: list[int]) -> int:
        import cplex

        rows = [self.customer_rows[c] for c in covered] + ["fleet"]
        self.cpx.variables.add(obj=[cost], lb=[0.0], ub=[1.0], columns=[cplex.SparsePair(rows, [1.0] * len(rows))])
        self.routes.append(route)
        self.arcs.append(frozenset(_route_arcs(self.inst, route)) if route else frozenset())
        if route is not None:
            self.index[route] = len(self.routes) - 1
        return len(self.routes) - 1

    def add_route(self, route: Route) -> bool:
        if route in self.index:
            return False
        self._add(route, route_distance(self.inst, route), list(route))
        return True

    def apply_node(self, forbidden: frozenset[Arc]) -> None:
        bounds = [(k, 0.0 if arcs & forbidden else 1.0) for k, arcs in enumerate(self.arcs)]
        self.cpx.variables.set_upper_bounds(bounds)

    def solve(self) -> tuple[float, list[float], dict[int, float], float]:
        self.cpx.solve()
        if not self.cpx.solution.is_primal_feasible():  # cannot happen thanks to the artificial column
            raise RuntimeError(f"master LP not solved: {self.cpx.solution.get_status_string()}")
        duals = list(self.cpx.solution.get_dual_values())
        customer_duals = {c: duals[k] for k, c in enumerate(self.inst.customers)}
        values = list(self.cpx.solution.get_values())
        return self.cpx.solution.get_objective_value(), values, customer_duals, duals[-1]


@dataclass(order=True)
class _Node:
    bound: float
    order: int
    forbidden: frozenset[Arc] = field(compare=False)


def branch_and_price(
    inst: Instance,
    time_limit: float | None = None,
    node_limit: int | None = None,
    columns_per_round: int = 20,
    preprocess: bool = True,
    log: bool = False,
) -> BPResult:
    """Solve ``inst`` to optimality (minimum distance) by branch-and-price."""
    original = inst
    if preprocess:
        inst = tighten_time_windows(inst)
    started = _time.monotonic()
    big_cost = 100.0 * (1.0 + sum(sum(row) for row in inst.distance))
    master = Master(inst, big_cost)

    incumbent = construct(inst)
    best_routes: tuple[Route, ...] | None = None
    best_cost = math.inf
    if incumbent is not None:
        best_routes, best_cost = incumbent.routes, incumbent.distance
        for route in incumbent.routes:
            if route:
                master.add_route(route)
    for c in inst.customers:  # singleton routes, feasible by validation
        master.add_route((c,))

    def out_of_time() -> bool:
        return time_limit is not None and _time.monotonic() - started > time_limit

    stats = {"nodes": 0, "rounds": 0}
    root_bound = math.nan

    def solve_node(forbidden: frozenset[Arc]) -> tuple[float, list[float]]:
        """Column generation until no negative reduced-cost route exists."""
        master.apply_node(forbidden)
        while True:
            value, lam, customer_duals, fleet_dual = master.solve()
            stats["rounds"] += 1
            if out_of_time():
                return value, lam
            new = price(inst, customer_duals, fleet_dual, forbidden, max_routes=columns_per_round)
            added = sum(master.add_route(route) for _, route in new)
            if not added:
                return value, lam
            master.apply_node(forbidden)

    def arc_flows(lam: list[float]) -> dict[Arc, float]:
        flows: dict[Arc, float] = {}
        for k, value in enumerate(lam):
            if value > 1e-9 and master.routes[k] is not None:
                for arc in master.arcs[k]:
                    flows[arc] = flows.get(arc, 0.0) + value
        return flows

    order = 0
    open_nodes: list[_Node] = [_Node(-math.inf, order, frozenset())]
    status = "optimal"
    while open_nodes:
        if out_of_time():
            status = "time_limit"
            break
        if node_limit is not None and stats["nodes"] >= node_limit:
            status = "node_limit"
            break
        node = heapq.heappop(open_nodes)
        if node.bound >= best_cost - 0.1 + 1e-6:  # distances are multiples of 0.1
            continue
        stats["nodes"] += 1
        value, lam = solve_node(node.forbidden)
        if stats["nodes"] == 1:
            root_bound = value
        if log:
            print(f"node {stats['nodes']}: bound {value:.1f}, incumbent {best_cost:.1f}, columns {len(master.routes)}")
        if value >= best_cost - 0.1 + 1e-6:
            continue
        if lam[0] > 1e-6:  # artificial column still in use: no real solution below the incumbent here
            continue
        flows = arc_flows(lam)
        fractional = [(abs(f - 0.5), arc) for arc, f in flows.items() if 1e-6 < f < 1 - 1e-6]
        if not fractional:
            routes = tuple(master.routes[k] for k, v in enumerate(lam) if v > 0.5 and master.routes[k] is not None)
            cost = sum(route_distance(inst, r) for r in routes)
            if cost < best_cost - 1e-9:
                best_cost, best_routes = cost, routes
            continue
        _, (i, j) = min(fractional)
        forbid_arc = node.forbidden | {(i, j)}
        force_arc = set(node.forbidden)
        if i != inst.depot:
            force_arc |= {(i, k) for k in inst.nodes if k != j and inst.arc_allowed(i, k)}
        if j != inst.end_depot:
            force_arc |= {(k, j) for k in inst.nodes if k != i and inst.arc_allowed(k, j)}
        for forbidden in (frozenset(force_arc), forbid_arc):
            order += 1
            heapq.heappush(open_nodes, _Node(value, order, forbidden))

    if open_nodes and status == "optimal":
        status = "optimal"
    lower_bound = min([n.bound for n in open_nodes] + [best_cost]) if status != "optimal" else best_cost
    if best_routes is None:
        return BPResult(None, lower_bound, "infeasible" if status == "optimal" else status, **_stats(stats, master))
    routes = tuple(r for r in best_routes if r)
    padded = (*routes, *(() for _ in range(original.vehicles - len(routes))))
    for route in routes:
        assert route_schedule(original, route) is not None
    solution = Solution(routes=padded, distance=round(sum(route_distance(original, r) for r in routes), 6))
    return BPResult(solution, round(lower_bound, 6), status, root_bound=root_bound, **_stats(stats, master))


def _stats(stats: dict, master: Master) -> dict:
    return {"nodes": stats["nodes"], "columns": len(master.routes) - 1, "pricing_rounds": stats["rounds"]}
