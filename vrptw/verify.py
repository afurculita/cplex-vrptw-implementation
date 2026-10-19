"""Solver-independent tools: a feasibility checker and a brute-force solver.

Both operate on plain routes (lists of customer indices), so they can be used
to validate the output of ``VRPTW.mod``, of :mod:`vrptw.model` or of any other
VRPTW solver.
"""

from __future__ import annotations

from dataclasses import dataclass
from itertools import permutations

from vrptw.data import Instance

Route = tuple[int, ...]


@dataclass(frozen=True)
class Solution:
    routes: tuple[Route, ...]  # one entry per vehicle; empty tuple = idle
    distance: float

    @property
    def vehicles_used(self) -> int:
        return sum(1 for r in self.routes if r)


def route_schedule(inst: Instance, route: Route) -> list[float] | None:
    """Earliest feasible start-of-service times along a route, or ``None``.

    Service at the first node starts at the depot's ready time; a vehicle may
    wait at a customer until its window opens but can never arrive late.
    """
    t = float(inst.ready[inst.depot])
    times = [t]
    prev = inst.depot
    for node in (*route, inst.end_depot):
        t = max(float(inst.ready[node]), t + inst.time[prev][node])
        if t > inst.due[node] + 1e-6:
            return None
        times.append(t)
        prev = node
    return times


def route_distance(inst: Instance, route: Route) -> float:
    if not route:
        return 0.0
    nodes = (inst.depot, *route, inst.end_depot)
    return sum(inst.distance[a][b] for a, b in zip(nodes, nodes[1:], strict=False))


def check_solution(inst: Instance, routes: list[Route] | tuple[Route, ...]) -> list[str]:
    """Return every constraint violated by ``routes`` (empty if feasible)."""
    problems: list[str] = []
    if len(routes) > inst.vehicles:
        problems.append(f"{len(routes)} routes but only {inst.vehicles} vehicles")
    seen: dict[int, int] = {}
    for r_idx, route in enumerate(routes):
        for c in route:
            if c not in inst.customers:
                problems.append(f"route {r_idx}: {c} is not a customer")
            seen[c] = seen.get(c, 0) + 1
        if not all(c in inst.customers for c in route):
            continue
        load = sum(inst.demand[c] for c in route)
        if load > inst.capacity:
            problems.append(f"route {r_idx}: load {load} exceeds capacity {inst.capacity}")
        if route_schedule(inst, route) is None:
            problems.append(f"route {r_idx}: time windows cannot be met")
    for c in inst.customers:
        if seen.get(c, 0) != 1:
            problems.append(f"customer {c} visited {seen.get(c, 0)} times (expected 1)")
    return problems


def brute_force(inst: Instance, max_customers: int = 8) -> Solution | None:
    """Exact solution by exhaustive enumeration, for small instances only.

    Every subset of customers is tried in every order to get the cheapest
    feasible single route; a set-partitioning DP then combines routes.
    Returns ``None`` when no feasible solution exists.
    """
    n = inst.n
    if n > max_customers:
        raise ValueError(f"brute force is limited to {max_customers} customers")
    custs = list(inst.customers)
    full = (1 << n) - 1
    best_route: dict[int, tuple[float, Route]] = {}
    for mask in range(1, full + 1):
        members = [custs[b] for b in range(n) if mask >> b & 1]
        if sum(inst.demand[c] for c in members) > inst.capacity:
            continue
        best: tuple[float, Route] | None = None
        for perm in permutations(members):
            if route_schedule(inst, perm) is None:
                continue
            d = route_distance(inst, perm)
            if best is None or d < best[0] - 1e-9:
                best = (d, perm)
        if best is not None:
            best_route[mask] = best

    INF = float("inf")
    # dp[used][mask] = (cost, routes) covering ``mask`` with ``used`` vehicles
    dp: list[dict[int, tuple[float, tuple[Route, ...]]]] = [{0: (0.0, ())}]
    for _ in range(inst.vehicles):
        prev = dp[-1]
        cur: dict[int, tuple[float, tuple[Route, ...]]] = {}
        for mask, (cost, routes) in prev.items():
            remaining = full & ~mask
            if not remaining:
                continue
            lowest = remaining & -remaining  # always serve the lowest unserved customer next
            sub = remaining
            while sub:
                if sub & lowest and sub in best_route:
                    rc, r = best_route[sub]
                    new_mask = mask | sub
                    if cost + rc < cur.get(new_mask, (INF, ()))[0] - 1e-9:
                        cur[new_mask] = (cost + rc, (*routes, r))
                sub = (sub - 1) & remaining
        dp.append(cur)
    candidates = [layer[full] for layer in dp if full in layer]
    if not candidates:
        return None
    cost, routes = min(candidates, key=lambda c: c[0])
    padded = (*routes, *(() for _ in range(inst.vehicles - len(routes))))
    return Solution(routes=padded, distance=round(cost, 6))
