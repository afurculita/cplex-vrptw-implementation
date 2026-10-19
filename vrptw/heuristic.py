"""Construction heuristic and local search, used to warm-start the MIP.

The construction is a time-oriented nearest-neighbour heuristic in the spirit
of Solomon (1987): routes are built one after the other and the next customer
is the unserved one that can be reached earliest.  A relocate local search
then moves single customers between positions while feasibility holds.
"""

from __future__ import annotations

from vrptw.data import Instance
from vrptw.verify import Route, Solution, route_distance, route_schedule


def nearest_neighbour(inst: Instance) -> Solution | None:
    """Build routes greedily. Returns ``None`` if more than ``v`` routes are needed."""
    unserved = set(inst.customers)
    routes: list[Route] = []
    while unserved:
        if len(routes) == inst.vehicles:
            return None
        route: list[int] = []
        load = 0
        now = float(inst.ready[inst.depot])
        node = inst.depot
        while True:
            best: tuple[float, float, int] | None = None
            for c in unserved:
                if load + inst.demand[c] > inst.capacity:
                    continue
                arrival = max(float(inst.ready[c]), now + inst.time[node][c])
                if arrival > inst.due[c] or arrival + inst.time[c][inst.end_depot] > inst.due[inst.end_depot]:
                    continue
                key = (arrival - now, inst.due[c] - arrival, c)  # earliest arrival, then urgency
                if best is None or key < best:
                    best = key
            if best is None:
                break
            c = best[2]
            now = max(float(inst.ready[c]), now + inst.time[node][c])
            load += inst.demand[c]
            route.append(c)
            unserved.discard(c)
            node = c
        if not route:
            return None  # a remaining customer fits in no route at all
        routes.append(tuple(route))
    return _solution(inst, routes)


def relocate(inst: Instance, routes: list[Route]) -> list[Route]:
    """Move single customers to the cheapest feasible position until no move improves."""
    routes = [list(r) for r in routes if r]
    improved = True
    while improved:
        improved = False
        for src in range(len(routes)):
            for pos in range(len(routes[src])):
                customer = routes[src][pos]
                base = routes[src][:pos] + routes[src][pos + 1 :]
                delta_remove = route_distance(inst, tuple(base)) - route_distance(inst, tuple(routes[src]))
                if route_schedule(inst, tuple(base)) is None:
                    continue
                best_move: tuple[float, int, int] | None = None
                targets = list(range(len(routes))) + ([len(routes)] if len(routes) < inst.vehicles else [])
                for dst in targets:
                    target = base if dst == src else (routes[dst] if dst < len(routes) else [])
                    load = sum(inst.demand[c] for c in target) + inst.demand[customer]
                    if dst != src and load > inst.capacity:
                        continue
                    old = route_distance(inst, tuple(target))
                    for ins in range(len(target) + 1):
                        candidate = tuple(target[:ins] + [customer] + target[ins:])
                        if route_schedule(inst, candidate) is None:
                            continue
                        delta = route_distance(inst, candidate) - old + (delta_remove if dst != src else 0.0)
                        if dst == src:
                            delta = route_distance(inst, candidate) - route_distance(inst, tuple(routes[src]))
                        if delta < -1e-9 and (best_move is None or delta < best_move[0]):
                            best_move = (delta, dst, ins)
                if best_move is None:
                    continue
                _, dst, ins = best_move
                if dst == src:
                    routes[src] = base[:ins] + [customer] + base[ins:]
                else:
                    routes[src] = base
                    if dst == len(routes):
                        routes.append([customer])
                    else:
                        routes[dst] = routes[dst][:ins] + [customer] + routes[dst][ins:]
                routes = [r for r in routes if r]
                improved = True
                break
            if improved:
                break
    return [tuple(r) for r in routes]


def construct(inst: Instance, improve: bool = True) -> Solution | None:
    """Nearest-neighbour construction followed (optionally) by relocate."""
    initial = nearest_neighbour(inst)
    if initial is None:
        return None
    routes = [r for r in initial.routes if r]
    if improve:
        routes = relocate(inst, routes)
    return _solution(inst, routes)


def _solution(inst: Instance, routes: list[Route]) -> Solution:
    idle = inst.vehicles - len(routes)
    padded = (*routes, *(() for _ in range(idle)))
    return Solution(routes=padded, distance=round(sum(route_distance(inst, r) for r in routes), 6))
