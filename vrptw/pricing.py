"""Pricing problem for branch-and-price: elementary shortest path with
resource constraints (ESPPRC), solved by a label-setting algorithm.

A label describes a partial path from the depot: its reduced cost, the time
service starts at its last node, the load collected so far and the set of
customers it has visited (as a bitmask).  Customers that can no longer be
reached from the label (because of time or load) are added to that set, which
makes the dominance rule much stronger (Feillet et al. 2004).
"""

from __future__ import annotations

import heapq
from dataclasses import dataclass

from vrptw.data import Instance
from vrptw.verify import Route


@dataclass(slots=True)
class Label:
    cost: float
    time: float
    load: int
    mask: int  # visited or unreachable customers, bit (c - 1)
    node: int
    path: tuple[int, ...]
    alive: bool = True

    def dominates(self, other: Label) -> bool:
        return (
            self.cost <= other.cost + 1e-9
            and self.time <= other.time + 1e-9
            and self.load <= other.load
            and self.mask & ~other.mask == 0
        )


def price(
    inst: Instance,
    customer_duals: dict[int, float],
    fleet_dual: float,
    forbidden: frozenset[tuple[int, int]] = frozenset(),
    max_routes: int = 20,
    threshold: float = -1e-6,
) -> list[tuple[float, Route]]:
    """Return up to ``max_routes`` routes with reduced cost below ``threshold``.

    The reduced cost of a route is its distance minus the duals of the
    customers it serves minus the dual of the fleet constraint.  Arcs in
    ``forbidden`` are not used (branching decisions).
    """
    depot, end = inst.depot, inst.end_depot
    customers = list(inst.customers)
    succ: dict[int, list[int]] = {
        i: [j for j in inst.nodes if inst.arc_allowed(i, j) and (i, j) not in forbidden] for i in inst.nodes
    }

    def arc_cost(i: int, j: int) -> float:
        dual = fleet_dual if i == depot else customer_duals.get(i, 0.0)
        return inst.distance[i][j] - dual

    def unreachable(mask: int, time: float, load: int, node: int) -> int:
        for c in customers:
            bit = 1 << (c - 1)
            if mask & bit:
                continue
            if load + inst.demand[c] > inst.capacity or max(inst.ready[c], time + inst.time[node][c]) > inst.due[c]:
                mask |= bit
        return mask

    labels: dict[int, list[Label]] = {i: [] for i in inst.nodes}
    start = Label(0.0, float(inst.ready[depot]), 0, 0, depot, (depot,))
    start.mask = unreachable(0, start.time, 0, depot)
    labels[depot].append(start)
    counter = 0
    heap: list[tuple[float, float, int, Label]] = [(start.time, start.cost, counter, start)]
    completed: list[Label] = []

    while heap:
        _, _, _, label = heapq.heappop(heap)
        if not label.alive:
            continue
        if label.node == end:
            completed.append(label)
            continue
        for j in succ[label.node]:
            if j != end and label.mask >> (j - 1) & 1:
                continue
            time = max(float(inst.ready[j]), label.time + inst.time[label.node][j])
            if time > inst.due[j]:
                continue
            load = label.load + (inst.demand[j] if j != end else 0)
            if load > inst.capacity:
                continue
            if j != end and time + inst.time[j][end] > inst.due[end]:
                continue
            mask = label.mask | (1 << (j - 1)) if j != end else label.mask
            if j != end:
                mask = unreachable(mask, time, load, j)
            new = Label(label.cost + arc_cost(label.node, j), time, load, mask, j, (*label.path, j))
            bucket = labels[j]
            if any(old.alive and old.dominates(new) for old in bucket):
                continue
            for old in bucket:
                if old.alive and new.dominates(old):
                    old.alive = False
            bucket[:] = [old for old in bucket if old.alive]
            bucket.append(new)
            counter += 1
            heapq.heappush(heap, (new.time, new.cost, counter, new))

    found = sorted((lab.cost, lab.path[1:-1]) for lab in completed if lab.cost < threshold)
    result: list[tuple[float, Route]] = []
    seen: set[Route] = set()
    for cost, route in found:
        if route and route not in seen:
            seen.add(route)
            result.append((cost, route))
        if len(result) >= max_routes:
            break
    return result
