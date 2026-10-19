"""Valid inequalities for the arc formulations, separated in a CPLEX callback.

Two families of cuts on the out-flow ``x(delta+(S))`` of a customer set ``S``:

* **rounded capacity cuts** ``x(delta+(S)) >= ceil(q(S) / Q)`` (Laporte &
  Nobert 1983), which generalise sub-tour elimination;
* **2-path cuts** ``x(delta+(S)) >= 2`` when no single vehicle can serve all
  of ``S`` within the time windows (Kohl et al. 1999); the check is an exact
  TSPTW feasibility test, so ``S`` is kept small.

Candidate sets come from the connected components of the fractional support
graph and from greedily growing sets around each customer.  The cuts are
added through CPLEX's generic callback in the *relaxation* context, i.e. as
user cuts: they tighten the LP bound but are not needed for correctness,
because the time/load propagation constraints already forbid sub-tours.
"""

from __future__ import annotations

import math
from dataclasses import dataclass, field
from typing import Any

from vrptw.data import Instance

Arc = tuple[int, int]


@dataclass(frozen=True)
class Cut:
    customers: frozenset[int]
    rhs: int
    violation: float

    def out_arcs(self, inst: Instance) -> list[Arc]:
        return [
            (i, j) for i in self.customers for j in inst.nodes if j not in self.customers and inst.arc_allowed(i, j)
        ]


def single_vehicle_can_serve(inst: Instance, customers: frozenset[int]) -> bool:
    """Exact TSPTW feasibility check for a route depot -> customers -> depot."""
    if sum(inst.demand[c] for c in customers) > inst.capacity:
        return False
    members = sorted(customers)
    pos = {c: k for k, c in enumerate(members)}
    full = (1 << len(members)) - 1
    best: dict[tuple[int, int], float] = {}
    for c in members:
        t = max(float(inst.ready[c]), inst.ready[inst.depot] + inst.time[inst.depot][c])
        if t <= inst.due[c]:
            best[(1 << pos[c], c)] = t
    for mask in range(1, full + 1):
        for last in members:
            key = (mask, last)
            if key not in best:
                continue
            t = best[key]
            if mask == full:
                if t + inst.time[last][inst.end_depot] <= inst.due[inst.end_depot]:
                    return True
                continue
            for nxt in members:
                bit = 1 << pos[nxt]
                if mask & bit:
                    continue
                arrival = max(float(inst.ready[nxt]), t + inst.time[last][nxt])
                if arrival <= inst.due[nxt]:
                    new_key = (mask | bit, nxt)
                    if arrival < best.get(new_key, math.inf):
                        best[new_key] = arrival
    return False


def out_flow(inst: Instance, flow: dict[Arc, float], customers: frozenset[int]) -> float:
    return sum(v for (i, j), v in flow.items() if i in customers and j not in customers)


def required_vehicles(inst: Instance, customers: frozenset[int], max_path_check: int) -> int:
    rhs = math.ceil(sum(inst.demand[c] for c in customers) / inst.capacity)
    if rhs < 2 and len(customers) <= max_path_check and not single_vehicle_can_serve(inst, customers):
        rhs = 2
    return max(rhs, 1)


def separate(
    inst: Instance,
    flow: dict[Arc, float],
    min_violation: float = 0.05,
    max_set_size: int = 8,
    max_path_check: int = 8,
    max_cuts: int = 20,
) -> list[Cut]:
    """Find violated capacity / 2-path cuts for an arc flow (fractional or not)."""
    customers = list(inst.customers)
    weight: dict[int, dict[int, float]] = {c: {} for c in customers}
    for (i, j), v in flow.items():
        if v > 1e-6 and i in weight and j in weight:
            weight[i][j] = weight[i].get(j, 0.0) + v
            weight[j][i] = weight[j].get(i, 0.0) + v

    candidates: set[frozenset[int]] = set()
    # 1. connected components of the support graph among customers
    unseen = set(customers)
    while unseen:
        stack = [unseen.pop()]
        comp = set(stack)
        while stack:
            c = stack.pop()
            for d in weight[c]:
                if d in unseen:
                    unseen.discard(d)
                    comp.add(d)
                    stack.append(d)
        if len(comp) <= max_set_size:
            candidates.add(frozenset(comp))
    # 2. greedy growth: repeatedly add the customer most connected to the set
    for start in customers:
        comp = {start}
        while len(comp) < max_set_size:
            candidates.add(frozenset(comp))
            gain = {d: sum(weight[c].get(d, 0.0) for c in comp) for d in customers if d not in comp}
            if not gain:
                break
            d, g = max(gain.items(), key=lambda kv: (kv[1], -kv[0]))
            if g <= 1e-6:
                break
            comp.add(d)
        candidates.add(frozenset(comp))

    cuts: list[Cut] = []
    for s in candidates:
        rhs = required_vehicles(inst, s, max_path_check)
        violation = rhs - out_flow(inst, flow, s)
        if violation >= min_violation:
            cuts.append(Cut(s, rhs, violation))
    cuts.sort(key=lambda c: (-c.violation, len(c.customers), sorted(c.customers)))
    return cuts[:max_cuts]


@dataclass
class CutCallback:
    """Generic CPLEX callback that separates cuts on the LP relaxation.

    ``arc_vars`` maps each arc to the docplex variables whose sum is the flow
    on that arc (one variable per vehicle in the three-index model).
    """

    inst: Instance
    arc_vars: dict[Arc, list[Any]]
    min_violation: float = 0.05
    max_set_size: int = 8
    cuts_added: int = 0
    calls: int = 0
    indices: dict[Arc, list[int]] = field(init=False)

    def __post_init__(self) -> None:
        self.indices = {arc: [v.index for v in vs] for arc, vs in self.arc_vars.items()}
        self._all = sorted({k for ks in self.indices.values() for k in ks})

    def invoke(self, context: Any) -> None:
        import cplex

        if not context.in_relaxation():
            return
        self.calls += 1
        values = dict(zip(self._all, context.get_relaxation_point(self._all), strict=True))
        flow = {arc: sum(values[k] for k in ks) for arc, ks in self.indices.items()}
        for cut in separate(self.inst, flow, self.min_violation, self.max_set_size):
            ind = [k for arc in cut.out_arcs(self.inst) for k in self.indices.get(arc, [])]
            if not ind:
                continue
            context.add_user_cut(
                cplex.SparsePair(ind, [1.0] * len(ind)), "G", float(cut.rhs), cplex.callbacks.UseCut.purge, False
            )
            self.cuts_added += 1


def install(model: Any, inst: Instance, arc_vars: dict[Arc, list[Any]], **options: Any) -> CutCallback:
    """Register the cut callback on a docplex model; returns it for statistics."""
    import cplex

    callback = CutCallback(inst, arc_vars, **options)
    model.get_cplex().set_callback(callback, cplex.callbacks.Context.id.relaxation)
    return callback
