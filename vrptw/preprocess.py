"""Time-window reduction (Desrochers, Desrosiers & Solomon 1992).

Tightening the windows is *sound*: every route that is feasible for the
original windows is feasible for the reduced ones, so the optimum does not
change, but fewer arcs are time-compatible and every big-M becomes smaller,
which strengthens the LP relaxation of the model.
"""

from __future__ import annotations

from vrptw.data import Instance


def tighten_time_windows(inst: Instance, max_rounds: int = 100) -> Instance:
    """Return a copy of ``inst`` with reduced customer time windows.

    Two necessary conditions are applied until a fixed point is reached:

    * service at ``j`` cannot start before the earliest arrival from any
      time-compatible predecessor: ``a_j := max(a_j, min_i (a_i + t_ij))``;
    * service at ``j`` must leave enough time to reach some time-compatible
      successor: ``b_j := min(b_j, max_k (b_k - t_jk))``.

    The depot windows are left unchanged. A customer that becomes unreachable
    keeps a window that no arc can satisfy, so the model stays infeasible
    rather than silently wrong.
    """
    ready = list(map(float, inst.ready))
    due = list(map(float, inst.due))
    t = inst.time
    depot, end = inst.depot, inst.end_depot
    preds = {j: [i for i in inst.nodes if i != j and i != end] for j in inst.customers}
    succs = {j: [k for k in inst.nodes if k != j and k != depot] for j in inst.customers}

    for _ in range(max_rounds):
        changed = False
        for j in inst.customers:
            arrivals = [ready[i] + t[i][j] for i in preds[j] if ready[i] + t[i][j] <= due[j]]
            if arrivals:
                new_ready = max(ready[j], min(arrivals))
                if new_ready > ready[j] + 1e-9:
                    ready[j] = new_ready
                    changed = True
            departures = [due[k] - t[j][k] for k in succs[j] if ready[j] + t[j][k] <= due[k]]
            if departures:
                new_due = min(due[j], max(departures))
                if new_due < due[j] - 1e-9:
                    due[j] = new_due
                    changed = True
        if not changed:
            break

    return Instance(
        vehicles=inst.vehicles,
        capacity=inst.capacity,
        demand=inst.demand,
        ready=tuple(ready),
        due=tuple(due),
        service=inst.service,
        x=inst.x,
        y=inst.y,
        name=inst.name,
    )
