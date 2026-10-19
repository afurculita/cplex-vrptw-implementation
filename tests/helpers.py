"""Shared fixtures for the test-suite."""

from __future__ import annotations

import random
from pathlib import Path

from vrptw.data import Instance, read_dat

ROOT = Path(__file__).resolve().parent.parent
SAMPLE_DAT = ROOT / "VRPTW.dat"
MODEL_FILE = ROOT / "VRPTW.mod"
FIXTURES = Path(__file__).resolve().parent / "fixtures"


def sample_instance() -> Instance:
    return read_dat(SAMPLE_DAT)


def relaxed_windows(inst: Instance, horizon: int = 1000) -> Instance:
    """Open every time window so the instance degenerates to a CVRP."""
    return Instance(
        vehicles=inst.vehicles,
        capacity=inst.capacity,
        demand=inst.demand,
        ready=tuple(0 for _ in inst.nodes),
        due=tuple(horizon for _ in inst.nodes),
        service=inst.service,
        x=inst.x,
        y=inst.y,
        name=inst.name + "-relaxed",
    )


def random_instance(seed: int, customers: int = 5, vehicles: int = 3, capacity: int = 50) -> Instance:
    """A small random but always valid instance (deterministic for a seed)."""
    rng = random.Random(seed)
    while True:
        xs = [rng.randint(0, 40) for _ in range(customers)]
        ys = [rng.randint(0, 40) for _ in range(customers)]
        demand = [rng.randint(1, capacity // 2) for _ in range(customers)]
        ready = [rng.randint(0, 150) for _ in range(customers)]
        due = [r + rng.randint(20, 80) for r in ready]
        inst = Instance(
            vehicles=vehicles,
            capacity=capacity,
            demand=(0, *demand, 0),
            ready=(0, *ready, 0),
            due=(400, *due, 400),
            service=(0, *(10 for _ in range(customers)), 0),
            x=(20, *xs, 20),
            y=(20, *ys, 20),
            name=f"random-{seed}",
        )
        if not inst.validate():
            return inst
        seed += 1000
        rng = random.Random(seed)
