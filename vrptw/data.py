"""Instance representation and file formats.

Node numbering follows the OPL model: node ``0`` is the starting depot, nodes
``1..n`` are the customers and node ``n + 1`` is a copy of the depot that every
route ends at.  All per-node arrays therefore have ``n + 2`` entries.
"""

from __future__ import annotations

import math
import re
from collections.abc import Sequence
from dataclasses import dataclass, field
from pathlib import Path


def truncated_distance(x1: float, y1: float, x2: float, y2: float) -> float:
    """Euclidean distance truncated to one decimal, as in ``VRPTW.mod``.

    Truncation (not rounding) to one decimal is the convention used for the
    Solomon benchmark results, so published optimal values can be reproduced.
    """
    return math.floor(math.hypot(x1 - x2, y1 - y2) * 10) / 10


@dataclass(frozen=True)
class Instance:
    """A VRPTW instance with ``n`` customers and ``n + 2`` nodes."""

    vehicles: int
    capacity: int
    demand: tuple[int, ...]  # length n + 2, zero at both depots
    ready: tuple[int, ...]  # earliest start of service per node (LBTW)
    due: tuple[int, ...]  # latest start of service per node (UBTW)
    service: tuple[int, ...]  # service duration per node
    x: tuple[int, ...]
    y: tuple[int, ...]
    name: str = field(default="instance", compare=False)
    distance: tuple[tuple[float, ...], ...] = field(init=False, repr=False, compare=False)
    time: tuple[tuple[float, ...], ...] = field(init=False, repr=False, compare=False)

    def __post_init__(self) -> None:
        n_nodes = len(self.x)
        for attr in ("demand", "ready", "due", "service", "y"):
            if len(getattr(self, attr)) != n_nodes:
                raise ValueError(f"{attr} must have {n_nodes} entries, one per node")
        if n_nodes < 2:
            raise ValueError("an instance needs at least the two depot nodes")
        if self.vehicles < 1:
            raise ValueError("at least one vehicle is required")
        distance = tuple(
            tuple(
                0.0 if i == j else truncated_distance(self.x[i], self.y[i], self.x[j], self.y[j])
                for j in range(n_nodes)
            )
            for i in range(n_nodes)
        )
        # Travel time from i to j includes the service time at i, exactly as
        # ``Time[i][j] = Distance[i][j] + ServiceTime[i]`` in the OPL model.
        time = tuple(
            tuple(0.0 if i == j else distance[i][j] + self.service[i] for j in range(n_nodes)) for i in range(n_nodes)
        )
        object.__setattr__(self, "distance", distance)
        object.__setattr__(self, "time", time)

    @property
    def n(self) -> int:
        """Number of customers."""
        return len(self.x) - 2

    @property
    def depot(self) -> int:
        return 0

    @property
    def end_depot(self) -> int:
        return self.n + 1

    @property
    def nodes(self) -> range:
        return range(self.n + 2)

    @property
    def customers(self) -> range:
        return range(1, self.n + 1)

    def big_m(self, i: int, j: int) -> float:
        """Smallest valid big-M for the time propagation constraint on arc (i, j)."""
        return max(0.0, self.due[i] + self.time[i][j] - self.ready[j])

    def arc_allowed(self, i: int, j: int) -> bool:
        """Arcs that can appear in a route.

        No self loops, nothing enters the start depot, nothing leaves the end
        depot and the arc must be compatible with the time windows.
        """
        if i == j or j == self.depot or i == self.end_depot:
            return False
        return self.ready[i] + self.time[i][j] <= self.due[j]

    def validate(self) -> list[str]:
        """Return a list of data problems (empty when the data is consistent)."""
        problems: list[str] = []
        n1 = self.end_depot
        if self.demand[0] != 0 or self.demand[n1] != 0:
            problems.append("depot nodes must have zero demand")
        if (self.x[0], self.y[0]) != (self.x[n1], self.y[n1]):
            problems.append("the end depot must have the same coordinates as the start depot")
        if self.service[0] != 0 or self.service[n1] != 0:
            problems.append("depot nodes must have zero service time")
        if (self.ready[0], self.due[0]) != (self.ready[n1], self.due[n1]):
            problems.append("the end depot must have the same time window as the start depot")
        for i in self.nodes:
            if self.ready[i] > self.due[i]:
                problems.append(f"node {i}: time window lower bound exceeds upper bound")
        for i in self.customers:
            if self.demand[i] > self.capacity:
                problems.append(f"customer {i}: demand exceeds vehicle capacity")
            if self.demand[i] < 0:
                problems.append(f"customer {i}: negative demand")
            if not self.arc_allowed(0, i) or not self.arc_allowed(i, n1):
                problems.append(f"customer {i}: cannot be served within its time window")
        return problems

    def with_vehicles(self, vehicles: int) -> Instance:
        return Instance(
            vehicles=vehicles,
            capacity=self.capacity,
            demand=self.demand,
            ready=self.ready,
            due=self.due,
            service=self.service,
            x=self.x,
            y=self.y,
            name=self.name,
        )


# ---------------------------------------------------------------------------
# OPL .dat format
# ---------------------------------------------------------------------------

_COMMENT_RE = re.compile(r"/\*.*?\*/|//[^\n]*", re.S)
_STATEMENT_RE = re.compile(r"(\w+)\s*=\s*(.*?);", re.S)
_ENTRY_RE = re.compile(r"(-?\d+)\s*:\s*(-?\d+(?:\.\d+)?)")

#: Arrays the OPL model reads, with their index range as (first, last) where
#: ``last`` is relative to ``CustomersNumber`` (Demand is indexed over the
#: customers only, the other arrays over all nodes including both depots).
DAT_ARRAYS = {
    "Demand": (1, 0),
    "ServiceTime": (0, 1),
    "XCoord": (0, 1),
    "YCoord": (0, 1),
    "LBTW": (0, 1),
    "UBTW": (0, 1),
}
DAT_SCALARS = ("v", "CustomersNumber", "Capacity")


def parse_dat(text: str) -> dict[str, int | dict[int, float]]:
    """Parse the subset of the OPL ``.dat`` syntax used by ``VRPTW.dat``.

    Supports integer scalars (``name = 3;``) and indexed arrays
    (``name = #[ 0: 1, 1: 2 ]#;``).
    """
    text = _COMMENT_RE.sub("", text)
    values: dict[str, int | dict[int, float]] = {}
    for name, raw in _STATEMENT_RE.findall(text):
        raw = raw.strip()
        if raw.startswith("#[") and raw.endswith("]#"):
            body = raw[2:-2]
            entries = _ENTRY_RE.findall(body)
            if len(entries) != len([p for p in body.split(",") if p.strip()]):
                raise ValueError(f"{name}: malformed indexed array")
            values[name] = {int(k): float(v) for k, v in entries}
        else:
            values[name] = int(raw)
    return values


def instance_from_dat_values(values: dict, name: str = "instance") -> Instance:
    """Build an :class:`Instance` from parsed ``.dat`` values."""
    missing = [k for k in (*DAT_SCALARS, *DAT_ARRAYS) if k not in values]
    if missing:
        raise ValueError(f"missing data: {', '.join(missing)}")
    n = int(values["CustomersNumber"])
    nodes = range(n + 2)

    def column(key: str) -> tuple[int, ...]:
        arr = values[key]
        first, last = DAT_ARRAYS[key]
        expected = set(range(first, n + last + 1))
        if set(arr) != expected:
            raise ValueError(f"{key}: expected indices {first}..{n + last}, got {sorted(arr)}")
        return tuple(int(arr.get(i, 0)) for i in nodes)

    return Instance(
        vehicles=int(values["v"]),
        capacity=int(values["Capacity"]),
        demand=column("Demand"),
        ready=column("LBTW"),
        due=column("UBTW"),
        service=column("ServiceTime"),
        x=column("XCoord"),
        y=column("YCoord"),
        name=name,
    )


def read_dat(path: str | Path) -> Instance:
    """Read an instance from an OPL ``.dat`` file."""
    path = Path(path)
    return instance_from_dat_values(parse_dat(path.read_text()), name=path.stem)


def format_dat(inst: Instance) -> str:
    """Serialise an instance in the ``.dat`` format expected by ``VRPTW.mod``."""

    def array(name: str, values: Sequence[int], start: int, stop: int) -> str:
        rows = ",\n".join(f"\t{i}: {values[i]}" for i in range(start, stop))
        return f"{name} = #[\n{rows}\n]#;\n"

    out = [
        f"// {inst.name}: {inst.n} customers, node 0 is the depot, node {inst.end_depot} is its copy\n",
        f"v = {inst.vehicles};\n",
        f"CustomersNumber = {inst.n};\n",
        f"Capacity = {inst.capacity};\n\n",
        array("Demand", inst.demand, 1, inst.n + 1),
        "\n",
        array("ServiceTime", inst.service, 0, inst.n + 2),
        "\n",
        array("XCoord", inst.x, 0, inst.n + 2),
        "\n",
        array("YCoord", inst.y, 0, inst.n + 2),
        "\n",
        array("LBTW", inst.ready, 0, inst.n + 2),
        "\n",
        array("UBTW", inst.due, 0, inst.n + 2),
    ]
    return "".join(out)


def write_dat(inst: Instance, path: str | Path) -> None:
    Path(path).write_text(format_dat(inst))


# ---------------------------------------------------------------------------
# Solomon benchmark format
# ---------------------------------------------------------------------------


def parse_solomon(text: str, customers: int | None = None, vehicles: int | None = None) -> Instance:
    """Parse a Solomon (1987) benchmark file such as ``R101.txt``.

    The file lists the depot as customer ``0`` followed by the customers with
    columns ``id x y demand ready due service``.  ``customers`` keeps only the
    first ``customers`` customers (the usual 25/50/100 subsets) and
    ``vehicles`` overrides the fleet size from the header.
    """
    lines = [ln.strip() for ln in text.splitlines()]
    non_empty = [ln for ln in lines if ln]
    if not non_empty:
        raise ValueError("empty Solomon file")
    name = non_empty[0]
    fleet: tuple[int, int] | None = None
    rows: list[tuple[int, ...]] = []
    for ln in non_empty[1:]:
        parts = ln.split()
        if not all(re.fullmatch(r"-?\d+(\.\d+)?", p) for p in parts):
            continue  # header line
        nums = tuple(int(float(p)) for p in parts)
        if len(nums) == 2 and fleet is None:
            fleet = (nums[0], nums[1])
        elif len(nums) == 7:
            rows.append(nums)
        else:
            raise ValueError(f"unexpected line in Solomon file: {ln!r}")
    if fleet is None or not rows:
        raise ValueError("Solomon file is missing the vehicle header or customer rows")
    if rows[0][0] != 0:
        raise ValueError("the first customer row must be the depot (id 0)")
    depot, custs = rows[0], rows[1:]
    if customers is not None:
        custs = custs[:customers]
    nodes = [depot, *custs, depot]
    return Instance(
        vehicles=vehicles if vehicles is not None else fleet[0],
        capacity=fleet[1],
        demand=tuple(r[3] for r in nodes),
        ready=tuple(r[4] for r in nodes),
        due=tuple(r[5] for r in nodes),
        service=tuple(r[6] for r in nodes),
        x=tuple(r[1] for r in nodes),
        y=tuple(r[2] for r in nodes),
        name=name,
    )


def read_solomon(path: str | Path, customers: int | None = None, vehicles: int | None = None) -> Instance:
    return parse_solomon(Path(path).read_text(), customers=customers, vehicles=vehicles)
