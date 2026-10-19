"""Command line interface: ``python -m vrptw --help``."""

from __future__ import annotations

import argparse
import sys
from pathlib import Path

from vrptw.data import read_dat, read_solomon, write_dat
from vrptw.heuristic import construct
from vrptw.verify import brute_force, check_solution, route_schedule


def _print_solution(inst, solution) -> None:
    print(f"Total distance: {solution.distance}")
    print(f"Vehicles used: {solution.vehicles_used} of {inst.vehicles}")
    for k, route in enumerate(solution.routes, start=1):
        if not route:
            print(f"vehicle {k}: idle")
            continue
        times = route_schedule(inst, route)
        assert times is not None
        stops = " -> ".join(f"{node}@{t:g}" for node, t in zip((0, *route, inst.end_depot), times, strict=True))
        print(f"vehicle {k}: {stops}")


def cmd_solve(args: argparse.Namespace) -> int:
    inst = read_dat(args.dat)
    problems = inst.validate()
    if problems:
        print("Invalid instance:", *problems, sep="\n  ", file=sys.stderr)
        return 2
    stats: dict = {}
    if args.brute_force:
        solution = brute_force(inst, objective=args.objective)
    elif args.heuristic:
        solution = construct(inst)
    elif args.method == "branch-and-price":
        from vrptw.branch_and_price import branch_and_price

        if args.objective != "distance":
            print("branch-and-price supports only --objective distance", file=sys.stderr)
            return 2
        result = branch_and_price(inst, time_limit=args.time_limit, preprocess=not args.no_preprocess, log=args.verbose)
        solution = result.solution
        stats = dict(
            status=result.status,
            nodes=result.nodes,
            columns=result.columns,
            pricing_rounds=result.pricing_rounds,
            root_bound=result.root_bound,
            lower_bound=result.lower_bound,
        )
    else:
        from vrptw.model import solve

        solution = solve(
            inst,
            formulation=args.formulation,
            objective=args.objective,
            time_limit=args.time_limit,
            mip_gap=args.mip_gap,
            preprocess=not args.no_preprocess,
            warm_start=not args.no_warm_start,
            cuts=args.cuts,
            log_output=args.verbose,
            stats=stats,
        )
    if solution is None:
        print("No feasible solution.", file=sys.stderr)
        return 1
    violations = check_solution(inst, solution.routes)
    if violations:  # defensive: should never happen
        print("Solver returned an infeasible solution:", *violations, sep="\n  ", file=sys.stderr)
        return 3
    _print_solution(inst, solution)
    if stats:
        print(
            "Statistics: " + ", ".join(f"{k}={v:.1f}" if isinstance(v, float) else f"{k}={v}" for k, v in stats.items())
        )
    return 0


def cmd_convert(args: argparse.Namespace) -> int:
    inst = read_solomon(args.solomon, customers=args.customers, vehicles=args.vehicles)
    write_dat(inst, args.output)
    print(f"Wrote {inst.n} customers, {inst.vehicles} vehicles to {args.output}")
    return 0


def cmd_validate(args: argparse.Namespace) -> int:
    inst = read_dat(args.dat)
    problems = inst.validate()
    if problems:
        print(*problems, sep="\n")
        return 2
    print(f"{Path(args.dat).name}: {inst.n} customers, {inst.vehicles} vehicles, capacity {inst.capacity}: OK")
    return 0


def main(argv: list[str] | None = None) -> int:
    parser = argparse.ArgumentParser(prog="vrptw", description=__doc__)
    sub = parser.add_subparsers(dest="command", required=True)

    p = sub.add_parser("solve", help="solve a .dat instance with CPLEX (docplex)")
    p.add_argument("dat")
    p.add_argument(
        "--method",
        choices=["mip", "branch-and-price"],
        default="mip",
        help="compact MIP (default) or set-partitioning branch-and-price",
    )
    p.add_argument("--formulation", choices=["three-index", "two-index"], default="two-index")
    p.add_argument("--cuts", action="store_true", help="separate capacity and 2-path cuts in a callback (MIP only)")
    p.add_argument(
        "--objective",
        choices=["distance", "lex"],
        default="distance",
        help="'lex' minimises the number of vehicles first, then the distance",
    )
    p.add_argument("--time-limit", type=float, default=None, help="seconds")
    p.add_argument("--mip-gap", type=float, default=None, help="relative MIP gap, e.g. 0.01")
    p.add_argument("--no-preprocess", action="store_true", help="skip the time-window tightening")
    p.add_argument("--no-warm-start", action="store_true", help="do not pass the heuristic solution to CPLEX")
    p.add_argument("--brute-force", action="store_true", help="use the exhaustive reference solver instead")
    p.add_argument("--heuristic", action="store_true", help="only run the construction heuristic")
    p.add_argument("-v", "--verbose", action="store_true", help="show the CPLEX log")
    p.set_defaults(func=cmd_solve)

    p = sub.add_parser("convert", help="convert a Solomon benchmark file to the OPL .dat format")
    p.add_argument("solomon")
    p.add_argument("-o", "--output", required=True)
    p.add_argument("--customers", type=int, default=None, help="keep only the first N customers")
    p.add_argument("--vehicles", type=int, default=None, help="override the fleet size")
    p.set_defaults(func=cmd_convert)

    p = sub.add_parser("validate", help="check a .dat file for data consistency")
    p.add_argument("dat")
    p.set_defaults(func=cmd_validate)

    args = parser.parse_args(argv)
    return args.func(args)


if __name__ == "__main__":
    sys.exit(main())
