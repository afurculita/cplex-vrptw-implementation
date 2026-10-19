import unittest

from tests.helpers import random_instance, relaxed_windows, sample_instance
from vrptw.cuts import out_flow, required_vehicles, separate, single_vehicle_can_serve
from vrptw.data import Instance
from vrptw.verify import brute_force, check_solution


def clustered_instance(vehicles: int = 4) -> Instance:
    """Three tight clusters of two customers; capacity forces one cluster per vehicle."""
    coords = [(0, 0), (10, 0), (11, 0), (0, 10), (0, 11), (-10, -10), (-11, -10), (0, 0)]
    return Instance(
        vehicles=vehicles,
        capacity=10,
        demand=(0, 5, 5, 5, 5, 5, 5, 0),
        ready=(0,) * 8,
        due=(500,) * 8,
        service=(0, 1, 1, 1, 1, 1, 1, 0),
        x=tuple(c[0] for c in coords),
        y=tuple(c[1] for c in coords),
        name="clustered",
    )


class TestSeparation(unittest.TestCase):
    def test_single_vehicle_check(self):
        inst = sample_instance()
        self.assertTrue(single_vehicle_can_serve(inst, frozenset({5, 3, 1})))
        self.assertTrue(single_vehicle_can_serve(inst, frozenset({1, 2})), "2 then 1 works: 2@50, 1@161")
        self.assertFalse(
            single_vehicle_can_serve(inst, frozenset({2, 5})), "5@34 -> 2 arrives 67.8 > 60; 2@50 -> 5 late"
        )
        self.assertFalse(single_vehicle_can_serve(inst.with_vehicles(1), frozenset(inst.customers)))

    def test_required_vehicles(self):
        inst = sample_instance()
        self.assertEqual(required_vehicles(inst, frozenset({2, 5}), 8), 2)
        self.assertEqual(required_vehicles(inst, frozenset({1, 2}), 8), 1)
        self.assertEqual(required_vehicles(inst, frozenset({5}), 8), 1)
        self.assertEqual(required_vehicles(clustered_instance(), frozenset({1, 2, 3}), 8), 2)

    def test_fractional_point_is_cut_off(self):
        inst = clustered_instance()
        # A fractional flow: 1 and 2 form a near-cycle with only half a vehicle
        # entering, while the other clusters are served by proper routes.
        flow = {(0, 1): 0.5, (1, 2): 1.0, (2, 1): 0.5, (2, 7): 0.5}
        flow.update({(0, 3): 1.0, (3, 4): 1.0, (4, 7): 1.0, (0, 5): 1.0, (5, 6): 1.0, (6, 7): 1.0})
        cuts = separate(inst, flow)
        self.assertTrue(cuts)
        best = cuts[0]
        self.assertEqual(best.customers, frozenset({1, 2}))
        self.assertEqual(best.rhs, 1)
        self.assertAlmostEqual(out_flow(inst, flow, best.customers), 0.5)
        self.assertAlmostEqual(best.violation, 0.5)
        self.assertEqual(
            sorted(best.out_arcs(inst)),
            [(1, 3), (1, 4), (1, 5), (1, 6), (1, 7), (2, 3), (2, 4), (2, 5), (2, 6), (2, 7)],
        )

    def test_integral_solution_has_no_violated_cut(self):
        inst = sample_instance()
        sol = brute_force(inst)
        flow = {}
        for route in sol.routes:
            nodes = (0, *route, inst.end_depot)
            for a, b in zip(nodes, nodes[1:], strict=False):
                flow[(a, b)] = 1.0
        self.assertEqual(separate(inst, flow), [])


class TestBranchAndCut(unittest.TestCase):
    def setUp(self):
        try:
            import docplex.mp.model  # noqa: F401
        except ImportError:  # pragma: no cover
            self.skipTest("docplex not installed")

    def test_cuts_do_not_change_the_optimum(self):
        from vrptw.model import solve

        for inst in (sample_instance(), relaxed_windows(sample_instance()), clustered_instance()):
            for formulation in ("two-index", "three-index"):
                stats: dict = {}
                sol = solve(inst, formulation=formulation, cuts=True, stats=stats)
                with self.subTest(instance=inst.name, formulation=formulation):
                    self.assertEqual(check_solution(inst, sol.routes), [])
                    self.assertAlmostEqual(sol.distance, brute_force(inst).distance, places=6)
                    self.assertIn("cuts", stats)

    def test_cuts_are_separated_on_random_instances(self):
        from vrptw.model import solve

        total_cuts = 0
        for seed in range(6):
            inst = random_instance(seed, customers=8, vehicles=4, capacity=30)
            stats: dict = {}
            sol = solve(inst, formulation="two-index", cuts=True, warm_start=False, capacity_cut=False, stats=stats)
            expected = brute_force(inst)
            if expected is None:
                self.assertIsNone(sol)
                continue
            self.assertAlmostEqual(sol.distance, expected.distance, places=6)
            total_cuts += stats["cuts"]
        self.assertGreater(total_cuts, 0, "the callback should have added at least one user cut")


if __name__ == "__main__":
    unittest.main()
