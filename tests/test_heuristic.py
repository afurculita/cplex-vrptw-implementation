import unittest

from tests.helpers import random_instance, relaxed_windows, sample_instance
from vrptw.heuristic import construct, nearest_neighbour, relocate
from vrptw.verify import brute_force, check_solution


class TestHeuristic(unittest.TestCase):
    def test_sample(self):
        inst = sample_instance()
        sol = construct(inst)
        self.assertIsNotNone(sol)
        self.assertEqual(check_solution(inst, sol.routes), [])
        self.assertEqual(len(sol.routes), inst.vehicles)
        self.assertGreaterEqual(sol.distance, brute_force(inst).distance - 1e-9)

    def test_relocate_never_worsens(self):
        for seed in range(6):
            inst = random_instance(seed)
            initial = nearest_neighbour(inst)
            if initial is None:
                continue
            improved = relocate(inst, list(initial.routes))
            with self.subTest(seed=seed):
                self.assertEqual(check_solution(inst, improved), [])
                self.assertLessEqual(construct(inst).distance, initial.distance + 1e-9)

    def test_relaxed_windows_use_one_vehicle(self):
        inst = relaxed_windows(sample_instance())
        sol = construct(inst)
        self.assertEqual(sol.vehicles_used, 1)

    def test_fleet_too_small(self):
        self.assertIsNone(construct(sample_instance().with_vehicles(1)))


if __name__ == "__main__":
    unittest.main()
