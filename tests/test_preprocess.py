import unittest

from tests.helpers import random_instance, relaxed_windows, sample_instance
from vrptw.preprocess import tighten_time_windows
from vrptw.verify import brute_force, check_solution


class TestTightenTimeWindows(unittest.TestCase):
    def test_windows_only_shrink_and_depots_are_untouched(self):
        inst = sample_instance()
        tight = tighten_time_windows(inst)
        for i in inst.customers:
            self.assertGreaterEqual(tight.ready[i], inst.ready[i])
            self.assertLessEqual(tight.due[i], inst.due[i])
            self.assertLessEqual(tight.ready[i], tight.due[i])
        for d in (inst.depot, inst.end_depot):
            self.assertEqual((tight.ready[d], tight.due[d]), (inst.ready[d], inst.due[d]))
        self.assertEqual(tight.validate(), [])

    def test_relaxed_windows_get_tightened_by_travel_times(self):
        inst = relaxed_windows(sample_instance())
        tight = tighten_time_windows(inst)
        # nobody can be reached before the travel time from the depot...
        for i in inst.customers:
            self.assertAlmostEqual(tight.ready[i], inst.time[0][i])
            # ...and everybody must leave early enough to get back to the depot
            self.assertAlmostEqual(tight.due[i], inst.due[inst.end_depot] - inst.time[i][inst.end_depot])

    def test_prunes_arcs(self):
        inst = relaxed_windows(sample_instance(), horizon=70)
        tight = tighten_time_windows(inst)
        before = sum(inst.arc_allowed(i, j) for i in inst.nodes for j in inst.nodes)
        after = sum(tight.arc_allowed(i, j) for i in inst.nodes for j in inst.nodes)
        self.assertLess(after, before)

    def test_optimum_is_preserved(self):
        for seed in range(6):
            inst = random_instance(seed)
            tight = tighten_time_windows(inst)
            with self.subTest(seed=seed):
                expected = brute_force(inst)
                got = brute_force(tight)
                if expected is None:
                    self.assertIsNone(got)
                    continue
                self.assertAlmostEqual(got.distance, expected.distance)
                self.assertEqual(check_solution(inst, got.routes), [])

    def test_idempotent(self):
        tight = tighten_time_windows(sample_instance())
        self.assertEqual(tighten_time_windows(tight), tight)


if __name__ == "__main__":
    unittest.main()
