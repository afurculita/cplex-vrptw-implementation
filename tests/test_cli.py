import contextlib
import io
import tempfile
import unittest
from pathlib import Path

from tests.helpers import FIXTURES, SAMPLE_DAT
from vrptw.__main__ import main
from vrptw.data import read_dat


def run(*argv):
    out, err = io.StringIO(), io.StringIO()
    with contextlib.redirect_stdout(out), contextlib.redirect_stderr(err):
        code = main([str(a) for a in argv])
    return code, out.getvalue(), err.getvalue()


class TestCli(unittest.TestCase):
    def test_validate(self):
        code, out, _ = run("validate", SAMPLE_DAT)
        self.assertEqual(code, 0)
        self.assertIn("5 customers, 5 vehicles", out)

    def test_solve_brute_force(self):
        code, out, _ = run("solve", SAMPLE_DAT, "--brute-force")
        self.assertEqual(code, 0)
        self.assertIn("Total distance: 156.2", out)
        self.assertIn("Vehicles used: 2 of 5", out)
        self.assertIn("vehicle 5: idle", out)

    def test_convert(self):
        with tempfile.TemporaryDirectory() as tmp:
            target = Path(tmp) / "r101_5.dat"
            code, out, _ = run("convert", FIXTURES / "R101_head.txt", "-o", target, "--customers", 5, "--vehicles", 5)
            self.assertEqual(code, 0)
            self.assertEqual(read_dat(target), read_dat(SAMPLE_DAT))

    def test_invalid_data_is_reported(self):
        with tempfile.TemporaryDirectory() as tmp:
            bad = Path(tmp) / "bad.dat"
            bad.write_text(SAMPLE_DAT.read_text().replace("6: 35", "6: 99"))
            code, out, err = run("validate", bad)
            self.assertEqual(code, 2)
            self.assertIn("same coordinates", out)
            code, _, err = run("solve", bad, "--brute-force")
            self.assertEqual(code, 2)
            self.assertIn("Invalid instance", err)


if __name__ == "__main__":
    unittest.main()
