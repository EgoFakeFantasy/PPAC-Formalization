"""Regressions for the actual Windows/Linux source-lock mismatch."""
import hashlib
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path
from source_hash import source_sha256


class SourceHashTests(unittest.TestCase):
    def digest(self, data: bytes, suffix: str = ".lean") -> str:
        with tempfile.TemporaryDirectory() as folder:
            path = Path(folder) / ("source" + suffix)
            path.write_bytes(data)
            return source_sha256(path)

    def test_lf_and_crlf_have_the_same_locked_hash(self):
        data = "theorem 中文 : ℕ = ℕ := rfl\n-- tail\n".encode()
        self.assertEqual(self.digest(data), hashlib.sha256(data).hexdigest())
        self.assertEqual(self.digest(data.replace(b"\n", b"\r\n")), self.digest(data))

    def test_real_content_change_is_rejected(self):
        self.assertNotEqual(self.digest(b"theorem x := True\n"), self.digest(b"theorem x := False\n"))

    def test_whitespace_and_lone_cr_are_not_discarded(self):
        self.assertNotEqual(self.digest(b"x y\n"), self.digest(b"x  y\n"))
        self.assertNotEqual(self.digest(b"x\ry\n"), self.digest(b"x\ny\n"))

    def test_utf8_bom_is_retained(self):
        self.assertNotEqual(self.digest(b"x\n"), self.digest(b"\xef\xbb\xbfx\n"))

    def test_binary_archive_cannot_use_source_hash(self):
        with self.assertRaises(ValueError):
            self.digest(b"PK\x03\x04\r\n", ".zip")


class SetupDownloadRetryTests(unittest.TestCase):
    retry = Path(__file__).with_name("ci_retry.py")

    def exercise(self, threshold):
        with tempfile.TemporaryDirectory() as folder:
            counter = Path(folder) / "counter.txt"
            child = Path(folder) / "setup command.py"
            child.write_text(
                "import pathlib, sys\n"
                "p = pathlib.Path(sys.argv[1])\n"
                "n = int(p.read_text()) + 1 if p.exists() else 1\n"
                "p.write_text(str(n))\n"
                "assert sys.argv[3] == 'literal space ; $value'\n"
                "sys.exit(0 if n >= int(sys.argv[2]) else 7)\n",
                encoding="utf-8",
            )
            result = subprocess.run(
                [sys.executable, str(self.retry), "--delay", "0", "--",
                 sys.executable, str(child), str(counter), str(threshold), "literal space ; $value"],
                capture_output=True,
            )
            return result.returncode, int(counter.read_text())

    def test_transient_download_failure_recovers_and_stops(self):
        self.assertEqual(self.exercise(3), (0, 3))

    def test_persistent_failure_is_bounded_and_remains_failure(self):
        self.assertEqual(self.exercise(9), (7, 4))

    def test_binary_download_replaces_partial_bytes_without_retry_log_pollution(self):
        with tempfile.TemporaryDirectory() as folder:
            counter = Path(folder) / "counter.txt"
            artifact = Path(folder) / "setup artifact.bin"
            child = Path(folder) / "download.py"
            child.write_text(
                "import pathlib, sys\n"
                "p = pathlib.Path(sys.argv[1])\n"
                "n = int(p.read_text()) + 1 if p.exists() else 1\n"
                "p.write_text(str(n))\n"
                "sys.stdout.buffer.write(b'partial' if n == 1 else b'\\x1f\\x8b\\xff\\x00\\r\\n')\n"
                "sys.exit(7 if n == 1 else 0)\n",
                encoding="utf-8",
            )
            result = subprocess.run(
                [sys.executable, str(self.retry), "--delay", "0", "--output", str(artifact), "--",
                 sys.executable, str(child), str(counter)], capture_output=True,
            )
            self.assertEqual(result.returncode, 0)
            self.assertEqual(counter.read_text(), "2")
            self.assertIn(b"CI setup attempt 1/4", result.stdout)
            self.assertEqual(artifact.read_bytes(), b"\x1f\x8b\xff\x00\r\n")

    def test_missing_program_is_not_retried_as_a_download(self):
        with tempfile.TemporaryDirectory() as folder:
            result = subprocess.run(
                [sys.executable, str(self.retry), "--delay", "0", "--", str(Path(folder) / "missing-program")],
                capture_output=True,
            )
            self.assertEqual(result.returncode, 127)


if __name__ == "__main__":
    unittest.main()
