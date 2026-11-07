"""Regressions for the actual Windows/Linux source-lock mismatch."""
import hashlib
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


if __name__ == "__main__":
    unittest.main()
