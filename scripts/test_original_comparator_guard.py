"""Fail-closed regressions for the actual ABI10/runner-ABI8 CI failure."""
import errno
import socket
import tempfile
import unittest
from pathlib import Path
from unittest.mock import Mock, patch
import original_comparator as gate


class ComparatorGuardTests(unittest.TestCase):
    def setUp(self):
        # Windows Python may omit AF_UNIX. This fixture tests Linux guard
        # control flow with mock sockets; no real acceptance runs on Windows.
        unix = patch.object(socket, "AF_UNIX", 1, create=True)
        unix.start()
        self.addCleanup(unix.stop)

    def test_supported_abi_and_low_abi_rejection(self):
        for abi in (-1, 0, 4, 5, 6, 7):
            with self.subTest(abi=abi), self.assertRaises(RuntimeError):
                gate.require_supported_abi(abi)
        for abi in (8, 9, 10):
            self.assertEqual(gate.require_supported_abi(abi), abi)

    def test_requires_no_new_privileges_and_zero_capabilities(self):
        gate.check_process_status("NoNewPrivs:\t1\nCapEff:\t0000000000000000\n")
        for status in ("", "NoNewPrivs: 0\nCapEff: 0", "NoNewPrivs: 1\nCapEff: 1"):
            with self.subTest(status=status), self.assertRaises(RuntimeError):
                gate.check_process_status(status)

    def test_all_socket_families_and_tcp_udp_are_checked(self):
        factory = Mock(side_effect=OSError(errno.EPERM, "Operation not permitted"))
        gate.check_network_denial(factory)
        self.assertEqual(factory.call_count, 5)
        self.assertEqual({call.args for call in factory.call_args_list}, {
            (socket.AF_UNIX, socket.SOCK_STREAM),
            (socket.AF_INET, socket.SOCK_STREAM), (socket.AF_INET, socket.SOCK_DGRAM),
            (socket.AF_INET6, socket.SOCK_STREAM), (socket.AF_INET6, socket.SOCK_DGRAM)})

    def test_one_allowed_socket_rejects_acceptance(self):
        for allowed in range(5):
            calls = []
            sock = Mock()
            def factory(*args):
                calls.append(args)
                if len(calls) - 1 == allowed:
                    return sock
                raise OSError(errno.EPERM, "Operation not permitted")
            with self.subTest(allowed=allowed), self.assertRaises(RuntimeError):
                gate.check_network_denial(factory)
            sock.close.assert_called_once()

    def test_unrelated_socket_error_is_not_guard_evidence(self):
        with self.assertRaises(OSError):
            gate.check_network_denial(Mock(side_effect=OSError(errno.EMFILE, "Too many open files")))

    def test_windows_never_claims_real_sandbox_acceptance(self):
        with tempfile.TemporaryDirectory() as folder, patch.object(gate.sys, "platform", "win32"):
            with self.assertRaisesRegex(RuntimeError, "unprivileged Linux"):
                gate.sandbox_preflight(Path(folder) / "landrun", Path(folder))
            self.assertFalse((Path(folder) / "sandbox-guards.json").exists())

    def test_root_never_claims_real_sandbox_acceptance(self):
        with tempfile.TemporaryDirectory() as folder, patch.object(gate.sys, "platform", "linux"), \
                patch.object(gate.os, "geteuid", return_value=0, create=True):
            with self.assertRaisesRegex(RuntimeError, "unprivileged Linux"):
                gate.sandbox_preflight(Path(folder) / "landrun", Path(folder))
            self.assertFalse((Path(folder) / "sandbox-guards.json").exists())


if __name__ == "__main__":
    unittest.main()
