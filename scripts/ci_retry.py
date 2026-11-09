"""Bounded retries for external CI setup downloads, never proof checks."""
from __future__ import annotations

import argparse
import subprocess
import sys
import time


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--attempts", type=int, choices=range(1, 5), default=4)
    parser.add_argument("--delay", type=float, default=10)
    parser.add_argument("command", nargs=argparse.REMAINDER)
    args = parser.parse_args()
    command = args.command[1:] if args.command[:1] == ["--"] else args.command
    if not command or not 0 <= args.delay <= 30:
        parser.error("supply a command and a delay between zero and 30 seconds")
    for attempt in range(1, args.attempts + 1):
        try:
            code = subprocess.run(command, check=False).returncode
        except OSError as exc:
            print(f"Cannot start CI setup command (errno {exc.errno})", file=sys.stderr)
            return 127
        if code == 0:
            return 0
        if attempt == args.attempts:
            return code if 1 <= code <= 255 else 1
        delay = min(args.delay * 2 ** (attempt - 1), 30)
        print(f"CI setup attempt {attempt}/{args.attempts} failed (exit {code}); retry in {delay:g}s", flush=True)
        time.sleep(delay)
    return 1


if __name__ == "__main__":
    raise SystemExit(main())
