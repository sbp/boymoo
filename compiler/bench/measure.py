"""Measure a child with wait4 when the system time cannot report resources."""

import os
import subprocess
import sys
import time


def main():
    executable, output_path, error_path = sys.argv[1:]
    with open(output_path, "wb") as output, open(error_path, "wb") as error:
        start = time.monotonic()
        process = subprocess.Popen([executable], stdout=output, stderr=error)
        _, status, usage = os.wait4(process.pid, 0)
        elapsed = time.monotonic() - start

    if os.WIFEXITED(status):
        process.returncode = os.WEXITSTATUS(status)
    else:
        process.returncode = -os.WTERMSIG(status)
    peak_bytes = usage.ru_maxrss
    if sys.platform.startswith("linux"):
        peak_bytes *= 1024
    print("{:.6f} {}".format(elapsed, peak_bytes))
    if process.returncode < 0:
        return 128 - process.returncode
    return process.returncode


if __name__ == "__main__":
    sys.exit(main())
