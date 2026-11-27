#!/usr/bin/env python3
"""Fail early when the documented equivalence-test toolchain is unavailable."""
import re
import shutil
import subprocess
import sys


def main():
    if sys.version_info < (3, 9):
        raise SystemExit('Equivalence tests require Python 3.9 or later.')
    for command in ['git', 'lake', 'z3']:
        if not shutil.which(command):
            raise SystemExit(f'Missing {command} on PATH. See README.md: Running the equivalence tests.')
    try:
        version = subprocess.run(['z3', '--version'], capture_output=True, text=True,
                                 timeout=10, check=True).stdout.strip()
        match = re.search(r'Z3 version (\d+\.\d+\.\d+)', version)
        if not match or match[1] != '5.4.0':
            raise SystemExit(f'Equivalence tests require Z3 5.4.0 on PATH; found {version!r}. '
                             'See README.md: Running the equivalence tests.')
        probe = subprocess.run(['z3', '-in'], input='(set-simplifier recfun-finder)\n'
                               '(assert true)\n(check-sat)\n', capture_output=True,
                               text=True, timeout=10, check=True)
        if probe.stdout.strip() != 'sat':
            raise SystemExit(f'Z3 recfun-finder probe failed: {probe.stdout}{probe.stderr}')
    except (OSError, subprocess.SubprocessError) as error:
        raise SystemExit(f'Could not run Z3 with recfun-finder: {error}') from error
    print(version)


if __name__ == '__main__':
    main()
