"""Test-only Z3 proxy: inject worker failures while preserving real models.

The test harness copies this file to a temporary executable named ``z3`` and
provides the real solver and worker modes through UPLC_TEST_Z3_* variables.
Receipt files beside that executable record PIDs, seeds and model requests.
The default mode applies until an explicit smt.random-seed option is received;
the seeded mode applies afterwards. Modes are real, unknown, block, block-model,
block-options, block-version, error, error-model and real-after-model-request.
"""
import json
import os
from pathlib import Path
import signal
import subprocess
import sys
import threading
import time


def main():
    real = os.environ['UPLC_TEST_Z3_REAL']
    default_mode = os.environ['UPLC_TEST_Z3_DEFAULT_MODE']
    seeded_mode = os.environ['UPLC_TEST_Z3_SEEDED_MODE']
    if '-in' not in sys.argv:
        if default_mode == 'block-version':
            time.sleep(30)
        os.execv(real, [real, *sys.argv[1:]])

    child = subprocess.Popen([real, *sys.argv[1:]], stdin=subprocess.PIPE,
                             stdout=subprocess.PIPE)
    receipt = Path(__file__).with_name(str(os.getpid()))
    receipt.with_suffix('.json').write_text(json.dumps([os.getpid(), child.pid]))

    def stop(*_):
        child.kill()
        child.wait()
        raise SystemExit(0)

    signal.signal(signal.SIGTERM, stop)

    def forward_output():
        while data := os.read(child.stdout.fileno(), 65536):
            os.write(1, data)

    threading.Thread(target=forward_output, daemon=True).start()
    seeded = False
    unknown = False
    for line in sys.stdin:
        if line.startswith('(set-option :smt.random-seed '):
            seeded = True
            seed = int(line.strip().removesuffix(')').split()[-1])
            receipt.with_suffix('.seed').write_text(str(seed))
        mode = seeded_mode if seeded else default_mode
        if mode == 'block-options' and line.startswith('(set-option :print-success '):
            receipt.with_suffix('.options').touch()
            time.sleep(30)
        if line.startswith('(eval ') or line.startswith('(get-model'):
            receipt.with_suffix('.model').touch()
            if mode == 'block-model':
                print('(partial', flush=True)
                time.sleep(30)
            if mode == 'error-model':
                print('(partial', flush=True)
                continue
        if mode == 'error-model' and line.startswith('(echo '):
            break
        if mode == 'real-after-model-request' and line.startswith('(check-sat)'):
            while not any(receipt.parent.glob('*.model')):
                time.sleep(0.01)
        if line.startswith('(check-sat)') and mode in ('block', 'error', 'unknown'):
            if mode == 'block':
                time.sleep(30)
            if mode == 'error':
                print('(error "test solver failure")', flush=True)
            else:
                unknown = True
                print('unknown', flush=True)
        elif unknown and line.startswith('(get-info :reason-unknown'):
            print('(:reason-unknown "incomplete")', flush=True)
        else:
            child.stdin.write(line.encode())
            child.stdin.flush()
            if line.startswith('(exit'):
                break
    child.stdin.close()
    child.wait()


if __name__ == '__main__':
    main()
