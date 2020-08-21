import subprocess
import tempfile
import time
import matplotlib.pyplot as plt
import numpy as np


def remove_last_line_from_string(s):
    return s[:s.rfind('\n')]


def trim_input(s):
    return remove_last_line_from_string(remove_last_line_from_string(s))


INF = 1000000
TIMEOUT = 180
MAX_WIDTH = 64
all_runs = []

runtime_data = []

for width in range(1, MAX_WIDTH+1):
    print("Doing width {0}".format(width))
    cmd_bf = ['python', './bin/banditfuzz', '-bvw', str(width),
              '-debug', '-bv', '-ban', 'None', '-t', '../runs/cvc4']
    solver_input = trim_input(
        subprocess.check_output(cmd_bf).decode()).encode()

    with tempfile.NamedTemporaryFile() as fp:
        fp.write(solver_input)

        cmd_z3 = ['../runs/z3', fp.name]
        cmd_cvc4 = ['../runs/cvc4', '--lang', 'smt', fp.name]
        try:
            z3_s = time.time()
            z3_output = subprocess.check_output(
                cmd_z3, stderr=subprocess.STDOUT, timeout=TIMEOUT)
            z3_e = time.time()
            z3_runtime = z3_e - z3_s
        except subprocess.TimeoutExpired:
            z3_output = "timed out!"
            z3_runtime = INF

        try:
            cvc4_s = time.time()
            cvc4_output = subprocess.check_output(
                cmd_cvc4, stderr=subprocess.STDOUT, timeout=TIMEOUT)
            cvc4e = time.time()
            cvc4_runtime = cvc4e - cvc4_s
        except subprocess.TimeoutExpired:
            cvc4_output = "timed out!"
            cvc4_runtime = INF
    print(solver_input.decode())
    print("Z3: ", z3_output)
    print("CVC4: ", cvc4_output)
    runtime_data.append([width, z3_runtime, cvc4_runtime])
    # breakpoint()
runtime_data = np.array(runtime_data)
widths = runtime_data[:, 0]
z3_times = runtime_data[:, 1]
cvc4_times = runtime_data[:, 2]

plt.plot(widths, z3_times, label="Z3")
plt.plot(widths, cvc4_times, label="CVC4")
plt.title("Cactus Plot of Z3 vs CVC4 Solver Performance")
plt.xlabel("Bitvector width")
plt.ylabel("Runtime")
plt.xlim(1, MAX_WIDTH)
plt.ylim(0, TIMEOUT/2)
plt.legend()
plt.show()
