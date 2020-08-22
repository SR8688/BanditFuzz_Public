import subprocess
import uuid
import time
import matplotlib.pyplot as plt
import numpy as np


def remove_last_line_from_string(s):
    return s[:s.rfind('\n')]


def trim_input(s):
    return remove_last_line_from_string(remove_last_line_from_string(s))


def fuzz_solvers(width, depth=5, num_vars=4, num_ast=5):
    print("Width: {0}\tDepth {1}\tNum vars: {2}\tNum ASTs: {3}".format(
        width, depth, num_vars, num_ast))
    cmd_bf = ['python', './bin/banditfuzz',
              '-d', str(depth),
              '-v', str(num_vars),
              '-n', str(num_ast),
              '-bv', '-bvw', str(width),  # bitvec + width
              '-ban', 'None',  # no banned commands
              '-t',
              '../runs/cvc4',
              '../runs/z3',
              '../runs/boolector']  # target solvers
    banditfuzz_out = subprocess.run(cmd_bf,
                                    capture_output=True, check=True).stdout
    solver_input = trim_input(banditfuzz_out.decode()).encode()
    uuid_str = str(uuid.uuid4())
    filename = "./inputs/{0}.smt2".format(uuid_str)
    with open(filename, 'w+b') as fp:
        fp.write(solver_input)

    cmd_z3 = ['../runs/z3', filename]
    cmd_cvc4 = ['../runs/cvc4', '--lang', 'smt', filename]
    cmd_boolector = ['../runs/boolector',  filename]
    # breakpoint()
    try:
        z3_s = time.time()
        z3_output = subprocess.run(cmd_z3,
                                   capture_output=True,
                                   check=False,
                                   timeout=TIMEOUT).stdout.decode().strip()
        z3_e = time.time()
        z3_runtime = z3_e - z3_s
    except subprocess.TimeoutExpired:
        z3_output = "timed out!"
        z3_runtime = INF
        # breakpoint()
    try:
        cvc4_s = time.time()
        cvc4_output = subprocess.run(cmd_cvc4,
                                     capture_output=True,
                                     check=False,
                                     timeout=TIMEOUT).stdout.decode().strip()
        cvc4e = time.time()
        cvc4_runtime = cvc4e - cvc4_s
    except subprocess.TimeoutExpired:
        cvc4_output = "timed out!"
        cvc4_runtime = INF

    try:
        # breakpoint()
        boolector_s = time.time()
        blctr_output = subprocess.run(cmd_boolector,
                                      capture_output=True,
                                      check=False,
                                      timeout=TIMEOUT).stdout.decode().strip()

        boolector_e = time.time()
        boolector_runtime = boolector_e - boolector_s
    except subprocess.TimeoutExpired:
        blctr_output = "timeout"
        boolector_runtime = INF

    runtime_data = [width, depth, num_vars, num_ast,
                    z3_runtime, cvc4_runtime, boolector_runtime]

    print("Input file: {0}".format(filename))
    print("Z3: ", z3_output)
    print("CVC4: ", cvc4_output)
    print("Boolector: ", blctr_output)

    if not (z3_output == cvc4_output == blctr_output):

        log_str = "/*-----------------------------------------------------*/"
        log_str += "\n Z3 {0}\t CVC4 {1}\t Boolector {2}\n".format(
            z3_output, cvc4_output, blctr_output)
        log_str += "INPUT: \n {0}\n".format(solver_input.decode())
        log_str += "/*----------------------------------------------------*/"
        log_str += "\n"
        with open(LOGFILE, 'a') as lgfile:
            lgfile.write(log_str)

    return runtime_data


def cactus_plots(input_data, variable):
    runtime_data = np.array(input_data)
    if variable == 'width':
        var_xlabel = "Bitvector Width"
        var_idx = 0
    elif variable == 'depth':
        var_xlabel = "Asserting AST depth"
        var_idx = 1
    elif variable == 'numvars':
        var_xlabel = "Number of Bitvector Variables"
        var_idx = 2
    elif variable == 'numasts':
        var_xlabel = "Number of asserting ASTs"
        var_idx = 3
    else:
        var_idx = -1
        var_xlabel = "ERROR"
        assert 0

    var_data = runtime_data[:, var_idx]
    z3_times = runtime_data[:, 4]
    cvc4_times = runtime_data[:, 5]
    boolector_times = runtime_data[:, 6]

    plt.plot(var_data, z3_times, label="Z3")
    plt.plot(var_data, cvc4_times, label="CVC4")
    plt.plot(var_data, boolector_times, label="Boolector")
    plt.title("Cactus Plot of Solver Performance")
    plt.xlabel(var_xlabel)
    plt.ylabel("Runtime")

    plt.xlim(min(var_data), max(var_data))
    plt.ylim(0, TIMEOUT/2)
    plt.legend()
    plt.show()


LOGFILE = "./inputs/runlogs.txt"
INF = 1000000
TIMEOUT = 360
MIN_WIDTH, MAX_WIDTH = (1, 64)
MIN_DEPTH, MAX_DEPTH = (1, 20)
MIN_NUMVARS, MAX_NUMVARS = (1, 10)
MIN_NUMASTS, MAX_NUMASTS = (1, 20)

width = range(MIN_WIDTH, MAX_WIDTH+1)
depth = range(MIN_DEPTH, MAX_DEPTH+1)
numvars = range(MIN_NUMVARS, MAX_NUMVARS+1)
numasts = range(MIN_NUMASTS, MAX_NUMASTS+1)

# width_data = [fuzz_solvers(width=w, depth=6, num_vars=4, num_ast=5)
#               for w in width]
# depth_data = [fuzz_solvers(width=w)
#               for w in width]
depth_data = [fuzz_solvers(width=16, depth=d)
              for d in depth]
numvar_data = [fuzz_solvers(width=16, num_vars=v)
               for v in numvars]
numast_data = [fuzz_solvers(width=16,  num_ast=a)
               for a in numasts]

# cactus_plots(width_data, 'width')
cactus_plots(depth_data, 'depth')
cactus_plots(numvar_data, 'numvars')
cactus_plots(numast_data, 'numasts')
#width_data = [fuzz_solvers(width=w, depth=6, num_vars=4, num_ast=5) for w in width]
#width_data = [fuzz_solvers(width=w, depth=6, num_vars=4, num_ast=5) for w in width]


# breakpoint()
#width_data = np.array(width_data)

#numvar_data = np.array(numvar_data)
#numast_data = np.array(numast_data)
