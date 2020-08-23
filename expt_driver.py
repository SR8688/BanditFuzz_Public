import subprocess
import uuid
import time
import matplotlib.pyplot as plt
import numpy as np


def remove_last_line_from_string(string):
    """ Removes the last \n ended portion of the string"""
    return string[:string.rfind('\n')]


def trim_input(string):
    """ Removes last two lines """
    return remove_last_line_from_string(remove_last_line_from_string(string))


def fuzz_solvers(width, depth=5, num_vars=4, num_ast=5):
    """ Creates an input and evaluates it on all solvers """
    print("Width: {0}\tDepth {1}\tNum vars: {2}\tNum ASTs: {3}".format(
        width, depth, num_vars, num_ast))
    # Build the banditfuzz command string
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
    # Get the solver input
    banditfuzz_out = subprocess.run(cmd_bf,
                                    capture_output=True, check=True).stdout
    solver_input = trim_input(banditfuzz_out.decode()).encode()
    # Creates unique filename for input
    uuid_str = str(uuid.uuid4())
    filename = "./inputs/{0}.smt2".format(uuid_str)
    print("Input file: {0}".format(filename))
    # Write input to file
    with open(filename, 'w+b') as inp_file:
        inp_file.write(solver_input)
    # Creates command strings for solvers
    cmd_z3 = ['../runs/z3', filename]
    cmd_cvc4 = ['../runs/cvc4', '--lang', 'smt', filename]
    cmd_boolector = ['../runs/boolector',  filename]

    try:
        z3_s = time.time()
        z3_output = subprocess.run(cmd_z3,
                                   capture_output=True,
                                   check=False,
                                   timeout=TIMEOUT).stdout.decode().strip()
        z3_e = time.time()
        z3_runtime = z3_e - z3_s
    except subprocess.TimeoutExpired:
        z3_output = "timeout"
        z3_runtime = INF
        # breakpoint()
    print("Z3: ", z3_output)
    try:
        cvc4_s = time.time()
        cvc4_output = subprocess.run(cmd_cvc4,
                                     capture_output=True,
                                     check=False,
                                     timeout=TIMEOUT).stdout.decode().strip()
        cvc4e = time.time()
        cvc4_runtime = cvc4e - cvc4_s
    except subprocess.TimeoutExpired:
        cvc4_output = "timeout"
        cvc4_runtime = INF

    print("CVC4: ", cvc4_output)
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
    print("Boolector: ", blctr_output)
    runtime_data = [width, depth, num_vars, num_ast,
                    z3_runtime, cvc4_runtime, boolector_runtime]

    if not z3_output == cvc4_output == blctr_output:
        # If discrepancies in outputs
        # Log it
        log_str = "/*-----------------------------------------------------*/"
        log_str += "\n Z3 {0}\t CVC4 {1}\t Boolector {2}\n".format(
            z3_output, cvc4_output, blctr_output)
        log_str += "INPUT: \n {0}\n".format(filename)
        log_str += "/*----------------------------------------------------*/"
        log_str += "\n"
        with open(LOGFILE, 'a') as lgfile:
            lgfile.write(log_str)

        # If we have SAT and unSAT: big problem!
        solver_outputs = [z3_output, cvc4_output, blctr_output]
        if 'sat' in solver_outputs and 'unsat' in solver_outputs:
            with open(INCONSISTENCIES, 'a') as inconfile:
                inconfile.write(log_str)
    else:
        print("Finished this round")

    return runtime_data


def cactus_plots(input_data, variable):
    """ Creates cactus plot of experiments """
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
INCONSISTENCIES = "./inputs/incons.txt"
INF = 1000000
TIMEOUT = 20
MIN_WIDTH, MAX_WIDTH = (1, 8)
MIN_DEPTH, MAX_DEPTH = (1, 10)
MIN_NUMVARS, MAX_NUMVARS = (1, 10)
MIN_NUMASTS, MAX_NUMASTS = (1, 10)

widths = range(MIN_WIDTH, MAX_WIDTH+1)
depths = range(MIN_DEPTH, MAX_DEPTH+1)
numvars = range(MIN_NUMVARS, MAX_NUMVARS+1)
numasts = range(MIN_NUMASTS, MAX_NUMASTS+1)

width_data = [fuzz_solvers(width=w, depth=8,  num_ast=15, num_vars=6)
              for w in widths]

cactus_plots(width_data, 'width')
