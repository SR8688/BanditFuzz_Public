import matplotlib
import multiprocessing
import itertools
import subprocess
import json
import os
import uuid
import time
import matplotlib.pyplot as plt
import numpy as np
from random import sample


def remove_last_line_from_string(string):
    """ Removes the last \n ended portion of the string"""
    return string[:string.rfind('\n')]


def trim_input(string):
    """ Removes last two lines """
    return remove_last_line_from_string(remove_last_line_from_string(string))


def create_smt_file(config=(8, 5, 4, 5), verbose=False):
    width, depth, num_vars, num_ast = config
    """ Given banditfuzz config, creates SMT input and returns filename """
    if verbose:
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
    filename = INPUT_DIR+"/{0}.smt2".format(uuid_str)
    if verbose:
        print("Input file: {0}".format(filename))
    # Write input to file
    with open(filename, 'w+b') as inp_file:
        inp_file.write(solver_input)
    # Creates command strings for solvers
    return filename


def fuzz_z3(infile):
    return fuzz_solver('z3', infile)


def fuzz_cvc4(infile):
    return fuzz_solver('cvc4', infile)


def fuzz_boolector(infile):
    return fuzz_solver('boolector', infile)


def fuzz_solver(solver, infile):

    if solver == 'z3':
        cmd = ['../runs/z3', infile]
    elif solver == 'cvc4':
        cmd = ['../runs/cvc4', '--lang', 'smt', infile]
    elif solver == 'boolector':
        cmd = ['../runs/boolector',  infile]
    else:
        cmd = 'error'
        assert 0
    try:
        t_start = time.time()
        output = subprocess.run(cmd,
                                capture_output=True,
                                check=False,
                                timeout=TIMEOUT).stdout.decode().strip()
        t_end = time.time()
        runtime = t_end - t_start
    except subprocess.TimeoutExpired:
        output = "timeout"
        runtime = INF
    print("{0}:\t{1}".format(solver, output))
    return [runtime, output]


def get_sample_files():
    filenames = [os.path.join(INPUT_DIR, infile)
                 for infile in os.listdir(INPUT_DIR) if infile[-4:] == 'smt2']
    sample_files = sample(filenames, SAMPLE_SIZE)
    return sample_files


def benchmark_solvers(sample_files):

    with multiprocessing.Pool(MAX_WORKERS) as pool_z3:
        outputs_z3 = pool_z3.map(fuzz_z3, sample_files)

    with multiprocessing.Pool(MAX_WORKERS) as pool_cvc4:
        outputs_cvc4 = pool_cvc4.map(fuzz_cvc4, sample_files)

    with multiprocessing.Pool(MAX_WORKERS) as pool_boolector:
        outputs_boolector = pool_boolector.map(fuzz_boolector, sample_files)

    outputs = np.array([outputs_z3, outputs_cvc4, outputs_boolector])
    # breakpoint()
    return outputs


def fuzz_expt(width, depth=5, num_vars=4, num_ast=5):
    """ Creates an input and evaluates it on all solvers """
    print("Width: {0}\tDepth {1}\tNum vars: {2}\tNum ASTs: {3}".format(
        width, depth, num_vars, num_ast))
    filename = create_smt_file(width, depth, num_vars, num_ast)
    z3_output, z3_runtime = fuzz_solver('z3', filename)
    cvc4_output, cvc4_runtime = fuzz_solver('cvc4', filename)
    blctr_output, blctr_runtime = fuzz_solver('boolector', filename)
    runtime_data = [width, depth, num_vars, num_ast,
                    z3_runtime, cvc4_runtime, blctr_runtime]

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


def create_smt_benchmarks():
    # breakpoint()
    widths = range(MIN_WIDTH, MAX_WIDTH+1)
    depths = range(MIN_DEPTH, MAX_DEPTH+1)
    numvars = range(MIN_NUMVARS, MAX_NUMVARS+1)
    numasts = range(MIN_NUMASTS, MAX_NUMASTS+1)

    configuration_space = itertools.product(widths,
                                            depths,
                                            numvars,
                                            numasts)

    with multiprocessing.Pool(MAX_WORKERS) as pool:
        filename_list = pool.map(
            create_smt_file, [el for el in configuration_space])

    return filename_list


def performance_plots(input_data, variable):
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
    plt.ylim(0, TIMEOUT)
    plt.legend()
    plt.show()


def log_interesting_behaviour(solver_data):
    z3_d, cvc4_d, bltr_d = solver_data
    agree = np.logical_and(z3_d[:, 1] == cvc4_d[:, 1],
                           z3_d[:, 1] == bltr_d[:, 1])
    disagree = np.logical_not(agree)
    # values = z3_d[disagree]
    conflicts = solver_data[:, disagree, 1]
    conflict_files = np.array(file_list)[disagree]
    assert conflicts.shape[-1] == conflict_files.size
    conflict_idxs = conflict_files.size
    for idx, soln_set in enumerate([conflicts[:, idx]
                                    for idx in range(conflict_idxs)]):
        z3_o, cvc4_o, blctr_o = soln_set
        fault_file = conflict_files[idx]
        log_dict = {"z3": z3_o,
                    "cvc4": cvc4_o,
                    "blctr": blctr_o,
                    "filename": fault_file}
        log_str = json.dumps(log_dict)

        # If discrepancies in outputs
        # Log it
        if 'sat' in soln_set and 'unsat' in soln_set:
            with open(INCONSISTENCIES, 'a') as inconfile:
                inconfile.write(log_str+'/n')

        with open(LOGFILE, 'a') as lgfile:
            lgfile.write(log_str+'/n')


INPUT_DIR = "./inputs/cactus"
LOGFILE = INPUT_DIR+"/runlogs.txt"
INCONSISTENCIES = INPUT_DIR+"/incons.txt"

INF = 1000000

TIMEOUT = 20
MAX_WORKERS = 8
SAMPLE_SIZE = 6
MIN_WIDTH, MAX_WIDTH = (1, 64)
MIN_DEPTH, MAX_DEPTH = (1, 10)
MIN_NUMVARS, MAX_NUMVARS = (1, 10)
MIN_NUMASTS, MAX_NUMASTS = (1, 10)

file_list = get_sample_files()
benchmark_data = benchmark_solvers(file_list)
# log_interesting_behaviour(benchmark_data)
z3_data, cvc4_data, bltr_data = benchmark_data
z3_times = np.sort(z3_data[z3_data[:, 1] != 'timeout'], axis=0)[
    :, 0].astype('float')
cvc4_times = np.sort(cvc4_data[cvc4_data[:, 1] != 'timeout'], axis=0)[
    :, 0].astype('float')
bltr_times = np.sort(bltr_data[bltr_data[:, 1] != 'timeout'], axis=0)[
    :, 0].astype('float')

time_intervals = np.logspace(-4, np.log10(TIMEOUT), 1000)
n_z3 = [z3_times[z3_times < interval].size
        for interval in time_intervals]
n_cvc4 = [cvc4_times[cvc4_times < interval].size
          for interval in time_intervals]
n_bltr = [bltr_times[bltr_times < interval].size
          for interval in time_intervals]
matplotlib.rcParams.update({'font.size': 22})
matplotlib.rc('xtick', labelsize=16)
matplotlib.rc('ytick', labelsize=16)
plt.title("Cactus/Survival plot of SMT Solvers with BanditFuzz input")
plt.plot(time_intervals, n_z3, label='Z3')
plt.plot(time_intervals, n_cvc4, label='CVC4')
plt.plot(time_intervals, n_bltr, label='Boolector')
plt.xscale('log')
plt.xlabel('Time (s)')
plt.ylabel('Instances Solved')
plt.legend()
plt.grid()
plt.tight_layout()
plt.show()


# z3_data.drop

# create_smt_benchmarks()

# widths = range(MIN_WIDTH, MAX_WIDTH+1)
# depths = range(MIN_DEPTH, MAX_DEPTH+1)
# numvars = range(MIN_NUMVARS, MAX_NUMVARS+1)
# numasts = range(MIN_NUMASTS, MAX_NUMASTS+1)

# width_data = [fuzz_expt(width=w, depth=8,  num_ast=15, num_vars=6)
#               for w in widths]

# performance_plots(width_data, 'width')
