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


def create_smt_file(config=(8, 5, 4, 5)):
    """ Given banditfuzz config, generates and saves an SMT file"""
    width, depth, num_vars, num_ast = config
    if VERBOSE:
        print("Width: {0}\tDepth {1}\tNum vars: {2}\tNum ASTs: {3}".format(
            width, depth, num_vars, num_ast))
    # Build the banditfuzz command string
    # Rewrite this security risk V
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
    if VERBOSE:
        print("Input file: {0}".format(filename))
    # Write input to file
    with open(filename, 'w+b') as inp_file:
        inp_file.write(solver_input)
    # Creates command strings for solvers
    return filename


def fuzz_z3(infile):
    """ Starts Z3 for multiprocessing """
    return fuzz_solver('z3', infile)


def fuzz_cvc4(infile):
    """ Starts CVC4 for multiprocessing """
    return fuzz_solver('cvc4', infile)


def fuzz_boolector(infile):
    """ Starts Boolector for multiprocessing """
    return fuzz_solver('boolector', infile)


def fuzz_solver(solver, infile):
    """ Runs a solver on an input file, returns run time and the output """
    if solver == 'z3':
        cmd = ['../runs/z3', infile]
    elif solver == 'cvc4':
        cmd = ['../runs/cvc4', '--lang', 'smt', infile]
    elif solver == 'boolector':
        cmd = ['../runs/boolector', infile]
    else:
        cmd = 'error in fuzz_solver (unhandled input)'
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
        runtime = -1
    if VERBOSE:
        print("{0}:\t{1}".format(solver, output))
    return [runtime, output]


def get_sample_files():
    """ Generates a sample of files """
    filenames = [os.path.join(INPUT_DIR, infile)
                 for infile in os.listdir(INPUT_DIR) if infile[-4:] == 'smt2']
    sample_files = sample(filenames, SAMPLE_SIZE)
    return sample_files


def benchmark_solvers(sample_files):
    """ Uses multiprocessing to run the solvers on the input sample"""
    print("[*] With {0} workers".format(MAX_WORKERS))
    print("[*] Sampling {0} files".format(SAMPLE_SIZE))
    print("[*] Timeout {0}s".format(TIMEOUT))

    print("[*] Starting Z3 benchmark")
    with multiprocessing.Pool(MAX_WORKERS) as pool_z3:
        outputs_z3 = pool_z3.map(fuzz_z3, sample_files)

    print("[*] Starting CVC4 benchmark")
    with multiprocessing.Pool(MAX_WORKERS) as pool_cvc4:
        outputs_cvc4 = pool_cvc4.map(fuzz_cvc4, sample_files)

    print("[*] Starting boolector benchmark")
    with multiprocessing.Pool(MAX_WORKERS) as pool_boolector:
        outputs_boolector = pool_boolector.map(fuzz_boolector, sample_files)
    print("[*] Finished benchmarking solvers")
    outputs = np.array([outputs_z3, outputs_cvc4, outputs_boolector])

    return outputs


def create_benchmark_files():
    """ Creates a set of files for benchmarking """
    widths = range(MIN_WIDTH, MAX_WIDTH+1)
    depths = range(MIN_DEPTH, MAX_DEPTH+1)
    numvars = range(MIN_NUMVARS, MAX_NUMVARS+1)
    numasts = range(MIN_NUMASTS, MAX_NUMASTS+1)
    n_combos = len(widths)*len(depths)*len(numvars)*len(numasts)

    cfg_space = itertools.product(widths,
                                  depths,
                                  numvars,
                                  numasts)
    print("[*] Creating {0} .smt2 files".format(n_combos))
    print("[*] With {0} processes".format(MAX_WORKERS))
    with multiprocessing.Pool(MAX_WORKERS) as pool:
        filename_list = pool.map(create_smt_file, cfg_space)
    return filename_list


def log_interesting_behaviour(solver_data, file_list):
    """ Logs satisfiability error in one file, everything in another """
    z3_d, cvc4_d, bltr_d = solver_data
    disagree = np.logical_not(np.logical_and(z3_d[:, 1] == cvc4_d[:, 1],
                                             z3_d[:, 1] == bltr_d[:, 1]))
    # values = z3_d[disagree]
    conflicts = solver_data[:, disagree, 1]
    conflict_files = np.array(file_list)[disagree]
    assert conflicts.shape[-1] == conflict_files.size
    conflict_idxs = conflict_files.size
    for idx, soln_set in enumerate([conflicts[:, idx]
                                    for idx in range(conflict_idxs)]):
        z3_o, cvc4_o, blctr_o = soln_set
        fault_file = conflict_files[idx]
        log_str = json.dumps({"z3": z3_o,
                              "cvc4": cvc4_o,
                              "blctr": blctr_o,
                              "filename": fault_file})

        # If discrepancies in outputs
        # Log it
        if 'sat' in soln_set and 'unsat' in soln_set:
            with open(INCONSISTENCIES, 'a') as inconfile:
                inconfile.write(log_str+'/n')

        with open(LOGFILE, 'a') as lgfile:
            lgfile.write(log_str+'/n')


def show_cactus_plot(solver_times):
    """ Creates cactus plot given 3 solver input time series """
    time_intervals = np.logspace(-4, np.log10(TIMEOUT), 1000)
    solver_labels = ['Z3', 'CVC4', 'Boolector']
    for idx, t_solver in enumerate(solver_times):
        n_solver = [t_solver[t_solver < interval].size
                    for interval in time_intervals]
        plt.plot(time_intervals, n_solver, label=solver_labels[idx])

    plt.title("Solver Survival with BanditFuzz (i9 9900K: {0} threads)".format(
        MAX_WORKERS))
    plt.xscale('log')
    plt.xlabel('Time (s)')
    plt.ylabel('Instances Solved')
    plt.legend()
    plt.grid()
    plt.tight_layout()
    plt.show()


def drop_timeouts_and_sort(solver_data):
    """ Removes timeouts and sorts by time given solver output data """
    sorted_no_timeouts = np.sort(solver_data[solver_data[:, 1] != 'timeout'],
                                 axis=0)[:, 0]

    return sorted_no_timeouts.astype('float')


# ##############               CONFIGURATION               ####################
matplotlib.rcParams.update({'font.size': 22})
matplotlib.rc('xtick', labelsize=16)
matplotlib.rc('ytick', labelsize=16)

INPUT_DIR = "./inputs/cactus"
LOGFILE = INPUT_DIR+"/runlogs.txt"
INCONSISTENCIES = INPUT_DIR+"/incons.txt"
VERBOSE = False

TIMEOUT = 5
MAX_WORKERS = 2  # Make the 9900K sweat
SAMPLE_SIZE = 10  # How many files to run solvers on

MIN_WIDTH, MAX_WIDTH = (1, 64)  # for benchmark file creation
MIN_DEPTH, MAX_DEPTH = (1, 10)
MIN_NUMVARS, MAX_NUMVARS = (1, 10)
MIN_NUMASTS, MAX_NUMASTS = (1, 10)
###############################################################################


def main(gen_input_files=False):
    """ Creates smt2 input files and places into input directory if arg is True, then runs solvers on a sample of the files in input dir """
    if not os.path.isdir(INPUT_DIR):
        print("[!] Please create {0} and run again".format(
            INPUT_DIR), flush=True)
        raise NotImplementedError
    if gen_input_files:
        create_benchmark_files()  # generate input files

    file_list = get_sample_files()  # get a sample of the files
    benchmark_data = benchmark_solvers(file_list)  # benchmark solvers
    # get any interesting behaviour
    log_interesting_behaviour(benchmark_data, file_list)

    z3_data, cvc4_data, bltr_data = benchmark_data

    z3_times = drop_timeouts_and_sort(z3_data)
    cvc4_times = drop_timeouts_and_sort(cvc4_data)
    bltr_times = drop_timeouts_and_sort(bltr_data)

    show_cactus_plot([z3_times, cvc4_times, bltr_times])


if __name__ == '__main__':
    main(gen_input_files=False)
