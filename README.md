# BanditFuzz

BanditFuzz runs in a virtualenv.

To install BanditFuzz, navigate to its root and run: `venv_install.sh` . This script will create a directory in the BanditFuzz root directory called `venv`.

To run Banditfuzz:
```
source venv/bin/activate

banditfuzz /Absolute/Path/To/Solver1/run.sh /Absolute/Path/To/Solver2/run.sh

```

When done: `deactivate`

In the above example, the `run.sh` script, takes one command line argument, the name of the smt2 input to be solved, and runs the solver on that input, and prints the result to stdout. 

`QF_S,QF_FP` are supported.

# Benchmarking
Update the configuration settings in `expt_driver.py`  
INPUT\_DIR: a directory containing .smt2 input files  
MAX\_WORKERS: Max processes available in pool  
TIMEOUT: in seconds  
SAMPLE\_SIZE: less than the number of input files  
Z3\_BIN, CVC4\_BIN, BOOLECTOR_BIN : ./path/to/solver  

Then run from the root dir:
```
source venv/bin/activate
python ./expt_driver.py
deactivate
```
Any timeouts, etc will be logged to LOGFILE  
Any contradicting SAT results will be logged to INCONSISTENCIES  

If any of the required libraries are missing from your venv, `pip install` them.
```
matplotlib
multiprocessing
itertools
subprocess
json
os
uuid
time
matplotlib.pyplot as plt
numpy as np
random.sample
```
