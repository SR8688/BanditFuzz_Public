# BanditFuzz

BanditFuzz runs in a virtualenv.

# Installation
1. Gain Root Access in the Terminal. Press Ctrl+Alt+T to open the terminal. In ubuntu, Use `sudo` to become root
```
sudo -i  
```
2. Navigate to its root and run: `venv_install.sh` . This script will create a directory in the BanditFuzz root directory called `venv`.

# Benchmarking
Update the configuration settings in `expt_driver.py`  
INPUT\_DIR: a directory containing .smt2 input files  
MAX\_WORKERS: Max processes available in pool  
TIMEOUT: in seconds  
SAMPLE\_SIZE: less than the number of input files  
Z3\_BIN, CVC4\_BIN, BOOLECTOR_BIN : ./runs

Then run from the root dir:
```
source venv/bin/activate
python ./expt_driver.py
deactivate
```
Any timeouts, etc will be logged to LOGFILE  
Any contradicting SAT results will be logged to INCONSISTENCIES  

With DEFAULT configuration settings in `expt_driver.py`, Banditfuzz should generate the following graph.

<img src="im/Figure_1.png"
     alt="Markdown Monster icon"
     style="float: left; margin-right: 10px;margin-bottom: 20px;" />  




# Running Baditfuzz

To run Banditfuzz:
```
source venv/bin/activate

banditfuzz /Absolute/Path/To/Solver1/run.sh /Absolute/Path/To/Solver2/run.sh

```

When done: `deactivate`

In the above example, the `run.sh` script, takes one command line argument, the name of the smt2 input to be solved, and runs the solver on that input, and prints the result to stdout. 

`QF_S,QF_FP,QF_BV` are supported.

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