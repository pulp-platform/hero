Readme for the Pipeline
=======================

The Experiment Execution Pipeline is a set of benchmark source files as well as Python 3 and Bash scripts that are used to automatically execute the experiments that have given the results in the report.

In order to reproduce the results, four steps are required:
1. Specify the run settings in the `config` file. This determines which PUTs will be co-run how many times with which PIs, and how much memory they use;
2. Run the `master` script to compile and execute the programs, followed by the extraction their execution times;
3. Specify evaluation options, such as which memory sizes, PUTs and PIs are of interest to be plotted;
4. Run the evaluation script to obtain the figures.

The pipeline implements the cross-compilation, remote deployment and execution,transferring of results, as well as the final plotting. As such, the scripts are intended to be executed on a workstation machine, using SSH to interact with the ZCU102 board. All interactions with the board are scripted, and do not need to be performed manually. To enable this, the pipeline must be properly pre-configured as outlined further below.

A high-level pseudo-code for the experiment execution pipeline looks like this:
```
for s in MEMORYSIZE:
    for f in TESTPROGRAM:
        cross-compile f with dataset size s into binary F
        copy F to REMOTEHOST:REMOTEPATH/F
        
    for b in BACKGROUNDPROGRAM:
        cross-compile b with dataset size s into binary B that loops forever
        copy B to REMOTEHOST:REMOTEPATH/B

for sample in SAMPLESIZE:
    for B in BACKGROUNDPROGRAM
        launch B on REMOTEHOST in the background 
        for F in TESTPROGRAM:
            launch and time F on REMOTEHOST
        kill B

save raw timing information to data/EXPERIMENTNAME on local machine
extract raw timing information to results/EXPERIMENTNAME
evaluate results/EXPERIMENTNAME
``` 

System Requirements
-------------------
The pipeline was built and operated using the following software:

- CentOS 7.7.1908
- zsh 5.0.2    
- Python 3.6.8
	- Pandas 0.25.3
	- Numpy 1.17.4
	- Matplotlib 3.1.2
	- tqdm 4.41.1

Directory Stucture and Usage Instructions
-----------------------------------------

### `config`
All experiment settings are defined in the `config` file in the root directory. The configuration is parsed line-by-line by the `master` script, using a simple format where the meaning is encoded by the order. This means that the arguments need to be given exactly in the order outlined below, and all options must be present. For increased understanding we have labeled each configuration parameter with their relevant use in the [pseudocode above](#Readme for the Pipeline), however, these labels are not to be included in the `config` file.

- `REMOTEHOST`: The DNS name or IP of the target board on which to execute the experiments. This is used to establish an SSH connection to the board, to deploy the compiled benchmarks, and start the execution of the experiment. The format is the same as for the SSH command, and can as such also include the username as which to connect: `[user@]hostname`.
- `REMOTEPATH`: The remote directory (on the ZCU102 board) to which the benchmarks are deployed after cross-compilation.
- `MEMORYSIZE`: The dataset size for the benchmarks, to allow testing benchmark configurations whose memory footprint is aligned with different levels of the cache hierarchy. This line is parsed as a space-separated list. All benchmarks will be executed once for each dataset size configuration, and the size is applied uniformly to all benchmarks.
- `TESTPROGRAM`: The benchmarks we wish to measure, i.e. the PUTs. Also a space-separated list. Each value here indicates one of the binaries `F` in `REMOTEPATH`.
- `BACKGROUNDPROGRAM`: The benchmarks that should loop their kernels in the background, thus causing interference (PI). In all cases, an iteration without any interfering programs will be made. This line is a space-separated list and it can be left empty;
- `SAMPLESIZE`: How many runs should be performed. One single positive integer;
- `EXPERIMENTNAME`: A human readable name for the experiment. After execution a subdirectory will be created under `data/` and `results/` with this name, containing the measurements performed during the experiment.


### `results/`
The `results` directory contains the experimental results of each experiment execution. After each run a subdirectory named `EXPERIMENTNAME` is created. Upon successful completion of an experiment, a results tensor (dict of dict) is stored inside the respective subdirectory. The tensor dimensions are as follows:

1. Size of the memory the benchmark uses;
2. Measured benchmark;
3. Interfering benchmark;
4. Sample number.	

Indexing through these dimensions, the execution time of the sample is retrieved. This task does not need to be performed manually, but is automated by the `evaluate` script described below.

### `data/`
The data directory stores intermediate results in the form of raw sample points from the experiments. As can be seen in the [pseudocode above](#Readme for the Pipeline), they are generated as follows: For every iteration of an experiment, the PIs are launched in the background first and alternate only when all PUT executed. The PUTs print their execution time to a logging file. To delimit every iteration, a `++STRT++` and `--STOP--` marker is logged. The file's naming scheme consists of the program size followed by the amount of iterations performed.

### `scripts/`

The drivers are located in the `scripts` directory. The experiments are started by executing the `master` script, which performs some housekeeping tasks while calling the other driver scripts that perform the following:

1. `compile` generates binaries and transfers them to the target;
2. `autogenerate` writes a driver script called \texttt{autogen.sh} to be executed on the target board and transfers it;
3. `remoterun` remotely executes `autogen.sh` on the target board and copies the results back into the `data` folder;
4. `extract` parses the results inside the `data` folder and extracts them into the `results` folder in the form of a tensor and its labels. 

#### `scripts/evaluate`
In addition to the driver scripts that set up the experiments, the `scripts` directory also contains the `evaluate` script to plot the results. The script must be edited as follows before each new run, using the `Configuration Parameters` that are visually highlighted:

- `experiment_name`: The experiment name as originally specified on line 7 of the `config` file (`EXPERIMENTNAME`);
- `size`: The benchmark memory size for which the histogram and barplots (min-avg-max plots, or `mamp` for short in the script) should be generated. In all cases, the time series plots are generated for all sizes;
- `ext`: The image format in which the plot should be saved;
- `hist_superpose`: Which interference benchmarks to superimpose on the histogram plots;
-	`hist_bins`: The granularity of the histogram plots.

After running `evaluate`, the plots are saved in the `EXPERIMENTNAME` folder in `results`. Every evaluation outputs three plots:

- a barplot displaying a subplot for every PUT in which the BCETs, ACETs and WCETs for the PIs are shown for the specified problem `size`;
- a histogram plot showing a subplot for every PUT without interference for a given `size`. If `hist_superpose` list is non-empty, the same PUT with relevant PIs interfering are plotted on top;
- a timeseries plot with all PUTs without interference for all program sizes.

As the first two plots depend on the problem size, their output files will have a suffix specifying the latter.
