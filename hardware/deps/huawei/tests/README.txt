Commands to run tests on 16 cores.


- Setup the pulp-runtime:
        go into pulp-runtime folder
        launch "source configs/pulp.sh"
        set the path to the toolchain: "export PATH=<path to the folder containing the bin folder of the toolchain>/bin:$PATH"

- Launch the test on 16 cores:
        go into test folder
        compile with: "make clean all CONFIG_NB_PE=16"
        run with: "make run"
        
