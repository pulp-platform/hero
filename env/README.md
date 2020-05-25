# Environments
To create and build heterogeneous applications (after setting up an embedded setup) an execution environment needs to be sourced. Before sourcing an execution environment `HERO_INSTALL` needs to be set to HERO installation directory during installation. This execution environment setups the relevant environmental variables to the correct value. Apart from setting up paths to the correct locations it also makes sure the correct linker configuration is used applicable to the target platform for building applications with the PULP software stack. Sourcing the wrong environment setup might for example lead to print output not being received.

The following environments are available:
* esim.sh: (PULP) standalone simulation environment
* ediggenesys2.sh: Genesys II environment
* exilzcu102.sh: ZCU102 environment
