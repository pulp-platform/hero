Dummy Readme
Marsellus RTL architecture.

The repo is organized as follow:

- rtl directory contains the top level RTL
- scripts contains some files to update the sw environment as well as the IPs
- setup dir containg configuration files to setup the environment
- Makefìle contains a set of commands to update sdk, build rtl and so on. type 'make help' for more info.
- sim contains simulation files.
 


TO DO:
- modify the name of top level, now is pulpissimo --> should be Marsellus or pulp
- if you prefer we can adopt a repo organization like the one in marsellus_gf22fdx, plese let me know.
- The SoC still has to be updated, together with SoC IPs.
- fpga directory must be updated, if needed.


How to run applications on Marsellus:

After setting the environment (sdk, rtl and so on), the apps can be run through a Makefile procedure.
Once you are in the directory of the selected app, the following commands need to be run:

make '+ options listed below'

- clean: remove binary and stim.txt files, if existing, together with traces and so on
- all: compiles the application and generates binary and stim.txt
- run: runs the application on the platform target specified in the config (in our case always RTL). To opens Questasim gui add also this option 'gui=1'
	Hence, for example, 'make clean all run gui=1' cleans build directory, compiles the app and runs it on RTL opening Questasim
