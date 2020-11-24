# Generate QuestaSim simulation wrappers for Aegis tests

# Author: Paul Scheffler <paulsc@iis.ee.ethz.ch>
# Author: Thomas Benz <tbenz@iis.ee.ethz.ch>

import sys
import json
import os
from os.path import dirname, realpath

VSIM_DEFAULT_FLAGS = '-coverage -voptargs="+acc +cover=bcesfx"'
VSIM_QUIT_ON_ERROR = r'if {[catch {exec grep -E "# Errors: \[^0\]" transcript}] == 0} {quit -code 5}'

script_file, aegis_json, test_name = sys.argv

# Read Aegis config for test
with open(aegis_json) as file:
    sim = json.load(file)['vsim'][test_name]

# Add design test name, forward CI_PROJECT_DIR
sim['tname'] = test_name
sim['ci_project_dir'] = dirname(dirname(dirname(realpath(script_file))))

# Sensible defaults
if 'vsim' not in sim:
    sim['vsim'] = os.getenv('VSIM') or 'vsim'
if 'timeres' not in sim:
    sim['timeres'] = '1ps'
if 'flags' not in sim:
    sim['flags'] = VSIM_DEFAULT_FLAGS
if 'runcmd' not in sim:
    sim['runcmd'] = 'run -all'

# Pass on variables for use in simulation script
for key, val in sim.items():
    if key in ('presim', 'runcmd', 'postsim', 'vsim', 'timeres', 'flags', 'params'):
        continue
    try:
        val = float(val)
    except (ValueError, TypeError):
        val = '"{}"'.format(val)
    print('set {} {}'.format(key.upper(), val))

# Stringify parameters if not already in string form
if 'params' in sim:
    if isinstance(sim['params'], dict):
        sim['params'] = ' '.join(['-G{}={}'.format(key, val) for key, val in sim['params'].items()])
else:
    sim['params'] = ''

# Compile and exit on error
print('\n# Compile simulation library')
assert('compile' in sim)
print('source ${COMPILE}')

# Pre-run commands: You can place any TCL code here, eg. sourcing or loops
print('\n# Load top level, check for prior errors, and run')
if 'presim' in sim:
    print(sim['presim'])

# Load design, exit on error in previous command, then run
print('{vsim} -c ${{TOPLEVEL}} -t {timeres} {params} {flags}'.format(**sim))
print(VSIM_QUIT_ON_ERROR)
print(sim['runcmd'])

# Post-run commands: You can place any TCL code here, eg. loop terminations
if 'postsim' in sim:
    print(sim['postsim'])

# Final error check and quit
print('\n# Check for errors and quit')
print(VSIM_QUIT_ON_ERROR + '\nquit')
