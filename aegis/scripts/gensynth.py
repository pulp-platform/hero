# Generates synthesis wrapper scripts defining variables from an Aegis JSON.
# Works for different technologies and tools.

# Author: Paul Scheffler <paulsc@iis.ee.ethz.ch>
# Author: Thomas Benz <tbenz@iis.ee.ethz.ch>

import sys
import json
from os.path import dirname, realpath

script_file, aegis_json, test_path, synth_tcl = sys.argv

# Read Aegis config
with open(aegis_json) as file:
    cfg = json.load(file)

# Navigate config to desired test
path = test_path.split('/')
for node in path:
    cfg = cfg[node]
design = cfg
test_name = path[-1]

# Add design test name and default synthesis script if not set
design['tname'] = test_name
if 'synth' not in design:
    design['synth'] = synth_tcl

# Forward CI_PROJECT_DIR to pregenerated TCL scripts
design['ci_project_dir'] = dirname(dirname(realpath(script_file)))

# Generate synth TCL file for design
for key, val in design.items():
    try:
        val = float(val)
    except ValueError:
        val = '"{}"'.format(val)
    print('set {} {}'.format(key.upper(), val))
print('\nsource ${SYNTH}')
