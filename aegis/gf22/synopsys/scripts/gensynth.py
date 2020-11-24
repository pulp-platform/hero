import sys
import json


_, aegis_json, test_name = sys.argv

with open(aegis_json) as file:
    design = json.load(file)['gf22']['synopsys'][test_name]

# Add design test name and synthesis script if not set
design['tname'] = test_name
if 'synth' not in design:
    design['synth'] = 'scripts/synth.tcl'

# Generate synth TCL file for design
for key, val in design.items():
    try:
        val = float(val)
    except ValueError:
        val = '"{}"'.format(val)
    print('set {} {}'.format(key.upper(), val))
print('\nsource ${SYNTH}')
