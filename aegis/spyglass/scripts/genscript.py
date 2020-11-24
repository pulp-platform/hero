import argparse
import json
import re
import os

parser = argparse.ArgumentParser(description='Create the SpyGlass script for Aegis')
parser.add_argument('aegis_json', type=str, help='the aegis json containing the tests')
parser.add_argument('test_name', type=str, help='the test to execute')
parser.add_argument('report_dir', type=str, help='the report directory')
parser.add_argument('project_dir', type=str, help='the project directory')
args = parser.parse_args()

with open(args.aegis_json) as file:
    design = json.load(file)['spyglass'][args.test_name]

with open('tests.json') as file:
    tests = json.load(file)['tests']

# read file list
flist = os.path.expandvars(open(design['sources']).read()).split('\n')[:-1]

# create project
print('new_project {} -projectwdir {} -force'.format(args.test_name, args.project_dir))

# read in the include dirs
includedirs = []
for ele in flist:
    if ele.startswith('+incdir+'):
        includedirs.append(ele[8:])
    else:
        break
if len(includedirs) > 0:
    print('set_option incdir {{ {} }}'.format(' '.join(includedirs)))

# read in the sources
for ele in flist:
    if ele.startswith('+incdir+'):
        continue
    else:
        print('read_file -type hdl {}'.format(ele))

# switch to systemverilog
if 'lang' not in design:
    design['lang'] == 'systemverilog'

if design['lang'] == 'systemverilog':
    print('set_option enableSV09 yes')

# compile
print('')
print('compile_design > {}/{}.initial.compile.rpt'.format(args.report_dir, args.test_name))

# clocks
if 'tck' not in design:
    design['tck'] = '10.0'

if 'clock' not in design:
    design['clock'] = 'clk_i'

# insert clocks
print('')
print('catch {{ create_clock -name "{0}" -add -period {1:8.3f} -waveform {{0.0 {2:8.3f}}} [get_ports {0}] }}'.format(
    design['clock'], float(design['tck']), float(design['tck']) / 2.0))
print('')

# execute each specified test
for test in tests:
    test_name = test.replace('/', '^')
    print('current_goal {} -top {}'.format(test, design['design']))
    print('run_goal')
    print('write_report spyglass_violations > {}/{}.{}.{}.rpt'.format(args.report_dir, args.test_name, test_name, 'violations'))
    print('write_report summary > {}/{}.{}.{}.rpt'.format(args.report_dir, args.test_name, test_name, 'summary'))
    print('write_report elab_summary > {}/{}.{}.{}.rpt'.format(args.report_dir, args.test_name, test_name, 'elab_summary'))
    print('')

# close tool
print('save_project')
print('close_project')
print('exit')
