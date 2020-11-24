import argparse
import json
import os

parser = argparse.ArgumentParser(description='Create the moore command for Aegis')
parser.add_argument('aegis_json', type=str, help='the aegis json containing the tests')
parser.add_argument('test_name', type=str, help='the test to execute')
args = parser.parse_args()

with open(args.aegis_json) as file:
    design = json.load(file)['moore'][args.test_name]

# read file list
flist = os.path.expandvars(open(design['sources']).read())
# replace +incdir+ with -I
flist = flist.replace('+incdir+', '-I ')
# replace newlines with spaces
flist = flist.replace('\n', ' ')

# create the moore command
print('{}--elaborate {}'.format(flist,design['design']))
