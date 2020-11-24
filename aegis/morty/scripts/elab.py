import argparse
import json
import os
from hierarchy import *

parser = argparse.ArgumentParser(description='Create the morty command for Aegis')
parser.add_argument('aegis_json', type=str, help='the aegis json containing the tests')
parser.add_argument('test_name', type=str, help='the test to execute')
args = parser.parse_args()

with open(args.aegis_json) as file:
    design = json.load(file)['morty'][args.test_name]

if not 'hierarchical' in design:
    design['hierarchical'] = False

# read file list
flist = os.path.expandvars(open(design['sources']).read())

files_only = flist.replace('+incdir+', '')
file_list = list(filter(None, files_only.split('\n')))

# divide flist into includes and files
includes = []
files = []
for f in list(filter(None, flist.split('\n'))):
    if f.startswith('+incdir+'):
        includes.append(f.lstrip('+incdir+'))
    else:
        files.append(f)

for i in includes:
    print('-I {}'.format(i))

if design['hierarchical']:
    files = strip_files(files, includes, design['design'])[0]

for f in files:
    print(f)
