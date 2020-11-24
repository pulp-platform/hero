import argparse
import json
import os
from hierarchy import *
from preprocess import get_common_base_path, replace_path_segment

parser = argparse.ArgumentParser(description='Create the sv2v command for Aegis')
parser.add_argument('aegis_json', type=str, help='the aegis json containing the tests')
parser.add_argument('test_name', type=str, help='the test to execute')
parser.add_argument('temp_dir', type=str, help='temporary directory')
args = parser.parse_args()

# canonicalize temp dir
temp_dir = os.path.normpath(args.temp_dir)

with open(args.aegis_json) as file:
    design = json.load(file)['sv2v'][args.test_name]

if not 'hierarchical' in design:
    design['hierarchical'] = False

# read file list
flist = os.path.expandvars(open(design['sources']).read())

files_only = flist.replace('+incdir+', '')
file_list = list(filter(None, files_only.split('\n')))
common_base_path = get_common_base_path(file_list)

# divide flist into includes and files
includes = []
files = []
for f in list(filter(None, flist.split('\n'))):
    if f.startswith('+incdir+'):
        includes.append(f.lstrip('+incdir+'))
    else:
        files.append(f)

for i in includes:
    print('-I {}'.format(replace_path_segment(i, common_base_path, args.temp_dir)))

if design['hierarchical']:
    files = strip_files(files, [temp_dir], design['design'])[0]

for f in files:
    print(replace_path_segment(f, common_base_path, temp_dir))
