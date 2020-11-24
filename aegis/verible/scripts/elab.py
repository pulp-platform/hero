import argparse
import json
import re

parser = argparse.ArgumentParser(description='Create the verible command for Aegis')
parser.add_argument('aegis_json', type=str, help='the aegis json containing the tests')
parser.add_argument('test_name', type=str, help='the test to execute')
args = parser.parse_args()

with open(args.aegis_json) as file:
    design = json.load(file)['verible'][args.test_name]

# read file list
flist = open(design['sources']).read()
# replace +incdir+ with -I
flist = re.sub(r'\+incdir\+.*\n', '', flist)
# replace newlines with spaces
flist = flist.replace('\n', ' ')

# create the verible command
print('{}'.format(flist))
