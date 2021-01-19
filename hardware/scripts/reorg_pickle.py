#!/usr/bin/env python3

import re
import argparse

parser = argparse.ArgumentParser(description='Reorg the pickle file.')
parser.add_argument('in_file_path', type=str)
parser.add_argument('out_file_path', type=str)
args = parser.parse_args()

pickled_file = args.in_file_path

pickle = open(pickled_file, 'r').read()

packages = re.findall(r'(\n *package.*?endpackage)', pickle, flags=re.DOTALL)
packageless = re.sub(r'(\n *package.*?endpackage)' ,'\n// removed package', pickle, flags=re.DOTALL)
packages = '\n\n'.join(packages)

interfaces = re.findall(r'(\n *interface.*?endinterface)', packageless, flags=re.DOTALL)
interfaceless = re.sub(r'(\n *interface.*?endinterface)' ,'\n// removed interface', packageless, flags=re.DOTALL)
interfaces = '\n\n'.join(interfaces)

pickle = packages + interfaces + interfaceless

pickle_processed = open(args.out_file_path, 'w')
pickle_processed.write(pickle)
pickle_processed.close()