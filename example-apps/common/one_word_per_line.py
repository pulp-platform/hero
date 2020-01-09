#!/usr/bin/env python3

import sys

slm_filepath = sys.argv[1]

output = list()
for line in open(slm_filepath, 'r'):
  words = line[:-1].split(' ')
  addr = int(words[0], 16)
  for word in words[1:]:
    if word:
      output.append("{:08x} {}".format(addr, word))
      addr += 4

with open(slm_filepath, 'w') as f:
  for line in output:
    f.write("0x{}\n".format(line))
