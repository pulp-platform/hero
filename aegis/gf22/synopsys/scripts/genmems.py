import sys


MEM_OUTDIR = '../mems/out/model/timing/lib/'
MEM_TECH = '104cpp'
MEM_CORNER = 'SSG_0P720V_0P000V_0P000V_M40C'


file = sys.stdin
if len(sys.argv) > 1:
    file = open(sys.argv[1])

mems = file.read().split()

lines = ['lappend search_path "{}"'.format(MEM_OUTDIR)]
for mem in mems:
    lines.append('lappend link_library {}_{}_{}.db'.format(mem, MEM_TECH, MEM_CORNER))

print('\n'.join(lines))
