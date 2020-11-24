import sys


MEM_OUTDIR = '../mems/out'

MEM_CORNER = 'TT_1p0V_25C'


file = sys.stdin
if len(sys.argv) > 1:
    file = open(sys.argv[1])

mems = file.read().split()

lines = ['lappend search_path "{}"'.format(MEM_OUTDIR)]
for mem in mems:
    lines.append('lappend link_library {}_{}.db'.format(mem, MEM_CORNER))

print('\n'.join(lines))
