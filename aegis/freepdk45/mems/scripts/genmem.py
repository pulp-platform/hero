import re

MEM_REGEX = r'openram_sram_D([0-9]+)_W([0-9]+)_B([0-9]+)_P([0-9]+)_freepdk45'
parsed_descr = re.findall(MEM_REGEX, input(''))[0]

# ---------------------------- OpenRAM  ------------------------------ #

num_words = int(parsed_descr[0])
word_size = int(parsed_descr[1])

# strobe
write_size = int(parsed_descr[2])

# number of ports
num_rw_ports = int(parsed_descr[3])

# Technology to use in $OPENRAM_TECH
tech_name = 'freepdk45'

# process corner
nominal_corner_only = True
process_corners = 'TT'
supply_voltages = [1.0]
temperatures = [25]

# debug
debug_level = 1

# speed-up process
route_supplies = False
check_lvsdrc = False
inline_lvsdrc = False
trim_netlist = False
use_pex = False

# Output directory for the results
output_path = 'out'
# Output file base name
output_name = 'openram_sram_D{0}_W{1}_B{2}_P{3}_{4}'.format(num_words, word_size, write_size, num_rw_ports, tech_name)
