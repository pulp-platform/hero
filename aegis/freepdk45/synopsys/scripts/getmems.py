import sys
import re


MISSING_CELLS_REGEX = r'tc_sram_(NumWords)?([0-9A-Fa-f]+)_(DataWidth)?([0-9A-Fa-f]+)_(ByteWidth)?([0-9A-Fa-f]+)_(NumPorts)?([0-9A-Fa-f]+)'


def detect_hex(inp_string: str) -> int:
    if not inp_string.startswith('0'):
        return int(inp_string)
    else:
        return int('0x' + inp_string, 16)


def get_sram_names(rpt: str) -> set:
    missing_cell_types = re.findall(MISSING_CELLS_REGEX, rpt)

    sram_names = []

    for cell in missing_cell_types:
        sram_names.append('openram_sram_D{}_W{}_B{}_P{}_freepdk45'.format(
            detect_hex(cell[1]), detect_hex(cell[3]), detect_hex(cell[5]), detect_hex(cell[7])))

    return set(sram_names)


if __name__ == "__main__":
    rpt = sys.stdin.read()
    sram_names = get_sram_names(rpt)
    print(' '.join(sram_names))
