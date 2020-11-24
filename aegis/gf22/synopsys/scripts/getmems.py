import sys
import re


MISSING_CELLS_REGEX = r'tc_sram_(NumWords)?([0-9]+)_(DataWidth)?([0-9]+)_(ByteWidth)?([0-9]+)_(NumPorts)?([0-9]+)'


def detect_hex(inp_string: str) -> int:
    if str(int(inp_string)) == inp_string:
        return int(inp_string)
    else:
        return int('0x' + inp_string, 16)


def get_sram_names(rpt: str) -> set:
    missing_cell_types = re.findall(MISSING_CELLS_REGEX, rpt)

    sram_names = []

    for cell in missing_cell_types:
        if detect_hex(cell[3]) > 80:
            mux = 2
        else:
            mux = 4
        sram_names.append('IN22FDX_R1PH_NFHN_W{:05}B{:03}M{:02}C{:03}'.format(
            detect_hex(cell[1]), detect_hex(cell[3]), mux, 256))

    return set(sram_names)


if __name__ == "__main__":
    rpt = sys.stdin.read()
    sram_names = get_sram_names(rpt)
    print(' '.join(sram_names))
