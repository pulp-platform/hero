#!/usr/bin/env python3

import argparse
import re
import subprocess
import sys


def main():
    parser = argparse.ArgumentParser(
        description='Extract device image from heterogeneous ELF.')
    parser.add_argument('input_elf_path',
                        type=str,
                        help='path to input heterogeneous ELF file')
    parser.add_argument('output_elf_path',
                        type=str,
                        help='path to output device ELF file')
    args = parser.parse_args()

    # Get information of OMP offloading device image symbol.
    symbols = readelf_symbols(args.input_elf_path)
    device_image = [
        symbol for symbol in symbols
        if symbol.name == '.omp_offloading.device_image'
    ]
    if len(device_image) == 0:
        fatal("No OMP offloading device image found!")
    if len(device_image) > 1:
        fatal("More than one OMP offloading device image found!")
    device_image = device_image[0]

    # Get information of section containing the OMP offloading device image.
    sections = readelf_section_headers(args.input_elf_path)
    device_image_section = [
        section for section in sections if section.nr == device_image.ndx
    ]
    if len(device_image_section) == 0:
        fatal("Section number {} of offloading device image not found!" %
              device_image.ndx)
    if len(device_image_section) > 1:
        fatal("Multiple sections with number {} found!" % device_image.ndx)
    device_image_section = device_image_section[0]

    # Calculate offset given by address.
    address_offset = int(device_image_section.address, 16) - int(
        device_image_section.off, 16)
    if address_offset < 0:
        fatal("Negative address offset calculated!")
    image_offset = int(device_image.value, 16) - address_offset

    # Execute `dd` to extract image.
    subprocess.check_call([
        'dd', 'if=' + args.input_elf_path, 'of=' + args.output_elf_path,
        'bs=1', 'count=' + device_image.size, 'skip=' + str(image_offset)
    ])


class ELFSymbol(object):

    def __init__(self, num, value, size, typ, bind, vis, ndx, name):
        # No `dataclass` before Python 3.7 (which we have to support for ancient Linux distros).
        self.num = num
        self.value = value
        self.size = size
        self.typ = typ
        self.bind = bind
        self.vis = vis
        self.ndx = ndx
        self.name = name

    def __repr__(self):
        from pprint import pformat
        return pformat(vars(self))

    re_SYM_TAB_ENTRY = re.compile(
        r"\s*(\d+):\s+([0-9a-fA-F]+)\s+(\d+)\s+(\S+)\s+(\S+)\s+(\S+)\s+(\S+)\s+(\S*)"
    )

    def from_readelf_line(line):
        m = ELFSymbol.re_SYM_TAB_ENTRY.search(line)
        if m:
            return ELFSymbol(m.group(1), m.group(2), m.group(3), m.group(4),
                             m.group(5), m.group(6), m.group(7), m.group(8))
        else:
            return None


def readelf_symbols(elf_path):
    lines = output_lines(['llvm-readelf', '--symbols', elf_path])
    symbols = [ELFSymbol.from_readelf_line(line) for line in lines]
    return [symbol for symbol in symbols if symbol]


class ELFSectionHeader(object):

    def __init__(self, nr, name, typ, address, off, size):
        # Again no `dataclass` before Python 3.7.
        self.nr = nr
        self.name = name
        self.typ = typ
        self.address = address
        self.off = off
        self.size = size

    def __repr__(self):
        from pprint import pformat
        return pformat(vars(self))

    re_SECTION_HEADER = re.compile(
        r"\s*\[\s*(\d+)\]\s+(\S+)\s+(\S+)\s+([0-9a-fA-F]+)\s+([0-9a-fA-F]+)\s+([0-9a-fA-F]+).*"
    )

    def from_readelf_line(line):
        m = ELFSectionHeader.re_SECTION_HEADER.search(line)
        if m:
            return ELFSectionHeader(m.group(1), m.group(2), m.group(3),
                                    m.group(4), m.group(5), m.group(6))
        return None


def readelf_section_headers(elf_path):
    lines = output_lines(['llvm-readelf', '--section-headers', elf_path])
    headers = [ELFSectionHeader.from_readelf_line(line) for line in lines]
    return [header for header in headers if header]


def stderr(*args, **kwargs):
    import sys
    print(*args, file=sys.stderr, **kwargs)


def fatal(*args, **kwargs):
    import sys
    stderr(*args, **kwargs)
    sys.exit(1)


def output_lines(args):
    return [
        str(line)[1:-1] for line in subprocess.check_output(args).splitlines()
    ]


if __name__ == "__main__":
    main()
