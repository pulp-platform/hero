# Parsing functions for Vivado reports

# Author: Paul Scheffler <paulsc@iis.ee.ethz.ch>
# Author: Thomas Benz <tbenz@iis.ee.ethz.ch>

import re
from collections import namedtuple


VIVADO_TABLE_HLINE1_REGEX = r'(?:(.*):\s*\n)?(?:\+-+)+\+'
VivadoTable = namedtuple('VivadoTable', 'title header rows')


# Returns dict of named and list of unnamed tables in a report
def vivado_parse_tables(rpt: str) -> (dict, list):
    table_segs = re.split(VIVADO_TABLE_HLINE1_REGEX, rpt)
    ret_dict = {}    # Group unnamed tables in list
    ret_list = []
    i = 0
    while i < len(table_segs):
        if len(table_segs) - i < 5:
            break
        _, title, header_str, _, content_str, _ = table_segs[i:i+6]
        header = re.split(r'\s?\|', header_str)[1:-1]
        rows = []
        for row in content_str.split('\n'):
            if row:
                rows.append(re.split(r'\s?\|', row)[1:-1])
        table = VivadoTable(title, header, rows)
        if title is None:
            ret_list.append(table)
        else:
            ret_dict[title] = table
        i += 6
    return ret_dict, ret_list


def vivado_process_table_cells(val_str: str):
    try:
        return int(val_str)
    except ValueError:
        try:
            return float(val_str)
        except ValueError:
            return val_str.strip()


# Post-processing of Vivado's tables:
# removes index columns, decodes 2-space-indent instance hierarchies, and casts ints and floats where applicable
def vivado_process_table(table: VivadoTable) -> VivadoTable:
    has_idx_column = int(table.header[0].strip() == '')
    has_inst_column = True
    inst_idx = None
    for idx, colname in enumerate(table.header):
        if colname.strip() == 'Instance':
            inst_idx = idx
            break
    else:
        has_inst_column = False
    if has_inst_column:
        rows_out = []
        inst_path = []
        inst_prev = None
        indent = lambda s: int((len(s) - len(s.lstrip()))//2)
        for row in table.rows:
            inst = row[inst_idx]
            indent_increase = indent(inst) - len(inst_path)
            if indent_increase > 0:
                assert indent_increase == 1
                inst_path.append(inst_prev)
            elif indent_increase < 0:
                for _ in range(-indent_increase):
                    inst_path.pop()
            inst_stripped = inst.strip()
            row_out = [vivado_process_table_cells(cell) for cell in row]
            full_path = '/'.join((*inst_path, inst_stripped))
            row_out[inst_idx] = full_path.replace('/\\', '.')   # Fix backslash as generate indicator
            rows_out.append(row_out[has_idx_column:])
            inst_prev = inst_stripped
    else:
        rows_out = [[vivado_process_table_cells(c) for c in r[has_idx_column:]] for r in table.rows ]

    header_out = [vivado_process_table_cells(colname) for colname in table.header]
    table = VivadoTable(table.title, header_out[has_idx_column:], rows_out)
    return table


def vivado_table_to_tuple_list(table: VivadoTable, tuple_name: str) -> list:
    tuple_spec_str = ' '.join([re.sub(r'\s+', '_', c.lower()) for c in table.header])
    tuple_type = namedtuple(tuple_name, tuple_spec_str)
    return [tuple_type(*row) for row in table.rows]


def vivado_parse_timing(rpt: str) -> dict:
    return {}


def vivado_parse_utilization(rpt: str) -> list:
    util_table = vivado_parse_tables(rpt)[1][0]     # First unnamed table in report
    return vivado_table_to_tuple_list(vivado_process_table(util_table), 'VivadoUtilItem')


def vivado_parse_synth(rpt: str) -> dict:
    named, unnamed = vivado_parse_tables(rpt)
    return {
        'bbs': vivado_table_to_tuple_list(vivado_process_table(named['Report BlackBoxes']), 'VivadoBlackboxItem'),
        'inst_area': vivado_table_to_tuple_list(vivado_process_table(named['Report Instance Areas']), 'VivadoInstareaItem'),
        'cell_usage': vivado_table_to_tuple_list(vivado_process_table(named['Report Cell Usage']), 'VivadoCellusageItem')
    }


def vivado_parse(rptdir: str) -> dict:
    rpt = lambda r: open('{}/{}.rpt'.format(rptdir, r)).read()
    return {
        'timing': vivado_parse_timing(rpt('timing')),
        'utilization': vivado_parse_utilization(rpt('utilization')),
        'synth': vivado_parse_synth(rpt('synth')),
    }


if __name__ == '__main__':
    import sys
    from pprint import pprint
    _, rpt_dir = sys.argv
    data = vivado_parse(rpt_dir)
    pprint(data)
