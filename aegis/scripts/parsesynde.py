# Parsing functions for Synopsys DE reports

# Author: Paul Scheffler <paulsc@iis.ee.ethz.ch>
# Author: Thomas Benz <tbenz@iis.ee.ethz.ch>

import re
from collections import namedtuple

SYNDE_KEYVAL_REGEX_ML = r'^([^\s][^:\n]+?)\s*:[ \t]+(.*)$'

SYNDE_AREA_HIERDIV = 'Hierarchical area distribution\n------------------------------'
SYNDE_AREA_TABLEDIV_REGEX = r'(?:-+\s+){7}'
SyndeAreaItem = namedtuple('SyndeAreaItem', 'cell glob_abstot glob_perctot loc_comb loc_noncomb loc_bb design')

SYNDE_TIMING_CLKDIV_PREFIX = 'Startpoint: '
SYNDE_TIMING_CLKDIV_REGEX = r'\n  {}'.format(SYNDE_TIMING_CLKDIV_PREFIX)
SYNDE_TIMING_HIERDIV_REGEX = r'\n-+\n'
SYNDE_TIMING_SLACK_REGEX = r'slack \((?:MET|VIOLATED)\)\s+([^\s]+)'
SYNDE_TIMING_POINT_REGEX_ML = r'^\s*([^\s]+)(?:\s+\(([^\)]+)\))?$'
SyndeTimingItem = namedtuple('SyndeTimingItem', 'point cell incr path edge')

SYNDE_QOR_TIMGROUPS_REGEX = r'Timing Path Group \'(.*)\''
SYNDE_QOR_KEYVAL_REGEX = r'(.*?):(.*?)\n'

SYNDE_DP_KEYVAL_REGEX = r'(.*?): +area = +([0-9\.]+)%, +parts = +([0-9]*)\n'

SYNDE_DPEXT_ISSUES_REGEX = r'(.*?) +\(([a-zA-Z]+-[0-9]+)\)'

SYNDE_MISM_TABLEDIV_REGEX = r'Design\s+Object\s+Type\s+Mismatch\n-+'
SYNDE_MISM_RETCODE = '\n\n'
SyndeMismItem = namedtuple('SyndeMismItem', 'design object type mismatch')


def to_float_if_numeric(val_str: str):
    try:
        return float(val_str)
    except ValueError:
        return val_str


def synde_parse_keyvals(rpt: str) -> dict:
    # Basic Key: Value infos in DE reports
    keyvals = re.findall(SYNDE_KEYVAL_REGEX_ML, rpt, flags=re.MULTILINE)
    return {key: to_float_if_numeric(val) for key, val in keyvals}


def synde_parse_area(rpt: str) -> dict:
    basic, hierarchy = rpt.split(SYNDE_AREA_HIERDIV)
    ret = synde_parse_keyvals(basic)
    hierarchy_rows = re.split(SYNDE_AREA_TABLEDIV_REGEX, hierarchy)[1].rstrip('\n').split('\n')
    ret['hier'] = [SyndeAreaItem(*(to_float_if_numeric(e) for e in row.split())) for row in hierarchy_rows]
    return ret


def synde_parse_timing(rpt: str) -> dict:
    basic, *paths = re.split(SYNDE_TIMING_CLKDIV_REGEX, rpt)
    paths = [SYNDE_TIMING_CLKDIV_PREFIX + p for p in paths]     # Reappend first entry consumed by Regex
    ret = synde_parse_keyvals(basic)
    ret_paths = []
    for path in paths:
        path = path.replace('\n  ', '\n')                     # Undo bizarre indent
        path_basic, lpath_rows, reqarr, slack = re.split(SYNDE_TIMING_HIERDIV_REGEX, path)
        lpath_rows = re.sub(r'\n\s+', '  ', lpath_rows)       # Undo table row splitting if any
        path_dict = synde_parse_keyvals(path_basic)
        path_dict['slack'] = float(re.findall(SYNDE_TIMING_SLACK_REGEX, slack)[0])
        # Parse longest path rows
        path_dict['elems'] = []
        for row in lpath_rows.split('\n'):
            # Distinguish timed ports of cells and "meta-increments" in timing
            match_tpl = re.split(r'\s\s+', row)
            if len(match_tpl) != 3:
                continue
            point, incr, totlen = match_tpl
            cell_points = re.findall(SYNDE_TIMING_POINT_REGEX_ML, point, flags=re.MULTILINE)
            cell = None
            if len(cell_points):
                point, cell = cell_points[0]
            edge = None
            # Parse rising or falling flank at end of path
            if totlen.endswith('r') or totlen.endswith('f'):
                edge = totlen[-1]
                totlen = totlen[:-2]
            path_dict['elems'].append(SyndeTimingItem(point, cell, float(incr), float(totlen), edge))
        # Extract required and arrival time
        path_dict['data_required'] = float(re.findall(r'data required time\s+([^\s]+)', reqarr)[0])
        path_dict['data_arrival'] = float(re.findall(r'data arrival time\s+([^\s]+)', reqarr)[0])
        ret_paths.append(path_dict)
        ret['paths'] = ret_paths
    return ret


def synde_parse_qor(rpt: str) -> dict:
    path_groups = re.findall(SYNDE_QOR_TIMGROUPS_REGEX, rpt)
    qor_report = re.findall(SYNDE_QOR_KEYVAL_REGEX, rpt)
    # go through qor keys and create a dict with all the data
    qor_dict = {}
    for qor_ele in qor_report:
        key = qor_ele[0].strip()
        # append to dict
        if key not in qor_dict:
            qor_dict[key] = to_float_if_numeric(qor_ele[1].strip())
        # multiple path groups introduce same keys -> create subdict
        else:
            # sub element can be a string -> second encounter of the key
            if not isinstance(qor_dict[key], dict):
                sub_dict = {path_groups[0]: qor_dict[key], path_groups[1]: qor_ele[1].strip()}
                qor_dict[key] = sub_dict
            # sub element is already a dict
            else:
                qor_dict[key][path_groups[len(qor_dict[key])]] = qor_ele[1].strip()
    return qor_dict


def synde_parse_dp(rpt: str) -> dict:
    ret = {}
    dp_report = re.findall(SYNDE_DP_KEYVAL_REGEX, rpt)
    for dp_ele in dp_report:
        ret[dp_ele[0]] = {'area': dp_ele[1], 'parts': dp_ele[2]}
    return ret


def synde_parse_dp_extraction(rpt: str) -> dict:
    issues = []
    dp_ext_report = re.findall(SYNDE_DPEXT_ISSUES_REGEX, rpt)
    # create a dict with all the metrics
    for dp_ele in dp_ext_report:
        issues.append({'id': dp_ele[1], 'msg': dp_ele[0]})
    return {'num_issues': len(issues), 'issues': issues}


def synde_parse_mismatches(rpt: str) -> dict:
    basic, table = re.split(SYNDE_MISM_TABLEDIV_REGEX, rpt)
    table.strip('\n')
    ret = synde_parse_keyvals(basic)
    mism = []
    for line in table.split('\n'):
        tpl = re.split('\t', line)
        if len(tpl) == 4:
            mism.append(SyndeMismItem(*tpl))
    ret['mismatches'] = mism
    return ret


def synde_parse(rptdir: str) -> dict:
    rpt = lambda r: open('{}/{}.rpt'.format(rptdir, r)).read()
    return {
        'area': synde_parse_area(rpt('area')),
        'timing': synde_parse_timing(rpt('timing')),
        'datapath': synde_parse_dp(rpt('datapath')),
        'datapath_extraction': synde_parse_dp_extraction(rpt('datapath_extraction')),
        'qor': synde_parse_qor(rpt('qor')),
        'mismatches':  synde_parse_mismatches(rpt('design_mismatch'))
    }


if __name__ == '__main__':
    import sys
    from pprint import pprint
    _, rpt_dir = sys.argv
    data = synde_parse(rpt_dir)
    pprint(data)
