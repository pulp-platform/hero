# Parsing functions for SV2V messages

# Author: Paul Scheffler <paulsc@iis.ee.ethz.ch>
# Author: Thomas Benz <tbenz@iis.ee.ethz.ch>

import re
from collections import namedtuple

SV2V_RPT = r'(.*):(\d+):(\d+):\s+(.*)'
Sv2vMsg = namedtuple('MooreMsg', 'file line col msg')


def sv2v_parse(rpt_file: str) -> list:
    ret = []
    rpt = open(rpt_file, 'r').read()
    for line_str in rpt.split('\n'):
        matches = re.findall(SV2V_RPT, line_str)
        if len(matches):
            file, line, col, msg = matches[0]
            ret.append(Sv2vMsg(file, int(line), int(col), msg))
    return ret


if __name__ == '__main__':
    import sys
    from pprint import pprint
    _, rpt_file = sys.argv
    data = sv2v_parse(rpt_file)
    pprint(data)
