# Parsing functions for Verible messages

# Author: Paul Scheffler <paulsc@iis.ee.ethz.ch>
# Author: Thomas Benz <tbenz@iis.ee.ethz.ch>

import re
from collections import namedtuple

VERIBLE_RPT = r'(.*):(\d+):(\d+):\s+(.*)\[Style: ([^\]]+)] \[([^\]]+)\]'
VeribleMsg = namedtuple('MooreMsg', 'file line col msg style style_item')


def verible_parse(rpt_file: str) -> list:
    ret = []
    rpt = open(rpt_file, 'r').read()
    for line_str in rpt.split('\n'):
        matches = re.findall(VERIBLE_RPT, line_str)
        if len(matches):
            file, line, col, msg, style, style_item = matches[0]
            ret.append(VeribleMsg(file, int(line), int(col), msg, style, style_item))
    return ret


if __name__ == '__main__':
    import sys
    from pprint import pprint
    _, rpt_file = sys.argv
    data = verible_parse(rpt_file)
    pprint(data)
