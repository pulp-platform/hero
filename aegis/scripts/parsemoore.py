# Parsing functions for Moore messages

# Author: Paul Scheffler <paulsc@iis.ee.ethz.ch>
# Author: Thomas Benz <tbenz@iis.ee.ethz.ch>

import re
from collections import namedtuple

MOORE_RPT = r'([a-zA-Z ]+): (.*)\n  --> (.*):([0-9]+):([0-9]+)-([0-9]+):([0-9]+)?\n\s+\|\s*\n\s+\|(.*)\n\s+\|\s*(.*)'
MooreMsg = namedtuple('MooreMsg', 'cause message file line col_start col_stop content bug_str')


def moore_parse(rpt_file: str) -> list:
    moore_rpt = open(rpt_file, 'r').read().split('\n\n')
    items = []
    for idx, elem in enumerate(moore_rpt):
        parsed_finds = re.findall(MOORE_RPT, elem)
        if len(parsed_finds) == 0:
            continue
        parsed = parsed_finds[0]
        if elem.startswith('compiler bug'):
            bug_str = moore_rpt[idx + 1] + moore_rpt[idx + 2]
            items.append(MooreMsg(*parsed[:6], parsed[7].strip(), bug_str))
            break
        else:
            items.append(MooreMsg(*parsed[:6], parsed[7].strip(), ''))
    return items


if __name__ == '__main__':
    import sys
    from pprint import pprint
    _, rpt_file = sys.argv
    data = moore_parse(rpt_file)
    pprint(data)
