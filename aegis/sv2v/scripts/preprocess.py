#!/usr/bin/env python3
import argparse
import sys
import re
import json
import os
import glob

GUARDED_REGEX = r'// *(pragma translate_off)(.*?)// *(pragma translate_on)'
SYN_PRAGMA_REGEX = r'/``\*(.*)\*``/'


def remove_guarded_code(content : str) -> str:
    return re.sub(GUARDED_REGEX, '// guarded code segment was removed', content, flags=(re.MULTILINE | re.DOTALL))


def remove_synopsys_pragmas(conten: str) -> str:
    return re.sub(SYN_PRAGMA_REGEX, '// synopsys pragma was removed', content)


def get_common_base_path(file_list: str) -> str:
    ret = os.path.commonpath(file_list)
    # If common path is not a directory <=> one source file: take parent directory
    if not os.path.isdir(ret):
        ret = os.path.dirname(ret)
    return ret


def replace_path_segment(path: str, oldbase: str, newbase: str) -> str:
    return os.path.normpath(path).replace(os.path.normpath(oldbase), os.path.normpath(newbase))


if __name__ == '__main__':

    parser = argparse.ArgumentParser(description='Preprocess fils for sv2v')
    parser.add_argument('aegis_json', type=str, help='the aegis json containing the tests')
    parser.add_argument('test_name', type=str, help='the test to execute')
    parser.add_argument('temp_dir', type=str, help='temporary directory')
    args = parser.parse_args()

    with open(args.aegis_json) as file:
        design = json.load(file)['sv2v'][args.test_name]

    # read file list
    flist = os.path.expandvars(open(design['sources']).read())

    # handle incdirs
    incdirs = re.findall(r'\+incdir\+(.*)', flist)
    flist = re.sub(r'\+incdir\+(.*)', '', flist)

    for incdir in incdirs:
        for incfile in glob.glob(incdir + '/**/*', recursive=True):
            if os.path.isfile(incfile):
                flist += '{}\n'.format(incfile)

    file_list = list(filter(None, flist.split('\n')))
    common_base_path = get_common_base_path(file_list)

    for file in file_list:

        # canonicalize path
        file = os.path.normpath(file)

        # transform file
        content = open(file, 'r').read()

        # remove guarded code
        content = remove_guarded_code(content)

        # remove synopsys pragmas
        content = remove_synopsys_pragmas(content)

        # write file
        outname = replace_path_segment(file, common_base_path, args.temp_dir)

        # create folder if it does not exist
        if not os.path.exists(os.path.dirname(outname)):
            os.makedirs(os.path.dirname(outname))

        outfile = open(outname, 'w')
        outfile.write(content)
        outfile.close()
