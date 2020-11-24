import re
import sys
import os


MODULE_DEF_REGEX = r'module ([a-zA-Z0-9_]+)(?:.*?)(?:\#)?\('
MODULE_INST_REGEX = r'([a-zA-Z0-9_]+) *(?:# *\([^;]*\))? *(?:[a-zA-Z0-9_]+) *(?:\( *\..*?\));'
INDIR_IMPORT_REGEX = r'([a-zA-Z0-9_]+)::'
PKG_REGEX = r'package ([a-zA-Z0-9_]+)'
INTERFACE_REGEX = r'interface ([a-zA-Z0-9_]+)(?:.*?)(?:\#)?\('
INCLUDE_MACRO_REGEX = r'`include "(.*?)"'

LINE_COMMENT_REGEX = r'//.*\n'
COMMENT_REGEX = r'\/\*.*?\*\/'
IFDEF_REGEX = r'`if[n]*def *([a-zA-Z0-9_]+) *(.*?)`endif'


def strip(content: str) -> str:
    content = re.sub(LINE_COMMENT_REGEX, '', content)
    content = re.sub(COMMENT_REGEX, '', content, flags=re.DOTALL)
    content = re.sub(r' +', ' ', content)
    content = re.sub(r'\n', ' ', content)
    content = re.sub(IFDEF_REGEX, '\g<2>', content)
    content = re.sub(r' +', ' ', content)
    content = re.sub(r'\n', ' ', content)
    content = content.replace('endmodule', 'endmodule\n')
    content = content.replace('endpackage', 'endpackage\n')
    return content

def extract_entities(entity: str, content: str) -> str:
    #print(module)
    #print(content)
    MODULE_CAPTURE_REGEX = r'(module.*?endmodule)'
    PACKAGE_CAPTURE_REGEX = r'(package.*?endpackage)'

    modules = re.findall(MODULE_CAPTURE_REGEX, content)
    packages = re.findall(PACKAGE_CAPTURE_REGEX, content)

    discoverd_modules = {}
    discovered_packages = {}

    # extract modules
    for module in modules:
        module_name = re.findall(r'module *([a-zA-Z0-9_]+)', module)[0]
        discoverd_modules[module_name] = module
        content = content.replace(module, '')

    # extract packages
    for package in packages:
        package_name = re.findall(r'package *([a-zA-Z0-9_]+)', package)[0]
        discovered_packages[package_name] = package
        content = content.replace(package, '')

    # reinsert wanted contend
    if entity in discoverd_modules:
        content += discoverd_modules[entity]
    elif entity in discovered_packages:
            content += discovered_packages[entity]

    return content


def locate_modules(file_list: list) -> dict:
    module_location = {}
    for file in file_list:
        modules = re.findall(MODULE_DEF_REGEX, strip(open(file).read()))
        if len(modules) > 0:
            for module in modules:
                #print(module, file)
                module_location[module] = file

    return module_location


def locate_interfaces(file_list: list) -> dict:
    interface_location = {}
    for file in file_list:
        interfaces = re.findall(INTERFACE_REGEX, open(file).read())
        if len(interfaces) > 0:
            for interface in interfaces:
                interface_location[interface] = file

    return interface_location


def locate_packages(file_list: list) -> dict:
    pkg_location = {}
    for file in file_list:
        pkgs = re.findall(PKG_REGEX, strip(open(file).read()))
        if len(pkgs) > 0:
            for pkg in pkgs:
                pkg_location[pkg] = file
    return pkg_location


def check_includes(inc_dirs: list, include: str) -> bool:
    valid_paths = []
    for inc_dir in inc_dirs:
        path = inc_dir + '/' + include
        if os.path.exists(path):
            valid_paths.append(path)

            # search for sub_includes...
            content = strip(open(path).read())
            includes = list(set(re.findall(INCLUDE_MACRO_REGEX, content)))
            if len(includes) > 0:
                for inc in includes:
                    valid_paths.extend(check_includes(inc_dirs, inc))

    return valid_paths


def discover_elements(module_name: str, module_location: dict, top_module: str, elements: list, blackboxes: list, inc_dirs: list, inc_files: list, missing_incs: list):

    # find filename for module
    if module_name in module_location:
        file_name = module_location[module_name]
        #print(module_name)
    else:
        blackboxes.append((module_name, module_location[top_module]))
        #print('bb    ' + module_name)
        return

    if not module_name in elements:
        elements.append(module_name)

    content = strip(open(file_name).read())

    #f = open('scripts/tmp/' + os.path.basename(file_name), 'w')
    #f.write(content)
    #f.close()

    modules = list(set(re.findall(MODULE_INST_REGEX, content)))
    imports = list(set(re.findall(INDIR_IMPORT_REGEX, content)))
    includes = list(set(re.findall(INCLUDE_MACRO_REGEX, content)))

    if len(includes) > 0:
        for inc in includes:
            valid_paths = check_includes(inc_dirs, inc)
            if len(valid_paths) > 0:
                inc_files.extend(valid_paths)
            else:
                if not inc in missing_incs:
                    missing_incs.append((inc, module_location[top_module]))

    if len(modules) > 0:
        for module in modules:
            if not module in elements:
                elements.append(module)
                #print('module: ' + module)
                discover_elements(module, module_location, module_name, elements, blackboxes, inc_dirs, inc_files, missing_incs)

    if len(imports) > 0:
        for imp in imports:
            if not imp in elements:
                elements.append(imp)
                #print('import: ' + imp)
                discover_elements(imp, module_location, module_name, elements, blackboxes, inc_dirs, inc_files, missing_incs)

    return


def get_filenames(sub_elements: list, module_location: dict) -> list:
    res = []
    for ele in sub_elements:
        if ele in module_location:
            res.append(module_location[ele])
    return res


def strip_files(file_list: list, inc_dirs: list, top_module: str) -> list:
    module_location = locate_modules(file_list)
    pkg_location = locate_packages(file_list)
    interface_location = locate_interfaces(file_list)
    module_location.update(pkg_location)
    module_location.update(interface_location)

    #for key in pkg_location:
    #    print('-' + pkg_location[key][41:])

    sub_elements = []
    blackboxes = []
    inc_files = []
    missing_incs = []
    discover_elements(top_module, module_location, 'root', sub_elements, blackboxes, inc_dirs, inc_files, missing_incs)
    used_files = get_filenames(sub_elements, module_location)

    # remove duplicate includes
    inc_files = list(set(inc_files))

    # arrange the files used in the correct order
    stripped_list = []
    unused_list = []
    for file in file_list:
        if file in used_files:
            stripped_list.append(file)
        else:
            unused_list.append(file)

    return [stripped_list, unused_list, blackboxes, inc_files, missing_incs]


if __name__ == '__main__':
    _, flist_name, top = sys.argv
    flist = os.path.expandvars(open(flist_name, 'r').read()).split('\n')
    files = []
    inc_dirs = []
    for f in flist:
        if not f.startswith('+') and f != '':
            files.append(f)
        elif f != '':
            inc_dirs.append(f[8:])

    [used, unused, bb, incs, missing_incs] = strip_files(files, inc_dirs, top)

    print('\033[1mUsed Source Files:\033[0m')
    for ele in used:
        print('\033[92m{}\033[0m'.format(ele))
    print('')

    print('\033[1mUnused Source Files:\033[0m')
    for ele in unused:
        print('\033[93m{}\033[0m'.format(ele))
    print('')

    print('\033[1mBlackboxes:\033[0m')
    for ele in bb:
        print('\033[91m{}\033[0m in {}'.format(ele[0], ele[1]))
    print('')

    print('\033[1mIncluded Files:\033[0m')
    for ele in incs:
        print('\033[92m{}\033[0m'.format(ele))
    print('')

    print('\033[1mMissing Includes:\033[0m')
    for ele in missing_incs:
        print('\033[91m{}\033[0m in {}'.format(ele[0], ele[1]))
    print('')
