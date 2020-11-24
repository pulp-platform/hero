from graphviz import Digraph
import argparse
import json
import sys
from hierarchy import *

def uniquify_names(name_db: dict, name: str) -> str:
    res = ''
    if not name in name_db:
        name_db[name] = 1
        res = '{}_{}'.format(name, '0')
    else:
        res = '{}_{}'.format(name, name_db[name])
        name_db[name] += 1
    return res


def traverse_sources(module_name: str, top_module: str, module_location: dict, inc_dirs: list, name_db: dict, shape: str, uniquify: bool, dot):

    if uniquify:
        # check if we are our parent...
        if '_'.join(top_module.split('_')[:-1]) == module_name:
            return
        unique_name = uniquify_names(name_db, module_name)
    else:
        # check if we are our parent...
        if top_module == module_name:
            return
        unique_name = module_name

    # find filename for module if not we are a blackbox :(
    if module_name in module_location:
        file_name = module_location[module_name]
        dot.node(unique_name, module_name, shape=shape, fontcolor='black')
        print(top_module, unique_name, file=sys.stderr)
        dot.edge(top_module, unique_name)
    else:
        dot.node(unique_name, module_name, shape=shape, fontcolor='red')
        print(top_module, unique_name, file=sys.stderr)
        dot.edge(top_module, unique_name)
        return

    content = strip(open(file_name).read())
    content = extract_entities(module_name, content)

    #print(content)

    modules = list(set(re.findall(MODULE_INST_REGEX, content)))
    imports = list(set(re.findall(INDIR_IMPORT_REGEX, content)))
    includes = list(set(re.findall(INCLUDE_MACRO_REGEX, content)))

    #print(modules, imports, includes, file=sys.stderr)

    if len(includes) > 0:
        for inc in includes:
            valid_files = check_includes(inc_dirs, inc)
            if len(valid_files) > 0:
                for valid_file in valid_files:
                    module_location.update({inc : valid_file})
                    traverse_sources(inc, unique_name, module_location, inc_dirs, name_db, 'hexagon', uniquify, dot)

    if len(modules) > 0:
        for module in modules:
            traverse_sources(module, unique_name, module_location, inc_dirs, name_db, 'oval', uniquify, dot)

    if len(imports) > 0:
        for imp in imports:
            if imp != 'package':
                traverse_sources(imp, unique_name, module_location, inc_dirs, name_db, 'box', uniquify, dot)

    return


def draw_graph(file_list: list, inc_dirs: list, top_module: str, uniquify: bool, dot):
    module_location = locate_modules(file_list)
    pkg_location = locate_packages(file_list)
    interface_location = locate_interfaces(file_list)
    module_location.update(pkg_location)
    module_location.update(interface_location)
    name_db = {}
    traverse_sources(top_module, 'root', module_location, inc_dirs, name_db, 'oval', uniquify, dot)


#if __name__ == '__main__':
#    _, flist_name, top = sys.argv
#    dot = Digraph(comment='SourceCode', filename=top + '.gv', format='pdf')
#    flist = open(flist_name, 'r').read().split('\n')
#    files = []
#    inc_dirs = []
#    for f in flist:
#        if not f.startswith('+') and f != '':
#            files.append(f)
#        elif f != '':
#            inc_dirs.append(f[8:])
#
#    draw_graph(files, inc_dirs, top, True, dot)
#
#    #print(dot.source)
#    dot.render()

if __name__ == '__main__':

    parser = argparse.ArgumentParser(description='Use Graphviz to map sources')
    parser.add_argument('aegis_json', type=str, help='the aegis json containing the tests')
    parser.add_argument('test_name', type=str, help='the test to execute')
    args = parser.parse_args()

    with open(args.aegis_json) as file:
        design = json.load(file)['graph'][args.test_name]

    # read file list
    flist = os.path.expandvars(open(design['sources']).read()).split('\n')

    # create graph
    dot = Digraph(comment='SourceCode')

    # split into sources and includes
    files = []
    inc_dirs = []
    for f in flist:
        if not f.startswith('+') and f != '':
            files.append(f)
        elif f != '':
            inc_dirs.append(f[8:])

    # create the graph
    draw_graph(files, inc_dirs, design['design'], True, dot)

    print(dot)
