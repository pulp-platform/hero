# Generates CI scripts for Aegis child pipelines.

# Author: Paul Scheffler <paulsc@iis.ee.ethz.ch>
# Author: Thomas Benz <tbenz@iis.ee.ethz.ch>

import sys
import os
import json

BEFORE_SCRIPT = '''before_script:
  - export AEGIS_FILE_PATH={aegis_file_path}
  - source {aegis_root}/aegis.bashrc
'''

STAGES_FMT = '''stages:
{stages}
'''

BUILD_STAGE_FMT = '''aegis_build:
  stage: aegis_build
  script:
    {script}
  artifacts:
    paths:
    - {artifacts}
'''

SYNTH_TARGET_FMT = '''{tname}_{tech}_synth:
  stage: {tech}_synth
  resource_group: dc_explore
  script:
    - make -C {aegis_root}/{tech}/synopsys synth_{tname}
  dependencies:
    - aegis_build
  artifacts:
    paths:
      - {aegis_root}/freepdk45/synopsys/reports/{tname}/*.rpt
'''

MOORE_TARGET_FMT = '''{tname}_moore:
  stage: moore
  allow_failure: true
  script:
    - make -C {aegis_root}/moore moore_{tname}
  dependencies:
    - aegis_build
  artifacts:
    when: always
    paths:
      - {aegis_root}/moore/reports/{tname}_moore.rpt
      - {aegis_root}/moore/out/{tname}.llhd
'''

SV2V_TARGET_FMT = '''{tname}_sv2v:
  stage: sv2v
  allow_failure: true
  script:
    - make -C {aegis_root}/sv2v sv2v_{tname}
  dependencies:
    - aegis_build
  artifacts:
    when: always
    paths:
      - {aegis_root}/sv2v/reports/{tname}_sv2v.rpt
      - {aegis_root}/sv2v/out/{tname}.v
'''

VIVADO_TARGET_FMT = '''{tname}_vivado:
  stage: vivado
  script:
    - make -C {aegis_root}/vivado vivado_{tname}
  dependencies:
    - aegis_build
  artifacts:
    when: always
    paths:
      - {aegis_root}/vivado/reports/{tname}/*.rpt
      - {aegis_root}/vivado/reports/{tname}.vivado.log
'''

VERIBLE_TARGET_FMT = '''{tname}_verible:
  stage: verible
  allow_failure: true
  script:
    - make -C {aegis_root}/verible verible_{tname}
  dependencies:
    - aegis_build
  artifacts:
    when: always
    paths:
      - {aegis_root}/verible/reports/*.rpt
'''

SPYGLASS_TARGET_FMT = '''{tname}_spyglass:
  stage: spyglass
  allow_failure: true
  script:
    - make -C {aegis_root}/spyglass spyglass_{tname}
  dependencies:
    - aegis_build
  artifacts:
    when: always
    paths:
      - {aegis_root}/spyglass/reports/{tname}.*.elab_summary.rpt
      - {aegis_root}/spyglass/reports/{tname}.*.summary.rpt
      - {aegis_root}/spyglass/reports/{tname}.*.violations.rpt
'''

# TODO: Really, we want everything in simdir _except_ work and modelsim.ini... but Gitlab proposal for exclusion is WIP
VSIM_TARGET_FMT = '''{tname}_vsim:
  stage: vsim
  allow_failure: false
  script:
    - make -C {aegis_root}/vsim vsim_{tname}
  dependencies:
    - aegis_build
  artifacts:
    when: always
    paths:
      - {aegis_root}/vsim/{tname}.simdir/transcript
'''

GRAPH_TARGET_FMT = '''{tname}_graph:
  stage: graph
  allow_failure: true
  script:
    - make -C {aegis_root}/graph graph_{tname}
  dependencies:
    - aegis_build
  artifacts:
    when: always
    paths:
      - {aegis_root}/graph/out/{tname}.gv
      - {aegis_root}/graph/out/{tname}.*
'''

MORTY_TARGET_FMT = '''{tname}_morty:
  stage: morty
  allow_failure: true
  script:
    - make -C {aegis_root}/morty morty_{tname}
  dependencies:
    - aegis_build
  artifacts:
    when: always
    paths:
      - {aegis_root}/morty/doc/{tname}/*
      - {aegis_root}/morty/reports/{tname}.rpt
'''

# TODO: We likely need to keep separate directories for complex simulations, but this works so far
VERILATOR_TARGET_FMT = '''{tname}_verilator:
  stage: verilator
  script:
    - make -C {aegis_root}/verilator verilator_{tname}
  dependencies:
    - aegis_build
  artifacts:
    when: always
    paths:
      - {aegis_root}/verilator/{tname}.*.log
'''

GTABLE_TARGET_FMT = '''{tname}_gtable:
  stage: gtable
  allow_failure: true
  script:
    - make -C {aegis_root}/gtable gtable_{tname}
  dependencies:
    - aegis_build
    - {dependencies}
'''

_, aegis_json, sub_pipeline, aegis_root, aegis_file_path = sys.argv

env_ci_proj_dir = os.getenv('CI_PROJECT_DIR')
if env_ci_proj_dir is not None:
    aegis_root      = '$CI_PROJECT_DIR/' + aegis_root
    aegis_file_path = '$CI_PROJECT_DIR/' + aegis_file_path

stages = ['aegis_build']
tgt_lines = []

with open(aegis_json) as file:
    config = json.load(file)
    for tech, tools in config.items():
        if tech == '_build':
            artifacts = '\n    - '.join(tools['artifacts'])
            tgt_lines.append(BUILD_STAGE_FMT.format(script=tools['script'], artifacts=artifacts))
        if sub_pipeline == 'lint':
            if tech == 'spyglass':
                stages.append('spyglass')
                for tname in tools:
                    tgt_lines.append(SPYGLASS_TARGET_FMT.format(tname=tname, aegis_root=aegis_root))
            elif tech == 'verible':
                stages.append('verible')
                for tname in tools:
                    tgt_lines.append(VERIBLE_TARGET_FMT.format(tname=tname, aegis_root=aegis_root))
            elif tech == 'moore':
                stages.append('moore')
                for tname in tools:
                    tgt_lines.append(MOORE_TARGET_FMT.format(tname=tname, aegis_root=aegis_root))
            elif tech == 'sv2v':
                stages.append('sv2v')
                for tname in tools:
                    tgt_lines.append(SV2V_TARGET_FMT.format(tname=tname, aegis_root=aegis_root))
        if sub_pipeline == 'synth':
            if tech == 'vivado':
                stages.append('vivado')
                for tname in tools:
                    tgt_lines.append(VIVADO_TARGET_FMT.format(tname=tname, aegis_root=aegis_root))
            elif 'synopsys' in tools:
                stages.append(tech + '_synth')
                for tname in tools['synopsys']:
                    tgt_lines.append(SYNTH_TARGET_FMT.format(tname=tname, tech=tech, aegis_root=aegis_root))
            elif tech == 'gtable':
                stages.append('gtable')
                for tname in tools:
                    dep_candidates = []
                    for s in stages:
                        if 'synth' in s:
                          dep_candidates.append(tname + '_' + s)
                    dependencies = '    - '.join(dep_candidates)
                    tgt_lines.append(GTABLE_TARGET_FMT.format(tname=tname, aegis_root=aegis_root, dependencies=dependencies))
        if sub_pipeline == 'sim':
            if tech == 'vsim':
                stages.append('vsim')
                for tname in tools:
                    tgt_lines.append(VSIM_TARGET_FMT.format(tname=tname, aegis_root=aegis_root))
            elif tech == 'verilator':
                stages.append('verilator')
                for tname in tools:
                    tgt_lines.append(VERILATOR_TARGET_FMT.format(tname=tname, aegis_root=aegis_root))
        if sub_pipeline == 'doc':
            if tech == 'graph':
                stages.append('graph')
                for tname in tools:
                    tgt_lines.append(GRAPH_TARGET_FMT.format(tname=tname, aegis_root=aegis_root))
            elif tech == 'morty':
                stages.append('morty')
                for tname in tools:
                    tgt_lines.append(MORTY_TARGET_FMT.format(tname=tname, aegis_root=aegis_root))



print(BEFORE_SCRIPT.format(aegis_root=aegis_root, aegis_file_path=aegis_file_path))
print(STAGES_FMT.format(stages='\n'.join(['    - ' + s for s in stages])))
print('\n'.join(tgt_lines))
