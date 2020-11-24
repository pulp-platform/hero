# Generates CI scripts for Aegis child pipelines.

# Author: Paul Scheffler <paulsc@iis.ee.ethz.ch>
# Author: Thomas Benz <tbenz@iis.ee.ethz.ch>

import sys
import json

BEFORE_SCRIPT = '''before_script:
  - source aegis.bashrc
'''

STAGES_FMT = '''stages:
{stages}
'''

BUILD_STAGE = '''aegis_build:
  stage: aegis_build
  script:
    - make -C test
  artifacts:
    paths:
      - test/*/analyze.tcl
      - test/*/analyze_vivado.tcl
      - test/*/compile_vsim.tcl
      - test/*/flist.txt
      - test/*/.bender
'''

SYNTH_TARGET_FMT = '''{tname}_{tech}_synth:
  stage: {tech}_synth
  resource_group: dc_explore
  script:
    - make -C {tech}/synopsys synth_{tname}
  dependencies:
    - aegis_build
  artifacts:
    paths:
      - freepdk45/synopsys/reports/{tname}/*.rpt
'''

MOORE_TARGET_FMT = '''{tname}_moore:
  stage: moore
  allow_failure: true
  script:
    - make -C moore moore_{tname}
  dependencies:
    - aegis_build
  artifacts:
    when: always
    paths:
      - moore/reports/{tname}_moore.rpt
      - moore/out/{tname}.llhd
'''

SV2V_TARGET_FMT = '''{tname}_sv2v:
  stage: sv2v
  allow_failure: true
  script:
    - make -C sv2v sv2v_{tname}
  dependencies:
    - aegis_build
  artifacts:
    when: always
    paths:
      - sv2v/reports/{tname}_sv2v.rpt
      - sv2v/out/{tname}.v
'''

VIVADO_TARGET_FMT = '''{tname}_vivado:
  stage: vivado
  script:
    - make -C vivado vivado_{tname}
  dependencies:
    - aegis_build
  artifacts:
    when: always
    paths:
      - vivado/reports/{tname}/*.rpt
      - vivado/reports/{tname}.vivado.log
'''

VERIBLE_TARGET_FMT = '''{tname}_verible:
  stage: verible
  allow_failure: true
  script:
    - make -C verible verible_{tname}
  dependencies:
    - aegis_build
  artifacts:
    when: always
    paths:
      - verible/reports/*.rpt
'''

SPYGLASS_TARGET_FMT = '''{tname}_spyglass:
  stage: spyglass
  allow_failure: true
  script:
    - make -C spyglass spyglass_{tname}
  dependencies:
    - aegis_build
  artifacts:
    when: always
    paths:
      - spyglass/reports/{tname}.*.elab_summary.rpt
      - spyglass/reports/{tname}.*.summary.rpt
      - spyglass/reports/{tname}.*.violations.rpt
'''

# TODO: Really, we want everything in simdir _except_ work and modelsim.ini... but Gitlab proposal for exclusion is WIP
VSIM_TARGET_FMT = '''{tname}_vsim:
  stage: vsim
  allow_failure: false
  script:
    - make -C vsim vsim_{tname}
  dependencies:
    - aegis_build
  artifacts:
    when: always
    paths:
      - vsim/{tname}.simdir/transcript
'''

GRAPH_TARGET_FMT = '''{tname}_graph:
  stage: graph
  allow_failure: true
  script:
    - make -C graph graph_{tname}
  dependencies:
    - aegis_build
  artifacts:
    when: always
    paths:
      - graph/out/{tname}.gv
      - graph/out/{tname}.*
'''

MORTY_TARGET_FMT = '''{tname}_morty:
  stage: morty
  allow_failure: true
  script:
    - make -C morty morty_{tname}
  dependencies:
    - aegis_build
  artifacts:
    when: always
    paths:
      - morty/doc/{tname}/*
      - morty/reports/{tname}.rpt
'''

# TODO: We likely need to keep separate directories for complex simulations, but this works so far
VERILATOR_TARGET_FMT = '''{tname}_verilator:
  stage: verilator
  script:
    - make -C verilator verilator_{tname}
  dependencies:
    - aegis_build
  artifacts:
    when: always
    paths:
      - verilator/{tname}.*.log
'''

_, aegis_json, sub_pipeline = sys.argv

stages = ['aegis_build']
tgt_lines = []

with open(aegis_json) as file:
    config = json.load(file)
    for tech, tools in config.items():
        if sub_pipeline == 'lint':
            if tech == 'spyglass':
                stages.append('spyglass')
                for tname in tools:
                    tgt_lines.append(SPYGLASS_TARGET_FMT.format(tname=tname))
            elif tech == 'verible':
                stages.append('verible')
                for tname in tools:
                    tgt_lines.append(VERIBLE_TARGET_FMT.format(tname=tname))
            elif tech == 'moore':
                stages.append('moore')
                for tname in tools:
                    tgt_lines.append(MOORE_TARGET_FMT.format(tname=tname))
            elif tech == 'sv2v':
                stages.append('sv2v')
                for tname in tools:
                    tgt_lines.append(SV2V_TARGET_FMT.format(tname=tname))
        if sub_pipeline == 'synth':
            if tech == 'vivado':
                stages.append('vivado')
                for tname in tools:
                    tgt_lines.append(VIVADO_TARGET_FMT.format(tname=tname))
            elif 'synopsys' in tools:
                stages.append(tech + '_synth')
                for tname in tools['synopsys']:
                    tgt_lines.append(SYNTH_TARGET_FMT.format(tname=tname, tech=tech))
        if sub_pipeline == 'sim':
            if tech == 'vsim':
                stages.append('vsim')
                for tname in tools:
                    tgt_lines.append(VSIM_TARGET_FMT.format(tname=tname))
            elif tech == 'verilator':
                stages.append('verilator')
                for tname in tools:
                    tgt_lines.append(VERILATOR_TARGET_FMT.format(tname=tname))
        if sub_pipeline == 'doc':
            if tech == 'graph':
                stages.append('graph')
                for tname in tools:
                    tgt_lines.append(GRAPH_TARGET_FMT.format(tname=tname))
            elif tech == 'morty':
                stages.append('morty')
                for tname in tools:
                    tgt_lines.append(MORTY_TARGET_FMT.format(tname=tname))



print(BEFORE_SCRIPT)
print(STAGES_FMT.format(stages='\n'.join(['    - ' + s for s in stages])))
print(BUILD_STAGE)
print('\n'.join(tgt_lines))
