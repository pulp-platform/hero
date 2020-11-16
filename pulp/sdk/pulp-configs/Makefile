#
# Copyright (C) 2018 ETH Zurich and University of Bologna and GreenWaves Technologies SAS
#
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
#     http://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.
#

# Authors: Martin Croome, GreenWaves Technologies

INSTALL_DIR ?= $(CURDIR)/install
# TARGET_INSTALL_DIR ?= $(CURDIR)/install
BUILD_DIR   ?= $(CURDIR)/build
RELEASE_TYPE ?= Debug
# propagate verbose for debugging
VERBOSE ?= 0

ifndef CMAKE
HAS_CMAKE3 = $(shell which cmake3)
ifeq '$(HAS_CMAKE3)' ''
CMAKE = $(shell which cmake-3.7.1)
ifeq '$(CMAKE)' ''
CMAKE = cmake
endif
else
CMAKE = cmake3
endif
endif

$(info #### Building in $(BUILD_DIR))
$(info #### Release type is $(RELEASE_TYPE))
$(info #### Installing to $(INSTALL_DIR))
# $(info #### Installing target files to $(TARGET_INSTALL_DIR))

MAKEFILE_DIR = $(dir $(realpath $(firstword $(MAKEFILE_LIST))))

all: install

install: $(BUILD_DIR)/Makefile
	( cd $(BUILD_DIR) ; make install $(DBG_CMAKE) VERBOSE=$(VERBOSE) )

gen: $(BUILD_DIR)/Makefile
	( cd $(BUILD_DIR) ; make gen $(DBG_CMAKE) VERBOSE=$(VERBOSE) )

clean:
	rm -rf $(BUILD_DIR)

gen.usecases:
	./bin/pulp_usecase_gen --configs=$(CURDIR)/configs --cam --output=configs/usecases/jtag-cam.json
	./bin/pulp_usecase_gen --configs=$(CURDIR)/configs --output=configs/usecases/jtag.json

gen.pulp:
	./bin/pulp_config_gen --configs=$(CURDIR)/configs --template=templates/chips/pulp/pulp.json --output-dir=$(CURDIR)/configs/chips/pulp --output=configs/systems/pulp.json --usecase=usecases/jtag-cam.json

gen.multino:
	./bin/pulp_config_gen --configs=$(CURDIR)/configs --template=templates/chips/multino/multino.json --output-dir=$(CURDIR)/configs/chips/multino --output=configs/systems/multino.json --usecase=usecases/jtag.json

gen.pulpissimo:
	./bin/pulp_config_gen --configs=$(CURDIR)/configs --template=templates/chips/pulpissimo/pulpissimo.json --output-dir=$(CURDIR)/configs/chips/pulpissimo --output=configs/systems/pulpissimo.json --usecase=usecases/jtag-cam.json

gen.arnold:
	./bin/pulp_config_gen --configs=$(CURDIR)/configs --template=templates/chips/arnold/arnold.json --output-dir=$(CURDIR)/configs/chips/arnold --output=configs/systems/arnold.json --usecase=usecases/jtag-cam.json

gen.pulpissimo.zeroriscy:
	./bin/pulp_config_gen --configs=$(CURDIR)/configs --template=templates/chips/pulpissimo-zeroriscy/pulpissimo-zeroriscy.json --output-dir=$(CURDIR)/configs/chips/pulpissimo-zeroriscy --output=configs/systems/pulpissimo-zeroriscy.json --usecase=usecases/jtag-cam.json

gen.pulpissimo.microriscy:
	./bin/pulp_config_gen --configs=$(CURDIR)/configs --template=templates/chips/pulpissimo-microriscy/pulpissimo-microriscy.json --output-dir=$(CURDIR)/configs/chips/pulpissimo-microriscy --output=configs/systems/pulpissimo-microriscy.json --usecase=usecases/jtag-cam.json

gen.pulpissimo.riscy:
	./bin/pulp_config_gen --configs=$(CURDIR)/configs --template=templates/chips/pulpissimo-riscy/pulpissimo-riscy.json --output-dir=$(CURDIR)/configs/chips/pulpissimo-riscy --output=configs/systems/pulpissimo-riscy.json --usecase=usecases/jtag-cam.json

gen.wolfe:
	./bin/pulp_config_gen --configs=$(CURDIR)/configs --template=templates/chips/wolfe/wolfe.json --output-dir=$(CURDIR)/configs/chips/wolfe --output=configs/systems/wolfe.json --usecase=usecases/jtag-cam.json

gen.oprecompkw:
	./bin/pulp_config_gen --configs=$(CURDIR)/configs --template=templates/chips/oprecompkw/oprecompkw.json --output-dir=$(CURDIR)/configs/chips/oprecompkw --output=configs/systems/oprecompkw.json

gen.oprecompkw_sfloat:
	./bin/pulp_config_gen --configs=$(CURDIR)/configs --template=templates/chips/oprecompkw_sfloat/oprecompkw_sfloat.json --output-dir=$(CURDIR)/configs/chips/oprecompkw_sfloat --output=configs/systems/oprecompkw_sfloat.json

gen.oprecompkw_sfloat_sa:
	./bin/pulp_config_gen --configs=$(CURDIR)/configs --template=templates/chips/oprecompkw_sfloat_sa/oprecompkw_sfloat_sa.json --output-dir=$(CURDIR)/configs/chips/oprecompkw_sfloat_sa --output=configs/systems/oprecompkw_sfloat_sa.json --usecase=usecases/jtag.json

gen.oprecompkw_sfloat_sa_dual_regfile:
	./bin/pulp_config_gen --configs=$(CURDIR)/configs --template=templates/chips/oprecompkw_sfloat_sa_dual_regfile/oprecompkw_sfloat_sa_dual_regfile.json --output-dir=$(CURDIR)/configs/chips/oprecompkw_sfloat_sa_dual_regfile --output=configs/systems/oprecompkw_sfloat_sa_dual_regfile.json --usecase=usecases/jtag.json

gen.oprecompkw_sa:
	./bin/pulp_config_gen --configs=$(CURDIR)/configs --template=templates/chips/oprecompkw_sa/oprecompkw_sa.json --output-dir=$(CURDIR)/configs/chips/oprecompkw_sa --output=configs/systems/oprecompkw_sa.json --usecase=usecases/jtag.json

gen.oprecompkw-dram:
	./bin/pulp_config_gen --configs=$(CURDIR)/configs --template=templates/chips/oprecompkw-dram/oprecompkw-dram.json --output-dir=$(CURDIR)/configs/chips/oprecompkw-dram --output=configs/systems/oprecompkw-dram.json

gen.vega:
	./bin/pulp_config_gen --configs=$(CURDIR)/configs --template=templates/chips/vega/vega.json --output-dir=$(CURDIR)/configs/chips/vega --output=configs/systems/vega.json --usecase=usecases/jtag-cam.json

gen.gap:
	./bin/pulp_config_gen --configs=$(CURDIR)/configs --template=templates/chips/gap/gap.json --output-dir=$(CURDIR)/configs/chips/gap --output=configs/systems/gap.json --usecase=usecases/jtag-cam.json

gen.vivosoc3:
	./bin/pulp_config_gen --configs=$(CURDIR)/configs --template=templates/chips/vivosoc3/vivosoc3.json --output-dir=$(CURDIR)/configs/chips/vivosoc3 --output=configs/systems/vivosoc3.json --usecase=usecases/jtag.json

gen.bigpulp-z-7045:
	./bin/pulp_config_gen --configs=$(CURDIR)/configs --template=templates/chips/bigpulp-z-7045/bigpulp-z-7045.json --output-dir=$(CURDIR)/configs/chips/bigpulp-z-7045 --output=configs/systems/bigpulp-z-7045.json --usecase=usecases/jtag.json

gen.bigpulp:
	./bin/pulp_config_gen --configs=$(CURDIR)/configs --template=templates/chips/bigpulp/bigpulp.json --output-dir=$(CURDIR)/configs/chips/bigpulp --output=configs/systems/bigpulp.json --usecase=usecases/jtag.json

gen.bigpulp-standalone:
	./bin/pulp_config_gen --configs=$(CURDIR)/configs --template=templates/chips/bigpulp-standalone/bigpulp.json --output-dir=$(CURDIR)/configs/chips/bigpulp-standalone --output=configs/systems/bigpulp-standalone.json --usecase=usecases/jtag.json

gen.fulmine:
	./bin/pulp_top_gen --configs=$(CURDIR)/configs --system=fulmine    --output=configs/systems/fulmine.json

gen.hero-z-7045:
	./bin/pulp_config_gen --configs=$(CURDIR)/configs --template=templates/chips/hero-z-7045/hero-z-7045.json --output-dir=$(CURDIR)/configs/chips/hero-z-7045 --output=configs/systems/hero-z-7045.json

gen.honey:
	./bin/pulp_top_gen --configs=$(CURDIR)/configs --system=honey      --output=configs/systems/honey.json

gen.neuraghe:
	./bin/pulp_top_gen --configs=$(CURDIR)/configs --system=neuraghe   --output=configs/systems/neuraghe.json

gen.quentin:
	./bin/pulp_top_gen --configs=$(CURDIR)/configs --system=quentin    --output=configs/systems/quentin.json

gen.vivosoc2_1:
	./bin/pulp_top_gen --configs=$(CURDIR)/configs --system=vivosoc2_1 --output=configs/systems/vivosoc2_1.json

gen.vivosoc2:
	./bin/pulp_top_gen --configs=$(CURDIR)/configs --system=vivosoc2   --output=configs/systems/vivosoc2.json

gen: gen.usecases gen.pulp gen.pulpissimo gen.pulpissimo.zeroriscy gen.pulpissimo.microriscy \
  gen.pulpissimo.riscy gen.wolfe gen.oprecompkw gen.vega gen.gap gen.vivosoc3 gen.bigpulp-z-7045 gen.bigpulp \
  gen.fulmine gen.hero-z-7045 gen.honey gen.multino gen.neuraghe \
  gen.quentin gen.vivosoc2_1 gen.vivosoc2

$(BUILD_DIR):
	mkdir -p $(BUILD_DIR)

$(BUILD_DIR)/Makefile: $(BUILD_DIR)
	( cd $(BUILD_DIR) ; \
	  $(CMAKE) -DCMAKE_BUILD_TYPE=$(RELEASE_TYPE) -DCMAKE_INSTALL_PREFIX=$(INSTALL_DIR) \
		$(EXTRA_CMAKE_ARGS) $(MAKEFILE_DIR) )
