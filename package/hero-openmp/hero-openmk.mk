################################################################################
#
# hero-openmp
#
################################################################################

HERO_OPENMP_VERSION = cd60aa669df18bba8315cac53d4abc2b71a3fd99
HERO_OPENMP_SITE_METHOD = git
HERO_OPENMP_SITE = ssh://git@iis-git.ee.ethz.ch/kwolters/openmp.git
HERO_OPENMP_INSTALL_STAGING = YES
HERO_OPENMP_INSTALL_TARGET = YES
HERO_OPENMP_LICENSE = MIT
HERO_OPENMP_LICENSE_FILES = LICENSE.txt
HERO_OPENMP_DEPENDENCIES = elfutils libffi hero-support

define HERO_OPENMP_FETCH_SUBMODULE
	cd $(HERO_OPENMP_DL_DIR)/git && git submodule update --init && \
	rsync -av $(HERO_OPENMP_DL_DIR)/git/libomptarget/plugins/pulp $(@D)/libomptarget/plugins/
endef
HERO_OPENMP_POST_EXTRACT_HOOKS += HERO_OPENMP_FETCH_SUBMODULE

HERO_OPENMP_PULP_INC_DIR = $(shell source $(BR2_EXTERNAL_HERO_PATH)/support/pulp-sdk/sourceme.sh > /dev/null 2>&1 && echo $$PULP_SDK_INSTALL/include)
HERO_OPENMP_CONF_ENV = LIBGOMP_PLUGIN_PULP_HERO_CPPFLAGS="-DPLATFORM=$(HERO_SUPPORT_PLATFORM)" HERO_PULP_INC_DIR=${HERO_OPENMP_PULP_INC_DIR}

$(eval $(cmake-package))
