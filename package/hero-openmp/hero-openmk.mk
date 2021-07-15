################################################################################
#
# hero-openmp
#
################################################################################

HERO_OPENMP_VERSION = 0.1
HERO_OPENMP_SITE_METHOD = local
HERO_OPENMP_SITE = $(BR2_EXTERNAL_HERO_PATH)/toolchain/llvm-project/openmp
HERO_OPENMP_INSTALL_STAGING = YES
HERO_OPENMP_INSTALL_TARGET = YES
HERO_OPENMP_LICENSE = MIT
HERO_OPENMP_LICENSE_FILES = LICENSE.txt
HERO_OPENMP_DEPENDENCIES = elfutils libffi libpulp
ifneq ($(strip $(BR2_PACKAGE_HERO_OPENMP_ENABLE_PREM)),)
	HERO_OPENMP_DEPENDENCIES += prem-cmux
endif

HERO_OPENMP_PULP_INC_DIR = $(shell source $(BR2_EXTERNAL_HERO_PATH)/pulp/sdk/sourceme.sh > /dev/null 2>&1 && echo $$PULP_SDK_INSTALL/include)
HERO_OPENMP_CONF_OPTS = -DCMAKE_BUILD_TYPE=Release -DLIBOMPTARGET_LLVM_INCLUDE_DIRS=$(BR2_EXTERNAL_HERO_PATH)/install/include/llvm
HERO_OPENMP_CONF_ENV = LIBGOMP_PLUGIN_PULP_HERO_CPPFLAGS="-DPLATFORM=$(BR2_PACKAGE_HERO_PLATFORM)" HERO_PULP_INC_DIR=${HERO_OPENMP_PULP_INC_DIR}

ifneq ($(strip $(BR2_PACKAGE_HERO_OPENMP_ENABLE_PREM)),)
	HERO_OPENMP_CONF_OPTS += "-DLIBOMPTARGET_ENABLE_PREM=ON"
endif

$(eval $(cmake-package))
