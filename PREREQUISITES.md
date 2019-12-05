# Build System Prerequisites

## Supported OSs
- Ubuntu 18.04-LTS, 16.04-LTS
- CentOS7

## HERO SDK
The HERO SDK build process requires additional packages to be installed with respect to a fresh Linux distribution installation.

#### Ubuntu 18.04-LTS, 16.04-LTS
```
sudo apt install curl flex gawk libtool-bin libtool-doc libncurses5-dev bison python3.6-dev  python3.6-venv python3.6-doc ninja-build
```

#### CentOS 7
```
sudo yum groupinstall "Development Tools"
sudo yum install http://repo.okay.com.mx/centos/7/x86_64/release/okay-release-1-1.noarch.rpm
sudo yum install ncurses-dev bison-devel ninja-build
```

Additional packages must be installed to build the PULP software stack contained within the HERO SDK (see [README.md](hero/pulp-sdk/README.md)).

#### Ubuntu 18.04-LTS, 16.04-LTS
```
sudo apt install git python3-pip gawk texinfo libgmp-dev libmpfr-dev libmpc-dev swig3.0 libjpeg-dev lsb-core doxygen python-sphinx sox graphicsmagick-libmagick-dev-compat libsdl2-dev libswitch-perl libftdi1-dev cmake
sudo pip3 install artifactory twisted prettytable sqlalchemy pyelftools openpyxl xlsxwriter pyyaml numpy
```

#### CentOS 7
```
sudo yum install git python3-pip python3-devel gawk texinfo gmp-devel mpfr-devel libmpc-devel swnig libjpeg-turbo-devel redhat-lsb-core doxygen python-sphinx sox GraphicsMagick-devel ImageMagick-devel SDL2-devel perl-Switch libftdi-devel cmake
sudo pip3 install artifactory twisted prettytable sqlalchemy pyelftools openpyxl xlsxwriter pyyaml numpy
```

## HERO Hardware Platform
TBD
