ifndef PULP_SDK_HOME
$(error PULP_SDK_HOME is not set)
endif

dirs = host pulp
dirs_pulp = pulp

build:
	@$(foreach dir,$(dirs), cd $(PWD)/$(dir) &&  make build;)

header:
	@$(foreach dir,$(dirs_pulp), cd $(PWD)/$(dir) &&  make header;)

all: header build install

.PHONY: install clean
install:
	@$(foreach dir,$(dirs), cd $(PWD)/$(dir) &&  make install;)

clean:
	@$(foreach dir,$(dirs), cd $(PWD)/$(dir) &&  make clean;)
