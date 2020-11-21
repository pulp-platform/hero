DIRECTORIES = $(wildcard */)

.PHONY: all
all:
	@$(foreach dir,$(DIRECTORIES), cd $(PWD)/$(dir) &&  make clean all;)

clean:
	@$(foreach dir,$(DIRECTORIES), cd $(PWD)/$(dir) &&  make clean;)
