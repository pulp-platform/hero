DIRECTORIES = $(wildcard */)

.PHONY: test
test:
	@$(foreach dir,$(DIRECTORIES), cd $(PWD)/$(dir) &&  make init-target-host clean all run;)
