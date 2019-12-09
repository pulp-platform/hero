.PHONY: pulp_linux_driver_doc.pdf
pulp_linux_driver_doc.pdf:
	doxygen
	git checkout -- latex/Makefile
	make -C latex
	mv latex/refman.pdf $@
