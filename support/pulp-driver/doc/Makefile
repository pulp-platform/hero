.PHONY: pulp_linux_driver_doc.pdf
pulp_linux_driver_doc.pdf:
	doxygen-1.8.17
	git checkout -- latex/Makefile
	make -C latex
	mv latex/refman.pdf $@
