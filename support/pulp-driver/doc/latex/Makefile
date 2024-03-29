LATEX_CMD=pdflatex-2016

all: refman.pdf

pdf: refman.pdf

.PHONY: .git_rev.txt
.git_rev.txt:
	git rev-parse HEAD > .git_rev.txt

refman.pdf: clean refman.tex .git_rev.txt
	# Remove output related to Data Structures.
	sed -i -e '/\\chapter{Data Structure Index}/,/\\input{annotated}/d' refman.tex
	sed -i -e '/\\chapter{Data Structure Documentation}/,/\\chapter{File Documentation}/{//p;d;}' \
        refman.tex
	sed -i -e '/\\chapter{Data Structure Documentation}/d' refman.tex
	# Remove separate output of README.
	sed -i -e '/\\input{_r_e_a_d_m_e_8md}/d' refman.tex
	# Shrink Doxygen reference on title page.
	sed -i -r -e 's/\\large (Generated by Doxygen)/\1/' refman.tex
	# Enlargen title.
	sed -i -r -e 's/\\Large (P\\\+U)/\\Huge \1/' refman.tex
	# Add PULP logo and revision information.
	grep -vq '^\\input{logo_rev.tex}' refman.tex && \
        sed -i -r -e 's/(\{Generated by Doxygen)/\\input\{logo_rev\.tex\}\n\1/' refman.tex
	# Run regular Doxygen LaTeX build.
	$(LATEX_CMD) refman
	makeindex refman.idx
	$(LATEX_CMD) refman
	latex_count=8 ; \
	while egrep -s 'Rerun (LaTeX|to get cross-references right)' refman.log && [ $$latex_count -gt 0 ] ;\
	    do \
	      echo "Rerunning latex...." ;\
	      $(LATEX_CMD) refman ;\
	      latex_count=`expr $$latex_count - 1` ;\
	    done
	makeindex refman.idx
	$(LATEX_CMD) refman


clean:
	rm -f *.ps *.dvi *.aux *.toc *.idx *.ind *.ilg *.log *.out *.brf *.blg *.bbl refman.pdf .git_rev.txt
