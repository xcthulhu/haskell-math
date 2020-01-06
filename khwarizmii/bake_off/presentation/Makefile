.PHONY: all clean

THEORIES := $(shell find .. -name \*.thy -print)

all: presentation.pdf isabelle_docs/pigeon.pdf

isabelle_docs/pigeon.pdf: $(THEORIES)
	mkdir -p $(dir $@)
	make -C ../Isabelle_Theories/Pigeon
	cp ../Isabelle_Theories/Pigeon/output/document.pdf $@

presentation.pdf: presentation.tex generated/snippets.tex $(THEORIES) bibliography.bib beamerthemedbt.sty
	rm -f $@
	latexmk -pdf -xelatex -use-make $<

presentation.bbl: presentation.tex presentation.aux
	bibtex presentation

generated/snippets.tex: $(THEORIES)
	isabelle build -c -v -d . LaTeX_Snippets
	touch $@

clean:
	latexmk -CA
	rm -rf generated isabelle_docs
	rm -f *.log _region_.* *.aux *.fdb_latexmk texput.fls presentation.bbl comment.cut *.nav *.snm *.vrb
	rm -rf auto/ _region_.prv/
