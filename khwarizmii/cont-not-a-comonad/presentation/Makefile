.PHONY: all clean

THEORIES := $(shell find .. -name \*.thy -print)

all: presentation.pdf

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
