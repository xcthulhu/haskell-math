.PHONY: all clean

all: presentation.pdf

presentation.pdf: ../presentation.md
	mkdir -p $(CURDIR)/../generated_figures
	rm -f generated_figures
	ln -s $(CURDIR)/../generated_figures generated_figures
	rm -f figures
	ln -s $(CURDIR)/../figures figures
	pandoc $< -o $@ --from markdown --listings --filter=pandoc-citeproc --lua-filter=../pandoc_filters/tikz.lua --biblio=../bibliography/bibliography.bib --csl ../bibliography/science.csl --to=beamer --pdf-engine=xelatex -V theme:dbt

clean:
	rm -f *.pdf generated_figures/*.pdf figures generated_figures
