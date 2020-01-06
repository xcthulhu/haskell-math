.PHONY: all clean

THEORIES := $(shell find .. -name \*.thy -print)

all: output/document.pdf

output/document.pdf: document/root.tex Pigeon.thy
	isabelle build -c -v -d . Pigeon

clean:
	rm -rf output
