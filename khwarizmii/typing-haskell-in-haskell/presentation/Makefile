.PHONY: all pdf clean

all: pdf/presentation.pdf

pdf: pdf/presentation.pdf

pdf/presentation.pdf: presentation.md
	make -C pdf/ presentation.pdf

clean:
	make -C pdf/ clean
