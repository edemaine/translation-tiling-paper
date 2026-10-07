.PHONY: all figures
PYTHON ?= python3
FIGURE_PDFS = figures/kim-input.pdf figures/kim-shell.pdf figures/kim-connected.pdf

all: paper.pdf slop.pdf

figures:
	$(PYTHON) figures/generate_connected.py

paper.tex slop.tex: %.tex: %.texlish
	texlish $<

paper.pdf slop.pdf: %.pdf: %.tex paper.bib $(FIGURE_PDFS)
	latexmk -pdf -interaction=nonstopmode -halt-on-error $<
