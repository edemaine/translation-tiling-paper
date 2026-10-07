.PHONY: all figures
PYTHON ?= python3
FIGURE_PDFS = figures/kim-input.pdf figures/kim-shell.pdf figures/kim-connected.pdf

all: paper.pdf

figures:
	$(PYTHON) figures/generate_connected.py

paper.tex: paper.texlish
	texlish paper.texlish

paper.pdf: paper.tex paper.bib $(FIGURE_PDFS)
	latexmk -pdf -interaction=nonstopmode -halt-on-error paper.tex
