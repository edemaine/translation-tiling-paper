.PHONY: all figures
PYTHON ?= python3
FIGURE_PDFS = figures/kim-input.pdf figures/kim-shell.pdf figures/kim-connected.pdf

all: paper.pdf slop.pdf

figures:
	$(PYTHON) figures/generate_connected.py

paper.tex slop.tex: %.tex: %.texlish
	texlish $<

lean-snippets/.stamp: lean/TranslationTiling/Abstract.lean figures/extract_lean_snippets.py
	$(PYTHON) figures/extract_lean_snippets.py
	touch $@

paper.pdf slop.pdf: %.pdf: %.tex paper.bib alpha-key.bst $(FIGURE_PDFS) lean-snippets/.stamp
	latexmk -pdf -interaction=nonstopmode -halt-on-error $<
