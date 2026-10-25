.PHONY: all figures website
PYTHON ?= python3
PANDOC ?= pandoc
FIGURE_PDFS = figures/kim-input.pdf figures/kim-shell.pdf figures/kim-connected.pdf

all: paper.pdf slop.pdf

website: paper.pdf slop.pdf website/index.md website/style.css
	mkdir -p build/site
	$(PANDOC) --standalone --to=html5 --css=style.css website/index.md -o build/site/index.html
	cp website/style.css paper.pdf slop.pdf build/site/

figures:
	$(PYTHON) figures/generate_connected.py

paper.tex slop.tex: %.tex: %.texlish
	texlish $<

paper.pdf slop.pdf: %.pdf: %.tex paper.bib alpha-key.bst $(FIGURE_PDFS)
	latexmk -pdf -interaction=nonstopmode -halt-on-error $<

# Lean excerpts are quoted by name from Abstract.lean with leanquote.sty.
paper.pdf: lean/TranslationTiling/Abstract.lean leanquote.sty figures/lean-logo.pdf
