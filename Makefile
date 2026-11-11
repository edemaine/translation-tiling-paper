.PHONY: all figures website
PYTHON ?= python3
PANDOC ?= pandoc
INKSCAPE ?= inkscape
FIGURE_PDFS = figures/kim-input.pdf figures/kim-shell.pdf figures/kim-connected.pdf \
              figures/translation-tiling-prototile.pdf figures/translation-tiling-patch.pdf

all: paper.pdf slop.pdf

website: paper.pdf slop.pdf website/index.md website/style.css
	mkdir -p build/site
	$(PANDOC) --standalone --to=html5 --css=style.css website/index.md -o build/site/index.html
	cp website/style.css paper.pdf slop.pdf build/site/

figures:
	$(PYTHON) figures/generate_connected.py
	$(PYTHON) figures/generate_translation_tiling.py
	$(INKSCAPE) figures/translation-tiling-prototile.svg -o figures/translation-tiling-prototile.pdf
	$(INKSCAPE) figures/translation-tiling-patch.svg -o figures/translation-tiling-patch.pdf

paper.tex slop.tex: %.tex: %.texlish
	texlish $<

lean-snippets/.stamp: lean/TranslationTiling/Abstract.lean figures/extract_lean_snippets.py
	$(PYTHON) figures/extract_lean_snippets.py
	touch $@

paper.pdf slop.pdf: %.pdf: %.tex paper.bib alpha-key.bst $(FIGURE_PDFS) lean-snippets/.stamp
	latexmk -pdf -interaction=nonstopmode -halt-on-error $<
