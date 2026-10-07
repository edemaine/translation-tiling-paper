.PHONY: all
all: paper.pdf

paper.tex: paper.texlish
	texlish paper.texlish

paper.pdf: paper.tex paper.bib
	latexmk -pdf -interaction=nonstopmode -halt-on-error paper.tex
