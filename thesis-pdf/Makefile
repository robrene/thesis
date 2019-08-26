.DEFAULT_GOAL := pdf

SHELL=/bin/sh
MAIN=main

TEX_MODULES=main \
            01-abstract \
            02-research-goal \
            03-background \
            04-prototype \
            05-piware-and-lambdaone \
            06-translation \
            07-correctness \
            08-conclusion \
						09-special-thanks \
						99-appendix

.PHONY: clean

run: $(MAIN).pdf

pdf: $(MAIN).pdf

$(MAIN).pdf: $(TEX_MODULES:%=%.tex) $(MAIN).bib $(MAIN).sty agda.sty
	latexmk -xelatex -outdir=out $(MAIN).tex
	ln -sf out/$(MAIN).pdf $(MAIN).pdf

%.tex: %.lagda thesis.fmt
	lhs2TeX --agda -o $@ $<
	sed -i '' 's/\\mathbin{\\circ}\\;/\\V{.}/g' $@
	sed -i '' 's/\\mathbin{\\$}/\\V{\\$}/g' $@
	sed -i '' 's/\\Hole{⋯}\\;\\mid/\\V{...}\\;\\mid/g' $@
	sed -i '' 's/«-/|-/g' $@

clean:
	rm -f $(MAIN).pdf
	rm -rf out/
	rm -rf $(TEX_MODULES:%=%.tex)
