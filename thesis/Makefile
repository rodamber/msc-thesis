FILE=Thesis

.PHONY: all i r clean veryclean v

all:
	latexmk

i:
	latexmk -pvc

clean:
	latexmk -c

veryclean:
	make clean
	latexmk -C
	(rm -rf *.bbl *.glo *.ist *.nlo *.upa *.upb)

v: all
	open -a Skim $(FILE).pdf
	grep 'LaTeX Warning' $(FILE).log || true
