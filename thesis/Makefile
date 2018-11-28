FILE=Thesis

.PHONY: all i r clean veryclean v

all:
	latexmk

i:
	latexmk -pvc

clean:
	(rm -rf *.glo *.ist *.nlo *.upa *.upb *.loa)
	latexmk -c

veryclean:
	make clean
	latexmk -C

v: all
	open -a Skim $(FILE).pdf
	grep 'LaTeX Warning' $(FILE).log || true
