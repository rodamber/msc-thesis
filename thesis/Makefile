FILE=Thesis

.PHONY: all v i clean

all:
	latexmk

v: all
	open -a Skim $(FILE).pdf
	grep 'LaTeX Warning' $(FILE).log || true

i:
	latexmk -pvc

clean:
	(rm -rf *.glo *.ist *.nlo *.upa *.upb *.loa)
	latexmk -C

