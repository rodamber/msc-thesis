# ---------------------------------------------------------
# type "make" command in Unix to create the PDF file 
# ---------------------------------------------------------

# Main filename
FILE=Thesis

# ---------------------------------------------------------
PDF_VIEWER ?= xdg-open

.PHONY: r clean veryclean v

all: Thesis_*.tex
	pdflatex  -shell-escape ${FILE}
# 	makeindex $(FILE).nlo -s nomencl.ist -o $(FILE).nls
# 	makeindex $(FILE).glo -s $(FILE).ist -o $(FILE).gls -t $(FILE).glg
	pdflatex  -shell-escape ${FILE}
	bibtex ${FILE}
	pdflatex  -shell-escape ${FILE}
	pdflatex  -shell-escape ${FILE}

clean:
	(rm -rf *.aux *.bbl *.blg *.glg *.glo *.gls *.ilg *.ist *.lof *.log *.lot *.nlo *.nls *.out *.toc *.loa *.auxlock)
	rm -f ./temp/*.*
	rm -f *~

veryclean:
	make clean
	rm -f *~
	rm -f $(FILE).pdf $(FILE).ps

v: all
	$(PDF_VIEWER) $(FILE).pdf 2>/dev/null &
	grep 'LaTeX Warning' $(FILE).log || true
