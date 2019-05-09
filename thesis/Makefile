SRCDIR = content
THESIS = $(SRCDIR)/Thesis
EXTABSTRACT = $(SRCDIR)/ExtendedAbstract

.PHONY: all v i clean c new n

all:
	latexmk -cd $(THESIS)
	latexmk -cd $(EXTABSTRACT)

i:
	latexmk -cd $(THESIS) -pvc

v:
	latexmk -cd $(THESIS) -pv

abs:
	latexmk -cd $(EXTABSTRACT)

absi:
	latexmk -cd $(EXTABSTRACT) -pvc

both:
	latexmk -cd $(THESIS) -pvc
	latexmk -cd $(EXTABSTRACT) -pvc


clean:
	latexmk -cd $(THESIS) -c
	latexmk -cd $(EXTABSTRACT) -c

c: clean

new: clean all

n: new
