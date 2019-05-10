SRCDIR = content
THESIS = $(SRCDIR)/Thesis
EXTABSTRACT = $(SRCDIR)/ExtendedAbstract
ZIPFILE=78942-Rodrigo-Bernardo.zip

.PHONY: all thesis i abs absi clean c new n zip

all: thesis abs

zip: all
	zip -j $(ZIPFILE) $(THESIS).pdf $(EXTABSTRACT).pdf

thesis:
	latexmk -cd $(THESIS)

i:
	latexmk -cd $(THESIS) -pvc

abs:
	latexmk -cd $(EXTABSTRACT)

absi:
	latexmk -cd $(EXTABSTRACT) -pvc

clean:
	latexmk -cd $(THESIS) -c
	latexmk -cd $(EXTABSTRACT) -c
	rm -f $(ZIPFILE)

c: clean

new: clean all

n: new


