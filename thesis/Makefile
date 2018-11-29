SRCDIR = content
MASTER = $(SRCDIR)/Thesis

.PHONY: all v i clean c new n

all:
	latexmk -cd $(MASTER)

i:
	latexmk -cd $(MASTER) -pvc

v:
	latexmk -cd $(MASTER) -pv

clean:
	latexmk -cd $(MASTER) -C

c: clean

new: clean all

n: new
