SRCDIR = content
MASTER = $(SRCDIR)/presentation

.PHONY: all v i clean c new n

all:
	latexmk -cd $(MASTER)

i:
	latexmk -cd $(MASTER) -pvc

v:
	latexmk -cd $(MASTER) -pv

clean:
	latexmk -cd $(MASTER) -c

c: clean

new: clean all

n: new
