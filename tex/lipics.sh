#! /bin/sh

set -x

TARGETDIR=lipics

OLDTARGET=comonads
NEWTARGET=p00-ahrens
MKTARGET=${NEWTARGET}

# process files, create .bbl file
latexmk -C && latexmk -pdf $OLDTARGET

mkdir -p $TARGETDIR

cd $TARGETDIR

rm -rf ./*

cp	../cc-by.pdf \
	../tri_rules.tex \
	../stream_rules.tex \
	../lipics.cls \
	../lipics-logo-bw.pdf \
	../literature.bib \
	../formal_table.tex \
	../comonads.tex \
	../ownstylelipics.sty \
	../defManSSR.tex \
	.

mv ${OLDTARGET}.tex ${MKTARGET}.tex

latexmk -C && latexmk -pdf ${MKTARGET}

diffpdf ../${OLDTARGET}.pdf ${MKTARGET}.pdf
latexmk -c -bibtex
rm ${MKTARGET}.vtc

exit 0
