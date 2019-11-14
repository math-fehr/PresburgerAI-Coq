.PHONY: clean coq2html docs

docs: coq2html
	# make the .v files
	make ../
	coq2html/coq2html -base PolyAI -external http://math-comp.github.io/math-comp/htmldoc mathcomp ../src/*.v -redirect

coq2html: 
	(cd coq2html; make)
	chmod +x coq2html/coq2html

clean:
	(cd coq2html; make clean)
	rm -f *.html *.css *.js

