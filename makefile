all: docs/ctlc.pdf

ctlc.pdf: ctlc.org
	emacs ctlc.org --batch -u `id -un` --eval '(load user-init-file)' -f org-latex-export-to-pdf

docs/ctlc.pdf: ctlc.pdf
	cp ctlc.pdf docs/ctlc.pdf

docs/ctlc-bw.pdf: ctlc.pdf
	./greyscale.sh ctlc.pdf
	cp output.pdf docs/ctlc-bw.pdf
	rm output.pdf

clean:
	rm ctlc.pdf
