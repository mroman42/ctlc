all: ctlc2.pdf

ctlc2.pdf: ctlc.org
	emacs ctlc.org --batch -u `id -un` --eval '(load user-init-file)' -f org-latex-export-to-pdf
	cp ctlc.pdf ctlc2.pdf

clean:
	rm ctlc.pdf
