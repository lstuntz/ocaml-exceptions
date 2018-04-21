main.pdf: out/main.pdf
	cp out/main.pdf main.pdf

out/main.pdf: $(wildcard *.tex)
	mkdir -p out
	pdflatex --output-directory=out main.tex

.PHONY: clean
clean:
	rm -f main.pdf
	rm -rf out/
