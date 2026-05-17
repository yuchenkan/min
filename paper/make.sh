set -ex
cd "$(dirname "$0")"
pdflatex -output-directory=output paper.tex
bibtex output/paper
pdflatex -output-directory=output paper.tex
pdflatex -output-directory=output paper.tex
echo "Output: output/paper.pdf"
