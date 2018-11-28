$pdf_mode = 1; # tex -> pdf
$pdf_previewer = 'open -a Skim';
$pdflatex = 'pdflatex -synctex=1 -interaction=nonstopmode';

@generated_exts = (@generated_exts, 'synctex.gz');
@default_files = ('Thesis.tex');
