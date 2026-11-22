% Build from the directory containing this driver and its section:
% pdflatex -halt-on-error -jobname=ParetoVonMangoldtManuscript ParetoVonMangoldtManuscript.tex.md (run twice).
\documentclass[11pt,letterpaper]{article}
\usepackage{amsmath,amssymb}
\usepackage[letterpaper,margin=1in]{geometry}
\usepackage{microtype}
\usepackage[hidelinks]{hyperref}
\hypersetup{pdftitle={The Pareto--von Mangoldt reduction for the Riemann hypothesis}}
\setcounter{secnumdepth}{0}
\setlength{\emergencystretch}{1em}
\newcommand{\pvmStandaloneLayout}{}
\begin{document}
\begin{center}
{\LARGE The Pareto--von Mangoldt reduction\\[3pt]
for the Riemann hypothesis\par}
\vspace{6pt}November 22, 2026
\end{center}
\begin{abstract}
For the Pareto measure on the positive integers, residues have mean
\(\log d\) and their M\"obius transforms have mean \(\Lambda(q)\).
Projection away from packets whose conductors have at least two distinct
prime factors leaves a single line inside the closed residue span.
We express the distance from the centered parity packet to the mixed
subspace as an exact projection deficit. Vanishing of this deficit would
place the constant function in the residue span and imply the Riemann
hypothesis. For dilations of the binary and ternary residues, a rational
quadratic form controls the full squared error within a uniform factor.
Explicit trials reach squared error below \(0.019711\). Vanishing of the
limiting error remains open.
\end{abstract}
\input{ParetoVonMangoldtReduction.tex.md}
\end{document}
