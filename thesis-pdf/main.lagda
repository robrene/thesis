\documentclass[12pt,a4paper,titlepage]{article}

\newif\ifsetmono
\setmonotrue

%include thesis.fmt

\usepackage{main}

\begin{document}

\pagenumbering{gobble}

\title{Verified Translation of a Strongly Typed Functional Language with Variables to a Language of Indexed Gates}
\author{Rob Spoel}
%\supervisor{Wouter Swierstra}
\date{2019}
\maketitle

\tableofcontents
\listoffigures
\listof{agdacodefloat}{List of Agda listings}
\newpage

\pagenumbering{arabic}

\nocite{flor2014pi}

\input{01-abstract.tex}
\input{02-research-goal.tex}
\input{03-background.tex}
\input{04-prototype.tex}
\input{05-piware-and-lambdaone.tex}
\input{06-translation.tex}
\input{07-correctness.tex}
\input{08-conclusion.tex}
\input{09-special-thanks.tex}

\newpage

\bibliographystyle{apalike}
\bibliography{main}

\end{document}
