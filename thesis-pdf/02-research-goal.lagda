%include thesis.fmt

\newpage
\section{Research goal}\label{sec:research-goal}

\subsection{Preamble}\label{sec:research-goal-preamble}

\emph{Domain-specific languages} (DSLs) are languages that are specialized for particular applications. They can provide benefits over their counterpart \emph{general-purpose languages} (GPLs) by providing specific structures that let users express certain solutions to certain problems more clearly. A common approach when designing a DSL is to embed it in an existing \emph{host} language (either inside another DSL or more commonly inside a GPL).

When embedding a DSL into a host language, there are multiple possible methods for handling variable binding. This work demonstrates a verified translation from an embedded hardware description DSL which represents variables using named De Bruijn bindings -- which are practical for the internal representation of the DSL -- to an embedded hardware description DSL which uses nameless bindings of indexed wires -- which is practical for the compilation to actual hardware.

\subsection{Research statement}\label{sec:research-goal-statement}

Given a hardware description language with variable bindings, can we translate it to a hardware description language without bindings but with input/output indexed wires\footnote{Section \fullref{sec:plugsvsvars}}? Given such a translation, can we prove that the translation is correct\footnote{Section \fullref{sec:background-verified-translation}} for all possible programs that can be written in the source language? How well does a dependently typed context\footnote{Section \fullref{sec:background-deptypagda}} lend itself to reason about hardware description languages?

\subsection{Contribution}\label{sec:research-goal-contribution}

We start this document with some background in section \ref{sec:background} in the form of literature research on topics such as dependent types, higher-order logic, and embedded languages.

We demonstrate a prototype translation in the form of the \emph{SKI transpiler}, showing that it is possible to translate from a language with bindings (simply-typed $\lambda$-calculus) to a nameless language (SKI combinators) in section \ref{sec:prototype}. Furthermore, we demonstrate that we can use Agda's dependent type system to prove the translation's correctness, based on the Curry-Howard isomorphism.

In section \ref{sec:piware-and-lambdaone}, we introduce a new hardware description DSL -- based on J. P. Pizani Flor's work -- called \lambdaone (pronounced \emph{lambda one}, named after the working name of \lambdapiware also by J. P. Pizani Flor). We demonstrate a complete translation from \lambdaone to \Piware in section \ref{sec:translation} before highlighting some parts of the correctness proof in section \ref{sec:correctness}.

\subsection{Scientific relevance}\label{sec:research-goal-scientific-relevance}

As hardware becomes more and more complex, the need for streamlined verification solutions becomes more and more pressing. Finding faults in circuits after their worldwide distribution is a scenario from which it is hard to recover, as the Intel FDIV bug in the mid 90's \cite{intel2004fdiv} demonstrates.

With the growing popularity of dependently typed programming languages such as Coq and Agda, there is an opportunity for a new hardware design language solution that can provide more mathematical soundness guarantees for the chips of the future. Verification and validation of hardware design play a considerable part in the cost of hardware design \cite{rekhi2003next}. Streamlining both of these steps into a single language could provide big savings as well as better scaling for big and small manufacturers alike.

For such a potential language to be attractive to developers, it is important to provide user-friendly abstractions of the underlying wires and plugs. For this reason, we believe it is of scientific significance to research the translating from higher-level user-space languages to lower-level machine-space languages, where a dependently typed context can provide strong mathematical soundness guarantees.
