%include thesis.fmt

\newpage
\section{Conclusion}\label{sec:conclusion}

\subsection{Research summary}\label{sec:researchsummary}

Our initial research goal stated that we'd like to translate a hardware description language with variable bindings to one without variable bindings. We've presented a complete translation from \lambdaone (an embedded hardware description language in Agda with variable bindings) to \Piware (an embedded hardware description language in Agda without variable bindings). We also proven the translation to be correct, highlighting some parts of that correctness proof inside this document. We showed how to successfully and efficiently use the dependent type system of Agda to facilitate this correctness proof, while also showing some small potential improvements to the Agda standard library.

\subsection{Future work}\label{sec:futurework}

\subsubsection{Remaining postulates and holes}

This document does not provide a complete view of the translation and correctness proof code, but rather highlights some interesting parts of it. At multiple points, we've referred to the accompanying code to get a complete view. For the sake of transparency, we need to mention that there are still a few holes left open in the code that we sadly were not able to solve. Although the two-step translation is $100\%$ complete, we've not managed to get the same completion ratio for the first step of the correctness proof. Agda allows for an option to interpret open holes as postulates, which lets us use the incomplete lemmas while treating them as proven true. This means we are able to show the high-level structure of the proof under the assumption that our lemmas are provable.

Although we've proven the correctness of the translation of the |case⨂_of_| constructor at a high level, the translation makes use of a lemma called |reduce-ctxt­-twice-correctness|. We mentioned in section \ref{sec:reducing-context} that we need some reordering plugs before we can reduce the context twice. Given that the hard part of the correctness proof lies in proving the correctness of |reduce-correctness|, we are confident that we could prove the remaining hole that proves the correct behavior of these reordering plugs.

Although we spent a considerable amount of time implementing a custom multiplexer and demultiplexer in intermediate language circuitry, and are quite confident that they work as intended, we did not manage to formally prove this correctness. Both these components use a lot of composite circuitry. Although proving the correctness of these components would have been an interesting case-study into the scalability of our correctness proof approach using equational reasoning in Agda, we decided to focus our efforts elsewhere given that the workings of multiplexers and demultiplexers are not very controversial.

Lastly, we did not manage to prove the correctness of the translation of our \emph{in-left} |inl₁| and \emph{in-right} |inr₁| constructors. Although we firmly believe that our new comparison function for natural numbers is superior to the existing one inside Agda's standard library, we were not able to convince the type system to use it in solving the lemma around padding.

\subsubsection{Potential follow-up}

Besides filling up the last remaining holes in the proof, this project offers other potential future follow-up research. For example, we made a conscious choice to remove looping constructors in order to focus the research on the translation to a nameless language. Reintroducing loops would be interesting since it would affect the evaluation semantics and thereby affect the correctness proof. Furthermore, it would be interesting to follow-up this work by allowing higher-order variables inside the source language.

We hope to see further research into hardware embedded languages that are embedded in dependent type systems in the future, as we believe there is still lots of untapped potential in this field.
