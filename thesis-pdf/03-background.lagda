%include thesis.fmt

\newpage
\section{Background}\label{sec:background}

\subsection{Dependently typed programming: Agda}\label{sec:background-deptypagda}

Agda is a dependently typed programming language based on Martin-L\"of type theory \cite{bove2009brief,martin1984intuitionistic}. It has a functional syntax which is close to that of Haskell. However, its type system is fundamentally different from Haskell's. The term \emph{dependent} in the phrase \emph{dependently typed} refers to the fact that \emph{types} can depend on \emph{values}. This means that, in Agda, types and values can be mixed freely. This is fundamentally different from the paradigm that most computer scientists are more closely familiar with, polymorphism. Polymorphism provides abstraction over \emph{types} in \emph{types}. A familiar example in the programming language Java is the abstract type \texttt{java.util.List}. The abstract type can be \emph{specialized}, i.e. turned into a complete type, by passing in another type. A dependent type system provides abstraction over \emph{values} in \emph{types}. Any Agda expression can be used in a type's definition to provide such values. Notably, these expressions can also depend on other terms that came before it in the type definition. This lets programmers define arbitrary constraints on types.

This expressibility comes at a cost, however. All expressions in Agda must be total. For all possible inputs of an expression, the expression must not produce an output which is undefined nor cause an infinite recursion. The Agda type system needs to be able to determine whether two types are equal, and thus needs to be able to execute any Agda expression in finite time.

Agda is often written in an interactive workflow. Whilst all Agda functions must be total, developers may want to (partially) leave implementations open to revisit in the future. The Agda compiler therefore supports the concept of "holes". At any time, a developer can leave a hole open inside the program by typing a |?|. The next time that the program gets compiled, the compiler will attempt to type-check the hole and replace the question mark with a marker in the form of \ensuremath{\Hole{\{!\ \ !\}}}. If the developer is using an editor with interactive Agda support, such as Emacs\footnote{\url{https://agda.readthedocs.io/en/latest/tools/emacs-mode.html}, accessed on \printdate{2019-05-01}} or Atom\footnote{\url{https://atom.io/packages/agda-mode}, accessed on \printdate{2019-05-01}}, the editor will display a list of open holes and their types. This workflow lets developers move on with their program while keeping track of lines of code that need to be revisited. If a type-checked hole's type depends on another value which still contains holes, the compiler will use temporary type-variables to indicate that it was not able to fully determine the constraints on this particular hole.

\subsection{The Curry-Howard isomorphism}\label{sec:background-curry-howard-iso}

The Curry-Howard isomorphism \cite{sorensen2006lectures} states that there exists a correspondence between formal logic systems and computational calculus, or in other words, between proof theory and type theory. According to the Curry-Howard isomorphism, dependent types correspond to higher order logic.

With this isomorphism in mind, Agda can be used as a proof system. Logical statements can be expressed in the form of Agda types, and a proof is given by constructing a value of that type. This is also called a constructive proof. Crucially, constructive proofs can not be created using proof strategies in the form $(¬¬p ⇒ p)$ and $(p ∨ ¬p)$.

In classical mathematics, a common proof pattern is to try and show the absurdity of the negation of a proposition. By proving that the negative of a proposition (i.e. $¬p$) is not valid, it must follow that the proposition itself is valid (i.e. $(¬¬p ⇒ p)$). For example, in a proposition of the form \emph{"There is an $x$ for which $f(x)$ holds true"}, in classical mathematics, one might try to start a proof in terms of \emph{"Imagine there is no such $x$..."}, and then end on \emph{"Since this is impossible, the opposite must be true"}. In a constructive proof system, just showing the absence of the opposite is not enough to prove a proposition to be true. One has to actually provide (or \emph{construct}) the $x$ in question. Similarly, the axiom of excluded middle $(p ∨ ¬p)$ places an unwanted restriction on possible values of $p$. It states that all $p$ must be either true or false, but doesn't leave open room for propositions which may be undecidable or otherwise undefined. In Agda, we cannot rely on these classical axioms and must instead always construct constructive proofs.

Agda's type checker forms a system in which we can do logical reasoning using existing functional programming techniques as well as more advanced dependently typed programming techniques. We mentioned the importance of all Agda expressions needing to terminate in order for the type checker to finish its static analysis in finite time. In the context of logical reasoning, it's also important for all functions to not be infinitely looping or otherwise undefined, in order to maintain the soundness of the system.

\subsection{Hardware design}\label{sec:background-hwdesign}

Moore's law, which states that the number of transistors on a circuit doubles approximately every two years, is likely not to hold up forever. In fact, some posit that there is a hard limit on miniaturisation of circuitry given by Heisenberg's uncertainty principle, where quantum effects will cause unwanted interference if transistors get too close to one another \cite{powell2008quantum}. Instead of improving the raw performance of general-purpose computing circuits by upping the number of transistors, another popular method to create high performance chips is to implement certain algorithms directly in hardware in the form of \emph{ASIC}s: application-specific integrated circuits. One very recent example of ASICs being used in the wild is for Bitcoin mining. Where miners used to run their block hashing algorithms on general computing chips like CPUs and GPUs, the ongoing competition for Bitcoin rewards has pushed everyone towards the most efficient and fastest computing methods of these well-defined algorithms.

Since the 1980s, researchers have been researching functional programming languages to design and reason about hardware \cite{sheeran2005hardware}. Functional programming and hardware design match up very nicely, not in the least because FP makes it easier to reason about program properties. Besides standalone functional hardware description languages made from scratch (e.g. $\mu$-FP \cite{sheeran1984mufp}), several \emph{embedded domain specific languages} (EDSLs) have been created as well (e.g. Lava \cite{bjesse1998lava}, ForSyDe \cite{sander2004system}, HAWK \cite{matthews1998microprocessor}).

Dependently typed programming is in many ways the logical next step after functional programming, a \emph{successor} of sorts. A dependent type system can offer advantages over \emph{simple} FP in the creation of domain specific languages \cite{oury2008power}. This together with the demonstrable effectiveness of functional languages for hardware description makes a language such as Agda very well-suited as a host of a hardware EDSL.

\subsection{Verified translation}\label{sec:background-verified-translation}

The words \term{compiler} and \term{transpiler} do not actually hold any real semantic difference. Both terms refer to pieces of software that translate a program description from one language to another language. In the way that these terms are usually used, a compiler will translate a user-level language to a machine-level representation, whereas a transpiler will translate between user-level languages. However, the terms \term{user-level} and \term{machine-level} aren't well-defined classifications in the context of programming languages. For all intents and purposes of this work, \term{compiler correctness} is synonymous to \term{transpiler correctness}.

The core idea behind verifying a compiler is to prove equality between evaluation of the source language and the target language. Dependent types let us formulate this equality as a type, for which we can write a constructive proof. There is a well-cited paper in the area of compiler correctness within dependently typed languages \cite{mckinna2006type}. In this article, McKinna and Wright describe the working of a verified compiler for an embedded expression-based language to an embedded stack-machine language, similar to low-level machine code.

The relationship between source language and target language, and the verified translation from one to the other, can be expressed as a graph (See figure \ref{fig:verified-translation-graph}).

\begin{figure}[b]
  \centering
  \begin{tikzpicture}[scale=1, auto]
    \matrix (m) [row sep=7em, column sep=9em]{
      \node[block] (src) {|code : Lₛ|}; &
      \node[block] (tgt) {|program : Lₜ|}; \\
      \node[block] (evl) {|resultₛ : Uₛ|}; &
      \node[block] (exc) {|resultₜ : Uₜ|}; \\};
    \draw [connector] (src) -- node[above] {\scriptsize|translate(code)|} (tgt);
    \draw [connector] (src) -- node[below,sloped] {\scriptsize|eval(code)|} (evl);
    \draw [connector] (tgt) -- node[above,sloped] {\scriptsize|exec(program)|} (exc);
    \draw [connector] (evl) -- node[below] {\scriptsize|convert(resultₛ)|} (exc);
  \end{tikzpicture}
  \caption{Graph demonstrating verified translation relation}
  \label{fig:verified-translation-graph}
\end{figure}

Given a |code| in a source language |Lₛ|, we can evaluate this code using the semantic evaluation rules of that language by passing in some |params| in the source language's value universe |Uₛ|. Alternatively, we can |translate| the |code| into a |program| of target language |Lₜ|. By |convert|ing the |params| to the target language's value universe |Uₜ|, we can execute the |program| passing in the converted |input|. The result of both evaluating the source language or executing the target language should land on the same result (after |convert|ing).

Note that even though we used different terms \emph{evaluate} and \emph{execute} to describe the running of either the source or the target language statements, they are conceptually the same operation, just on different inputs.

\subsection{Embeddings and EDSLs}\label{sec:background-embeddings-and-edsls}

\subsubsection{Variable binding in embedded domain specific languages}\label{sec:background-varbindings}

When talking about EDSLs, one has to differentiate between shallow and deep embeddings in the host language \cite{gibbons2014folding,boulton1992experience}. In a deeply embedded DSL, syntactic structures are represented as data types inside the host language to allow quantifiable inspection. This is extra work for the developer of the library, but provides invaluable benefits when reasoning about the semantics of the embedded language, especially in a dependently typed context. A shallow embedding avoids such work, and only offers a mapping between the embedded language's syntax and the host's semantics. The deep embedding has the major benefit of splitting up the definition of \emph{which} language constructs exist and \emph{how} they have to be interpreted. This lets us inspect expressions of the embedded language without having to reflect on the definition of the shallow embedded semantics.

When developing a deeply embedded language, the library author has different choices for the representation of variables, each with their own caveats.

\subsubsection{Nameless}\label{sec:background-nameless}

In the context of variable binding representation techniques, nameless refers to a system where there are no variable bindings. Perhaps the most famous example of nameless binding is combinatorial logic, for example using the SKI basis \cite{smullyan1985mock,curry1972combinatory}.

In SKI combinator calculus, the combinators $S$, $K$ and $I$ form the three basic building blocks out of which programs can be constructed. Composing any two terms also forms a valid term, through application. The basic terms' semantics are defined as such:\nopagebreak

\begin{align*}
I\,x        &\,=\, x         \\
K\,x\,y     &\,=\, x         \\
S\,x\,y\,z  &\,=\, xz\,(yz)  \\
\end{align*}

Even though the denotational semantics of these terms use variable identifiers $x$, $y$ and $z$ for their internal representation, the language of SKI combinator calculus only allows the terms $S$, $K$ and $I$, as well as their compositions through functional application. A legal expression in this language does not contain any variable bindings.

\subsubsection{De Bruijn}\label{sec:background-debruijn}

De Bruijn is a system of variable binding commonly used when expressing $\lambda$-calculus. It is a notation which identifies a variable occurrence with the \emph{distance} to the location of the binding $\lambda$ \cite{debruijn1994lambda,turing1937computability}. Traditionally, in $\lambda$-calculus, a new lambda abstraction would introduce a new named variable that can be referred to in the body of the abstraction. This naming scheme however comes with caveats. One has to consider how to handle non-uniqueness of names. This can be especially troublesome if a variable in an expression has to be replaced by a second expression that contains a free variable of the same name ($\beta$-reduction). Another difficulty with this naming scheme arises when one attempts to establish equivalence between two expressions where the only difference lies in the names of the bound variables.

The De Bruijn system solves these ambiguities, since each reference points directly to its binding location. The main disadvantage is that it is harder to find usage of a given variable throughout an expression for a human observer, since the identifier may change its value depending on the number of lambda abstractions in the expression at any given point. However, this representation makes it much easier to reason about expressions for a computer system, for example in a dependently typed proof assistant such as Agda.

\subsubsection{HOAS/PHOAS}\label{sec:background-hoasphoas}

The approaches for variable binding discussed above can be implemented entirely inside the data type which represents the deep embedding. Another strategy can be to use variable binding of the host language. The host language usually has an advanced binding system which deals well with naming and shadowing and other cases where there are multiple definitions. Using the host language binding constructs is referred to as \emph{higher-order abstract syntax}, or HOAS for short. A very simple example of lambda calculus using HOAS:\nopagebreak

\begin{center}
\begin{code}
data L : Set where
  Lam : (L → L) → L

app : L → L → L
app (Lam f) x = f x
\end{code}
\end{center}

\pagebreak

The |Lam| constructor takes a function of the type |(L → L)|, which represents the body of the lambda abstraction. A user who wants to create something of this type would typically feed in an anonymous function (a lambda expression) in the host language, and use the host language's binding constructs to represent the embedded language's bindings, for example as such:\nopagebreak

\begin{center}
\begin{code}
id = Lam (λ x → x)
\end{code}
\end{center}

Note how the binding of the named variable |x| is the host language's binding, but how it represents the binding in the embedded language.

The data type |L|, in the way it is presented above, is actually not legal Agda code. The |Lam| constructor is problematic. Agda only allows inductive appearances of the type in \emph{strictly positive} positions. By looking at the |Lam| constructor as a function that takes a function as an argument, we can see that the first occurrence of |L| is contravariant in that position. This leads to a type system error in Agda. In order to see why this could be problematic, look at the following example:

\begin{center}
\begin{code}
ω = Lam (λ x → app x x)
Ω = app ω ω
\end{code}
\end{center}

If Agda were to try and evaluate |Ω|, it would construct a term that is the combinator equivalent of $(λx . xx) (λx . xx)$, of which the normal form does not terminate. This is unacceptable in the context of dependent types, since the type checker would run into an infinite loop if this were allowed. All valid expressions must be total in order for the static type checking phase to be guaranteed to terminate. Furthermore, we can't accept such undefined values in our types without making the logic they represent unsound. A solution to this problem is to use \term{parametrized higher-order abstract syntax}, or PHOAS for short \cite{chlipala2008parametric}. Let's add a parameter to the |L| data type:\nopagebreak

\begin{center}
\begin{code}
data P (a : Set) where
  Lam : (a → P a) → P a
  Var : a → P a
\end{code}
\end{center}

By adding the type parameter to the data type |P|, the Agda type checker will catch ill-typed constructs such as |Ω| as defined above. The |Lam| constructor no longer has negative occurrences, and will be accepted by Agda. Lastly, we added the |Var| constructor to lift objects of type |a| to |P a|.

There is work by \cite{atkey2009unembedding} which converts expressions of untyped $\lambda$-calculus back and forth between HOAS and De Bruijn representation embedded in Haskell. Since the Haskell type checker is less restrictive than Agda's, this issue did not become a problem in their implementation. Only after they moved to simply typed $\lambda$-calculus did they run into what they refer to as \emph{exotic} types. For their work, they also chose to add a type parameter to their higher-order abstract syntax in order to ensure well-typedness of their embedded language.
