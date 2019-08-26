%include thesis.fmt

\newpage
\section{\Piware and \lambdaone}\label{sec:piware-and-lambdaone}

\subsection{\Piware}\label{sec:piware}

\Piware is a deeply embedded domain specific language to describe hardware, which uses Agda as the host language \cite{flor2014pi}. It allows for the simulation, synthesis, and verification of hardware design. At the heart of \Piware lies the circuit data type |ℂ| (Agda listing \ref{agda:piware-circuit-def}). This data type defines how basic building blocks in the form of gates are interconnected in order to form a working circuit. It uses dependent types to guarantee the soundness of the number of connections between composited circuit elements.

\begin{agdacodefloat}\small
\begin{tcolorbox}
\begin{code}
data ℂ[_] (G : Gates) : {s : IsComb} → Ix → Ix → Set
    Gate       : ∀ {g# s}           → ℂ[ G ] {s} (|in| G g#) (|out| G g#)

    Plug       : ∀ {i o s}          → Vec (Fin i) o
                                    → ℂ[ G ] {s} i o

    _⟫_        : ∀ {i m o s}        → ℂ[ G ] {s} i m
                                    → ℂ[ G ] {s} m o
                                    → ℂ[ G ] {s} i o

    _∥_        : ∀ {i₁ o₁ i₂ o₂ s}  → ℂ[ G ] {s} i₁ o₁
                                    → ℂ[ G ] {s} i₂ o₂
                                    → ℂ[ G ] {s} (i₁ + i₂) (o₁ + o₂)

    DelayLoop  : ∀ {i o l}          → ℂ[ G ] {σ} (i + l) (o + l)
                                    → ℂ[ G ] {ω} i o
\end{code}
\end{tcolorbox}
\caption{\Piware circuit definition}
\label{agda:piware-circuit-def}
\end{agdacodefloat}

The circuit data type is parametrized with a set of basic gates as a record of type |Gates|, the choice of which is up to the user. Two popular options are |BoolTrio| and |Nand|. The former contains logical negation, logical conjunction and logical disjunction. Each gate has a number of input and output wires. Notice how the |Gate| constructor above calls the |∣in∣| and |∣out∣| functions, which works on the |Gates| record taking an argument for the gate identifier |g#|, in order to specify the number of input and output wires for the given gate.

Furthermore, the circuit data type is indexed with an enumeration |(s : IsComb)| to indicate if the circuit contains loops (indicated by |ω|) or not (indicated by |σ|). The circuit is also indexed with two numbers |Ix| for input and output wires respectively. In order to get a better feel for the input and output wires, imagine that the entire circuit defines a function from a vector of the size of the number of input wires to a vector of the size of the number of output wires.

\begin{figure}[h]
  \centering
  \begin{code}
  (Gate AND) : ℂ[ BoolTrio ] {σ} 2 1
  \end{code}
  \begin{tikzpicture}[scale=0.5, auto]
    \draw (0,0) node (input0) {};
    \draw (0,-2) node (input1) {};
    \draw (2,-1) node[block,minimum height=2cm,minimum width=1cm,text width=1cm,align=center] (and) {|Gate|\\|AND|};
    \draw (4,-1) node (output) {};
    \draw [connector] (input0) -- (and.west «- input0);
    \draw [connector] (input1) -- (and.west «- input1);
    \draw [connector] (and) -- (output);
  \end{tikzpicture}
  \caption{|AND| gate in \Piware}
  \label{fig:piware-gate-and}
\end{figure}

See figure \ref{fig:piware-gate-and} where we present an illustration of a simple example circuit consisting of a single |Gate| named |AND| from the |BoolTrio| set of |Gates|. It does not loop (indicated by |{σ}|). Finally, it takes |2| inputs and produces |1| output.

Circuits can be composited either in sequence (|_⟫_|) or in parallel (|_∥_|). By composing gates in parallel, the user creates a circuit that has the number of inputs and outputs of both gates added together. These gates can then be composited sequentially to create longer circuits which represent multiple chained logical steps.

By default, sequential composition will just map each output wire with index $i$ to the input wire with index $i$. If this is not the desired effect, the user can employ the |Plug| constructor. Looking at the code of the |Plug| constructor, we can see it uses a vector of size |o|, where each element is a number in the range $[0, i - 1]$. This lets users remap the wiring of outputs of circuits by composing the original circuit with a plug. Not only that, but by omitting or repeating certain indices in the vector, it also allows for the \emph{forgetting} or the \emph{duplication} of certain outputs respectively.

\begin{figure}[h]
  \centering
  \begin{code}
  ((Plug (0 ∷ 0 ∷ []) ⟫ Gate NAND) ∥ (Plug (0 ∷ 0 ∷ []) ⟫ Gate NAND)) ⟫ Gate NAND
  \end{code}
  \begin{tikzpicture}[scale=0.5, auto]
    % NAND A A
    \draw (-2,0) node (a) {$A$};
    \draw (-0.5,0) node[branch] (brancha) {};
    \draw (0,-2) node (belowbrancha) {};
    \draw (2,-1) node[block,minimum height=2cm,minimum width=1cm,text width=1cm,align=center] (anand) {|Gate|\\|NAND|};
    \draw (4,-1) node (anandout) {};
    \draw [line] (a) -- (brancha);
    \draw [connector] (brancha) -- (anand.west «- brancha);
    \draw [connector] (brancha) «- (anand.west «- belowbrancha);
    %\draw [line] (anand) -- (anandout.mid);
    % NAND B B
    \draw (-2,-5) node (b) {$B$};
    \draw (-0.5,-5) node[branch] (branchb) {};
    \draw (0,-7) node (belowbranchb) {};
    \draw (2,-6) node[block,minimum height=2cm,minimum width=1cm,text width=1cm,align=center] (bnand) {|Gate|\\|NAND|};
    \draw (4,-6) node (bnandout) {};
    \draw [line] (b) -- (branchb);
    \draw [connector] (branchb) -- (bnand.west «- branchb);
    \draw [connector] (branchb) «- (bnand.west «- belowbranchb);
    %\draw [line] (bnand) -- (bnandout.mid);
    % NAND (NAND A A) (NAND B B)
    \draw (4,-2.5) node (finput0) {};
    \draw (4,-4.5) node (finput1) {};
    \draw (6,-3.5) node[block,minimum height=2cm,minimum width=1cm,text width=1cm,align=center] (fnand) {|Gate|\\|NAND|};
    \draw (10,-3.5) node (ab) {$A + B$};
    \draw [connector] (anand) -- ++(2,0) «- (fnand.west «- finput0);
    \draw [connector] (bnand) -- ++(2,0) «- (fnand.west «- finput1);
    \draw [connector] (fnand) -- (ab);
  \end{tikzpicture}
  \caption{Implementation of $(A + B)$ in \Piware}
  \label{fig:piware-example-with-nands}
\end{figure}

See figure \ref{fig:piware-example-with-nands} where we present an illustration of how plugs, gates, and constructed circuitry can be composed in parallel and in sequence to produce more complex behavior. In this example, we first duplicate both the inputs (labeled $A$ and $B$ for convenience) using a |Plug| which outputs it's |0|th input twice before connecting them to their own |NAND| gate respectively. These operations are composed sequentially in order to generate the "left hand side" circuit which takes two inputs and produces two outputs. Finally, we apply sequential composition to connect the two "left hand side" outputs to another |NAND| gate, to produce our final output $A + B$.

In order to loop back wires from the output of a circuit back to its input, the user can use the |DelayLoop| constructor. Note how this is the only constructor which places a restriction on its argument's circuit, ensuring that its implicit index |{s : IsComb}| must be equal to |σ|. It constructs a circuit with the combinational index set to |ω| to indicate the looping nature of the resulting circuit. All other constructors inside |ℂ| maintain the combinational index of their given input.

\subsection{Plugs versus named variables}\label{sec:plugsvsvars}

The circuit data structure |ℂ| uses indexed inputs and outputs. If a user wants to design a circuit with sequential composition, the Agda type checker will ensure that the number of outputs of the first circuit matches the number of inputs of the second circuit. However, the user has to pay attention themself that the wires are connected in a way that reflects the logical structure they are trying to build. \Piware's use of indexed gates and lack of variable bindings means that it is, similarly to SKI combinators, nameless (See section \ref{sec:background-nameless}).

This representation is very close to the actual hardware representation of gates and wires, which is evident by the descriptions of the data structures given here. However, it requires the user to keep very precise track of outputs and inputs of circuits. This process is prone to human error when designing more complicated circuits.

Existing high-level programming languages have had support for named variables instead of indexed inputs and outputs for a long time. Using named variables creates self-documenting code, reducing the chance for human error during development. They also provide a user-friendly method to share computations across several parts of the program.

\subsection{\lambdaone}\label{sec:lambdaone}

At the end of J. P. Pizani Flor's master thesis which introduces \Piware, there is mention of future work of a higher-level applicative interface language that would be nicer to use for circuit designers \cite{flor2014pi}. This follow-up work has since been published  \cite{flor2018verified}, presenting a new language called \lambdapiware. \lambdapiware comes in two flavors: |λB| and |λH|. These variations use De Bruijn variable bindings (See section \ref{sec:background-debruijn}) and HOAS style bindings (See section \ref{sec:background-hoasphoas}), respectively. We'll be focusing on the former, especially since a program of the latter can be unembedded into an equivalent program of the former.

The |λB| language inside \lambdapiware is indexed with a type universe and a type context, and also parametrized by a set of logical gates similar to \Piware. It offers several constructors, for example for referring to variables, for introducing sharing through \emph{let}-binding, and for application.

% \lambdapiware does not have classical lambda abstractions like in normal $\lambda$-calculus. Instead of general terms, only gates can be applied. The reason for this is the lack of synthesis of higher-order terms. Instead, it uses \emph{let}-bindings for sharing purposes. Furthermore, \lambdaone includes a more advanced type universe than \Piware's circuits, which were merely indexed by their input and output size.

During the development of the proofs for this thesis, \lambdapiware was still under active development. For this reason, we've made the decision to fork this language. Our fork offers many of the same features as \lambdapiware, with a few differences. Most notably, the absence of a \emph{loop} constructor and a modification of the type universe.

We've named this fork \lambdaone (pronounced \emph{lambda one}), after the working name that was used while J. P. Pizani Flor was developing the embedded language of \lambdapiware. See Agda listing \ref{agda:lambdaone-def} for the formal definition of this fork.

\begin{agdacodefloat}\small
\begin{tcolorbox}
\begin{code}
data Λ₁ : (Γ : Ctxt) → (Δ : List Uₚ) → (τ : Uₚ) → Set where

  ⟨_⟩               : ∀ {Γ}          → (g : Gate)
                                     → Λ₁ Γ (inputs g) (output g)

  #[_]              : ∀ {Γ τ}        → (r : Ref Γ τ)
                                     → Λ₁ Γ [] τ

  _$₁_              : ∀ {Γ Δ α β}    → (f : Λ₁ Γ (α ∷ Δ) β)
                                     → (x : Λ₁ Γ [] α)
                                     → Λ₁ Γ Δ β

  letₓ_inₑ_         : ∀ {Γ Δ α τ}    → (x : Λ₁ Γ [] α)
                                     → (e : Λ₁ (α ∷ Γ) Δ τ)
                                     → Λ₁ Γ Δ τ

  _,₁_              : ∀ {Γ α β}      → (x : Λ₁ Γ [] α)
                                     → (y : Λ₁ Γ [] β)
                                     → Λ₁ Γ [] (α ⨂ β)

  case⨂_of_         : ∀ {Γ Δ α β τ}  → (xy : Λ₁ Γ [] (α ⨂ β))
                                     → (f : Λ₁ (α ∷ β ∷ Γ) Δ τ)
                                     → Λ₁ Γ Δ τ

  inl₁              : ∀ {Γ α β}      → (x : Λ₁ Γ [] α)
                                     → Λ₁ Γ [] (α ⨁ β)

  inr₁              : ∀ {Γ α β}      → (y : Λ₁ Γ [] β)
                                     → Λ₁ Γ [] (α ⨁ β)

  case⨁_either_or_  : ∀ {Γ Δ α β τ}  → (xy : Λ₁ Γ [] (α ⨁ β))
                                     → (f : Λ₁ (α ∷ Γ) Δ τ)
                                     → (g : Λ₁ (β ∷ Γ) Δ τ)
                                     → Λ₁ Γ Δ τ
\end{code}
\end{tcolorbox}
\caption{\lambdaone language definition}
\label{agda:lambdaone-def}
\end{agdacodefloat}

\subsubsection{Type universe}\label{sec:lambdaone-type-universe}

So far, the type safety provided by the \Piware circuit data type |ℂ| (after being fed with a parameter for the |Gates| to be used) consisted only of the input and output wire count. Using the input and output sizes of circuits as typing provided us with certain soundness guarantees, most notably the absence of short-circuits.

An alternative approach would be to index the circuits by the actual \emph{type} of atomic data being transported over each input and output wire. We haven't touched on what can actually be transported along these wires, and just assumed that we were always talking about single bits. However, \Piware does not restrict us to transport only bits on wires. Since \Piware is a deep embedding rather than a shallow embedding (See section \ref{sec:background-varbindings}), the behavioral semantics of the language are defined separately from the language's structure. \Piware allows any data type that is finite and enumerable to be used as the so-called |Atom| to be transported over the wires.

\lambdaone uses a method of indexing input and output types separately. Instead of a type class that can be implemented for \emph{atomic} data which can be transported along wires, it introduces a finite type universe similar to the Haskell reflective type universe, being a universe of products of sums. We present the definition of this type universe (named |Uₚ|) in Agda listing \ref{agda:polytypes-def}.

\begin{agdacodefloat}\small
\begin{tcolorbox}
\begin{code}
data Uₚ : Set where
  𝟙    : Uₚ
  _⨂_  : Uₚ → Uₚ → Uₚ
  _⨁_  : Uₚ → Uₚ → Uₚ
\end{code}
\end{tcolorbox}
\caption{Polytypes, the type universe for \lambdaone}
\label{agda:polytypes-def}
\end{agdacodefloat}

The \emph{p} in |Uₚ| was chosen to refer to the term \term{polytype}, since |Uₚ| can be used to represent any non-recursive generic type through induction over that type's structure. In Agda, all datatypes are defined as a list of constructors, where each constructor can have any number of arguments of arbitrary types themselves. The sum type represents an \emph{alternation}. As such, the list of possible constructors for a datatype can be encoded as a sum over all possible constructors:\nopagebreak

\begin{center}
\begin{code}
MyDataTypeₚ = Constructor¹ ⨁ (Constructor² ⨁ (… ⨁ Constructorⁿ))
\end{code}
\end{center}

The product type represents a \emph{combination}. Each constructor can be encoded as a product of its arguments:\nopagebreak

\begin{center}
\begin{code}
Constructorⁱₚ = DataType¹ ⨂ (DataType² ⨂ (… ⨂ Datatypeᵐ))
\end{code}
\end{center}

It has been shown that a type universe such as this one is enumerable for non-recursive types \cite{altenkirch2007generic}, which means we can atomize any non-recursive composition of |Uₚ| into |Atom|s to be transported over wires in \Piware. More about this in section \ref{sec:atomization}.

The |Λ₁| data type has an index |τ| of type |Uₚ| to specify the \emph{output} type of the circuit. The \emph{input}s of a circuit are described by a list |Δ| of |Uₚ|. This is different from the published design of \lambdapiware, which only has a single index on |λB| for the type universe. |λB| gets away with just a single polytype index since it uses a type universe that includes function types through an arrow constructor. This lets it define inputs and outputs directly in that index.

By removing the function constructor from the definition of |Uₚ| and instead encoding the inputs and output of any |Λ₁| program explicitly in its type definition, we can forbid higher-order types. This means we can guarantee that, whenever we are given a circuit of |Λ₁|, it will not contain any contravariant occurrences of type variables.

We also provide a function |Tₚ| to map types in |Uₚ| to their corresponding Agda type in Agda listing \ref{agda:polytypes-unembedding}. This allows us to create values in Agda that belong to an (un)embedded type |(Tₚ τ)|.

\begin{agdacodefloat}\small
\begin{tcolorbox}
\begin{code}
Tₚ : Uₚ → Set
Tₚ 𝟙        = ⊤
Tₚ (σ ⨂ τ)  = Tₚ σ × Tₚ τ
Tₚ (σ ⨁ τ)  = Tₚ σ ⊎ Tₚ τ
\end{code}
\end{tcolorbox}
\caption{Mapping of polytypes to Agda types}
\label{agda:polytypes-unembedding}
\end{agdacodefloat}

\begin{agdacodefloat}\small
\begin{multicols}{2}%\footnotesize
\begin{tcolorbox}
\begin{code}
Bool : Set
Bool = Tₚ (𝟙 ⨁ 𝟙)
\end{code}
\begin{code}
pattern false  = inj₁ ⊤.tt
pattern true   = inj₂ ⊤.tt
\end{code}
\begin{code}
_∧_ : Bool → Bool → Bool
false  ∧ b  = false
true   ∧ b  = b
\end{code}
\end{tcolorbox}
\begin{tcolorbox}
\begin{code}
Maybe : Uₚ → Set
Maybe A = Tₚ (𝟙 ⨁ A)
\end{code}
\begin{code}
pattern nothing  = inj₁ ⊤.tt
pattern just x   = inj₂ x
\end{code}
\begin{code}
is-just : ∀ {A} → Maybe A → Bool
is-just nothing   = false
is-just (just _)  = true
\end{code}
\end{tcolorbox}
\end{multicols}
\caption{Examples of common data types encoded as polytypes}
\label{agda:polytypes-examples}
\end{agdacodefloat}

\pagebreak

Finally, in Agda listing \ref{agda:polytypes-lambdaset}, we also present a method to transform the list of input types together with a single output type as used in the indices of |Λ₁| into Agda function types. We introduce a new datatype |ΛSet| which lets us store the tuple of |Δ| and |τ| in an alternative representation. Note how, even though we are technically reintroducing an arrow constructor, there is no way to create higher-order function types, because this arrow constructor strictly only allows adding of first-order (i.e. non-arrow) types |Uₚ| to the left-growing type term.

\begin{agdacodefloat}\small
\begin{tcolorbox}
\begin{code}
Λ⟦_⟧ : ΛSet → Set
Λ⟦ τ ⊩     ⟧  = Tₚ τ
Λ⟦ σ ⇀ τs  ⟧  = Tₚ σ → Λ⟦ τs ⟧
\end{code}
\begin{code}
data ΛSet : Set where

  _⊩   : Uₚ → ΛSet
  _⇀_  : Uₚ → ΛSet → ΛSet
\end{code}
\begin{code}
_↣_ : (Δ : List Uₚ) → (τ : Uₚ) → ΛSet
ε        ↣ τ  = τ ⊩
(x ∷ Δ)  ↣ τ  = x ⇀ (Δ ↣ τ)
\end{code}
\end{tcolorbox}
\caption{How to transform |Δ|, |τ| to an Agda function type using |Λ⟦ Δ ↣ τ ⟧|}
\label{agda:polytypes-lambdaset}
\end{agdacodefloat}

\subsubsection{Variable bindings}\label{sec:lambdaone-varbindings}

\lambdaone uses De Bruijn indices to bind variable references. Since the language is defined recursively, any subterm has no direct knowledge of the terms that encompass it. Each term therefore carries with it a \emph{context} |Γ|, which contains type information for the environment in which the term is being used. |Γ| works as a lookup table for type information, with the De Bruijn index of a variable being used as the index into the list.

\pagebreak

\subsubsection{Gates}\label{sec:lambdaone-gates}

We have removed the parametrisation of a gate library, instead hardcoding a set of gates. The translation of primitive gates is not of interest to this work. By choosing a fixed set of gates, the translation code is cleaner and easier to follow. It also allows us to depend on these basic gates when constructing building blocks to translate certain constructors, as we will see in section \ref{sec:translation}.\nopagebreak

\begin{agdacodefloat}\small
\begin{tcolorbox}
\begin{code}
data Gate : Set where
  TRUE FALSE NOT AND OR : Gate
\end{code}
\end{tcolorbox}
\caption{Gates used in \lambdaone}
\label{agda:lambdaone-gates}
\end{agdacodefloat}

% Hack to work around weird bug where ending on a agdacodefloat ignores the new section's newpage
\begin{code}

\end{code}
