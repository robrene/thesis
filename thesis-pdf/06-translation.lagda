%include thesis.fmt

\newpage
\section{Translation}\label{sec:translation}

\subsection{Intermediate language}\label{sec:intermediatelang}

When we translated Simply Typed Lambda Calculus with typed variable bindings to SKI combinators without any bindings in section \ref{sec:prototype}, we used a strategy that involved an intermediate language. The intermediate language was chosen to be close to the target language, which is supposed to be bindingless. However, we included a list of types as a context |Ctx| and allowed for an additional term constructor for references.

When translating from \lambdaone to \Piware, we choose a similar approach. First, we translate to an intermediate language (See Agda listing \ref{agda:intermediate-lang-def}) which is almost identical to the target language \Piware, but also includes some type context for a term that represents a reference to a binding. It helps to visualise the references as holes in the completed circuit. The holes are always in the shape of missing circuitry on the \emph{input}, since this is where the circuit expects the value of a specific variable. The context dictates how many output wires each placeholder has. In the second stage, when we translate the intermediate language to the target language, we need to connect the circuitry which represents the value of the variable binding to the outputs of the placeholder as we replace them. The goal is to replace every placeholder and end up with a circuit that does not need placeholders, and thus represents a valid \Piware circuit without variable bindings.

\begin{agdacodefloat}\small
\begin{tcolorbox}
\begin{code}
data IL[_] (G : Gates) : (Γ : Ctxt) → ℕ → ℕ → Set where

  G⟨_⟩  : ∀ {Γ}              → (g# : Gate# G)
                             → IL[ G ] Γ (#in G g#) (#out G g#)

  Grnd  : ∀ {Γ o}            → IL[ G ] Γ 0 o

  Plug  : ∀ {Γ i o}          → i ⇇ o
                             → IL[ G ] Γ i o

  _⟫_   : ∀ {Γ i j o}        → IL[ G ] Γ i j
                             → IL[ G ] Γ j o
                             → IL[ G ] Γ i o

  _∥_   : ∀ {Γ i₁ o₁ i₂ o₂}  → IL[ G ] Γ i₁ o₁
                             → IL[ G ] Γ i₂ o₂
                             → IL[ G ] Γ (i₁ + i₂) (o₁ + o₂)

  Var   : ∀ {Γ τ}            → Ref Γ τ
                             → IL[ G ] Γ 0 (sz τ)
\end{code}
\end{tcolorbox}
\caption{Intermediate language definition}
\label{agda:intermediate-lang-def}
\end{agdacodefloat}

Looking at the definition of our intermediate language, it should be immediately obvious that it is very close to \Piware. There are some differences, however. Most notably, the addition of the |(Γ : Ctxt)| index on |IL[_]|'s type. The added constructor |Var| holds a variable in the form of a contextualized reference |Ref| (See Agda listing \ref{agda:intermediate-lang-ref}). Note that this reference only contains information about the \emph{type} of the variable, not the \emph{value}. We don't care about the value of the reference until we actually run the circuit, at which point we provide the evaluation function with a list of values, one for each item in the context. We will need evaluation semantics for this intermediate language later on in the correctness proof in section \ref{sec:eval-semantics}.

\begin{agdacodefloat}\small
\begin{tcolorbox}
\begin{code}
data Ref : Ctxt → Uₚ → Set where
  top  : ∀ {Γ τ}    → Ref (τ ∷ Γ) τ
  pop  : ∀ {Γ σ τ}  → Ref Γ τ → Ref (σ ∷ Γ) τ
\end{code}
\end{tcolorbox}
\caption{Definition of variable references used in the intermediate language}
\label{agda:intermediate-lang-ref}
\end{agdacodefloat}

We already took a look at an equivalent |Ref| data type in section \ref{sec:simply-typed-lambda-calc} The |Ref| datatype's implementation lets us refer to freely occuring variables in the context in a De Bruijn fashion (See section \ref{sec:background-debruijn}). It uses repeated calls of |pop| to encode the remaining iteration steps into the list of types |(Γ : Ctxt)|. For example, |(top) : Ref (α ∷ β ∷ γ ∷ []) α| represents a reference to the first type, |α|. Next, |(pop top) : Ref (α ∷ β ∷ γ ∷ []) β| represents a reference to the second type, |β|. Note how the dependent type system is enforcing a sound reference chain into the context as we unzip the structure of |pop| calls.

While designing the intermediate language, there were two options to use as the type universe for the binding context. One option is to stay closer to the target language \Piware and to store the number of output wires for each reference. The alternative option is to stay closer to the source language \lambdaone and to store the type from that type universe (as shown in section \ref{sec:lambdaone-type-universe}). Even though both strategies should be manageable to bring to a working solution, we've chosen the latter option for our solution. When compared against numbers and arithmetic operations, the structured type data from the type universe of polytypes |Uₚ| is easier to manage in a dependent programming environment. The structured type data contains some information that tends to get lost when dealing with raw numbers.

Finally, the definition of |IL[_]| also contains a constructor for |Grnd|. This was added as an easy way to add null inputs inside the circuit, by essentially attaching the input wire to a \emph{ground}. We technically don't need this constructor, but it eases the implementation effort and increases the readability for certain components that are needed later.

\pagebreak

\subsection{Atomization of polytypes}\label{sec:atomization}

The domain of |Λ₁| is different from that used in \Piware. Where |Λ₁| circuits input and output polytypes |Uₚ|, \Piware circuits work on vectors of |Atom| for their input and output. Since \Piware lets users use any |Atom| with the only restriction being that it is enumerable, it makes sense for us to use the simplest possible |Atom|, namely |Bool|. We refer to a vector of |Bool| as a \emph{word}, or |W| in the code.

First, let us introduce a translation between polytyped values and words. We showed an alternative representation of input types and output type of |Λ₁| using a datatype |ΛSet| in section \ref{sec:lambdaone-type-universe}. As we will see in the correctness proof in section \ref{sec:correctness}, we will need the ability to \emph{atomize} the unembedding of the \lambdaone circuit in order to be able to compare the behavioral equality of circuits translated to \Piware to programs in \lambdaone. When we speak about atomizing the circuit, we mean the translation of inputs and outputs of the circuit from the space of polytypes to the space of words. This lets us feed \lambdaone programs with a word for the input and get a word as output. To achieve this, we require the translation of the circuit output from polytypes to words, but also the translation of the input word to polytypes. See Agda listing \ref{agda:polytype-word-translation-def}.

\begin{agdacodefloat}\small
\begin{tcolorbox}
\begin{code}
⤋ : ∀ {τ} → (v : Tₚ τ) → W (sz τ)

⤋ {𝟙}      _         = []
⤋ {σ ⨂ τ}  (x , y)   = ⤋ x ++ ⤋ y
⤋ {σ ⨁ τ}  (inj₁ x)  = false ∷ pad₁ (sz τ) (⤋ x)
⤋ {σ ⨁ τ}  (inj₂ y)  = true ∷ pad₂ (sz σ) (⤋ y)
\end{code}
\begin{code}
⤊ : ∀ {τ} → (w : W (sz τ)) → Tₚ τ

⤊ {𝟙}      _            = ⊤.tt
⤊ {σ ⨂ τ}  w            = ⤊ (take (sz σ) w) , ⤊ (drop (sz σ) w)
⤊ {σ ⨁ τ}  (false ∷ w)  = inj₁ (⤊ (unpad₁ (sz σ) (sz τ) w))
⤊ {σ ⨁ τ}  (true ∷ w)   = inj₂ (⤊ (unpad₂ (sz σ) (sz τ) w))
\end{code}
\end{tcolorbox}
\caption{Definition of |⤋| and |⤊|, to translate between polytypes and words}
\label{agda:polytype-word-translation-def}
\end{agdacodefloat}

Remember that polytypes |Uₚ| can be used to describe any data type by performing induction over its generic structure. The function |⤋| lets us transform a polytyped value |v| into a word |w|. Conversely, the function |⤊| transforms a given word |w| back into a polytyped value |v|. Of course, the size of the word is dependent on how many bits we need to encode.

The unit type |𝟙| doesn't need any bits to represent its possible values, since there is only a single value possible. Product types |_⨂_| represent tuples. They require enough bits to encode both parts of the tuple. Hence, we translate product types into words by translating each part of the tuple into words and concatenating them. Finally, sum types |_⨁_| describe a choice between two polytypes. We need a single bit in order to encode which choice has been made, and then we need to encode the polytype that was actually chosen as well.

However, there exists a caveat when encoding the chosen polytype in |σ ⨁ τ|. Our size function |sz| just returns a single size that would guarantee to fit the given polytype. Since the two possible polytypes |σ| and |τ| can potentially have different sizes, we need to choose the larger of the two sizes as the size for |σ ⨁ τ|. This in turn means that when encoding the smaller of the two polytypes, we need to pad the result with some dummy bits to meet the word-size requirement. See Agda listing \ref{agda:pad-unpad-def}.

Note that we are using our own custom \emph{max} function for natural numbers |(_⊔₂_)|. The Agda standard library does provide a max function, but it doesn't allow for easy inspection. We will go into more detail around |(_⊔₂_)| and the improvements it brings over the standard Agda one in section \ref{sec:atomization-correctness}. For now, suffice it to say that type arguments which use |(_⊔₂_)| can be inspected by using |compare₂|, which tells us which of the two operands was greater (or less-or-equal respectively) and by how much.

We can use this property to implement the necessary padding of meaningless bits when required for the translation of a polytype into a word. When translating a polytype value |(inj₁ x)| of type |{σ ⨁ τ}|, where |x| is of type |σ|, we can just translate |x| directly into a word of |(sz σ)| and pad it \emph{up to} a size of |(sz τ)| using |pad₁|. Conversely, |pad₂| allows us to do the same when dealing with the other operand of |{σ ⨁ τ}| (i.e. padding |y| from |(inj₂ y)| to up to |sz σ| bits).

In a similar fashion, when translating from words back to polytypes, we need to "unpad" the word. This throws away the meaningless bits from the word and allows us to translate the meaningful bits back into a polytyped value.

\begin{agdacodefloat}
\begin{multicols}{2}\footnotesize
\begin{tcolorbox}
\begin{code}
pad₁ : ∀ {m} n → W m → W (m ⊔₂ n)

pad₁ {m} n w with compare₂ m n
pad₁ {.m}            .(m + k)  w
  | lesseq m k   = w ++ replicate false
pad₁ {.(m + suc k)}  .m        w
  | greater m k  = w
\end{code}
\begin{code}
pad₂ : ∀ m {n} → W n → W (m ⊔₂ n)

pad₂ m {n} w with compare₂ m n
pad₂ .m            {.(m + k)}  w
  | lesseq m k   = w
pad₂ .(m + suc k)  {.m}        w
  | greater m k  = w ++ replicate false
\end{code}
\end{tcolorbox}
\begin{tcolorbox}
\begin{code}
unpad₁ : ∀ m n → W (m ⊔₂ n) → W m

unpad₁ m n w with compare₂ m n
unpad₁ .m            .(m + k)  w
  | lesseq m k   = take m w
unpad₁ .(m + suc k)  .m        w
  | greater m k  = w
\end{code}
\begin{code}
unpad₂ : ∀ m n → W (m ⊔₂ n) → W n

unpad₂ m n w with compare₂ m n
unpad₂ .m            .(m + k)  w
  | lesseq m k   = w
unpad₂ .(m + suc k)  .m        w
  | greater m k  = take m w
\end{code}
\end{tcolorbox}
\end{multicols}
\caption{Definition of |pad| and |unpad|}
\label{agda:pad-unpad-def}
\end{agdacodefloat}

Finally, we present a function |atomize| in Agda listing \ref{agda:atomize-def} which is able to take functions in the |ΛSet| space and let us run them in the |W→W| space. We achieved this by piecewise transforming chunks of the input word into polytyped values to partially apply to the |ΛSet| for each input type inside |Δ|. Once all inputs are exhausted we can transform the output back to a word.

\begin{agdacodefloat}\small
\begin{tcolorbox}
\begin{code}
atomize : ∀ {Δ τ} → Λ⟦ Δ ↣ τ ⟧ → W→W (sz-list Δ) (sz τ)

atomize {[]}     l  = const $ ⤋ l
atomize {σ ∷ Δ}  l  = λ i → atomize {Δ} (l $ ⤊ {σ} (take (sz σ) i)) (drop (sz σ) i)
\end{code}
\end{tcolorbox}
\caption{Definition of |atomize|}
\label{agda:atomize-def}
\end{agdacodefloat}

\vspace*{2em}

\subsection{Stage 1}\label{sec:stage1}

In our two-step translation approach, the first stage is by far the more complex one of the two. The first stage is all about translating |Λ₁| terms to an intermediate language representation. We need to convert every possible constructor in |Λ₁| into equivalent constructions made out of gates and plugs. The only thing we get to keep is variable bindings.

\subsubsection{Translation}\label{sec:stage1-translation}

We present the definition of our first stage's |translate| function in Aga listing \ref{agda:stage1-translate-def}. As expected, primitive gates and variable bindings can be translated directly into our intermediate language. Tuples (|_,₁_|) are simply representable by compositing each part of the tuple using parallel composition.

\begin{agdacodefloat}[H]\small
\begin{tcolorbox}
\begin{code}
translate : ∀ {Γ Δ τ} → Λ₁ Γ Δ τ → IL[ ΛBoolTrio ] Γ (sz-list Δ) (sz τ)

translate ⟨ g ⟩                  =  G⟨ g ⟩

translate #[ r ]                 =  Var r

translate (f $₁ x)               =  (translate x ∥ PlugId')
                                    ⟫ translate f

translate (letₓ x inₑ e)         =  (translate x ∥ PlugId')
                                    ⟫ reduce-ctxt (translate e)

translate (x ,₁ y)               =  translate x ∥ translate y

translate (case⊗ xy of f)        =  (translate xy ∥ PlugId')
                                    ⟫ reduce-ctxt-twice (translate f)

translate (inl₁ {_} {α} {β} x)   =  G⟨ FALSE ⟩
                                    ∥ left-pad (sz α) (sz β) (translate x)

translate (inr₁ {_} {α} {β} y)   =  G⟨ TRUE ⟩
                                    ∥ right-pad (sz α) (sz β) (translate y)

translate (case⊕_either_or_ {α = α} xy f g)
                                 =  branching-circuit {a = sz α}
                                    (translate xy)
                                    (reduce-ctxt (translate f))
                                    (reduce-ctxt (translate g))
\end{code}
\end{tcolorbox}
\caption{Definition of |Stage1.translate|}
\label{agda:stage1-translate-def}
\end{agdacodefloat}

For function application (|_$₁_|), we just attach the input |(translate x)| to the first set of wires of |(translate f)|, using an identity plug (See Agda listing \ref{agda:plugid}) for the remaining input wires. Our |PlugId'| function is smart enough to implicitly use the correct number of wires, which can also be zero. This means this definition works for both total and partial function application. See figure \ref{fig:partial-application} for an illustration.

We achieve the implicit choice of the correct number of identity wires by letting Agda decide the size of the parameter |n| implicitly. The standard library function |allFin| provides us with a simple enumeration of numbers $(0, ..., n - 1)$ which map each output to the corresponding input.

\begin{agdacodefloat}[H]
\begin{multicols}{2}\small
\begin{tcolorbox}
\begin{code}
⇇-id : ∀ n → n ⇇ n
⇇-id n = allFin n
\end{code}
\end{tcolorbox}
\begin{tcolorbox}
\begin{code}
PlugId' : ∀ {G Γ n} → IL[ G ] Γ n n
PlugId' {n = n} = Plug $ ⇇-id n
\end{code}
\end{tcolorbox}
\end{multicols}
\caption{Definition of the identity |Plug|}
\label{agda:plugid}
\end{agdacodefloat}

%0     |```|-- --|```|
%1     |   |-- --|   |
%2     | x | ... |   |
%3     |___|-- --|   |
%4   --------- --| f |
%5   --------- --|   |
%6      ...      |   |
%7   --------- --|___|
%  0     2    4    6

\begin{figure}[h]
  \centering
  \begin{tikzpicture}[scale=0.5, auto]
    \draw (0,-4) node (inputp0) {};
    \draw (0,-5) node (inputp1) {};
    \draw (0,-7) node (inputp3) {};
    \draw (4,0) node (outputx0) {};
    \draw (4,-1) node (outputx1) {};
    \draw (4.1,-2) node (outputxdots) {$\dots$};
    \draw (4,-3) node (outputx3) {};
    \draw (4,-4) node (outputp0) {};
    \draw (4,-5) node (outputp1) {};
    \draw (4,-7) node (outputp3) {};
    \draw (2,-1.5) node[block,minimum height=2cm,minimum width=1cm] (x) {|x|};
    \draw (2,-6) node (plug) {$\dots$};
    \draw [connector] (x.east «- outputx0) -- (outputx0);
    \draw [connector] (x.east «- outputx1) -- (outputx1);
    \draw [connector] (x.east «- outputx3) -- (outputx3);
    \draw [connector] (inputp0) -- (outputp0);
    \draw [connector] (inputp1) -- (outputp1);
    \draw [connector] (inputp3) -- (outputp3);
    \draw (4.2,0) node (inputf0) {};
    \draw (4.2,-1) node (inputf1) {};
    \draw (4.2,-3) node (inputf3) {};
    \draw (4.2,-4) node (inputf4) {};
    \draw (4.2,-5) node (inputf5) {};
    \draw (4.2,-7) node (inputf7) {};
    \draw (6.2,-3.5) node[block,minimum height=4cm,minimum width=1cm] (f) {|f|};
    \draw [connector] (inputf0) -- (f.west «- inputf0);
    \draw [connector] (inputf1) -- (f.west «- inputf1);
    \draw [connector] (inputf3) -- (f.west «- inputf3);
    \draw [connector] (inputf4) -- (f.west «- inputf4);
    \draw [connector] (inputf5) -- (f.west «- inputf5);
    \draw [connector] (inputf7) -- (f.west «- inputf7);
    \draw (8.2,-2) node (outputf0) {};
    \draw (8.2,-3) node (outputf1) {};
    \draw (8.2,-4) node (outputfdots) {$\dots$};
    \draw (8.2,-5) node (outputf3) {};
    \draw [connector] (f.east «- outputf0) -- (outputf0);
    \draw [connector] (f.east «- outputf1) -- (outputf1);
    \draw [connector] (f.east «- outputf3) -- (outputf3);
  \end{tikzpicture}
  \caption{Partial function application of gates}
  \label{fig:partial-application}
\end{figure}

Both translations for the sum-type constructors \emph{in-left} |inl₁| and \emph{in-right} |inr₁| are similar to each other in nature. They closely follow the logic described in section \ref{sec:atomization}, where we encode a single bit to indicate the choice that the sum type represents. After this indicator bit, we encode the actual chosen circuit by recursively calling |translate| on the body of the sum-type constructor. We potentially need to pad the result of that translation with some dummy output wires in order to reach the required number of output wires as dictated by the maximum between the two possible sizes of the sum-type operands.

\subsubsection{Let constructor}\label{sec:stage1-let-constructor}

The |letₓ_inₑ_| constructor introduces a new variable binding. Looking back at the definition of this constructor, we can immediately see that the \emph{let}-body is an expression that has an added element in its context:

\begin{center}
\begin{code}
(x : Λ₁ Γ [] α) → (e : Λ₁ (α ∷ Γ) Δ τ) → Λ₁ Γ Δ τ
\end{code}
\end{center}

However, our |translate| function only transforms from |Λ₁| to |IL| with identical contexts. Similarly, our circuit composition functions, |_⟫_| and |_∥_|, also only operate on |IL| circuits with identical contexts. This poses the question; how can we fit together the two inherently different |Λ₁| expressions |x| and |e|?

The answer is that we need to \emph{reduce} the context. By ``reducing the context'', we mean that we remove the added element from the context, and instead add it as an element of the inputs. More on this in section \ref{sec:reducing-context}.

Finally, now that we've transformed the circuit from a circuit with a variable in its context to one with an input to feed the variable's value, we can just feed our translations of the variable's value |x| into this reduced circuit the same way that we fed an input to our (partial) function application constructor |_$₁_|. The |reduce-ctxt| function will be called every time that we go under a variable binding, in order to map all occurrences of variable bindings to their appropriate inputs.

\subsubsection{Case constructors}\label{sec:stage1-case-constructors}

The translations for our two case switch constructors that let us operate on product types and sum types respectively are very close in nature to the let constructor. The product case constructor |case⊗_of_| is already mostly a glorified let constructor for all intents and purposes. Just like the evaluation for a let expression just adds the chosen value |x| to the evaluation environment list before evaluating the main body |e|, the evaluation for a product case expression just adds both components of |xy| to the evaluation environment list separately before evaluating the main body |f|. During the translation of the product case constructor, we need to reduce the context twice to remove both components of |xy| from the context. We use a separate function |reduce-ctxt-twice| for this rather than just calling the |reduce-ctxt| function twice. More about this choice in section \ref{sec:reducing-context}.

Lastly, the sum case switch constructor actually presents the control flow with a branching path. The logic for this is outlined in section \ref{sec:branching-circuits}.

\subsubsection{Vector coercion}\label{sec:vec-coercion}

%\todo{Example of |xs ++ [] : Vec A (n + 0)| and |xs : Vec A n| not being equal in Agda.}

Agda's dependent type system lets users reduce terms based on their structural equality. In the case of integer arithmetics, this means that Agda's type system will not evaluate the value of a given arithmetic expression to any sort of normal form. In fact, since arithmetic expressions can contain arbitrary bindings, a consistent normal form cannot necessarily be guaranteed by static analysis. Instead, the arithmetic expressions are compared syntactically. If a user wants to reduce two terms that are arithmetically equal but not syntactically equal, such as for example $(a + b)$ and $(b + a)$, the user can provide some |rewrite| clauses. By providing the type system with an equality lemma which states that |∀ {a b} → a + b ≡ b + a|, Agda can replace instances of $(a + b)$ with $(b + a)$, thereby achieving structural equality and the ability to reduce the term to |refl|, the Agda constructor for reflective equality.

However, function definitions that make extended use of |rewrite| are hard to examine. When writing proofs about such functions, the author of the proof will need to pay special attention to take the rewrites into consideration. This often leads to cryptic errors by the type-system when the author makes small mistakes. We would often run into such problems when writing the correctness proof as discussed in section \ref{sec:correctness}, especially when dealing with vectors that represent inputs and outputs of circuitry.

Instead of using rewrites of integer arithmetic for vector length encoding in our translation implementation, we've opted to introduce the concept of \emph{coercion}. A simple but powerful definition lets us coerce a circuit's input or output vectors from any integer arithmetic structure to any other equal structure. Since the caller needs to provide the equality relationship as an argument, we can use this argument when inspecting the function during our proofs later on. This has proven to be far easier to handle when compared to |rewrite| statements.

\begin{agdacodefloat}\small
\begin{tcolorbox}
\begin{code}
coerceᵢ : ∀ {G Γ i i' o} → i ≡ i' → IL[ G ] Γ i o → IL[ G ] Γ i' o
coerceᵢ refl e = e
\end{code}
\begin{code}
coerceₒ : ∀ {G Γ i o o'} → o ≡ o' → IL[ G ] Γ i o → IL[ G ] Γ i o'
coerceₒ refl e = e
\end{code}
\end{tcolorbox}
\caption{Definition of |coerce| for intermediate language}
\end{agdacodefloat}

Note the simplicity of the definition. Since there is only one possible constructor |refl| for the argument |i ≡ i'|, we start our function definition on that case switch. Once |refl| has been filled in, Agda is able to structurally reduce |IL[ G ] Γ i' o| to |IL[ G ] Γ i o|, allowing us to just pass the input as the result. This is as expected, since we are not changing the definition of the circuit. However, at the call-site of this coercion function, the caller can choose to transform the circuit's input (or output) to any equivalent arithmetic structure.

\subsubsection{Combinator circuits}\label{sec:combinator-circuits}

In section \ref{sec:background-nameless}, we showed a computational system SKI that consists of three combinators $S$, $K$, and $I$, which can be combined to form more complex terms. Each of the combinators serves a different purpose. In this section, we show how to recreate the semantics of these combinators in our intermediate language circuitry.

\vspace*{1em}
\header{Sequential and parallel combinators}
\vspace*{-2em}
\begin{center}
$$
S x y z = x z (y z)
$$
\end{center}

The $S$ combinator is often called a \emph{substitution} operator. It takes the output of $(y z)$ and uses it as the second argument passed to $x$ in the expression $(x z (y z))$. Another way to see this combinator is as a way to sequentially pass the same value into the argument list of two different functions. We've created our own version of such a combinator in our intermediate language as |S[_]·_·_| and called it the \emph{sequential} combinator.

\pagebreak

\begin{agdacodefloat}[H]\small
\begin{tcolorbox}
\begin{code}
S-bypass : ∀ {G Γ} k i → IL[ G ] Γ (k + i) (k + (k + i))
S-bypass k i = coerceₒ (+-assoc k k i) $ PlugDup k ∥ PlugId i
\end{code}
\begin{code}
S[_]·_·_  : ∀ {G Γ i j o} k
            → IL[ G ] Γ (k + i) j
            → IL[ G ] Γ (k + j) o
            → IL[ G ] Γ (k + i) o

S[_]·_·_ {i = i} k x y = S-bypass k i ⟫ PlugId k ∥ x ⟫ y
\end{code}
\end{tcolorbox}
\caption{|S[_]·_·_| combinator circuitry}
\label{agda:s-combinator}
\end{agdacodefloat}

%        ,-- k ----------- k --|`````|
%    k --+-- k --|`````|       |  y  |-- o
%                |  x  |-- j --|_____|
%    i ----- i --|_____|

\begin{figure}[h]
  \centering
  \begin{tikzpicture}[scale=1, auto]
    \draw (0,-1) node (inputk) {$k$};
    \draw (0,-3) node (inputi) {$i$};
    \draw (1,-1) node[branch] (branch) {};
    \draw (2,0) node (splitk0) {$k$};
    \draw (2,-1) node (splitk1) {$k$};
    \draw (2,-3) node (spliti) {$i$};
    \draw (4,-2) node[block,minimum height=5em,minimum width=5em] (x) {|x|};
    \draw (6,0) node (midk) {$k$};
    \draw (6,-2) node (midj) {$j$};
    \draw (8,-1) node[block,minimum height=5em,minimum width=5em] (y) {|y|};
    \draw (10,-1) node (outputo) {$o$};
    \draw [line] (inputk) -- (branch);
    \draw [line] (branch.north) «- (splitk0);
    \draw [line] (branch) -- (splitk1);
    \draw [line] (inputi) -- (spliti);
    \draw [line] (splitk0) -- (midk);
    \draw [connector] (splitk1) -- (x.155);
    \draw [connector] (spliti) -- (x.205);
    \draw [line] (x) -- (midj);
    \draw [connector] (midk) -- (y.155);
    \draw [connector] (midj) -- (y.205);
    \draw [connector] (y) -- (outputo);
  \end{tikzpicture}
  \caption{|S[_]·_·_| combinator circuitry}
  \label{fig:s-combinator}
\end{figure}

Since circuits work with wires, we need to provide the combinator with a number of wires |k| to indicate how many wires of input we want to duplicate. The wires get duplicated using a \emph{bypass} construction, so that we can attach them as the first input of each argument circuit |x| and |y|.

At this point, we also introduce a new combinator circuit to supplement the sequential one, namely a \emph{parallel} combinator |P[_]·_·_|. This combinator circuit provides an easy way to copy |k| input wires and partially apply them to both argument circuits |x| and |y| by attaching them as their first inputs.

\begin{agdacodefloat}[H]\small
\small
\begin{tcolorbox}
\begin{code}
P-insert : ∀ {G Γ} k i₁ i₂ → IL[ G ] Γ (k + (i₁ + i₂)) ((k + i₁) + (k + i₂))
P-insert k i₁ i₂ =
  coerceᵢₒ (+-assoc k i₁ i₂) (+-assoc (k + i₁) k i₂) $ PlugCopyK i₁ k ∥ PlugId i₂
\end{code}
\begin{code}
P[_]·_·_  : ∀ {G Γ i₁ o₁ i₂ o₂} k
            → IL[ G ] Γ (k + i₁) o₁
            → IL[ G ] Γ (k + i₂) o₂
            → IL[ G ] Γ (k + (i₁ + i₂)) (o₁ + o₂)

P[_]·_·_ {i₁ = i₁} {i₂ = i₂} k x y = P-insert k i₁ i₂ ⟫ x ∥ y
\end{code}
\end{tcolorbox}
\caption{|P[_]·_·_| combinator circuitry}
\label{agda:p-combinator}
\end{agdacodefloat}

%    k ---+-- k --|`````|
%         |       |  x  |-- o₁
%    i₁ - | - i₁ -|_____|
%         |
%         `-- k --|`````|
%                 |  y  |-- o₂
%    i₂ ----- i₂ -|_____|

\begin{figure}[h]
  \centering
  \begin{tikzpicture}[scale=1, auto]
    \draw (0,0) node (inputk) {$k$};
    \draw (0,-2) node (inputi1) {$i_1$};
    \draw (0,-6) node (inputi2) {$i_2$};
    \draw (1,0) node[branch] (branch) {};
    \draw (1,-2) node (gap) {};
    \draw (2,0) node (midk1) {$k$};
    \draw (2,-2) node (midi1) {$i_1$};
    \draw (2,-4) node (midk2) {$k$};
    \draw (2,-6) node (midi2) {$i_2$};
    \draw (4,-1) node[block,minimum height=5em,minimum width=5em] (x) {|x|};
    \draw (4,-5) node[block,minimum height=5em,minimum width=5em] (y) {|y|};
    \draw (6,-1) node (outputo1) {$o_1$};
    \draw (6,-5) node (outputo2) {$o_2$};
    \draw [line] (inputk) -- (branch);
    \draw [line] (branch) -- (midk1);
    \draw [line] (branch) -- (gap);
    \draw [line] (gap) «- (midk2);
    \draw [line] (inputi1) -- (midi1);
    \draw [line] (inputi2) -- (midi2);
    \draw [connector] (midk1) -- (x.155);
    \draw [connector] (midi1) -- (x.205);
    \draw [connector] (midk2) -- (y.155);
    \draw [connector] (midi2) -- (y.205);
    \draw [connector] (x) -- (outputo1);
    \draw [connector] (y) -- (outputo2);
  \end{tikzpicture}
  \caption{|P[_]·_·_| combinator circuitry}
  \label{fig:p-combinator}
\end{figure}

\vspace*{1em}
\header{Kill combinator}
\vspace*{-2em}
\begin{center}
$$
K x y = x
$$
\end{center}

The $K$ combinator is usually referred to as the \emph{constant} function. When we demonstrated our SKI transpiler in section \ref{sec:prototype-translation}, we used the $K$ combinator inside the function |lambda| to reduce the context of terms whenever we wanted to introduce a new dummy parameter, whose only purpose was to satisfy the requirement for an additional (unused) input parameter. We are achieving a similar feat with our combinator |K[_]·_| for circuits. It takes in a circuit |x| and adds |k| dummy input wires which are are not connected to anything. For this reason, in the context of circuitry, we've dubbed this the \emph{kill} combinator.

\begin{agdacodefloat}[H]\small
\begin{tcolorbox}
\begin{code}
K[_]·_ : ∀ {G Γ i o} k → IL[ G ] Γ i o → IL[ G ] Γ (k + i) o
K[ k ]· x = PlugNil k ∥ x
\end{code}
\end{tcolorbox}
\caption{|K[_]·_| combinator circuitry}
\label{agda:k-combinator}
\end{agdacodefloat}

%    k -----!
%        |`````|
%    i --|  x  |-- o
%        |_____|

\begin{figure}[h]
  \centering
  \begin{tikzpicture}[scale=1, auto]
    \draw (0,-0.5) node (inputk) {$k$};
    \draw (0,-2) node (inputi) {$i$};
    \draw (2,-0.5) node[branch] (dead) {};
    \draw (2,-2) node[block,minimum height=5em,minimum width=5em] (x) {|x|};
    \draw (4,-2) node (outputo) {$o$};
    \draw [connector] (inputk) -- (dead);
    \draw [connector] (inputi) -- (x);
    \draw [connector] (x) -- (outputo);
  \end{tikzpicture}
  \caption{|K[_]·_| combinator circuitry}
  \label{fig:k-combinator}
\end{figure}

\vspace*{1em}
\header{Identity combinator}
\vspace*{-2em}
\begin{center}
$$
I x = x
$$
\end{center}

The $I$ combinator represents \emph{identity}. We don't need to write any custom circuitry for this combinator, since we can just use an identity such as |PlugId'| (See Agda listing \ref{agda:plugid}) that maps each output to the corresponding input.

\subsubsection{Reducing context}\label{sec:reducing-context}

The goal of context reduction is to move a binding from the head of the context list to the head of the list of inputs. One way to visualise this change is to think of it as adding a new input to the circuit, and attaching the wires of this input to every place inside the circuit where the variable binding was used. This lets us \emph{share} a value for the binding – for example, in the form of the output of another circuit – among all the different places where that value is needed. This is similar to the bracket abstraction used in our SKI transpiler as shown in section \ref{sec:prototype-translation}. We present the context reduction logic for our intermediate language in Agda listing \ref{agda:reduce-ctxt}.

\begin{agdacodefloat}\small
\begin{tcolorbox}
\begin{code}
reduce-ctxt : ∀ {G τ Γ i o} → IL[ G ] (τ ∷ Γ) i o → IL[ G ] Γ (sz τ + i) o

reduce-ctxt {_} {τ} G⟨ g# ⟩        =  K[ sz τ ]· G⟨ g# ⟩

reduce-ctxt {_} {τ} Grnd           =  K[ sz τ ]· Grnd

reduce-ctxt {_} {τ} (Plug x)       =  K[ sz τ ]· Plug x

reduce-ctxt {_} {τ} (x ⟫ y)        =  S[ sz τ ]· reduce-ctxt x · reduce-ctxt y

reduce-ctxt {_} {τ} (x ∥ y)        =  P[ sz τ ]· reduce-ctxt x · reduce-ctxt y

reduce-ctxt {_} {τ} (Var top)      =  coerceᵢ (sym $ +-right-identity (sz τ)) $
                                      PlugId (sz τ)

reduce-ctxt {_} {τ} (Var (pop i))  =  K[ sz τ ]· Var i
\end{code}
\end{tcolorbox}
\caption{Definition of |reduce-ctxt|}
\label{agda:reduce-ctxt}
\end{agdacodefloat}

Our goal is to create a circuit with |(sz τ)| extra input connections, since |τ| is the type that we are removing from the context. In the case of the first three constructors, we don't actually need the value of the binding that we are removing. We can use our \emph{kill} combinator to add the required wires without attaching them to the given circuit. Our \emph{sequential} combinator lets us copy the new input wires to the start of two sequential circuits while keeping their sequential attachment structure intact. Similarly, the \emph{parallel} combinator lets us do this while keeping the parallel attachment structure intact. In both cases, we recursively call |reduce-ctxt| to make sure that the new input wires are connected where they are required in the body of these circuits.

Finally, in the case of a variable reference, we need to inspect exactly which variable reference is in our hands. Remember from our variable constructor definition that the variable references are encoded in a De Bruijn fashion. In the case when the reference we encounter is not the one that we are currently trying to reduce from the context of bindings, we can safely kill the input wires, as there is no dependency between variable references. We just need to reduce the De Bruijn reference identifier by one, since, in the new reduced context, it refers to an earlier element of the list. In the case when we are actually dealing with the reference which we are removing from the context, we use an identity |Plug| to connect the new input wires into this location of the circuit.

At the end of section \ref{sec:stage1-case-constructors}, we mentioned a special function for reducing the context twice. The reason we cannot simply call the |reduce-ctxt| twice can actually be inferred from its type signature. Given an intermediate language circuit with a context |(α ∷ β ∷ Γ)|, calling |reduce-ctxt| would result in a remaining context |(β ∷ Γ)| with the initial context variable being moved to the input |(sz α + i)|. A second call to |reduce-ctxt| will not result our desired output |(sz α + sz β + i)|, but instead an input of |(sz β + (sz α + i))|.

For this reason, we're introducing a special function |reduce-ctxt-twice| to take two elements from the context list and add them to our input in the desired order.

\subsubsection{Branching circuits}\label{sec:branching-circuits}

To translate the sum case switch constructor of |Λ₁|, we introduced a helper function -- aptly named |branching-circuit| -- that takes the two circuit bodies |f| and |g| and implements the branch in the control flow between the two, depending on the payload |xy|. As a rough outline, we implemented the circuit as a pipeline of sequentially arranged stages. The first bit of |xy| is extracted, since this is the decision-maker bit in the control flow. We feed this bit together with the rest of |xy| into a \emph{demultiplexer} to separate the values of |x| and |y| respectively. These values are then fed into the circuitry for |rdc-f| and |rdc-g|, context reduced versions of |f| and |g| respectively. Finally, the outputs of both these circuits are attached to a \emph{multiplexer}, again using the decision bit to output the correct one of the two.

%0                        ,-- 1 ----------------- 1 ------- 1 ------------- 1 --,
%1                        |                                                     `--|`````|
%2     |``````|-- 1 ------+-- 1 ------|```````|-- a ------- a --|```````|          |     |
%3     |  xy  |                       | demux |                 | rdc-f |-- o -----| mux |-- o
%4     |______|-- a ⊔ b ----- a ⊔ b --|_______|-- b --, ,-- i --|_______|          |     |
%5                                                     ×                        ,--|_____|
%6 i ------------ i --------- i ----------------- i --⟨ `-- b --|```````|       |
%7                                                     \        | rdc-g |-- o --´
%8                                                      `-- i --|_______|
%  0      2       4                       6       8         9       11      13       15      17
\begin{figure}[h]
  \centering
  \begin{code}
  (xy     : IL[ ΛBoolTrio ] Γ 0 (1 + (a ⊔₂ b))) →
  (rdc-f  : IL[ ΛBoolTrio ] Γ (a + i) o) →
  (rdc-g  : IL[ ΛBoolTrio ] Γ (b + i) o) →
  IL[ ΛBoolTrio ] Γ i o
  \end{code}
  \begin{tikzpicture}[scale=0.8, auto]
    \draw (0,-6) node (inputi) {$i$};
    \draw (2,-3) node[block,minimum height=5em,minimum width=3.5em] (xy) {|xy|};
    \draw (4,-2) node (first1) {$1$};
    \draw (4,-4) node (ab) {$a ⊔ b$};
    \draw (6,-3) node[block,minimum height=5em,minimum width=3.5em] (demux) {|demux|};
    \draw (8,-2) node (a) {$a$};
    \draw (8,-4) node (b) {$b$};
    \draw (8,-6) node (firsti) {$i$};
    \draw (8.5,-5) node (cross) {};
    \draw (9,-4) node (topi) {$i$};
    \draw (9,-6) node (secondb) {$b$};
    \draw (9,-8) node (bottomi) {$i$};
    \draw (11,-3) node[block,minimum height=5em,minimum width=3.5em] (rdcf) {|rdc-f|};
    \draw (11,-7) node[block,minimum height=5em,minimum width=3.5em] (rdcg) {|rdc-g|};
    \draw (13,0) node (last1) {$1$};
    \draw (13,-3) node (topo) {$o$};
    \draw (13,-7) node (bottomo) {$o$};
    \draw (15,-3) node[block,minimum height=7.5em,minimum width=3.5em] (mux) {|mux|};
    \draw (17,-3) node (outputo) {$o$};
    \draw [line] (inputi) -- (firsti);
    \draw [connector] (xy.east «- first1) -- (first1);
    \draw [connector] (xy.east «- ab) -- (ab);
    \draw [line] (first1) «- (last1);
    \draw [connector] (first1) -- (demux.west «- first1);
    \draw [connector] (ab) -- (demux.west «- ab);
    \draw [connector] (demux.east «- a) -- (a);
    \draw [connector] (demux.east «- b) -- (b);
    \draw [connector] (a) -- (rdcf.west «- a);
    \draw [line] (b) -- (secondb);
    \draw [line] (firsti) -- (cross);
    \draw [line] (cross) -- (topi);
    \draw [line] (firsti) -- (bottomi);
    \draw [connector] (topi) -- (rdcf.west «- topi);
    \draw [connector] (secondb) -- (rdcg.west «- secondb);
    \draw [connector] (bottomi) -- (rdcg.west «- bottomi);
    \draw [connector] (rdcf.east «- topo) -- (topo);
    \draw [connector] (rdcg.east «- bottomo) -- (bottomo);
    \draw [connector] (last1.south) «- (mux.125);
    \draw [connector] (topo) -- (mux.west «- topo);
    \draw [connector] (bottomo.north) «- (mux.235);
    \draw [connector] (mux) -- (outputo);
  \end{tikzpicture}
  \caption{Branching circuit control flow}
  \label{fig:branching-circuit}
\end{figure}

Looking at the circuit diagram in figure \ref{fig:branching-circuit}, we can see two new components that are not part of the argument circuitry, namely |demux| and |mux|. These represent a demultiplexer and a multiplexer, respectively.

The demultiplexer takes two inputs: one selector wire of a single bit, and one actual input of the maximum size between $a$ and $b$, also referred to as size $(a ⊔ b)$. The selector wire will determine whether the first $a$ wires of the actual input will get output to the first $a$ output wires, or whether the the first $b$ wires of the actual input will get output to the last $b$ output wires.

The multiplexer takes three inputs: One selector wire of a single bit and two candidate inputs of identical size. The selector wire determines which of the two candidates gets passed to the output.

We refer to the code accompanying this document to see how we implemented the demultiplexer and multiplexer circuit fully in our intermediate language. The inner workings of multiplexers and demultiplexers are not controversial in terms of correctness and as such are not as interesting to the research goal at hand. We do note that the implementation depends on the use of |AND|, |OR|, and |NOT| gates, which is why the signature of |branching-circuit| shown below the circuit diagram is hard-coded to use the |ΛBoolTrio| gates.

\subsection{Stage 2}\label{sec:stage2}

In the second stage of our translation, we need to translate from our intermediate language |IL| to actual \Piware circuitry |ℂ|. We present the definition of out second stage's |translate| function in Agda listing \ref{agda:stage2-translate-def}. We only need to do this for |IL| circuits with empty contexts, since the total translation pipeline only accepts |Λ₁| programs without open bindings. The only reason the first stage's translation function accepts arbitrary inputs with potential context is to let us use that function recursively on the bodies of constructors that introduce bindings.

\begin{agdacodefloat}\small
\begin{tcolorbox}
\begin{code}
grnd-circuit : ∀ {o} → ℂ[ ΛBoolTrio ] 0 o

grnd-circuit {zero}   = Plug (⇇-nil zero)
grnd-circuit {suc o}  = Gate FALSE ∥ grnd-circuit
\end{code}
\begin{code}
translate : ∀ {i o} → IL[ ΛBoolTrio ] [] i o → ℂ[ ΛBoolTrio ] i o

translate G⟨ g# ⟩   = Gate g#
translate Grnd      = grnd-circuit
translate (Plug x)  = Plug x
translate (x ⟫ y)   = translate x ⟫ translate y
translate (x ∥ y)   = translate x ∥ translate y
translate (Var ())
\end{code}
\end{tcolorbox}
\caption{Definition of |Stage2.translate|}
\label{agda:stage2-translate-def}
\end{agdacodefloat}

In the case of the |Grnd| constructor, we check how many null outputs were actually requested. If none, we substitute a null plug with zero inputs and zero output. In other words: no circuitry at all. If some dummy outputs were required, we just hook them up to some |FALSE| outputs which can represent the value $0$ and be grounded. We only needed this constructor inside the implementation of our multiplexer, and it was only there to aid the readability of the multiplexer's implementation.

\pagebreak

\subsection{Final translation}

In this chapter, we've shown how we can translate from \lambdaone to our intermediate language and how we can translate from our intermediate language to \Piware. All that remains is to combine these translation steps into a final translation definition, as seen in Agda listing \ref{agda:final-translate-def}.

\begin{agdacodefloat}\small
\begin{tcolorbox}
\begin{code}
open import ... .Stage1.LambdaOne2IL using ()
  renaming (translate to Λ₁⟶IL)

open import ... .Stage2.IL2PiWare using ()
  renaming (translate to IL⟶ΠW)
\end{code}
\begin{code}
translate : ∀ {Δ τ} → (e : Λ₁ [] Δ τ) → ℂ[ ΛBoolTrio ] (sz-list Δ) (sz τ)

translate = IL⟶ΠW ∘ Λ₁⟶IL
\end{code}
\end{tcolorbox}
\caption{Definition of |translate|, which translates from \lambdaone to \Piware}
\label{agda:final-translate-def}
\end{agdacodefloat}

% Hack to work around weird bug where ending on a agdacodefloat ignores the new section's newpage
\begin{code}

\end{code}
