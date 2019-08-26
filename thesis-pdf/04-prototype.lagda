%include thesis.fmt

\newpage
\section{SKI transpiler}\label{sec:prototype}

In this chapter, we investigate the feasibility of translating a language with typed variables to a language without such constructs, as well as proving correctness of said translation. It goes without saying that we use Agda as the platform for this work.

\subsection{Simply-typed $λ$-calculus}\label{sec:simply-typed-lambda-calc}


The simply-typed $\lambda$-calculus is an extension of the $\lambda$-calculus which we already saw in \ref{sec:background-debruijn} and \ref{sec:background-hoasphoas}. Its type system is simple, because it only consists of the unit type $(\iota)$ and the function constructor $(\rightarrow)$. Simply-typed $\lambda$-calculus is a very interesting language to study the effects of type systems. However, this is not the focus of this chapter. Instead, we intend to translate the simply-typed $\lambda$-calculus into a nameless representation, in order to show that it is possible to go from a language which has variable bindings in the form of De Bruijn indices to a nameless language.

\begin{agdacodefloat}[H]\small
\begin{multicols}{2}
\begin{tcolorbox}
\begin{code}
data U : Set where
  unit  : U
  _⇒_   : U → U → U
\end{code}
\end{tcolorbox}
\begin{tcolorbox}
\begin{code}
⟦_⟧ : U → Set
⟦ unit   ⟧  = ⊤
⟦ σ ⇒ τ  ⟧  = ⟦ σ ⟧ → ⟦ τ ⟧
\end{code}
\end{tcolorbox}
\end{multicols}
\caption{Simple type system}
\label{agda:prototype-type-system}
\end{agdacodefloat}

We model the simple type system in Agda listing \ref{agda:prototype-type-system}. The type universe is represented with |U|. The translation which relates the type universe to the Agda type system is defined with |⟦_⟧|.

\begin{agdacodefloat}[H]\small
\begin{tcolorbox}
\begin{code}
Ctx = List U
\end{code}
\end{tcolorbox}
\caption{Type context}
\label{agda:prototype-context}
\end{agdacodefloat}

The term \emph{context} is often used to mean very different things in different situations. In the frame of reference of this work, we use \emph{context} to refer to a list of types (See Agda listing \ref{agda:prototype-context}), which are used to capture the free variables in a given expression.

\begin{agdacodefloat}[H]\small
\begin{tcolorbox}
\begin{code}
data Ref : Ctx → U → Set where
  top  : ∀ {Γ τ}    → Ref (τ ∷ Γ) τ
  pop  : ∀ {Γ σ τ}  → Ref Γ τ → Ref (σ ∷ Γ) τ
\end{code}
\begin{code}
data Term : Ctx → U → Set where
  app  : ∀ {Γ σ τ}  → Term Γ (σ ⇒ τ) → Term Γ σ → Term Γ τ
  lam  : ∀ {Γ σ τ}  → Term (σ ∷ Γ) τ → Term Γ (σ ⇒ τ)
  var  : ∀ {Γ τ}    → Ref Γ τ → Term Γ τ
\end{code}
\end{tcolorbox}
\caption{Simply typed lambda calculus language definition in Agda}
\label{agda:prototype-stlc}
\end{agdacodefloat}

The simply-typed $\lambda$-calculus is encoded in the |Term| data type (See Agda listing \ref{agda:prototype-stlc}). Terms are indexed with a context |Ctx| which defines the types of free variables that appear in the term. Furthermore, terms are also indexed with a type |U|. Agda's type checker will only let us create valid terms that are type-safe. This is due to the \emph{intrinsically typed} \cite{reynolds2000meaning} nature of the object language |Term| in the host language Agda.

Pay special attention to the |var| constructor, which takes a |Ref| as a parameter. |Ref| encodes a specialized version of Peano numbers, where |top| represents \emph{zero} and |pop| represents the \emph{successor} operation. The specialization lies in the fact that |Ref| is indexed with a context and a type. Each call of |lam| pushes a new type onto the context stack of its argument term. This allows |var| calls to refer to that binding by encoding the depth of |lam| calls in its stack of |pop| and |top| calls.

The intrinsic design of our embedded simply-typed $\lambda$-calculus language also lets us define a meaningful evaluation function, which, given an expression in the object language together with a list of values for free occurring variables, will run the described program by mapping each term to the host language's semantics (See Agda listing \ref{agda:prototype-stlc-eval}).

\begin{agdacodefloat}[H]\small
\begin{tcolorbox}
\begin{code}
data Env : Ctx → Set where
  nil   : Env []
  cons  : ∀ {Γ τ} → ⟦ τ ⟧ → Env Γ → Env (τ ∷ Γ)
\end{code}
\begin{code}
eval : ∀ {Γ τ} → Term Γ τ → Env Γ → ⟦ τ ⟧
eval (app t₁ t₂)  env  = eval t₁ env (eval t₂ env)
eval (lam t)      env  = λ x → eval t (cons x env)
eval (var ref)    env  = env ! ref
\end{code}
\end{tcolorbox}
\caption{Simply typed lambda calculus evaluation semantics}
\label{agda:prototype-stlc-eval}
\end{agdacodefloat}

\pagebreak

\subsection{SKI combinators}\label{sec:ski-combinators}

We touched upon SKI combinator calculus in section \ref{sec:background-nameless}. To reiterate, they represent a Turing-complete language without any variable bindings.

\begin{agdacodefloat}[H]\small
\begin{tcolorbox}
\begin{code}
data SKI : U → Set where
  S    : ∀ {a b c}  → SKI ((a ⇒ b ⇒ c) ⇒ (a ⇒ b) ⇒ a ⇒ c)
  K    : ∀ {a b}    → SKI (a ⇒ b ⇒ a)
  I    : ∀ {a}      → SKI (a ⇒ a)
  _·_  : ∀ {α β}    → SKI (α ⇒ β) → SKI α → SKI β
\end{code}
\begin{code}
apply : ∀ {τ} → SKI τ → ⟦ τ ⟧
apply S x y z    = x z (y z)
apply K x y      = x
apply I x        = x
apply (c₁ · c₂)  = apply c₁ (apply c₂)
\end{code}
\end{tcolorbox}
\caption{SKI combinators in Agda}
\label{agda:prototype-ski-def}
\end{agdacodefloat}

We've directly encoded |S|, |K|, and |I| as Agda constructors in Agda listing \ref{agda:prototype-ski-def} by using implicit type variables and recreating the expected shape for these combinators as their index of the type |SKI|. Similar to our definition of |Term|, this leads to an intrinsic embedding in Agda using the type universe |U|. We can combine these combinators using |_·_|. We've also included an unembedding function here called |apply|, which is the SKI equivalent of |eval| on the simply-typed $\lambda$-calculus side. The name |apply| was chosen to avoid confusion between these semantic evaluation methods.

\pagebreak

\subsection{Translation}\label{sec:prototype-translation}

Translating arbitrary |Term| expressions directly to |SKI| is not always possible. Terms that appear inside the body of a |lam| are \emph{open}, i.e. they contain references inside them which are bound outside of the term. It will only be possible to translate \emph{closed} terms to a SKI representation. To work around this restriction, we introduce an intermediate translation of possibly open terms to an intermediate representation |SKI'|, which supports bindings in Agda listing \ref{agda:ski-intermediate}.

\begin{agdacodefloat}[H]\small
\begin{tcolorbox}
\begin{code}
data SKI' : Ctx → U → Set where
  S    : ∀ {Γ a b c}  → SKI' Γ ((a ⇒ b ⇒ c) ⇒ (a ⇒ b) ⇒ a ⇒ c)
  K    : ∀ {Γ a b}    → SKI' Γ (a ⇒ b ⇒ a)
  I    : ∀ {Γ a}      → SKI' Γ (a ⇒ a)
  _·_  : ∀ {Γ α β}    → SKI' Γ (α ⇒ β) → SKI' Γ α → SKI' Γ β
  ⟨_⟩  : ∀ {Γ τ}      → Ref Γ τ → SKI' Γ τ
\end{code}
\begin{code}
cmp' : ∀ {Γ τ} → Term Γ τ → SKI' Γ τ
cmp' (app t₁ t₂)  = cmp' t₁ · cmp' t₂
cmp' (lam t)      = lambda (cmp' t)
cmp' (var x)      = ⟨ x ⟩
\end{code}
\begin{code}
lambda : ∀ {Γ σ τ} → SKI' (σ ∷ Γ) τ → SKI' Γ (σ ⇒ τ)
lambda S          = K · S
lambda K          = K · K
lambda I          = K · I
lambda (c₁ · c₂)  = S · lambda c₁ · lambda c₂
lambda ⟨ top ⟩    = I
lambda ⟨ pop x ⟩  = K · ⟨ x ⟩
\end{code}
\end{tcolorbox}
\caption{Translation of a simply-typed $\lambda$-calculus |Term| to an intermediate representation |SKI'|}
\label{agda:ski-intermediate}
\end{agdacodefloat}

The intermediate representation carries a context to capture the freely occuring variable bindings. Translating from |Term| to |SKI'| is trivial in the case of |app| and |var|, where we recursively compile each part of the application and store the variable reference, respectively.

The difficulty lies in translating the |lam| constructor. We introduce a helper function |lambda| to remove a variable binding from the |SKI'| expression and transform it into a new |SKI'| expression of an embedded function type. In essence, we are building a new expression in the form of a function which takes the previous variable binding as an input, thereby eliminating the binding.

This new function input will replace the value of the first reference within the context (of the type |σ| in the type signature above). Our function |lambda| has to define how to pass or discard this input value for each possible |SKI'| expression. In the case of simple occurrences of either |S|, |K|, or |I|, we can discard the input value. This is achieved by applying the combinator |K|, which does exactly that: it discards an argument. In the case of an application |_·_|, we need to recursively call |lambda| on each part of the application and also duplicate the input value for use in both parts. This is achieved by applying the combinator |S|, which applies an input to two expressions. Finally, in the case of a variable binding |⟨_⟩|, we need to inspect the De Bruijn index of that variable. If it is indeed the variable that is being replaced by our function input, we inject the input using the identity combinator |I|. For other variable bindings, we just reduce the De Bruijn index by one to make sure the reference points to the correct location in the context, which will also have been reduced by one element.

Since a closed |SKI'| expression, i.e. one with an empty context, contains no variable bindings, it can be converted to a |SKI| expression trivially. The |cmp'| function maintains the context of the input |Term|, so closed terms are translated to closed |SKI'| expressions which in turn can be translated to |SKI| expressions. This completes our translation of simply-typed $\lambda$-calculus to SKI:

\begin{agdacodefloat}[H]\small
\begin{tcolorbox}
\begin{code}
closed : ∀ {τ} → SKI' [] τ → SKI τ
closed S = S
closed K = K
closed I = I
closed (c₁ · c₂) = closed c₁ · closed c₂
closed ⟨ () ⟩
\end{code}
\begin{code}
cmp : ∀ {τ} → Term [] τ → SKI τ
cmp = closed ∘ cmp'
\end{code}
\end{tcolorbox}
\caption{Final translation of simply-typed $\lambda$-calculus to |SKI|}
\label{agda:ski-cmp}
\end{agdacodefloat}

\pagebreak

\subsection{Correctness}\label{sec:prototype-correctness}

The compiler correctness property is expressed as follows in Agda:

\begin{agdacodefloat}[H]\small
\begin{tcolorbox}
\begin{code}
correct : ∀ {τ} → (t : Term [] τ) → apply (cmp t) ≡ eval t nil
\end{code}
\end{tcolorbox}
\caption{SKI transpiler correctness proposition}
\label{agda:prototype-correct}
\end{agdacodefloat}

It states that, given a closed |Term| (i.e. no free variables, i.e. an empty context) of any type |(τ : U)|, compiling the term and evaluating the resulting SKI combinators using |apply| is equivalent to evaluating the term directly.

The complete version of the correctness proof code is not included inside this document for conciseness' sake. We refer to the code accompanying this document. However, we can give a high-level description of what is going on. The type signature of |correct| states that given any closed term |t| of any embedded type |τ|, compiling the term to a SKI representation and applying it should give the same result as evaluating the term directly.

Agda can only check structural equality, so this requirement is stricter than just semantic equality. The strategy to prove this is to prove a similar correctness proof between term evaluation and the intermediate |SKI'| interpretation, which can include De Bruijn variables. Some notable lemmas that were required for this proof were: one to prove the correctness of the |lambda| function above, and one to prove that the environment is treated equally in the evaluation of terms and the application of the intermediate |SKI'| expressions.

\todo{More explanation about the correctness proof? Maybe a short section about functional extensionality?}
