%include thesis.fmt

\newpage
\section{Correctness}\label{sec:correctness}

In this chapter, we take a closer look at how we proved the correctness of our translation from \lambdaone to \Piware. To reiterate, our correctness requirement is that, for any closed expression |e| written in \lambdaone, we expect the same end result regardless of whether we translate |e| to \Piware and run the circuit, or unembed |e| and translate that result into \Piware atoms. Note the call to |atomize| in the correctness proposition's signature below. In order to be able to compare the \Piware circuit that resulted from translating |e| to the circuit |e| itself, we need to bring both into the same input/output space. Since \Piware works on words and \lambdaone works on polytypes, we have the choice to bring either one into the space of the other. We already showed how |atomize| brings a function in the input/output space |ΛSet| of \lambdaone into the input/output space |W→W| of \Piware in section \ref{sec:atomization}.

This chapter starts by introducing some concepts used for the correctness proof, after which we highlight some parts of the actual proof. We won't spell out the details of the entire proof in this document. The mathematics as described in code explain the proof more precisely and concisely than what we could achieve in written description in the English language. Please refer to the code accompanying this document for the full proof. The Agda type of the translation correctness proposition -- i.e. the proposition that we intend to prove in this chapter -- is as stated in Agda listing \ref{agda:translate-correctness-decl}.

\begin{agdacodefloat}\small
\begin{tcolorbox}
\begin{code}
translate-correctness : ∀ {Δ τ}
  → (e : Λ₁ [] Δ τ)
  → ⟦ translate e ⟧[ ΛBoolTrioσ ] ≡ atomize {Δ} (unembed e ε)
\end{code}
\end{tcolorbox}
\caption{Declaration of the translation correctness proposition}
\label{agda:translate-correctness-decl}
\end{agdacodefloat}

Since our translation works in two stages, we will split up the proof in two stages as well. In the code accompanying this document, there are two different modules that each define their own |translate-correctness| function. One of them is for \emph{stage one correctness}, i.e. the correctness of translating \lambdaone to the intermediate language. The other is for \emph{stage two correctness}, i.e. the correctness of translating the intermediate language to \Piware.

\pagebreak

\subsection{Equational reasoning in Agda}\label{sec:equational-reasoning}

In Agda, we can define equality as follows:

\begin{agdacodefloat}[H]\small
\begin{tcolorbox}
\begin{code}
data _≡_ {A : Set} (x : A) : A → Set where
  refl : x ≡ x
\end{code}
\end{tcolorbox}
\caption{Agda definition of equality |(_≡_)|}
\end{agdacodefloat}

Given any |x| of type |A|, |x| is equal to itself. This property is more commonly known as propositional equality. Agda has built-in ways to handle this equality property. We briefly touched upon the interactive nature of writing Agda in section \ref{sec:background-deptypagda}. A very common workflow heavily involves the use of equality.

Whenever we define a type signature for a function in Agda, for example a signature to express a certain property that we want to prove is true, we typically start off by writing the function body as a hole:

\begin{agdacodefloat}[H]\small
\begin{tcolorbox}
\begin{code}
+-zero : (a : ℕ) → (a + 0) ≡ a
+-zero a = ?
\end{code}
\end{tcolorbox}
\caption*{\textbf{Agda listing:} Declaration of |+-zero|}
\end{agdacodefloat}

We can instruct the interactive Agda editor to do a \emph{case split} on the possible cases for a chosen identifier. For example, by splitting on |a|, we end up with the following definition:

\begin{agdacodefloat}[H]\small
\begin{tcolorbox}
\begin{code}
+-zero : (a : ℕ) → (a + 0) ≡ a
+-zero zero     = ?
+-zero (suc a)  = ?
\end{code}
\end{tcolorbox}
\caption*{\textbf{Agda listing:} Case switch on |+-zero|}
\end{agdacodefloat}

The first case will be trivial to solve, as Agda will fill in the definitions of |zero| as well as |_+_| to normalize the goal to |zero ≡ zero|, which we can fulfill with the |refl| reflective equality.

For the second case, Agda will also normalize the goal, but end up stuck on the goal |suc (a + 0) ≡ suc a|. We can solve this goal by applying the concept of congruence, which states that if two values |x| and |y| are equal, for any given function |f| when applied |(f x)| and |(f y)| are also equal.

\begin{agdacodefloat}[H]\small
\begin{tcolorbox}
\begin{code}
cong : ∀ {A B : Set} (f : A → B) {x y : A} → x ≡ y → f x ≡ f y
cong f refl = refl

+-zero : (a : ℕ) → (a + 0) ≡ a
+-zero zero     = refl
+-zero (suc a)  = cong suc (+-zero a)
\end{code}
\end{tcolorbox}
\caption{Definition of |+-zero| using congruence |cong|}
\end{agdacodefloat}

In our example of proving that |(a + 0)| is equal to |a|, we were able to prove the equality directly for each case of |a|. However, often we want to prove equality of two expressions by proving that both expressions are equal to a different intermediary expression. This concept is called transitivity:

\begin{agdacodefloat}[H]\small
\begin{tcolorbox}
\begin{code}
trans : ∀ {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
trans refl refl = refl
\end{code}
\end{tcolorbox}
\caption{Definition of transitivity |trans|}
\end{agdacodefloat}

By providing two proofs, that |x| is equal to |y| and that |y| is equal to |z|, we effectively prove that |x| must be equal to |z|. This pattern of proving through intermediary steps is so common that there is an Agda module that greatly simplifies the execution of such proofs. This module is named \emph{equational reasoning}: |≡-Reasoning|.

\begin{agdacodefloat}[h]\small
\begin{tcolorbox}
\begin{code}
module ≡-Reasoning {A : Set} where

  infix   1 begin_
  infixr  2 _≡⟨_⟩_
  infix   3 _∎

  begin_ : ∀ {x y : A} → x ≡ y → x ≡ y
  begin x≡y = x≡y

  _≡⟨_⟩_ : ∀ (x : A) {y z : A} → x ≡ y → y ≡ z → x ≡ z
  x ≡⟨ x≡y ⟩ y≡z = trans x≡y y≡z

  _∎ : ∀ (x : A) → x ≡ x
  x ∎ = refl
\end{code}
\end{tcolorbox}
\caption{Module for equational reasoning |≡-Reasoning|}
\end{agdacodefloat}

This module provides a syntax that lets us write equality proofs in a very readable way. In equational reasoning, we write down the explicit values for each step as well as proofs to show equality between each value. This works by chaining together a number of |_≡⟨_⟩_| operators. The first argument of this operator is the initial value |x| that we wish to prove equality about. The middle argument is an equality proof between |x| and a second value |y|. The last argument is (surprisingly) not the target value, but rather another proof of equality between |y| and |z|. The operator returns the transitive proof that |x| is equal to |z|. A caller can use the \emph{QED} (Quod Erat Demonstrandum, that which was to be demonstrated) operator |(_∎)| to transform the final target value into a reflective equality proof. Thanks to the right associativity of the |_≡⟨_⟩_| operator, we can chain a number of steps together to create code that is very pleasant to read.

\begin{agdacodefloat}[h]\small
\begin{tcolorbox}
\begin{code}
example : ∀ {A : Set} {x y z : A} → x ≡ y → y ≡ z → x ≡ z
example {_} {x} {y} {z} x≡y y≡z = begin
    x
  ≡⟨ x≡y ⟩
    y
  ≡⟨ y≡z ⟩
    z
  ∎
\end{code}
\end{tcolorbox}
\caption{Simple example using |≡-Reasoning|}
\end{agdacodefloat}

While writing proofs in the interactive Agda environment, this approach to equational reasoning also allows developers to use holes |?| to let the Agda type checker assist in finding expressions that fulfill the type requirements.

\subsection{Functional extensionality in Agda}\label{sec:fun-ext}

So far, we've seen Agda being able to deduce equality between values based on reflective equality. We've also seen a few lemmas that expand this equality through congruence and transitivity. Agda's standard library also provides us with lemmas for -- among others -- symmetry (|x ≡ y → y ≡ x|), substitution (|x ≡ y → P x → P y|) and congruence of application (|f ≡ g → f x ≡ g x|). This last one is especially interesting, since we haven't seen equality of functions yet.

On first glance, it would seem reasonable for Agda to provide a lemma in its standard library that states that if two functions have the same result for all possible inputs, the functions must be the same: |(∀ {x} → f x ≡ g x) → f ≡ g|. However, this lemma isn't available by default.

In order to clarify this ommission, we have to look at the difference between \emph{intensional} equality and \emph{extensional} equality \cite{hottbook}. Intensional equality deals with equality through equal definition, whereas extensional equality distinguishes objects based on their observable behavior. Agda's type system is an intensional type system.

Agda's intensional type system uses $\beta$-reduction and $\eta$-reduction to normalize terms using their definitions in order to work out typing constraints. Extensional equality cannot be used for this, since extensional equality only equates things that behave the same. In the intensional type system of Agda, two functions are only equal if we can prove this using reflexivity.

Agda's standard library gives us a workaround for this problem. We can |postulate| functional extensionality, i.e. a lemma that two functions which, for each element of their domain map to identical elements of their codomain, are equal to each other. This postulate is known to be consistent. Using it will not compromise the soundness of our development.

This equivalence relation between functions explicitly states that we only care about values. Other side effects such as running time or memory usage are not of concern. This is good enough for our correctness proof, where we want to prove that the circuits provide the same output value regardless of whether we run the higher-level hardware description directly or translate it to gates and wires first, without regard for the runtime of our unembedding functions.

Functional extensionality is important for the correctness proof of our translation. The function signature for |translate-correctness| expresses an equality between two functions, namely between two |W→W| functions. The left hand side is the result of the translation of the \lambdaone expression and the right hand side is the atomized version of the \lambdaone expression. In order to prove the correctness of the translation, we want to prove that the evaluation of both these variants results in the same output for every possible input word. Given functional extensionality postulated under |fun-ext|, we can rephrase our correctness proposition for the first stage in the two-step translation pipeline as in Agda listing \ref{agda:stage1-translate-correctness-ext-decl}

\begin{agdacodefloat}[h]\small
\begin{tcolorbox}
\begin{code}
translate-correctness : ∀ {Γ Δ τ} {env : Env Γ}
  → (e : Λ₁ Γ Δ τ)
  → eval[ gσ ] (translate e) env ≡ atomize {Δ} (unembed e env)
translate-correctness e = fun-ext λ w → translate-correctness-ext e w
\end{code}
\begin{code}
translate-correctness-ext : ∀ {Γ Δ τ} {env : Env Γ}
  → (e : Λ₁ Γ Δ τ)
  → (w : W (sz-list Δ))
  → eval[ gσ ] (translate e) env w ≡ atomize {Δ} (unembed e env) w
\end{code}
\end{tcolorbox}
\caption{Functional extensionality for |Stage1.translate-correctness|}
\label{agda:stage1-translate-correctness-ext-decl}
\end{agdacodefloat}

\pagebreak

\subsection{Atomization correctness}\label{sec:atomization-correctness}

In section \ref{sec:atomization}, we showed how we can transform back and forth between polytypes and vectors of \Piware atoms (i.e. \emph{words}). It seems reasonable to prove that, when we do a back-and-forth translation, the result should be unchanged. We introduce a proof for a proposition that specifies this in Agda listing \ref{agda:polytypes-words-correctness}. The proposition states that, for any value |(x : Tₚ τ)| of a polytype |τ|, translating it to a word and subsequently back to a polytype value, the value remains identical.

\begin{agdacodefloat}\small
\begin{tcolorbox}
\begin{code}
⤊∘⤋-identity : ∀ {τ} (x : Tₚ τ) → ⤊ (⤋ x) ≡ x

⤊∘⤋-identity {𝟙}      _         = refl

⤊∘⤋-identity {σ ⨂ τ}  (x , y)   = begin
    ⤊ (take (sz σ) (⤋ x ++ ⤋ y)) , ⤊ (drop (sz σ) (⤋ x ++ ⤋ y))
  ≡⟨ cong₂ (λ p q → ⤊ p , ⤊ q) take-++-identity (drop-++-identity (⤋ x)) ⟩
    ⤊ (⤋ x) ,  ⤊ (⤋ y)
  ≡⟨ cong₂ (λ p q → p , q) (⤊∘⤋-identity x) (⤊∘⤋-identity y) ⟩
    x , y
  ∎

⤊∘⤋-identity {σ ⨁ τ}  (inj₁ x)  = begin
    inj₁ (⤊ (unpad₁ (sz σ) (sz τ) (pad₁ (sz τ) (⤋ x))))
  ≡⟨ cong (λ z → inj₁ (⤊ z)) (unpad₁∘pad₁-identity (sz τ)) ⟩
    inj₁ (⤊ (⤋ x))
  ≡⟨ cong inj₁ (⤊∘⤋-identity x) ⟩
    inj₁ x
  ∎

⤊∘⤋-identity {σ ⨁ τ}  (inj₂ y)  = begin
    inj₂ (⤊ (unpad₂ (sz σ) (sz τ) (pad₂ (sz σ) (⤋ y))))
  ≡⟨ cong (λ z → inj₂ (⤊ z)) (unpad₂∘pad₂-identity (sz σ)) ⟩
    inj₂ (⤊ (⤋ y))
  ≡⟨ cong inj₂ (⤊∘⤋-identity y) ⟩
    inj₂ y
  ∎
\end{code}
\end{tcolorbox}
\caption{Correctness proof for translating back and forth between words and polytypes}
\label{agda:polytypes-words-correctness}
\end{agdacodefloat}

Since Agda can't case switch on |(x : Tₚ τ)|, as it does not have a way to know what results of |(Tₚ τ)| to expect, we do a case switch on the implicit parameter |τ| instead and let Agda fill in possible values for |x| from there.

In the case of tuples, we use a lemma of our own creation (See Agda listing \ref{agda:take-++-identity}) that proves that taking |m| items from an |m + n| vector that was built using the |(_++_)| operator results in the first operand. We use a similar one for dropping the first |m| items as well, resulting in the second operand. This gives us the intermediate value |(⤊ (⤋ x) ,  ⤊ (⤋ y))|, on which we can recursively use the proposition that we are proving.

\begin{agdacodefloat}\small
\begin{tcolorbox}
\begin{code}
take-++-identity :
    ∀ {A : Set} {m n} {v₁ : Vec A m} {v₂ : Vec A n} → take m (v₁ ++ v₂) ≡ v₁

take-++-identity {m = zero}   {v₁ = []}      = refl
take-++-identity {m = suc m}  {v₁ = x ∷ v₁}  =
    cong (λ z → x ∷ z) take-++-identity
\end{code}
\end{tcolorbox}
\caption{Lemma |take-++-identity|}
\label{agda:take-++-identity}
\end{agdacodefloat}

In the case of sums, we also use a lemma of our own creation (See Agda listing \ref{agda:unpad-pad-identity}) that proves the nature of \emph{unpadding} a \emph{padded} word results in the original word. This lemma relies heavily on our own improved version |(_⊔₂_)| of a \emph{max} function for natural numbers.

\begin{agdacodefloat}\small
\begin{tcolorbox}
\begin{code}
unpad₁∘pad₁-identity : ∀ {m} n {w : W m} → unpad₁ m n (pad₁ n w) ≡ w

unpad₁∘pad₁-identity {m} n with compare₂ m n
unpad₁∘pad₁-identity {.m}            .(m + k)  | lesseq m k   = take-++-identity
unpad₁∘pad₁-identity {.(m + suc k)}  .m        | greater m k  = refl
\end{code}
\end{tcolorbox}
\caption{Lemma |unpad₁∘pad₁-identity|}
\label{agda:unpad-pad-identity}
\end{agdacodefloat}

The Agda standard library version of the natural number max function works by rebuilding a result based on the arguments passed to it. We're introducing a version that lets Agda keep a reference to the actual maximum argument, including the difference between the arguments. We're providing this max function in two flavors. The first one distinguishes between \emph{less}, \emph{equal}, and \emph{greater}. The second, which is incidentally the one that is used in the code for the transpiler, only distinguishes between \emph{less or equal} and \emph{greater}. Since the implementation of |(_⊔₂_)| is based on the result of |compare₂|, we can use the same comparison function to do case splits in our proofs.

\pagebreak

\begin{agdacodefloat}[H]\small
\begin{tcolorbox}
\begin{code}
_⊔_ : ℕ → ℕ → ℕ

zero  ⊔ n      = n
suc m ⊔ zero   = suc m
suc m ⊔ suc n  = suc (m ⊔ n)
\end{code}
\end{tcolorbox}
\caption{Agda standard library version of \emph{max}}
\label{agda:stdlib-max}
\end{agdacodefloat}

\begin{agdacodefloat}[H]\small
\begin{tcolorbox}
\begin{code}
data Ordering₂ : Rel ℕ Level.zero where

  lesseq   : ∀ m k → Ordering₂ m (m + k)
  greater  : ∀ m k → Ordering₂ (m + suc k) m
\end{code}
\begin{code}
compare₂ : ∀ m n → Ordering₂ m n

compare₂ zero     n    = lesseq zero n
compare₂ (suc m)  zero = greater zero m
compare₂ (suc m)  (suc n) with compare₂ m n
compare₂ (suc m)             (suc .(m + k))  | lesseq .m k   = lesseq (suc m) k
compare₂ (suc .(n + suc k))  (suc n)         | greater .n k  = greater (suc n) k
\end{code}
\begin{code}
_⊔₂_ : ℕ → ℕ → ℕ

m ⊔₂ n with compare₂ m n
m             ⊔₂ .(m + k)  | lesseq .m k   = m + k
.(n + suc k)  ⊔₂ n         | greater .n k  = n + suc k
\end{code}
\end{tcolorbox}
\caption{Our improved version of \emph{max}}
\label{agda:improved-max}
\end{agdacodefloat}

\subsection{Evaluation semantics}\label{sec:eval-semantics}

The correctness proposition as stated at the beginning of this chapter depends on the evaluation semantics of both \lambdaone and \Piware. Furthermore, our proof is split in two stages, just like the translation was. First, we want to prove a correctness proposition for translating from \lambdaone to our intermediate language. Second, we want to prove a correctness proposition for translating from our intermediate language to \Piware. This means that we also require an unembedding of our intermediate language.

\subsubsection{Semantics of \Piware and intermediate language}\label{sec:eval-semantics-piware}

The evaluation semantics for \Piware are based on input and output of \emph{words}. An unembedded circuit is nothing more than a function which takes an input word and produces an output word. Since the intermediate language is designed to closely represent \Piware, the same applies there. The intermediate language also supports variables that exist in the polytype universe, for which we need to additionally unembed the value that we extract from the environment. Since the \Piware semantics are a subset of the \lambdaone semantics, we just demonstrate the latter in Agda listing \ref{agda:il-semantics}.

\begin{agdacodefloat}[H]\small
\begin{tcolorbox}
\begin{code}
plugσ : ∀ {i o} → i ⇇ o → W→W i o
plugσ p w = tabulate (flip lookup w ∘ flip lookup p)
\end{code}
\begin{code}
seqσ : ∀ {i m o} → W→W i m → W→W m o → W→W i o
seqσ f₁ f₂ = f₂ ∘ f₁
\end{code}
\begin{code}
parσ : ∀ {i₁ o₁ i₂ o₂} → W→W i₁ o₁ → W→W i₂ o₂ → W→W (i₁ + i₂) (o₁ + o₂)
parσ {i₁} f₁ f₂ w = f₁ (take i₁ w) ++ f₂ (drop i₁ w)
\end{code}
\begin{code}
eval[_] : ∀ {G Γ i o} → Gateσ G → IL[ G ] Γ i o → Env Γ → W→W i o

eval[ gσ ] G⟨ g# ⟩   env  = gσ g#
eval[ gσ ] Grnd      env  = const (replicate false)
eval[ gσ ] (Plug x)  env  = plugσ x
eval[ gσ ] (x ⟫ y)   env  = seqσ (eval[ gσ ] x env) (eval[ gσ ] y env)
eval[ gσ ] (x ∥ y)   env  = parσ (eval[ gσ ] x env) (eval[ gσ ] y env)
eval[ gσ ] (Var x)   env  = const $ ⤋ (env ! x)
\end{code}
\end{tcolorbox}
\caption{Intermediate language semantics}
\label{agda:il-semantics}
\end{agdacodefloat}

The caller needs to supply the evaluation function with gate semantics |(gσ : Gateσ)| which define how each gate operates. Furthermore, since our intermediate language supports variables of polytypes, callers also need to provide the evaluation function with an environment of values that act as a lookup table when evaluating the |Var| constructor. Note how the evaluation semantics cast the value inside the environment from a polytype value into a word by calling the |⤋| function. \Piware defines the semantics for plugs as well as for sequential and parallel compositions. We are swapping out the Agda standard library's version of |take| and |drop| for our own versions (See Agda listing \ref{agda:improved-take-drop}). Even though the standard library provides a functional one, our version makes it easier to prove some equality lemmas.

\begin{agdacodefloat}\small
\begin{tcolorbox}
\begin{code}
take : ∀ {A} m {n} → Vec A (m + n) → Vec A m
take m xs           with splitAt m xs
take m .(ys ++ zs)  | (ys , zs , refl) = ys
\end{code}
\begin{code}
drop : ∀ {A} m {n} → Vec A (m + n) → Vec A n
drop m xs           with splitAt m xs
drop m .(ys ++ zs)  | (ys , zs , refl) = zs
\end{code}
\end{tcolorbox}
\caption{Agda standard library version of |take| and |drop|}
\label{agda:stdlib-take-drop}
\end{agdacodefloat}

\begin{agdacodefloat}\small
\begin{tcolorbox}
\begin{code}
take : ∀ {A} m {n} → Vec A (m + n) → Vec A m
take zero     v        = []
take (suc m)  (x ∷ v)  = x ∷ take m v
\end{code}
\begin{code}
drop : ∀ {A} m {n} → Vec A (m + n) → Vec A n
drop zero     v        = v
drop (suc m)  (x ∷ v)  = drop m v
\end{code}
\end{tcolorbox}
\caption{Our improved version of |take| and |drop|}
\label{agda:improved-take-drop}
\end{agdacodefloat}

\subsubsection{Semantics of \lambdaone}\label{sec:eval-semantics-lambdaone}

The evaluation semantics of \lambdaone use unembedded polytypes for the inputs, output and environment of the unembedding function. In section \ref{sec:lambdaone-type-universe}, we already demonstrated the workings of |ΛSet| and how, together with |Λ⟦_⟧|, it can be used to transform a pair of inputs and output polytypes into an Agda function type with an arbitrary number of function parameters. This allows us to specify the unembedding in a very native Agda way as seen in Agda listing \ref{agda:lambdaone-unembed}.

\begin{agdacodefloat}[H]\small
\begin{tcolorbox}
\begin{code}
unembed : ∀ {Γ Δ τ} → (x : Λ₁ Γ Δ τ) → Env Γ → Λ⟦ Δ ↣ τ ⟧
unembed ⟨ g ⟩                     env  =  unembed-gate g
unembed #[ r ]                    env  =  env ! r
unembed (f $₁ x)                  env  =  (unembed f env) (unembed x env)
unembed (letₓ x inₑ e)            env  =  unembed e ((unembed x env) ∷ env)
unembed (x ,₁ y)                  env  =  (unembed x env) , (unembed y env)
unembed (case⨂ xy of f)           env  =  unembed f (
                                              (proj₁ $ unembed xy env) ∷
                                              (proj₂ $ unembed xy env) ∷
                                              env)
unembed (inl₁ x)                  env  =  inj₁ (unembed x env)
unembed (inr₁ y)                  env  =  inj₂ (unembed y env)
unembed (case⨁ xy either f or g)  env  with unembed xy env
... | inj₁ x                           =  unembed f (x ∷ env)
... | inj₂ y                           =  unembed g (y ∷ env)
\end{code}
\end{tcolorbox}
\caption{Unembedding of \lambdaone}
\label{agda:lambdaone-unembed}
\end{agdacodefloat}

\vspace*{2em}

\subsection{Let correctness}\label{sec:let-correctness}

In order to look at the correctness of the |letₓ_inₑ_| constructor's translation, we first need to take a closer look at the semantics of both the constructor itself as well as its translation. The evaluation semantics of the |letₓ_inₑ_| constructor dictate that the unembedding of |x| is added to the head of the variable environment before unembedding |f| itself. When atomized, this looks as follows:

\begin{center}
\begin{code}
atomize {Δ} (unembed e ((unembed x env) ∷ env)) w
\end{code}
\end{center}

\pagebreak

Recalling from section \ref{sec:stage1-let-constructor}, the translation of the |letₓ_inₑ_| constructor into \Piware takes the translation of |x| and supplements it with a parallel identity plug in order to partially apply it to a reduced-context version of the translation of |e|:

\begin{center}
\begin{code}
(translate x ∥ PlugId') ⟫ reduce-ctxt (translate e)
\end{code}
\end{center}

When looking at the definition of the evaluation semantics of \Piware, the expression above normalizes to the following expression when evaluated. This is the expression for which we need to show that it is equal to the atomization of the unembedding of the |letₓ_inₑ_| constructor:

\begin{center}
\begin{code}
(
  (eval[ gσ ] (reduce-ctxt (translate e)) env) ∘
  (parσ
    (eval[ gσ ] (translate x) env)
    (plugσ (⇇-id (sz-list Δ)))
  )
) w
\end{code}
\end{center}

Using equational reasoning together with the concept of congruence |cong|, we can piecewise break down this complex evaluation with equality lemmas until we arrive at the desired atomization expression. First, let us massage this expression into a more readable form by replacing some calls with their actual definitions:

\begin{agdacodefloat}[H]\small
\begin{tcolorbox}
\begin{code}
translate-correctness-ext {Δ = Δ} {env = env} (letₓ x inₑ e) w =

  let open ≡-Reasoning in ≡-Reasoning.begin

(
  (eval[ gσ ] (reduce-ctxt (translate e)) env) ∘
  (parσ
    (eval[ gσ ] (translate x) env)
    (plugσ (⇇-id (sz-list Δ)))
  )
) w

  ≡⟨ refl ⟩

eval[ gσ ] (reduce-ctxt (translate e)) env
(
  (eval[ gσ ] (translate x) env (take 0 w)) ++
  (plugσ (⇇-id (sz-list Δ)) (drop 0 w))
)

...
\end{code}
\end{tcolorbox}
\caption{Correctness of |letₓ_inₑ_| translation (1)}
\label{agda:let-correctness-1}
\end{agdacodefloat}

First, we've restructured the function composition call |_∘_| in order to pass |w| directly to |parσ|. Second, we've actually inserted the definition of |parσ| to explicitly pass the appropriate |take| and |drop| calls on |w| to both components of the parallel composition. We know that the variable |x| inside a \emph{let} constructor cannot have any inputs; we can see that here since the expression reduces to one where we take zero atoms from the input word |w|. Thanks to our effort of making the expression more readable, we can immediately see that we can replace the call to |(take 0 w)| with an empty vector |[]| as well as the call to |(drop 0 w)| with the full word |w|. This is possible thanks to our design of custom |take| and |drop| functions earlier.

At this point, we can try to replace some of the parts of this expression by injecting lemmas through congruence:

\begin{agdacodefloat}[H]\small
\begin{tcolorbox}
\begin{code}
...

  ≡⟨ cong (λ z → ...) plug-id-semantics-lemma ⟩

eval[ gσ ] (reduce-ctxt (translate e)) env
(
  (eval[ gσ ] (translate x) env []) ++
  w
)

  ≡⟨ cong (λ z → ...) (translate-correctness-ext x []) ⟩

eval[ gσ ] (reduce-ctxt (translate e)) env
(
  (atomize {[]} (unembed x env) []) ++
  w
)

  ≡⟨ refl ⟩

eval[ gσ ] (reduce-ctxt (translate e)) env (⤋ (unembed x env) ++ w)

...
\end{code}
\end{tcolorbox}
\caption{Correctness of |letₓ_inₑ_| translation (2)}
\label{agda:let-correctness-2}
\end{agdacodefloat}

The calls to |cong| inside these Agda listings have been shortened by not explicitly writing down the function body. This was done to keep this document readable. The contents of \ensuremath{\Hole{⋯}} repeat most of the expression, just replacing the sub-expression for which we want to replace it with an alternative (given the lemma) with |z|.

In the first step, we call our lemma |plug-id-semantics-lemma| which proves that identity plugs, when applied to a word, are equal to that word itself: |(plugσ (⇇-id k) w ≡ w)|. We refer to the accompanying code for the implementation of this lemma.

In the second step, we recursively use the correctness proposition on |x|. Since we know that |x| doesn't have any inputs, |(atomize {[]} (unembed x env) [])| reduces to |(⤋ (unembed x env))| as per the definition of |atomize|.

At this point, we need a proposition that proves the correctness of |reduce-ctxt|. We know from section \ref{sec:reducing-context} that, when we call |reduce-ctxt| on circuitry expressions, we move a variable binding from the context into the list of inputs by transforming the underlying circuitry to share the input at all the necessary positions. We call this proposition |reduce-ctxt-correctness| and will take a close look at it in the next section.

\begin{agdacodefloat}[H]\small
\begin{tcolorbox}
\begin{code}
...

  ≡⟨ reduce-ctxt-correctness (translate e) (unembed x env) ⟩

eval[ gσ ] (translate e) (unembed x env ∷ env) w

  ≡⟨ translate-correctness-ext e w ⟩

atomize {Δ} (unembed e ((unembed x env) ∷ env)) w

  ∎
\end{code}
\end{tcolorbox}
\caption{Correctness of |letₓ_inₑ_| translation (3)}
\label{agda:let-correctness-3}
\end{agdacodefloat}

Finally, we can make a recursive call to |(translate-correctness-ext e w)|. It makes intuitive sense that, for the |letₓ_inₑ_| constructor to be correct, both components |x| and |e|'s correctness would be necessary too.

\subsection{Reduce context correctness}\label{sec:reduce-ctxt-correctness}

The proof that our |reduce-ctxt| function works as intended is one of the main proofs within our correctness proof. To recap, context reduction was the method that we used to remove variable bindings by sharing their value to all the reference sites of that variable. This is the critical step when translating \lambdaone (which has variable bindings) to \Piware (which is nameless).

\begin{agdacodefloat}\small
\begin{tcolorbox}
\begin{code}
reduce-ctxt-correctness :
  ∀ {G τ Γ i o} {gσ : Gateσ G} {env : Env Γ} {w : W i}
  → (e : IL[ G ] (τ ∷ Γ) i o)
  → (x : Tₚ τ)
  → (eval[ gσ ] (reduce-ctxt e) env (⤋ x ++ w)) ≡ (eval[ gσ ] e (x ∷ env) w)
\end{code}
\end{tcolorbox}
\caption{Correctness proposition for |reduce-ctxt|}
\label{agda:reduce-ctxt-correctness-decl}
\end{agdacodefloat}

The |reduce-ctxt-correctness| proposition (See Agda listing \ref{agda:reduce-ctxt-correctness-decl}) states that, given an intermediate language expression |e| and a value |x|, evaluating |e| after reducing whilst giving it |(⤋ x)| as an additional input should output the same word as evaluating a non-reduced |e| with |x| being part of the environment instead. Note that since our intermediate language uses polytypes on its environment, the type of |x| here is a polytyped value, which means that we need to cast it to a word when passing it as an input on the left hand side. In the previous section, when we made a call to |reduce-ctxt-correctness|, we actually passed |(unembed x env)| (where |x| refers to the \lambdaone expression of the \emph{let} constructor) as the argument for our new identifier |x| here.

We need to prove the proposition for the |reduce-ctxt| call on every possible constructor in our intermediate language. Looking back at the actual definition of |reduce-ctxt| in section \ref{sec:reducing-context}, we used combinator circuits of our own creation to implement the sharing of the new input. Let's take a look at a few examples to illustrate how the proof works for some of these combinators.

\subsubsection{Reducing gates}\label{sec:reduce-ctxt-correctness-gate}

\begin{center}
\begin{code}
reduce-ctxt {_} {τ} G⟨ g# ⟩ = K[ sz τ ]· G⟨ g# ⟩
\end{code}
\end{center}
\vspace*{-3em}
\begin{center}
\begin{code}
K[ k ]· x = PlugNil k ∥ x
\end{code}
\end{center}

Recall that evaluating gates in \Piware and our intermediate language doesn't depend on the environment. This means that we expect that, during our equational reasoning, we will at some point manage to remove any reference to |(x : Tₚ τ)|.

\begin{agdacodefloat}[H]\small
\begin{tcolorbox}
\begin{code}
reduce-ctxt-correctness {τ = τ} {gσ = gσ} {w = w} G⟨ g# ⟩ x =

  let open ≡-Reasoning in ≡-Reasoning.begin

parσ (plugσ (⇇-nil (sz τ))) (gσ g#) (⤋ x ++ w)

  ≡⟨ refl ⟩

plugσ (⇇-nil (sz τ)) (take (sz τ) (⤋ x ++ w)) ++
(gσ g#) (drop (sz τ) (⤋ x ++ w))

  ≡⟨ refl ⟩

(gσ g#) (drop (sz τ) (⤋ x ++ w))

...
\end{code}
\end{tcolorbox}
\caption{Correctness of |reduce-ctxt| for gates (1)}
\label{agda:reduce-ctxt-correctness-gate-1}
\end{agdacodefloat}

In fact, we can see that we are able to remove the entire empty part of our killer plug |PlugNil| without needing any additional lemmas. Once again, once we wrote out the definition of |parσ| explicitly with calls to our custom |take| and |drop| functions, we get a clear picture of how we can clean up both components of the parallel composition. In this case, the first part dropped away completely. Agda isn't able to normalize |(drop (sz τ) (⤋ x ++ w))| by itself, so we help it along with a lemma:

\begin{agdacodefloat}[H]\small
\begin{tcolorbox}
\begin{code}
...

  ≡⟨ cong (λ z → (gσ g#) z) (drop-++-identity (⤋ x)) ⟩

gσ g# w

  ∎
\end{code}
\end{tcolorbox}
\caption{Correctness of |reduce-ctxt| for gates (2)}
\label{agda:reduce-ctxt-correctness-gate-2}
\end{agdacodefloat}

The |drop-++-identity| lemma works very similar to the |take-++-identity| lemma that we saw earlier. Both depend on our custom implementation of |drop| and |take|, respectively. Note how the proof here follows the concept behind the implementation of |reduce-ctxt| closely. We implemented the plug to kill the extra input wires that are given, since we don't need them for the implementation of this constructor once the variable has been removed from the context. The steps in the proof clearly show how we first remove the extra input and then massage the remainder with a lemma to bring it to the desired form. By splitting up the proofs into smaller (sometimes reusable) sub-proofs, we create a pleasant environment where we can write proofs that are not only sound, but also easy to follow step-by-step.

\subsubsection{Reducing compositions}\label{sec:reduce-ctxt-correctness-seq}

\begin{center}
\begin{code}
reduce-ctxt {_} {τ} (x ⟫ y) = S[ sz τ ]· reduce-ctxt x · reduce-ctxt y

reduce-ctxt {_} {τ} (x ∥ y) = P[ sz τ ]· reduce-ctxt x · reduce-ctxt y
\end{code}
\end{center}
\vspace*{-3em}
\begin{center}
\begin{code}
S-bypass k i = coerceₒ (+-assoc k k i) $ PlugDup k ∥ PlugId i

S[_]·_·_ {i = i} k x y = S-bypass k i ⟫ PlugId k ∥ x ⟫ y
\end{code}
\end{center}
\vspace*{-3em}
\begin{center}
\begin{code}
P-insert k i₁ i₂ =
  coerceᵢₒ (+-assoc k i₁ i₂) (+-assoc (k + i₁) k i₂) $ PlugCopyK i₁ k ∥ PlugId i₂

P[_]·_·_ {i₁ = i₁} {i₂ = i₂} k x y = P-insert k i₁ i₂ ⟫ x ∥ y
\end{code}
\end{center}

The sequential and parallel composition constructors use custom combinators |S[_]·_·_| and |P[_]·_·_| respectively. The actual proof of |reduce-ctxt-correctness| for these two cases is quite verbose, given the number of plugs and compositions that they use. For that reason, we refer to the accompanying code for the full evidence. Even though we're not explaining the entire proof for these cases in this document, we do want to touch on the use of vector coercion, since we introduced it in section \ref{sec:vec-coercion} specifically with the intent of making writing proofs easier.

We mentioned that we want to carry the transformations of vectors explicitly rather than relying on |rewrite| mechanisms. The proofs for these two cases of |reduce-ctxt-correctness| make use of the benefit of this explicitness. For example, let's take a look at the |S-bypass| construct. For the bypass to work, we want it to have an output of |(k + (k + i))| wires. Note the explicit placement of parentheses here. Even though we are all intuitively familiar with the associativity of |_+_| on natural numbers, Agda does not have this intuition built-in. Due to |_+_| being defined asymmetrically based on a case switch on it's first argument, concepts such as associativity or even commutativity are not given. Of course, Agda's standard library provides us with lemmas that prove these concepts, for example by giving us equality between |(k + (k + i))| and |((k + k) + i)| in the form of |(+-assoc k k i)|.

Vector sizes are specified as a natural number on their type index. The |coerce-vec| function lets us change the type of a vector by modifying its size index according to an equality lemma. Now, when we encounter such a coerced vector in our equational reasoning, we need a way to transform it back to the original. We were not able to provide a single catch-all lemma that uncoerces vectors in Agda, but we managed to write easy lemmas proving that coerced vectors behave as expected when we pass them as arguments to other functions. Without showing the full code of these lemmas (we refer to the accompanying code for that), one example to illustrate the use of coerced vectors can be found in Agda listing \ref{agda:lemma-example-uncoerce}. This lemma proves that |take m| works on an associativity-coerced vector as expected. We can use lemmas like this one inside steps of equational reasoning to get rid of the calls to |coerce-vec|.

\begin{agdacodefloat}[H]\small
\begin{tcolorbox}
\begin{code}
take-++-identity-c+a :
  ∀ {A} {m k₀ k₁} →
  (vₘ : Vec A m) → (v₀ : Vec A k₀) → (v₁ : Vec A k₁) →
  take m (coerce-vec (+-assoc m k₀ k₁) ((vₘ ++ v₀) ++ v₁)) ≡ vₘ
\end{code}
\end{tcolorbox}
\caption{Example lemma using |coerce-vec|}
\label{agda:lemma-example-uncoerce}
\end{agdacodefloat}

\pagebreak

\subsection{Final correctness}\label{sec:final-correctness}

In this chapter, we've shown how we can use equational reasoning and functional extensionality to prove the correctness proposition which we started with. We showed and explained some highlights of proofs inside the two-step translation pipeline. Finally, we'd like to state the correctness proof one more time, this time with the proof's body. For the full implementation, we -- once again -- refer to the code accompanying this document.

\begin{agdacodefloat}[H]\small
\begin{tcolorbox}
\begin{code}
open import ... .Stage1.LambdaOne2IL using () renaming (translate to Λ₁⟶IL)

open import ... .Stage2.IL2PiWare using () renaming (translate to IL⟶ΠW)

open import ... .Translation using (translate)
\end{code}
\begin{code}
open import ... .Stage1.Properties.Correctness using ()
  renaming (translate-correctness to stage1-correctness)

open import ... .Stage2.Properties.Correctness using ()
  renaming (translate-correctness to stage2-correctness)
\end{code}
\begin{code}
translate-correctness : ∀ {Δ τ}
  → (e : Λ₁ [] Δ τ)
  → ⟦ translate e ⟧[ ΛBoolTrioσ ] ≡ atomize {Δ} (unembed e ε)

translate-correctness {Δ} e =

  let open ≡-Reasoning in ≡-Reasoning.begin

    ⟦ translate e ⟧[ ΛBoolTrioσ ]

  ≡⟨ refl ⟩

    ⟦ IL⟶ΠW (Λ₁⟶IL e) ⟧[ ΛBoolTrioσ ]

  ≡⟨ stage2-correctness (Λ₁⟶IL e) ⟩

    eval[ ΛBoolTrioσ ] (Λ₁⟶IL e) ε

  ≡⟨ stage1-correctness e ⟩

    atomize {Δ} (unembed e ε)

  ∎
\end{code}
\end{tcolorbox}
\caption{Final translation correctness proof}
\label{agda:final-correctness}
\end{agdacodefloat}
