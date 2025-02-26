_Martin Escardo, Paulo Oliva, 2022

Warning. This module is a mess. We plan to clean it up soon. At the
moment the proofs are in "blackboard" style (improvised proofs that
work) rather than "article" style (proofs written in a more
presentable way).

This generalizes (but also uses) the file Games.FiniteHistoryDependent
with a monad parameter 𝓣. When 𝓣 is the identity monad 𝕀𝕕, the
original development is obtained. We apply the selection-monad
transformer 𝕁-transf to 𝓣. See [1] for background.

The main examples of 𝓣 we have in mind are the powerset monad (for the
Herbrand Functional Interpretation [2]), probability distribution
monads (for mixed strategies) and the reader monad (for alpha-beta
pruning in the file Games.alpha-beta).

[1] https://doi.org/10.48550/arXiv.2212.07735
[2] https://doi.org/10.1017/jsl.2017.8

\begin{code}

{-# OPTIONS --safe --without-K #-} -- --exact-split

open import Games.TypeTrees
open import Games.Monad
open import Games.J
open import Games.K
open import MLTT.Spartan hiding (J)
open import UF.Base
open import UF.FunExt


module Games.FiniteHistoryDependentTransformer
        (fe : Fun-Ext)
        (𝓣  : Monad)
        (R  : Type)
        (𝓐  : Algebra 𝓣 R)
 where

open import Games.FiniteHistoryDependent R

fext : DN-funext 𝓤₀ 𝓤₀
fext = dfunext fe

open K-definitions R
open T-definitions 𝓣
open α-definitions 𝓣 R 𝓐

\end{code}

For some of the results proved below, we need the monad T to satisfy
the condition extᵀ-const defined below. Ohad Kammar pointed out to us
that this condition is equivalent to the monad being affine. A proof
is included in the module Games.Monad.

\begin{code}

open import UF.Equiv

mapᵀ-path-head : {X : Type} {Xf : X → 𝕋} (a : T X) (b : (x : X)
               → T (Path (Xf x)))
               → ext-const 𝓣
               → mapᵀ path-head (a ⊗ᵀ b) ＝ a
mapᵀ-path-head {X} {Xf} a b ext-const =
  mapᵀ path-head (a ⊗ᵀ b)                                  ＝⟨ refl ⟩
  extᵀ (ηᵀ ∘ path-head) (a ⊗ᵀ b)                           ＝⟨ refl ⟩
  extᵀ g (a ⊗ᵀ b)                                          ＝⟨ refl ⟩
  extᵀ g (extᵀ (λ x → mapᵀ (x ::_) (b x)) a)               ＝⟨ refl ⟩
  extᵀ g (extᵀ (λ x → extᵀ (ηᵀ ∘ (x ::_)) (b x)) a)        ＝⟨ ⦅1⦆ ⟩
  extᵀ (extᵀ g ∘ (λ x → extᵀ (ηᵀ ∘ (x ::_)) (b x))) a      ＝⟨ refl ⟩
  extᵀ (extᵀ g ∘ (λ x → extᵀ (f x) (b x))) a               ＝⟨ refl ⟩
  extᵀ (λ x → extᵀ g (extᵀ (f x) (b x))) a                 ＝⟨ refl ⟩
  extᵀ (λ x → (extᵀ g ∘ extᵀ (f x)) (b x)) a               ＝⟨ ⦅2⦆ ⟩
  extᵀ (λ x → extᵀ (extᵀ g ∘ (f x)) (b x)) a               ＝⟨ refl ⟩
  extᵀ (λ x → extᵀ (λ xs → extᵀ g (ηᵀ (x :: xs))) (b x)) a ＝⟨ ⦅3⦆ ⟩
  extᵀ (λ x → extᵀ (λ xs → g (x :: xs)) (b x)) a           ＝⟨ refl ⟩
  extᵀ (λ x → extᵀ (λ _ → ηᵀ x) (b x)) a                   ＝⟨ ⦅4⦆ ⟩
  extᵀ ηᵀ a                                                ＝⟨ extᵀ-η a ⟩
  a                                                        ∎
 where
  g : Path (X ∷ Xf) → T X
  g = ηᵀ ∘ path-head

  f : (x : X) → Path (Xf x) → T (Path (X ∷ Xf))
  f x = ηᵀ ∘ (x ::_)

  I : ∀ x → (extᵀ g ∘ extᵀ (f x)) (b x) ＝ extᵀ (extᵀ g ∘ (f x)) (b x)
  I x = (assocᵀ g (f x) (b x))⁻¹

  II : (x : X) (xs : Path (Xf x)) → extᵀ g (ηᵀ (x :: xs)) ＝ g (x :: xs)
  II x xs = unitᵀ g (x :: xs)

  ⦅1⦆ = (assocᵀ g (λ x → extᵀ (f x) (b x)) a)⁻¹
  ⦅2⦆ = ap (λ - → extᵀ - a) (fext I)
  ⦅3⦆ = ap (λ - →  extᵀ (λ x → extᵀ (- x) (b x)) a) (fext (λ x → fext (II x)))
  ⦅4⦆ = ap (λ - → extᵀ - a) (fext (λ x → ext-const (ηᵀ x) (b x)))


open JT-definitions 𝓣 R 𝓐 fe

𝓙𝓣 :  𝕋 → Type
𝓙𝓣 = structure JT

sequenceᴶᵀ : {Xt : 𝕋} → 𝓙𝓣 Xt → JT (Path Xt)
sequenceᴶᵀ = path-sequence (𝕁-transf fe 𝓣 R)

T-Strategy : 𝕋 -> Type
T-Strategy = structure T

T-strategic-path : {Xt : 𝕋} → T-Strategy Xt → T (Path Xt)
T-strategic-path = path-sequence 𝓣

varextᵀ : {A : Type} → (A → R) → T A → R
varextᵀ q = α ∘ mapᵀ q

T-sub : {X : Type} {Y : X → Type}
         → ((Σ x ꞉ X , Y x) → R)
         → (x : X) → T (Y x) → R
T-sub q x = varextᵀ (λ y → q (x , y))

-- Not used:
-- overline : {X : Type} → JT X → K X
-- overline ε = λ p → varextᵀ p (ε (ηᵀ ∘ p))

-- Def. p ≣ q if ηᵀ ∘ α ∘ p ∼ ηᵀ ∘ α ∘ q
-- Fact. p ≣ ηᵀ ∘ α ∘ p
-- Fact. In  this case ϕ p = ϕ q
-- Def. p is pure if p ∼ ηᵀ ∘ α ∘ p
-- p : X → T R
-- α ∘ p : X → R
-- ηᵀ ∘ α ∘ p : X → T R
-- Fact. Every pure p is of the form η ∘ q for some q : X → R.

-- weak-attains ϕ = (p : X → R) → ϕ p = α (extᵀ (ηᵀ ∘ p) (ε (ηᵀ ∘ p)))

{- False: this only holds for pure p.
conjecture : {X : Type} (ε : JT X) → ε attainsᵀ (overline ε)
conjecture {X} ε p =
  overlineᵀ ε p ＝⟨ refl ⟩
  α (extᵀ p (ε p)) ＝⟨ {!!} ⟩
  {!!} ＝⟨ {!!} ⟩
  {!!} ＝⟨ {!!} ⟩
  α (extᵀ (ηᵀ ∘ α ∘ p) (ε (ηᵀ ∘ α ∘ p))) ＝⟨ refl ⟩
  overline ε (α ∘ p) ∎
-}


{- Next time

1. Clean-up the following lemma
2. Proof "try" below (commented out)

-}


-- (Lemmas 3.2 and 3.5 of the paper are missing but they don't seem to be needed.)

-- Lemma 3.4 (paper).
module _ {X  : Type}
         {Y  : X → Type}
         (ε  : JT X)
         (δ  : (x : X) → JT (Y x))
 where

 private
  ν : ((Σ x ꞉ X , Y x) → T R) → (x : X) → T (Y x)
  ν q x = δ x (λ y → q (x , y))

  τ : ((Σ x ꞉ X , Y x) → T R) → T X
  τ q = ε (λ x → extᵀ (λ y → q (x , y)) (ν q x))

 ⊗ᴶᵀ-in-terms-of-⊗ᵀ : (q : (Σ x ꞉ X , Y x) → T R)
                    → (ε ⊗ᴶᵀ δ) q ＝ τ q ⊗ᵀ ν q
 ⊗ᴶᵀ-in-terms-of-⊗ᵀ q =
    (ε ⊗ᴶᵀ δ) q                                          ＝⟨ refl ⟩
    extᴶᵀ (λ x → extᴶᵀ (λ y _ → ηᵀ (x , y)) (δ x)) ε q   ＝⟨ ⦅1⦆ ⟩
    extᴶᵀ Θ ε q                                          ＝⟨ refl ⟩
    extᵀ (λ x → Θ x q) (ε (λ x → extᵀ q (Θ x q)))        ＝⟨ ⦅2⦆ ⟩
    extᵀ (λ x → Θ x q) (τ q)                             ＝⟨ refl ⟩
    τ q ⊗ᵀ ν q                                           ∎
     where
      Θ : X → JT (Σ x ꞉ X , Y x)
      Θ x r = extᵀ (λ y → ηᵀ (x , y)) (ν r x)

      I : (λ x → extᴶᵀ (λ y _ → ηᵀ (x , y)) (δ x)) ＝ Θ
      I = fext (λ x →
          fext (λ r → ap (λ - → extᵀ (λ y → ηᵀ (x , y)) (δ x (λ y → - (x , y))))
                         (fext (unitᵀ r))))

      ⦅1⦆ = ap (λ - → extᴶᵀ - ε q) I

      II : ∀ x → extᵀ q ∘ extᵀ (λ y → ηᵀ (x , y)) ＝ extᵀ (λ y → q (x , y))
      II x = extᵀ q ∘ extᵀ (λ y → ηᵀ (x , y))               ＝⟨ ⦅i⦆ ⟩
             (λ x' → extᵀ (extᵀ q ∘ (λ y → ηᵀ (x , y))) x') ＝⟨ refl ⟩
             extᵀ (λ y → ((extᵀ q) ∘ ηᵀ) (x , y))           ＝⟨ ⦅ii⦆ ⟩
             extᵀ (λ y → q (x , y))                         ∎
       where
        ⦅i⦆  = fext (λ x' → (assocᵀ q (λ y → ηᵀ (x , y)) x')⁻¹)
        ⦅ii⦆ = ap extᵀ (fext (λ y → unitᵀ q (x , y)))

      III : ε (λ x → extᵀ q (extᵀ (λ y → ηᵀ (x , y)) (ν q x))) ＝ τ q
      III = ap ε (fext (λ x → ap (λ - → - (ν q x)) (II x)))

      ⦅2⦆ = ap (extᵀ (λ x → Θ x q)) III

is-T-pe : (G : Game) (σ : T-Strategy (Xt G)) → Type
is-T-pe (game [] q ⟨⟩)              ⟨⟩        = 𝟙
is-T-pe (game (X ∷ Xf) q (ϕ :: ϕf)) (t :: σf) =
   (varextᵀ q (T-strategic-path (t :: σf))
 ＝ ϕ (λ x → T-sub q x (T-strategic-path (σf x))))


is-T-sgpe' : {Xt : 𝕋} → 𝓚 Xt → (Path Xt → R) → T-Strategy Xt → Type
is-T-sgpe' {[]}     ⟨⟩        q ⟨⟩        = 𝟙
is-T-sgpe' {X ∷ Xf} (ϕ :: ϕf) q (t :: σf) =
      is-T-pe (game (X ∷ Xf) q (ϕ :: ϕf)) (t :: σf)
    × ((x : X) → is-T-sgpe' {Xf x} (ϕf x) (subpred q x) (σf x))

is-T-sgpe : (G : Game) (σ : T-Strategy (Xt G)) → Type
is-T-sgpe (game Xt q ϕt) = is-T-sgpe' {Xt} ϕt q

\end{code}

The main lemma is that the optimal outcome is the same thing as the
application of the outcome function to the path induced by a strategy
in perfect subgame equilibrium.

The following is Theorem 3.1 of reference [1].

\begin{code}

T-sgpe-lemma : (Xt : 𝕋) (ϕt : 𝓚 Xt) (q : Path Xt → R) (σ : T-Strategy Xt)
             → is-T-sgpe' ϕt q σ
             → sequenceᴷ ϕt q ＝ varextᵀ q (T-strategic-path σ)
T-sgpe-lemma [] ⟨⟩ q ⟨⟩ ⟨⟩ =
  sequenceᴷ ⟨⟩ q                  ＝⟨ refl ⟩
  q ⟨⟩                             ＝⟨ (α-unitᵀ (q ⟨⟩))⁻¹ ⟩
  α (ηᵀ (q ⟨⟩))                    ＝⟨ ap α ((unitᵀ (ηᵀ ∘ q) ⟨⟩)⁻¹) ⟩
  α (extᵀ (ηᵀ ∘ q) (ηᵀ ⟨⟩))        ＝⟨ refl ⟩
  varextᵀ q (T-strategic-path ⟨⟩)  ∎

T-sgpe-lemma (X ∷ Xf) (ϕ :: ϕt) q (a :: σf) (h :: t) =
 sequenceᴷ (ϕ :: ϕt) q                        ＝⟨ refl ⟩
 ϕ (λ x → sequenceᴷ (ϕt x) (subpred q x))     ＝⟨ ap ϕ (fext IH) ⟩
 ϕ (λ z → T-sub q z (T-strategic-path (σf z))) ＝⟨ h ⁻¹ ⟩
 varextᵀ q (T-strategic-path (a :: σf))        ∎
  where
   IH : (x : X) → sequenceᴷ (ϕt x) (subpred q x)
                ＝ T-sub q x (T-strategic-path (σf x))
   IH x = T-sgpe-lemma (Xf x) (ϕt x) (subpred q x) (σf x) (t x)

\end{code}

This can be reformulated as follows in terms of the type of games:

\begin{code}

-- Not used anywhere:
T-perfect-equilibrium-theorem : (G : Game) (σ : T-Strategy (Xt G))
                              → is-T-sgpe G σ
                              → optimal-outcome G
                              ＝ varextᵀ (q G) (T-strategic-path σ)
T-perfect-equilibrium-theorem (game Xt q ϕt) = T-sgpe-lemma Xt ϕt q

\end{code}

We now show how to use selection functions to compute a sgpe strategy.

The following, which defines a strategy from given selection
functions, is defined in Theorem 5.4 of [1], with the difference that
here, for the moment, we consider only single-valued quantifiers.

\begin{code}

T-selection-strategy : {Xt : 𝕋} → 𝓙𝓣 Xt → (Path Xt → R) → T-Strategy Xt
T-selection-strategy {[]}     ⟨⟩           q = ⟨⟩
T-selection-strategy {X ∷ Xf} εt@(ε :: εf) q = t :: σf
 where
  t : T X
  t = mapᵀ path-head (sequenceᴶᵀ εt (ηᵀ ∘ q))

  σf : (x : X) → T-Strategy (Xf x)
  σf x = T-selection-strategy {Xf x} (εf x) (λ xs → q (x :: xs))

strategic-path-lemma : ext-const 𝓣
                     → {Xt : 𝕋} (εt : 𝓙𝓣 Xt) (q : Path Xt → R)
                     → sequenceᴶᵀ εt (ηᵀ ∘ q)
                     ＝ T-strategic-path (T-selection-strategy εt q)
strategic-path-lemma ext-const {[]}     ⟨⟩           q = refl
strategic-path-lemma ext-const {X ∷ Xf} εt@(ε :: εf) q = γ
 where

  δ : (x : X) → JT (Path (Xf x))
  δ x = sequenceᴶᵀ {Xf x} (εf x)

  q' : (x : X) → Path (Xf x) → T R
  q' x = ηᵀ ∘ subpred q x

  σf : (x : X) → T-Strategy (Xf x)
  σf x = T-selection-strategy {Xf x} (εf x) (subpred q x)

  b c : (x : X) → T (Path (Xf x))
  b x = δ x (q' x)
  c x = T-strategic-path (σf x)

  IH : b ∼ c
  IH x = strategic-path-lemma ext-const (εf x) (subpred q x)

  t : T X
  t = mapᵀ path-head (sequenceᴶᵀ εt (ηᵀ ∘ q))

  I = ε (λ x → extᵀ (q' x) (c x))                       ＝⟨ ⦅1⦆ ⟩
      mapᵀ path-head (ε (λ x → extᵀ (q' x) (c x)) ⊗ᵀ c) ＝⟨ ⦅2⦆ ⟩
      mapᵀ path-head (ε (λ x → extᵀ (q' x) (b x)) ⊗ᵀ b) ＝⟨ ⦅3⦆ ⟩
      mapᵀ path-head ((ε ⊗ᴶᵀ δ) (ηᵀ ∘ q))               ＝⟨ refl ⟩
      mapᵀ path-head (sequenceᴶᵀ εt (ηᵀ ∘ q))          ＝⟨ refl ⟩
      t                                                 ∎
   where
    ⦅1⦆ = (mapᵀ-path-head (ε (λ x → extᵀ (q' x) (c x))) c ext-const)⁻¹
    ⦅2⦆ = ap (λ - → mapᵀ path-head (ε (λ x → extᵀ (q' x) (- x)) ⊗ᵀ -))
            (fext (λ x → (IH x)⁻¹))
    ⦅3⦆ = (ap (mapᵀ path-head) (⊗ᴶᵀ-in-terms-of-⊗ᵀ ε δ (ηᵀ ∘ q)))⁻¹

  γ : sequenceᴶᵀ (ε :: εf) (ηᵀ ∘ q)
    ＝ T-strategic-path (T-selection-strategy (ε :: εf) q)
  γ = sequenceᴶᵀ (ε :: εf) (ηᵀ ∘ q)                    ＝⟨ refl ⟩
      (ε ⊗ᴶᵀ δ) (ηᵀ ∘ q)                                ＝⟨ ⦅1⦆ ⟩
      ε (λ x → extᵀ (q' x) (b x)) ⊗ᵀ b                  ＝⟨ ⦅2⦆ ⟩
      (ε (λ x → extᵀ (q' x) (c x)) ⊗ᵀ c)                ＝⟨ ⦅3⦆ ⟩
      t ⊗ᵀ c                                            ＝⟨ refl ⟩
      t ⊗ᵀ (λ x → T-strategic-path {Xf x} (σf x))       ＝⟨ refl ⟩
      T-strategic-path (t :: σf)                        ＝⟨ refl ⟩
      T-strategic-path (T-selection-strategy (ε :: εf) q) ∎
   where
    ⦅1⦆ = ⊗ᴶᵀ-in-terms-of-⊗ᵀ ε δ (ηᵀ ∘ q)
    ⦅2⦆ = ap (λ - → ε (λ x → extᵀ (q' x) (- x)) ⊗ᵀ -) (fext IH)
    ⦅3⦆ = ap (_⊗ᵀ c) I

-- This corresponds to Definition 3.6 (paper)
is-in-head-equilibrium : (G : Game) → 𝓙𝓣 (Xt G) → Type
is-in-head-equilibrium (game [] q ϕt) εs = 𝟙
is-in-head-equilibrium G@(game (X ∷ Xf) q (ϕ :: ϕf)) εt@(ε :: εf) =
  ε attainsᵀ ϕ → is-T-pe G (T-selection-strategy εt q)

overlineᵀ-lemma : {X : Type} (ε : JT X)
                → (Σ ϕ ꞉ K X , ε attainsᵀ ϕ)
                → overlineᵀ ε ∼ λ p → overlineᵀ ε (ηᵀ ∘ α ∘ p)
overlineᵀ-lemma ε (ϕ , a) p =
 overlineᵀ ε p           ＝⟨ a p ⟩
 ϕ (α ∘ p)               ＝⟨ refl ⟩
 ϕ (id ∘ α ∘ p)          ＝⟨ ap (λ - → ϕ (- ∘ α ∘ p)) (fext (λ r → (α-unitᵀ r)⁻¹)) ⟩
 ϕ (α ∘ ηᵀ ∘ α ∘ p)      ＝⟨ (a (ηᵀ ∘ α ∘ p))⁻¹ ⟩
 overlineᵀ ε (ηᵀ ∘ α ∘ p) ∎

-- Main theorem.
-- This corresponds to Theorem 3.10 (paper), but only for the root. To
-- get the full theorem, we need to talk about subgames.
head-equilibrium : ext-const 𝓣
                 → (G : Game) (εt : 𝓙𝓣 (Xt G))
                 → is-in-head-equilibrium G εt
head-equilibrium ext-const (game [] q ⟨⟩) ⟨⟩ = ⟨⟩
head-equilibrium ext-const G@(game (X ∷ Xf) q (ϕ :: ϕf)) εt@(ε :: εf) = γ
 where
  δ : (x : X) → JT (Path (Xf x))
  δ x = sequenceᴶᵀ {Xf x} (εf x)

  f : X → JT (Σ x ꞉ X , Path (Xf x))
  f x = mapᴶᵀ (x ::_) (δ x)

  q' : Path (X ∷ Xf) → T R
  q' = ηᵀ ∘ q

  p : X → T R
  p x = extᵀ q' (f x q')

  σ : (x : X) → T (Path (Xf x))
  σ x = T-strategic-path (T-selection-strategy {Xf x} (εf x) (subpred q x))

  I : (λ x → δ x (ηᵀ ∘ subpred q x)) ＝ σ
  I = fext (λ x → strategic-path-lemma ext-const (εf x) (subpred q x))

  γ : ε attainsᵀ ϕ → is-T-pe G (T-selection-strategy εt q)
  γ h =
   varextᵀ q (T-strategic-path (T-selection-strategy εt q))                                     ＝⟨ ⦅1⦆ ⟩
   varextᵀ q (sequenceᴶᵀ εt q')                                                              ＝⟨ refl ⟩
   varextᵀ q ((ε ⊗ᴶᵀ δ) q')                                                                   ＝⟨ refl ⟩
   varextᵀ q (extᴶᵀ f ε q')                                                                   ＝⟨ refl ⟩
   varextᵀ q (extᵀ (λ x → f x q') (ε p))                                                      ＝⟨ refl ⟩
   (α ∘ mapᵀ q) (extᵀ (λ x → f x q') (ε p))                                                   ＝⟨ refl ⟩
   (α ∘ extᵀ q') (extᵀ (λ x → f x q') (ε p))                                                  ＝⟨ refl ⟩
   (α ∘ extᵀ q') (extᵀ (λ x → f x q') (ε p))                                                  ＝⟨ refl ⟩
   α (extᵀ q' (extᵀ (λ x → f x q') (ε p)))                                                    ＝⟨ ⦅2⦆ ⟩
   α (extᵀ p (ε p))                                                                           ＝⟨ refl ⟩
   overlineᵀ ε p                                                                               ＝⟨ ⦅3⦆ ⟩
   overlineᵀ ε (ηᵀ ∘ α ∘ p)                                                                    ＝⟨ ⦅4⦆ ⟩
   ϕ (λ x → α ((ηᵀ ∘ α ∘ p) x))                                                               ＝⟨ refl ⟩
   ϕ (λ x → α (ηᵀ (α (extᵀ q' (mapᴶᵀ (x ::_) (δ x) q')))))                                    ＝⟨ refl ⟩
   ϕ (λ x → α (ηᵀ (α (extᵀ q' (extᵀ (ηᵀ ∘ (x ::_)) (δ x (λ xs → extᵀ q' (ηᵀ (x :: xs))))))))) ＝⟨ ⦅5⦆ ⟩
   ϕ (λ x → α (extᵀ q' (extᵀ (ηᵀ ∘ (x ::_)) (δ x (λ xs → extᵀ q' (ηᵀ (x :: xs)))))))          ＝⟨ ⦅6⦆ ⟩
   ϕ (λ x → α (extᵀ (λ xs → extᵀ q' (ηᵀ (x :: xs))) (δ x (λ xs → extᵀ q' (ηᵀ (x :: xs))))))   ＝⟨ ⦅7⦆ ⟩
   ϕ (λ x → α (extᵀ (λ xs → ηᵀ (q (x :: xs))) (δ x (λ xs → ηᵀ (q (x :: xs))))))               ＝⟨ refl ⟩
   ϕ (λ x → T-sub q x (δ x (ηᵀ ∘ subpred q x)))                                                   ＝⟨ ⦅8⦆ ⟩
   ϕ (λ x → T-sub q x (σ x))                                                                  ∎
    where
     ⦅1⦆ = ap (varextᵀ q) ((strategic-path-lemma ext-const εt q)⁻¹)
     ⦅2⦆ = ap α ((assocᵀ q' (λ x → f x q') (ε p))⁻¹)
     ⦅3⦆ = overlineᵀ-lemma ε (ϕ , h) p
     ⦅4⦆ = h (ηᵀ ∘ α ∘ p)
     ⦅5⦆ = ap ϕ (fext (λ x → α-unitᵀ (α (extᵀ q' (extᵀ (ηᵀ ∘ (x ::_)) (δ x (λ xs → extᵀ q' (ηᵀ (x :: xs)))))))))
     ⦅6⦆ = ap (λ - → ϕ (λ x → α (- x))) ((fext (λ x → assocᵀ q' (ηᵀ ∘ (x ::_)) (δ x (λ xs → extᵀ q' (ηᵀ (x :: xs))))))⁻¹)
     ⦅7⦆ = ap (λ - → ϕ (λ x → α (extᵀ (- x) (δ x (- x))))) (fext (λ x → fext (λ xs → unitᵀ q' (x :: xs))))
     ⦅8⦆ = ap (λ - → ϕ (λ x → T-sub q x (- x))) I


\end{code}

Last time, in the other file, we tried examples such as tic-tac-toe in
Agda. But this had a number of disadvantages, including inefficiency.

So I think we should actually code the examples is Haskell. This
amounts to translating the parts of this file which are constructions
rather than proofs of correctness.

We don't work with subgames induced by partial paths any more:

\begin{code}

Subpred : {Xt : 𝕋} → (Path Xt → R) → (xs : pPath Xt) → Path (sub𝕋 Xt xs) → R
Subpred {[]} q ⟨⟩ ⟨⟩ = q ⟨⟩
Subpred {X ∷ Xf} q (inl ⟨⟩) (y :: ys) = q (y :: ys)
Subpred {X ∷ Xf} q (inr (x :: xs)) ys = Subpred {Xf x} (subpred q x) xs ys

sub𝓚 : {Xt : 𝕋} → 𝓚 Xt → (xs : pPath Xt) → 𝓚 (sub𝕋 Xt xs)
sub𝓚 {[]} ϕt ⟨⟩ = ⟨⟩
sub𝓚 {X ∷ Xf} ϕt (inl ⟨⟩) = ϕt
sub𝓚 {X ∷ Xf} (ϕ :: ϕf) (inr (x :: xs)) = sub𝓚 {Xf x} (ϕf x) xs

sub𝓙𝓣 : {Xt : 𝕋} → 𝓙𝓣 Xt → (xs : pPath Xt) → 𝓙𝓣 (sub𝕋 Xt xs)
sub𝓙𝓣 {[]} εt ⟨⟩ = ⟨⟩
sub𝓙𝓣 {X ∷ Xf} εt (inl ⟨⟩) = εt
sub𝓙𝓣 {X ∷ Xf} (ε :: εf) (inr (x :: xs)) = sub𝓙𝓣 {Xf x} (εf x) xs

subgame : (G : Game) → pPath (Xt G) → Game
subgame (game Xt q ϕt) xs = game (sub𝕋 Xt xs) (Subpred q xs) (sub𝓚 ϕt xs)

sub-T-Strategy : {Xt : 𝕋} → T-Strategy Xt → (xs : pPath Xt) → T-Strategy (sub𝕋 Xt xs)
sub-T-Strategy {[]} ⟨⟩ ⟨⟩ = ⟨⟩
sub-T-Strategy {X ∷ Xf} (t :: σf) (inl ⟨⟩) = t :: σf
sub-T-Strategy {X ∷ Xf} (t :: σf) (inr (x :: xs)) = sub-T-Strategy {Xf x} (σf x) xs

is-T-sgpe₂ : (G : Game) (σ : T-Strategy (Xt G)) → Type
is-T-sgpe₂ G σ = (xs : pPath (Xt G)) → is-T-pe (subgame G xs) (sub-T-Strategy σ xs)

T-sgpe-equiv : (G : Game) (σ : T-Strategy (Xt G))
             → is-T-sgpe G σ ⇔ is-T-sgpe₂ G σ
T-sgpe-equiv (game Xt q ϕt) σ = I ϕt q σ , II ϕt q σ
 where
  I : {Xt : 𝕋} (ϕt : 𝓚 Xt) (q : Path Xt → R) (σ : T-Strategy Xt)
    → is-T-sgpe (game Xt q ϕt) σ → is-T-sgpe₂ (game Xt q ϕt) σ
  I {[]}     ⟨⟩        q ⟨⟩        ⟨⟩        ⟨⟩              = ⟨⟩
  I {X ∷ Xf} (ϕ :: ϕf) q (t :: σf) (i :: _)  (inl ⟨⟩)        = i
  I {X ∷ Xf} (ϕ :: ϕf) q (t :: σf) (_ :: is) (inr (x :: xs)) =
    I {Xf x} (ϕf x) (subpred q x) (σf x) (is x) xs

  II : {Xt : 𝕋} (ϕt : 𝓚 Xt) (q : Path Xt → R) (σ : T-Strategy Xt)
    → is-T-sgpe₂ (game Xt q ϕt) σ → is-T-sgpe (game Xt q ϕt) σ
  II {[]}     ⟨⟩        q ⟨⟩        j = ⟨⟩
  II {X ∷ Xf} (ϕ :: ϕf) q (t :: σf) j =
     j (inl ⟨⟩) ,
     (λ x → II {Xf x} (ϕf x) (subpred q x) (σf x) (λ xs → j (inr (x :: xs))))

is-in-equilibrium : (G : Game) → 𝓙𝓣 (Xt G) → Type
is-in-equilibrium G εt = (xs : pPath (Xt G))
                       → is-in-head-equilibrium (subgame G xs) (sub𝓙𝓣 εt xs)


main-corollary : ext-const 𝓣
               → (G : Game)
                 (εt : 𝓙𝓣 (Xt G))
               → is-in-equilibrium G εt
main-corollary ext-const G εt xs = head-equilibrium ext-const (subgame G xs) (sub𝓙𝓣 εt xs)

\end{code}
