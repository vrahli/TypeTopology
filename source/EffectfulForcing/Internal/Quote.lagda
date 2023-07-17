Currently porting those:
https://github.com/vrahli/opentt/blob/master/encoding2.lagda
https://github.com/vrahli/opentt/blob/master/encoding3.lagda

\begin{code}

{-# OPTIONS --without-K --exact-split --safe --no-sized-types --no-guardedness --auto-inline #-}

module EffectfulForcing.Internal.Quote where

open import MLTT.Spartan hiding (rec ; _^_ ; _+_)
open import Naturals.Order renaming (_≤ℕ_ to _≤_; _<ℕ_ to _<_)
open import Naturals.Addition
 using (_+_; _+ᴸ_; succ-right; sum-to-zero-gives-zero; addition-commutativity;
        zero-right-neutral; zero-left-neutral; succ-left; addition-associativity)
open import Naturals.Multiplication
 using (_*_; mult-left-id; mult-commutativity; distributivity-mult-over-addition;
        mult-right-id; mult-by-2-is-self-sum)
open import Naturals.Properties using (positive-not-zero; ℕ-cases)
open import EffectfulForcing.MFPSAndVariations.SystemT
 using (type ; ι ; _⇒_ ; 〖_〗)
open import EffectfulForcing.MFPSAndVariations.Combinators
open import Naturals.Division using (_∣_)
open import UF.Base
open import EffectfulForcing.Internal.SystemT
open import EffectfulForcing.Internal.Subst using (dec-type)
open import UF.Base using (transport₂ ; transport₃ ; ap₂ ; ap₃)

\end{code}

Boolean ∧

\begin{code}


_∧_ : 𝟚 → 𝟚 → 𝟚
₁ ∧ b = b
₀ ∧ b = ₀

infixr 6 _∧_

\end{code}

System T with quoting.

\begin{code}

-- The Boolean is to differentiate 2 universe, where ₁ is the universe without quoting, i.e., System T.
data QT' : (b : 𝟚) (Γ : Cxt) (σ : type) → 𝓤₀ ̇  where
 Zero    : {b        : 𝟚} {Γ : Cxt}              → QT' b Γ ι
 Succ    : {b        : 𝟚} {Γ : Cxt}              → QT' b Γ ι → QT' b Γ ι
 Rec     : {b₁ b₂ b₃ : 𝟚} {Γ : Cxt} {σ   : type} → QT' b₁ Γ (ι ⇒ σ ⇒ σ) → QT' b₂ Γ σ → QT' b₃ Γ ι → QT' (b₁ ∧ b₂ ∧ b₃) Γ σ
 ν       : {b        : 𝟚} {Γ : Cxt} {σ   : type} → ∈Cxt σ Γ  → QT' b Γ σ
 ƛ       : {b        : 𝟚} {Γ : Cxt} {σ τ : type} → QT' b (Γ ,, σ) τ → QT' b Γ (σ ⇒ τ)
 _·_     : {b₁ b₂    : 𝟚} {Γ : Cxt} {σ τ : type} → QT' b₂ Γ (σ ⇒ τ) → QT' b₂ Γ σ → QT' (b₁ ∧ b₂) Γ τ
 Quote   : {b        : 𝟚} {Γ : Cxt} {σ   : type} → QT' b Γ σ → QT' ₀ Γ ι
 Unquote : {b        : 𝟚} {Γ : Cxt} {σ   : type} → QT' b Γ ι → QT' ₀ Γ σ

data QT : (Γ : Cxt) (σ : type) → 𝓤₀ ̇  where
 Zero    : {Γ : Cxt}              → QT Γ ι
 Succ    : {Γ : Cxt}              → QT Γ ι → QT Γ ι
 Rec     : {Γ : Cxt} {σ   : type} → QT Γ (ι ⇒ σ ⇒ σ) → QT Γ σ → QT Γ ι → QT Γ σ
 ν       : {Γ : Cxt} {σ   : type} → ∈Cxt σ Γ  → QT Γ σ
 ƛ       : {Γ : Cxt} {σ τ : type} → QT (Γ ,, σ) τ → QT Γ (σ ⇒ τ)
 _·_     : {Γ : Cxt} {σ τ : type} → QT Γ (σ ⇒ τ) → QT Γ σ → QT Γ τ
 Quote   : {Γ : Cxt} {σ   : type} → QT Γ σ → QT Γ ι
 Unquote : {Γ : Cxt} {σ   : type} → QT Γ ι → QT Γ σ

\end{code}

\begin{code}

succ-injective : ∀ {m n} → succ m ＝ succ n → m ＝ n
succ-injective refl = refl

<ℕind2 : (P : ℕ → Set)
       → ((n : ℕ) → ((m : ℕ) → m < n → P m) → P n)
       → (n : ℕ) → P n
<ℕind2 P ind n = course-of-values-induction P ind n

∧＝true→ₗ : {a b : 𝟚} → a ∧ b ＝ ₁ → a ＝ ₁
∧＝true→ₗ {₁} {b} x = refl

∧＝true→ᵣ : {a b : 𝟚} → a ∧ b ＝ ₁ → b ＝ ₁
∧＝true→ᵣ {₁} {b} x = x

∧＝true→1-3 : {a b c : 𝟚} → a ∧ b ∧ c ＝ ₁ → a ＝ ₁
∧＝true→1-3 {a} {b} {c} x = ∧＝true→ₗ {a} {b ∧ c} x

∧＝true→2-3 : {a b c : 𝟚} → a ∧ b ∧ c ＝ ₁ → b ＝ ₁
∧＝true→2-3 {a} {b} {c} x = ∧＝true→ₗ {b} {c} (∧＝true→ᵣ {a} {b ∧ c} x)

∧＝true→3-3 : {a b c : 𝟚} → a ∧ b ∧ c ＝ ₁ → c ＝ ₁
∧＝true→3-3 {a} {b} {c} x = ∧＝true→ᵣ {b} {c} (∧＝true→ᵣ {a} {b ∧ c} x)

\end{code}

The following function is used for the purposes of defining the pairing.

\begin{code}

sum-up-to : ℕ → ℕ
sum-up-to 0        = 0
sum-up-to (succ i) = succ i + sum-up-to i

\end{code}

The pairing function `pair`:

\begin{code}

pair : ℕ × ℕ → ℕ
pair (m , n) = n + sum-up-to (n + m)

\end{code}

Pairing functions for triples and quadruples:

\begin{code}

pair₃ : ℕ × ℕ × ℕ → ℕ
pair₃ (x , y , z) = pair (x , pair (y , z))

pair₄ : ℕ × ℕ × ℕ × ℕ → ℕ
pair₄ (x , y , z , w) = pair (x , pair₃ (y , z , w))

pair₅ : ℕ × ℕ × ℕ × ℕ × ℕ → ℕ
pair₅ (x , y , z , w , v) = pair (x , pair₄ (y , z , w , v))

\end{code}

The unpairing function `unpair`:

\begin{code}

natrec : {A : 𝓤  ̇} → A → (ℕ → A → A) → ℕ → A
natrec z s zero     = z
natrec z s (succ n) = s n (natrec z s n)

𝔥 : ℕ → ℕ → ℕ × ℕ
𝔥 zero     y = succ y , zero
𝔥 (succ x) y = x      , succ y

unpair : ℕ → ℕ × ℕ
unpair zero     = zero , zero
unpair (succ n) = uncurry 𝔥 (unpair n)

\end{code}

First projection for a pair.

\begin{code}

π₁ : ℕ → ℕ
π₁ = pr₁ ∘ unpair

\end{code}

Second projection for a pair.

\begin{code}

π₂ : ℕ → ℕ
π₂ = pr₂ ∘ unpair

\end{code}

The first projection of a triple.

\begin{code}

π3₁ : ℕ → ℕ
π3₁ = π₁

\end{code}

The second projection for a triple.

\begin{code}

π3₂ : (n : ℕ) → ℕ
π3₂ = π₁ ∘ π₂

\end{code}

The third projection from a triple.

\begin{code}

π3₃ : (n : ℕ) → ℕ
π3₃ = π₂ ∘ π₂

\end{code}

The first projection of a quadruple.

\begin{code}

π4₁ : ℕ → ℕ
π4₁ = π₁

\end{code}

The second projection for a quadruple.

\begin{code}

π4₂ : (n : ℕ) → ℕ
π4₂ = π₁ ∘ π₂

\end{code}

The third projection from a quadruple.

\begin{code}

π4₃ : (n : ℕ) → ℕ
π4₃ = π₁ ∘ π₂ ∘ π₂

\end{code}

The fourth projection from a quadruple.

\begin{code}

π4₄ : (n : ℕ) → ℕ
π4₄ = π₂ ∘ π₂ ∘ π₂

\end{code}

\begin{code}

sum-zero-means-both-summands-zero : (n m : ℕ) → n + m ＝ 0 → (n ＝ 0) × (m ＝ 0)
sum-zero-means-both-summands-zero n m h =
 sum-to-zero-gives-zero m n h′ , sum-to-zero-gives-zero n m h
  where
   h′ : m + n ＝ 0
   h′ = m + n ＝⟨ addition-commutativity m n ⟩ n + m ＝⟨ h ⟩ 0 ∎

sum-up-to-zero-means-zero : (n : ℕ) → sum-up-to n ＝ 0 → n ＝ 0
sum-up-to-zero-means-zero zero     refl = refl
sum-up-to-zero-means-zero (succ n) p    =
 pr₁ (sum-zero-means-both-summands-zero (succ n) (sum-up-to n) p)

pair-zero-means-both-components-zero : (m n : ℕ)
                                     → pair (m , n) ＝ 0
                                     → (m ＝ 0) × (n ＝ 0)
pair-zero-means-both-components-zero m n p = † , ‡
 where
  ♣ : sum-up-to (n + m) ＝ 0
  ♣ = pr₂ (sum-zero-means-both-summands-zero n (sum-up-to (n + m)) p)

  ♥ : n + m ＝ 0
  ♥ = sum-up-to-zero-means-zero (n + m) ♣

  ‡ : n ＝ 0
  ‡ = pr₁ (sum-zero-means-both-summands-zero n (sum-up-to (n + m)) p)

  † : m ＝ 0
  † = pr₂ (sum-zero-means-both-summands-zero n m ♥)

pairing-with-0-lemma : (n : ℕ) → pair (n , 0) ＝ sum-up-to n
pairing-with-0-lemma n =
 0 + sum-up-to (0 + n) ＝⟨ zero-left-neutral (sum-up-to (0 + n)) ⟩
 sum-up-to (0 + n)     ＝⟨ ap sum-up-to (zero-left-neutral n)    ⟩
 sum-up-to n            ∎

pairing-with-succ-and-zero-lemma : (n : ℕ)
                                 → pair (succ n , 0) ＝ succ (pair (0 , n))
pairing-with-succ-and-zero-lemma n =
 0 + sum-up-to (0 + succ n) ＝⟨ zero-left-neutral (sum-up-to (0 + succ n))  ⟩
 sum-up-to (0 + succ n)     ＝⟨ ap sum-up-to (zero-left-neutral (succ n))   ⟩
 sum-up-to (succ n)         ＝⟨ refl                                        ⟩
 succ n + sum-up-to n       ＝⟨ succ-left n (sum-up-to n)                   ⟩
 succ (n + sum-up-to n)     ∎

\end{code}

\begin{code}

pairing-succ-lemma : (m n : ℕ) → pair (m , succ n) ＝ succ (pair (succ m , n))
pairing-succ-lemma m n =
 succ n + sum-up-to (succ n + m)        ＝⟨ Ⅰ ⟩
 succ (n + sum-up-to (succ n + m))      ＝⟨ Ⅱ ⟩
 succ (n + sum-up-to (succ (n + m)))    ∎
  where
   Ⅰ = succ-left n (sum-up-to (succ n + m))
   Ⅱ = ap (λ - → succ (n + sum-up-to -)) (succ-left n m)

unpair-pairing-aux : (p : ℕ × ℕ) (n : ℕ) → pair p ＝ n → unpair n ＝ p
unpair-pairing-aux (x , y) 0 h = to-×-＝ † ‡
 where
  † : 0 ＝ x
  † = pr₁ (pair-zero-means-both-components-zero x y h) ⁻¹
  ‡ : 0 ＝ y
  ‡ = pr₂ (pair-zero-means-both-components-zero x y h) ⁻¹

unpair-pairing-aux (x , 0) (succ n) h with x
... | 0 = 𝟘-elim (positive-not-zero n (h ⁻¹))
... | succ x
 with unpair-pairing-aux (0 , x) n
... | z with unpair n
... | 0 , b = ap (λ k → succ k , 0) (pr₂ (from-×-＝' (z (succ-injective ((pairing-with-succ-and-zero-lemma x) ⁻¹ ∙ h)))))
... | succ a , b = 𝟘-elim (positive-not-zero a (pr₁ (from-×-＝' (z (succ-injective (pairing-with-succ-and-zero-lemma x ⁻¹ ∙ h))))))
unpair-pairing-aux (x , succ y) (succ n) h with unpair-pairing-aux (succ x , y) n
... | z with unpair n
... | 0 , b = 𝟘-elim (positive-not-zero x (pr₁ (from-×-＝' (z (succ-injective (pairing-succ-lemma x y ⁻¹ ∙ h)))) ⁻¹))
... | succ a , b =
 to-×-＝
  (succ-injective (pr₁ (from-×-＝' (z (succ-injective ((pairing-succ-lemma x y) ⁻¹ ∙ h))))))
  (ap succ (pr₂ (from-×-＝' (z (succ-injective ((pairing-succ-lemma x y) ⁻¹ ∙ h))))))

unpair-is-retraction-of-pair : (p : ℕ × ℕ) → unpair (pair p) ＝ p
unpair-is-retraction-of-pair p = unpair-pairing-aux p (pair p) refl

π₁-pair : (x₁ x₂ : ℕ) → π₁ (pair (x₁ , x₂)) ＝ x₁
π₁-pair x₁ x₂ = ap pr₁ (unpair-is-retraction-of-pair (x₁ , x₂))

＝pairing→₁ : {x₁ x₂ : ℕ} → x₁ ＝ x₂ → π₁ x₁ ＝ π₁ x₂
＝pairing→₁ {x₁} {x₂} refl = refl

π₂-pair : (x₁ x₂ : ℕ) → π₂ (pair (x₁ , x₂)) ＝ x₂
π₂-pair x₁ x₂ = ap pr₂ (unpair-is-retraction-of-pair (x₁ , x₂))

＝pairing→₂ : {x₁ x₂ : ℕ} → x₁ ＝ x₂ → π₂ x₁ ＝ π₂ x₂
＝pairing→₂ {x₁} {x₂} refl = refl

π3₁-pairing3 : (x₁ x₂ x₃ : ℕ) → π3₁ (pair₃ (x₁ , x₂ , x₃)) ＝ x₁
π3₁-pairing3 x₁ x₂ x₃ = ap pr₁ (unpair-is-retraction-of-pair (x₁ , pair (x₂ , x₃)))

＝π3₁ : {x₁ x₂ : ℕ} → x₁ ＝ x₂ → π3₁ x₁ ＝ π3₁ x₂
＝π3₁ {x₁} {x₂} refl = refl

π3₂-pairing3 : (x₁ x₂ x₃ : ℕ) → π3₂ (pair₃ (x₁ , x₂ , x₃)) ＝ x₂
π3₂-pairing3 x₁ x₂ x₃ =
 ap (λ k → pr₁ (unpair (pr₂ k))) (unpair-is-retraction-of-pair (x₁ , pair (x₂ , x₃)))
 ∙ ap pr₁ (unpair-is-retraction-of-pair (x₂ , x₃))

＝π3₂ : {x₁ x₂ : ℕ} → x₁ ＝ x₂ → π3₂ x₁ ＝ π3₂ x₂
＝π3₂ {x₁} {x₂} refl = refl

pairing3→₃-pairing3 : (x₁ x₂ x₃ : ℕ) → π3₃ (pair₃ (x₁ , x₂ , x₃)) ＝ x₃
pairing3→₃-pairing3 x₁ x₂ x₃ =
 ap (λ k → pr₂ (unpair (pr₂ k))) (unpair-is-retraction-of-pair (x₁ , pair (x₂ , x₃)))
 ∙ ap pr₂ (unpair-is-retraction-of-pair (x₂ , x₃))

＝pairing3→₃ : {x₁ x₂ : ℕ} → x₁ ＝ x₂ → π3₃ x₁ ＝ π3₃ x₂
＝pairing3→₃ {x₁} {x₂} refl = refl

pair-is-injective : (p q : ℕ × ℕ) → pair p ＝ pair q → p ＝ q
pair-is-injective p q h =
 unpair-is-retraction-of-pair p ⁻¹ ∙ † ∙ unpair-is-retraction-of-pair q
  where
   † : unpair (pair p) ＝ unpair (pair q)
   † = ap unpair h

unpair＝ : (n : ℕ) → Σ x ꞉ ℕ , Σ y ꞉ ℕ , unpair n ＝ (x , y)
unpair＝ n with unpair n
... | x , y = x , y , refl

fst-unpair＝ : (n x y : ℕ) → unpair n ＝ (x , y) → pr₁ (unpair n) ＝ x
fst-unpair＝ n x y u = ap pr₁ u

snd-unpair＝ : (n x y : ℕ) → unpair n ＝ (x , y) → pr₂ (unpair n) ＝ y
snd-unpair＝ n x y u = ap pr₂ u

pair-is-retract-of-unpair : (n : ℕ) → pair (unpair n) ＝ n

lemma₁ : (n n₂ : ℕ) → unpair n ＝ (zero , n₂) → pair (unpair (succ n)) ＝ succ n
lemma₁ n n₂ p =
 pair (unpair (succ n))  ＝⟨ ap (λ - → pair (uncurry 𝔥 -)) p      ⟩
 pair (succ n₂ , zero)   ＝⟨ pairing-with-succ-and-zero-lemma n₂  ⟩
 succ (pair (zero , n₂)) ＝⟨ ap (succ ∘ pair) p ⁻¹                ⟩
 succ (pair (unpair n))  ＝⟨ ap succ (pair-is-retract-of-unpair n) ⟩
 succ n                  ∎

lemma₂ : (n n₁ n₂ : ℕ)
       → unpair n ＝ (succ n₁ , n₂)
       → pair (unpair (succ n)) ＝ succ n
lemma₂ n n₁ n₂ p =
 pair (unpair (succ n))      ＝⟨ ap (λ - → pair (uncurry 𝔥 -)) p       ⟩
 pair (n₁ , succ n₂)         ＝⟨ pairing-succ-lemma n₁ n₂              ⟩
 succ (pair (succ n₁ , n₂))  ＝⟨ ap (succ ∘ pair) (p ⁻¹)               ⟩
 succ (pair (unpair n))      ＝⟨ ap succ (pair-is-retract-of-unpair n) ⟩
 succ n                      ∎

pair-is-retract-of-unpair zero = refl
pair-is-retract-of-unpair (succ n) with unpair＝ n
pair-is-retract-of-unpair (succ n) | zero    , n₂ , p = lemma₁ n n₂ p
pair-is-retract-of-unpair (succ n) | succ n₁ , n₂ , p = lemma₂ n n₁ n₂ p

unpair-inj : (n m : ℕ) → unpair n ＝ unpair m → n ＝ m
unpair-inj n m h =
 pair-is-retract-of-unpair n ⁻¹ ∙ † ∙ (pair-is-retract-of-unpair m)
  where
   † : pair (unpair n) ＝ pair (unpair m)
   † = ap pair h

+assoc-aux : (m n : ℕ) → m + m + (n + n) ＝ n + m + (n + m)
+assoc-aux m n =
 (m + m) + (n + n)   ＝⟨ addition-associativity (m + m) n n ⁻¹        ⟩
 ((m + m) + n) + n   ＝⟨ ap (_+ n) (addition-commutativity (m + m) n) ⟩
 (n + (m + m)) + n   ＝⟨ ap (_+ n) (addition-associativity n m m ⁻¹)  ⟩
 ((n + m) + m) + n   ＝⟨ addition-associativity (n + m) m n           ⟩
 (n + m) + (m + n)   ＝⟨ ap ((n + m) +_) (addition-commutativity m n) ⟩
 n + m + (n + m)     ∎

\end{code}

\begin{code}

pairing-spec-aux : (n x y : ℕ) → n ＝ y + x → pair (x , y) * 2 ＝ y * 2 + n * succ n
pairing-spec-aux = {!!}

pairing-spec : (x y : ℕ) → pair (x , y) * 2 ＝ y * 2 + (y + x) * succ (y + x)
pairing-spec x y = pairing-spec-aux (y + x) x y refl

→＝+ₗ : {a b c : ℕ} → a ＝ b → a + c ＝ b + c
→＝+ₗ {a} {b} {c} refl = refl

m≤m*m : (n : ℕ) → n ≤ n * n
m≤m*m zero     = ⋆
m≤m*m (succ m) =
 ≤-trans
  (succ m)
  (1 + 1 * m)
  (succ m * succ m)
  †
  (multiplication-preserves-order 1 (succ m) (succ m) ⋆)
   where
    † : succ m ≤ 1 + 1 * m
    † = transport
         (λ - → succ m ≤ (1 + -))
         (mult-left-id m ⁻¹)
         (transport
           (λ - → succ m ≤ -)
           (addition-commutativity m 1)
           (≤-refl m))

\end{code}

\begin{code}

squaring-lemma : (n : ℕ) → succ n * succ n ＝ (n * n) + 2 * n + 1
squaring-lemma n =
 (n + 1) * (n + 1)                ＝⟨ Ⅰ ⟩
 ((n + 1) * n) + (n + 1) * 1      ＝⟨ Ⅱ ⟩
 n * (n + 1) + (n + 1) * 1        ＝⟨ Ⅲ ⟩
 (n * n) + (n * 1) + (n + 1) * 1  ＝⟨ Ⅳ ⟩
 (n * n) + n + (n + 1) * 1        ＝⟨ Ⅴ ⟩
 (n * n) + n + (n + 1)            ＝⟨ Ⅵ ⟩
 (n * n) + (n + (n + 1))          ＝⟨ Ⅶ ⟩
 (n * n) + (n + n) + 1            ＝⟨ Ⅷ ⟩
 (n * n) + (2 * n) + 1              ∎
  where
   Ⅰ = distributivity-mult-over-addition (n + 1) n 1
   Ⅱ = ap (λ - → - + (n + 1) * 1) (mult-commutativity (n + 1) n)
   Ⅲ = ap (λ - → - + (n + 1) * 1) (distributivity-mult-over-addition n n 1)
   Ⅳ = ap (λ - → (n * n) + - + (n + 1) * 1) (mult-right-id n)
   Ⅴ = ap (λ - → (n * n) + n + -) (mult-right-id (n + 1))
   Ⅵ = addition-associativity (n * n) n (n + 1)
   Ⅶ = ap ((n * n) +_) (addition-associativity n n 1)
   Ⅷ = ap (λ - → (n * n) + - + 1) (mult-by-2-is-self-sum n ⁻¹)

division-by-2-lemma : (n : ℕ) → 2 ∣ (n + n * n)
division-by-2-lemma zero     = 0 , refl
division-by-2-lemma (succ n) = k + n + 1 , †
 where
  IH : 2 ∣ n + n * n
  IH = division-by-2-lemma n

  k = pr₁ IH

  † : 2 * (k + n + 1) ＝ succ n + succ n * succ n
  † = 2 * (k + n + 1)                ＝⟨ {!squaring-lemma!} ⟩
      (2 * k) + (2 * n) + 2          ＝⟨ {!!} ⟩
      (n + n * n) + (2 * n) + 2      ＝⟨ {!!} ⟩
      (n + 1) + (n * n + 2 * n + 1)  ＝⟨ ap (λ - → succ n + -) (squaring-lemma n ⁻¹) ⟩
      succ n + (succ n * succ n)     ∎

{--
2∣+* (suc x)
  rewrite *-suc x x
        | +-suc x (x + (x + x * x))
        | sym (+-assoc x x (x + x * x))
  with 2∣+* x
... | divides z q rewrite q = divides (1 + x + z) (→s＝s (→s＝s h1))
  where
    h1 : x + x + z * 2 ＝ (x + z) * 2
    h1 rewrite *-comm (x + z) 2
             | *-comm z 2
             | +0 z
             | +0 (x + z)
             | +-comm x z = +assoc-aux x z
--}

unpair≤ : (n : ℕ)
        → pr₁ (unpair n) ≤ n
        × pr₂ (unpair n) ≤ n
unpair≤ 0 = ≤-refl 0 , ≤-refl 0
unpair≤ (succ n) = {!!}
{-with unpairing≡ n
... | suc x , y , p rewrite p =
  ≤-trans (m<n⇒m≤1+n (≡→≤ (suc x) (proj₁ (unpairing n)) (sym (fst-unpairing≡ n (suc x) y p))))
          (_≤_.s≤s (fst (unpairing≤ n))) ,
  _≤_.s≤s (≤-trans (≡→≤ y (snd (unpairing n)) (sym (snd-unpairing≡ n (suc x) y p))) (snd (unpairing≤ n)))
... | 0 , y , p rewrite p | sym (snd-unpairing≡ n 0 y p) = _≤_.s≤s (snd (unpairing≤ n)) , _≤_.z≤n
-}

π₁≤ : (n : ℕ) → π₁ n ≤ n
π₁≤ n = pr₁ (unpair≤ n)

π₂≤ : (n : ℕ) → π₂ n ≤ n
π₂≤ n = pr₂ (unpair≤ n)

π3₁≤ : (n : ℕ) → π3₁ n ≤ n
π3₁≤ n = pr₁ (unpair≤ n)

π3₂≤ : (n : ℕ) → π3₂ n ≤ n
π3₂≤ n = ≤-trans (π3₂ n) (π₂ n) n (π₁≤ (π₂ n)) (π₂≤ n)

π3₃≤ : (n : ℕ) → π3₃ n ≤ n
π3₃≤ n = ≤-trans (π3₃ n) (π₂ n) n (π₂≤ (π₂ n)) (π₂≤ n)

π4₁≤ : (n : ℕ) → π4₁ n ≤ n
π4₁≤ n = pr₁ (unpair≤ n)

π4₂≤ : (n : ℕ) → π4₂ n ≤ n
π4₂≤ n = ≤-trans (π4₂ n) (π₂ n) n (π₁≤ (π₂ n)) (π₂≤ n)

π4₃≤ : (n : ℕ) → π4₃ n ≤ n
π4₃≤ n = ≤-trans (π4₃ n) (π₂ n) n (≤-trans (π4₃ n) (π₂ (π₂ n)) (π₂ n) (π₁≤ (π₂ (π₂ n))) (π₂≤ (π₂ n))) (π₂≤ n)

π4₄≤ : (n : ℕ) → π4₄ n ≤ n
π4₄≤ n = ≤-trans (π4₄ n) (π₂ n) n (≤-trans (π4₄ n) (π₂ (π₂ n)) (π₂ n) (π₂≤ (π₂ (π₂ n))) (π₂≤ (π₂ n))) (π₂≤ n)

\end{code}

{--

{-
pairing-spec2 : (x y : ℕ) → pair (x , y) ＝ y + (y + x) * suc (y + x) / 2
pairing-spec2 x y = trans (sym (m*n/n＝m (pairing (x , y)) 2)) (trans h1 h2)
  where
    h1 : (pairing (x , y) * 2) / 2 ＝ (y * 2 + (y + x) * suc (y + x)) / 2
    h1 rewrite sym (pairing-spec x y) = refl

    h3 : (y * 2 / 2) + ((y + x) + (y + x) * (y + x)) / 2 ＝ y + ((y + x) + (y + x) * (y + x)) / 2
    h3 = →＝+ₗ {y * 2 / 2} {y} {((y + x) + (y + x) * (y + x)) / 2} (m*n/n＝m y 2)

    h2 : (y * 2 + (y + x) * suc (y + x)) / 2 ＝ y + (y + x) * suc (y + x) / 2
    h2 rewrite *-suc (y + x) (y + x)
             | +-distrib-/-∣ʳ {y * 2} ((y + x) + (y + x) * (y + x)) {2} (2∣+* (y + x)) = h3
-}

{-
≤/2 : (y : ℕ) → y ≤ y * suc y / 2
≤/2 y rewrite *-suc y y = ≤-trans h1 h2
  where
    h0 : y ＝ y * 2 / 2
    h0 = sym (m*n/n＝m y 2)

    h1 : y ≤ y * 2 / 2
    h1 rewrite sym h0 = ≤-refl

    h3 : y * 2 ≤ y + y * y
    h3 rewrite *-suc y 1 | *-suc y 0 | *-zeroʳ y | +0 y = +-mono-≤ {y} {y} {y} {y * y} ≤-refl (m≤m*m y)

    h2 : y * 2 / 2 ≤ (y + (y * y)) / 2
    h2 = /-mono-≤ {y * 2} {y + (y * y)} {2} h3 ≤-refl
-}

{-
→≤/2 : (x y : ℕ) → x ≤ y → x ≤ y * suc y / 2
→≤/2 x y h = ≤-trans h (≤/2 y)
-}

{-
pairing-non-dec : (x y : ℕ) → y + x ≤ pair (x , y)
pairing-non-dec x y
  rewrite pairing-spec2 x y
  = +-mono-≤ {y} {y} {x} {(y + x) * suc (y + x) / 2} ≤-refl h1
  where
    h1 : x ≤ (y + x) * suc (y + x) / 2
    h1 = →≤/2 x (y + x) (m≤n+m x y)
-}

\end{code}

From the standard library

\begin{code}

data Reflects {p} (P : Set p) : 𝟚 → Set p where
  ofʸ : ( p :   P) → Reflects P ₁
  ofⁿ : (¬p : ¬ P) → Reflects P ₀

record Dec {p} (P : Set p) : Set p where
  constructor _because_
  field
    does  : 𝟚
    proof : Reflects P does

isYes : {P : Type} → Dec P → 𝟚
isYes (₁ because _) = ₁
isYes (₀ because _) = ₀

isYes≗does : {P : Type} (P? : Dec P) → isYes P? ＝ Dec.does P?
isYes≗does (₁ because _) = refl
isYes≗does (₀ because _) = refl

-- The traditional name for isYes is ⌊_⌋, indicating the stripping of evidence.
⌊_⌋ = isYes

not : 𝟚 → 𝟚
not ₁ = ₀
not ₀ = ₁

isNo : {P : Type} → Dec P → 𝟚
isNo = not ∘ isYes

TRUE : 𝟚 → Type
TRUE ₁ = 𝟙
TRUE ₀ = 𝟘

True : {P : Type} → Dec P → Set
True Q = TRUE (isYes Q)

False : {P : Type} → Dec P → Set
False Q = TRUE (isNo Q)

infix 4 _≟_
_≟_ : (x y : ℕ) → Dec (x ＝ y)
zero ≟ zero     = ₁ because ofʸ refl
zero ≟ succ n   = ₀ because ofⁿ (λ ())
succ m ≟ zero   = ₀ because ofⁿ (λ ())
succ m ≟ succ n with m ≟ n
... | ₁ because ofʸ p = ₁ because (ofʸ (ap succ p))
... | ₀ because ofⁿ ¬p = ₀ because (ofⁿ (λ p → ¬p (succ-injective p)))

mod-helper : (k m n j : ℕ) → ℕ
mod-helper k m zero     j        = k
mod-helper k m (succ n) 0        = mod-helper 0        m n m
mod-helper k m (succ n) (succ j) = mod-helper (succ k) m n j

div-helper : (k m n j : ℕ) → ℕ
div-helper k m zero     j        = k
div-helper k m (succ n) zero     = div-helper (succ k) m n m
div-helper k m (succ n) (succ j) = div-helper k        m n j

infixl 7 _%_
_%_ : (dividend divisor : ℕ) {≢0 : False (divisor ≟ 0)} → ℕ
m % (succ n) = mod-helper 0 n m n

infixl 7 _/_
_/_ : (dividend divisor : ℕ) {≢0 : False (divisor ≟ 0)} → ℕ
m / (succ n) = div-helper 0 n m n

infixl 6 _-_
_-_ : ℕ → ℕ → ℕ
n     - zero = n
zero  - succ m = zero
succ n - succ m = n - m

<-transʳ : {a b c : ℕ} → a ≤ b → b < c → a < c
<-transʳ {a} {b} {c} h1 h2 = ≤-trans (succ a) (succ b) c h1 h2

\end{code}

From OpenTT

\begin{code}

comp-ind-ℕ-aux : (P : ℕ → Set)
               → ((n : ℕ) → ((m : ℕ) → m < n → P m) → P n)
               → (n m : ℕ) → m ≤ n → P m
comp-ind-ℕ-aux P ind 0 0 z = ind 0 (λ m ())
comp-ind-ℕ-aux P ind (succ n) 0 z = ind 0 (λ m ())
comp-ind-ℕ-aux P ind (succ n) (succ m) z =
  ind (succ m) (λ k h → comp-ind-ℕ-aux P ind n k (≤-trans k m n (succ-order-injective k m h) z))

comp-ind-ℕ : (P : ℕ → Set)
          → ((n : ℕ) → ((m : ℕ) → m < n → P m) → P n)
          → (n : ℕ) → P n
comp-ind-ℕ P ind n = comp-ind-ℕ-aux P ind n n (≤-refl n)

succ-/≤ : (n m k : ℕ) → ¬ (n ＝ 0) → succ ((n - m) / (succ k)) ≤ n
succ-/≤ n m k ¬n0 = {!!} --≤-trans (suc-/m n m) (suc/≤ n d0)

{-
[m+kn]%n≡m%n : ∀ m k n → (m + k * (succ n)) % succ n ＝ m % succ n
[m+kn]%n≡m%n m zero    n-1 = ap (_% succ n-1) {!!} --(+-identityʳ m)
[m+kn]%n≡m%n m (succ k) n-1 = {!!} {-
  (m + (n + k * n)) % n ＝⟨ ap (_% n) ? {-((+-assoc m n (k * n)) ⁻¹)-} ⟩
  (m + n + k * n)   % n ＝⟨ ? {-[m+kn]%n≡m%n (m + n) k n-1-} ⟩
  (m + n)           % n ＝⟨ ? {-[m+n]%n≡m%n m n-1-} ⟩
  m                 % n ∎
  where n = succ n-1
-}
-}

*%≡k : (k x n : ℕ) → k ≤ n → (k +ᴸ (x * (succ n))) % (succ n) ＝ k
*%≡k k x n cond = {!!} --([m+kn]%n≡m%n k x n) ∙ {!!} -- (m≤n⇒m%n≡m (s≤s-inj cond))

m*sn/sn≡m : (m n : ℕ) → (m * succ n / succ n) ＝ m
m*sn/sn≡m m n = {!!} --m*n/n≡m m (suc n)

\end{code}

The encoding function `encode`:

\begin{code}

#terms : ℕ
#terms = 8

#terms-1 : ℕ
#terms-1 = #terms - 1

#types : ℕ
#types = 2

#types-1 : ℕ
#types-1 = #types - 1

#cxts : ℕ
#cxts = 2

#cxts-1 : ℕ
#cxts-1 = #cxts - 1

encode-type : type → ℕ
encode-type ι       = 0
encode-type (σ ⇒ τ) = 1 +ᴸ (pair (encode-type σ , encode-type τ) * #types)

-- d is n % #types, i.e. (succ z) % #types
decode-type-aux-aux : (d : ℕ) (z : ℕ) → ((m : ℕ) → m < succ z → type) → type
decode-type-aux-aux 0 z ind = ι
decode-type-aux-aux (succ _) z ind = ind x₁ cx₁ ⇒ ind x₂ cx₂
 where
  n : ℕ
  n = succ z

  m : ℕ
  m = (n - 1) / #types

  x₁ : ℕ
  x₁ = π₁ m

  cx₁ : x₁ < n
  cx₁ = <-transʳ {x₁} {m} {n} (π₁≤ m) (succ-/≤ n 1 #types-1 (λ ()))

  x₂ : ℕ
  x₂ = π₂ m

  cx₂ : x₂ < n
  cx₂ = <-transʳ {x₂} {m} {n} (π₂≤ m) (succ-/≤ n 1 #types-1 (λ ()))

decode-type-aux : (n : ℕ) → ((m : ℕ) → m < n → type) → type
decode-type-aux 0 ind = ι
decode-type-aux n@(succ z) ind = decode-type-aux-aux (n % #types) z ind

decode-type : ℕ → type
decode-type = comp-ind-ℕ (λ _ → type) decode-type-aux

＝decode-type-aux-aux : (d : ℕ) (z : ℕ) → (f g : (m : ℕ) → m < succ z → type)
                      → ((m : ℕ) (p q : m < succ z) → f m p ＝ g m q)
                      → decode-type-aux-aux d z f ＝ decode-type-aux-aux d z g
＝decode-type-aux-aux zero z f g i = refl
＝decode-type-aux-aux (succ d) z f g i = ap₂ _⇒_ (i _ _ _) (i _ _ _)

＝decode-type-aux : (z : ℕ) → (f g : (m : ℕ) → m < z → type)
                  → ((m : ℕ) (p q : m < z) → f m p ＝ g m q)
                  → decode-type-aux z f ＝ decode-type-aux z g
＝decode-type-aux 0 f g i = refl
＝decode-type-aux (succ w) f g i = ＝decode-type-aux-aux _ _ _ _ i

＝comp-ind-ℕ-aux : (P : ℕ → Set) (ind : (n : ℕ) → ((m : ℕ) → m < n → P m) → P n) (n1 n2 m : ℕ) (p : m ≤ n1) (q : m ≤ n2)
                 → ((n : ℕ) (i j : (m : ℕ) → m < n → P m) → ((m : ℕ) (u v : m < n) → i m u ＝ j m v) → ind n i ＝ ind n j)
                 → comp-ind-ℕ-aux P ind n1 m p ＝ comp-ind-ℕ-aux P ind n2 m q
＝comp-ind-ℕ-aux P ind zero zero zero p q ii = refl
＝comp-ind-ℕ-aux P ind zero (succ n2) zero p q ii = refl
＝comp-ind-ℕ-aux P ind (succ n1) zero zero p q ii = refl
＝comp-ind-ℕ-aux P ind (succ n1) (succ n2) zero p q ii = refl
＝comp-ind-ℕ-aux P ind (succ n1) (succ n2) (succ m) p q ii =
  ii _ _ _ (λ k u v → ＝comp-ind-ℕ-aux P ind n1 n2 k
                                       (≤-trans k m n1 (succ-order-injective k m u) p)
                                       (≤-trans k m n2 (succ-order-injective k m v) q)
                                       ii)

comp-ind-ℕ-aux≡decode-type : {n m : ℕ} (p : m ≤ n)
                            → comp-ind-ℕ-aux (λ _ → type) decode-type-aux n m p ＝ decode-type m
comp-ind-ℕ-aux≡decode-type {zero} {zero} p = refl
comp-ind-ℕ-aux≡decode-type {succ n} {zero} p = refl
comp-ind-ℕ-aux≡decode-type {succ n} {succ m} p =
 decode-type-aux-aux (succ m % #types) m f
 ＝⟨ ＝decode-type-aux-aux (succ m % #types) m f g e ⟩ decode-type-aux-aux (succ m % #types) m g
 ＝⟨ refl ⟩ comp-ind-ℕ-aux (λ _ → type) decode-type-aux (succ m) (succ m) (≤-refl (succ m)) ∎
 where
  f = λ k h → comp-ind-ℕ-aux (λ _ → type) decode-type-aux n k (≤-trans k m n h p)
  g = λ k h → comp-ind-ℕ-aux (λ _ → type) decode-type-aux m k (≤-trans k m m (succ-order-injective k m h) (≤-refl (succ m)))

  e : (k : ℕ) (q1 q2 : k < succ m) → f k q1 ＝ g k q2
  e k q1 q2 = ＝comp-ind-ℕ-aux (λ _ → type) decode-type-aux n m k _ _
                               (λ z i j ii → ＝decode-type-aux z _ _ ii)

decode-is-retraction-of-encode-⇒ : (σ τ : type)
                                 → decode-type (encode-type σ) ＝ σ
                                 → decode-type (encode-type τ) ＝ τ
                                 → decode-type (1 +ᴸ (pair (encode-type σ , encode-type τ) * #types)) ＝ σ ⇒ τ
decode-is-retraction-of-encode-⇒ σ τ hσ hτ =
 decode-type (1 +ᴸ (pair (Eσ , Eτ) * #types))                  ＝⟨ refl ⟩
 comp-ind-ℕ-aux (λ _ → type) decode-type-aux p1 p1 (≤-refl p1) ＝⟨ refl ⟩
 decode-type-aux p1 r                                          ＝⟨ refl ⟩
 decode-type-aux-aux (p1 % #types) p r                         ＝⟨ ap (λ k → decode-type-aux-aux k p r) (*%≡k 1 (pair (Eσ , Eτ)) 1 ⋆) ⟩
 decode-type-aux-aux 1 p r                                     ＝⟨ refl ⟩
 r (π₁ (p / #types)) cx₁ ⇒ r (π₂ (p / #types)) cx₂             ＝⟨ ap₂ _⇒_ (comp-ind-ℕ-aux≡decode-type {p} {π₁ (p / #types)} (≤-trans (π₁ (p / #types)) p p (succ-order-injective (π₁ (p / #types)) p cx₁) (≤-refl p1))) (comp-ind-ℕ-aux≡decode-type {p} {π₂ (p / #types)} (≤-trans (π₂ (p / #types)) p p (succ-order-injective (π₂ (p / #types)) p cx₂) (≤-refl p))) ⟩
 decode-type (π₁ (p / #types)) ⇒ decode-type (π₂ (p / #types)) ＝⟨ ap₂ _⇒_ (ap (λ k → decode-type (π₁ k)) ((m*sn/sn≡m pE #types-1))) (ap (λ k → decode-type (π₂ k)) ((m*sn/sn≡m pE #types-1))) ⟩
 decode-type (π₁ pE) ⇒ decode-type (π₂ pE)                     ＝⟨ ap₂ _⇒_ (ap decode-type (π₁-pair Eσ Eτ)) (ap decode-type (π₂-pair Eσ Eτ)) ⟩
 decode-type Eσ ⇒ decode-type Eτ                               ＝⟨ ap₂ _⇒_ hσ hτ ⟩
 σ ⇒ τ ∎
 where
  Eσ : ℕ
  Eσ = encode-type σ

  Eτ : ℕ
  Eτ = encode-type τ

  pE : ℕ
  pE = pair (Eσ , Eτ)

  p : ℕ
  p = pE * #types

  p1 : ℕ
  p1 = 1 +ᴸ p

  r = λ k h → comp-ind-ℕ-aux (λ _ → type) decode-type-aux p k (≤-trans k p p (succ-order-injective k p h) (≤-refl p1))

  cx₁ : π₁ (p / #types) < p1
  cx₁ = <-transʳ {π₁ (p / #types)} {p / #types} {p1} (π₁≤ (p / #types)) (succ-/≤ p1 1 #types-1 (λ ()))

  cx₂ : π₂ (p / #types) < p1
  cx₂ = <-transʳ {π₂ (p / #types)} {p / #types} {p1} (π₂≤ (p / #types)) (succ-/≤ p1 1 #types-1 (λ ()))

decode-type-is-retraction-of-encode-type : (σ : type) → decode-type (encode-type σ) ＝ σ
decode-type-is-retraction-of-encode-type ι = refl
decode-type-is-retraction-of-encode-type (σ ⇒ τ) =
 decode-is-retraction-of-encode-⇒
   σ τ
   (decode-type-is-retraction-of-encode-type σ)
   (decode-type-is-retraction-of-encode-type τ)

encode-Cxt : Cxt → ℕ
encode-Cxt 〈〉       = 0
encode-Cxt (Γ ,, σ) = 1 +ᴸ pair (encode-Cxt Γ , encode-type σ) * #cxts

decode-Cxt-aux : (n : ℕ) → ((m : ℕ) → m < n → Cxt) → Cxt
decode-Cxt-aux 0 ind = 〈〉
decode-Cxt-aux n@(succ z) ind with n % #cxts
... | 0 = 〈〉
... | succ _ = ind x₁ cx₁ ,, decode-type (π₂ m)
  where
    m : ℕ
    m = (n - 1) / #cxts

    x₁ : ℕ
    x₁ = π₁ m

    cx₁ : x₁ < n
    cx₁ = <-transʳ {x₁} {m} {n} (π₁≤ m) (succ-/≤ n 1 #cxts-1 (λ ()))

decode-Cxt : ℕ → Cxt
decode-Cxt = comp-ind-ℕ (λ _ → Cxt) decode-Cxt-aux

encode : {Γ : Cxt} {σ : type} → QT Γ σ → ℕ
encode {Γ} {ι} Zero          = 0
encode {Γ} {ι} (Succ t)      = 1 +ᴸ encode t * #terms
encode {Γ} {σ} (Rec t t₁ t₂) = 2 +ᴸ pair₄ (encode-type σ , encode t , encode t₁ , encode t₂) * #terms
encode {Γ} {σ} (ν x)         = 3 +ᴸ pair  (encode-type σ , {!!}) * #terms
encode {Γ} {σ ⇒ τ} (ƛ t)     = 4 +ᴸ pair₃ (encode-type σ , encode-type τ , encode t) * #terms
encode {Γ} {σ} (_·_ {Γ} {τ} {σ} t t₁) = 5 +ᴸ pair₄ (encode-type σ , encode-type τ , encode t , encode t₁) * #terms
encode {Γ} {ι} (Quote t)     = 6 +ᴸ encode t * #terms
encode {Γ} {σ} (Unquote t)   = 7 +ᴸ pair  (encode-type σ , encode t) * #terms

record Tσ (Γ : Cxt) : 𝓤₀ ̇  where
 constructor tσ
 field
  Tσ-σ : type
  Tσ-t : T Γ Tσ-σ

-- default term of type σ
σ→T : (Γ : Cxt) (σ : type) → T Γ σ
σ→T Γ ι = Zero
σ→T Γ (σ ⇒ τ) = ƛ (σ→T (Γ ,, σ) τ)

→Tσ : (Γ : Cxt) → Tσ Γ
→Tσ Γ = tσ ι (σ→T Γ ι)

Tσ→T : {Γ : Cxt} (σ : type) (t : Tσ Γ) → T Γ σ
Tσ→T {Γ} σ (tσ τ t) with dec-type σ τ
... | inl refl = t
... | inr _ = σ→T Γ σ

-- d is n % #terms, i.e. (succ z) % #terms
decode-aux-aux : (d : ℕ) (z : ℕ) → ((m : ℕ) → m < succ z → {Γ : Cxt} → Tσ Γ) → {Γ : Cxt} → Tσ Γ
-- Zero
decode-aux-aux 0 z ind {Γ} = tσ ι Zero
-- Succ
decode-aux-aux k@1 z ind {Γ} = tσ ι (Succ (Tσ→T ι t))
 where
  n : ℕ
  n = succ z

  m : ℕ
  m = (n - k) / #terms

  t : Tσ Γ
  t = ind m (succ-/≤ n k #terms-1 (λ ())) {Γ}
-- Rec
decode-aux-aux k@2 z ind {Γ} = tσ σ (Rec (Tσ→T (ι ⇒ σ ⇒ σ) t₁) (Tσ→T σ t₂) (Tσ→T ι t₃))
 where
  n : ℕ
  n = succ z

  m : ℕ
  m = (n - k) / #terms

  x₁ : ℕ
  x₁ = π4₁ m

  -- no need
  --cx₁ : x₁ < n
  --cx₁ = <-transʳ {x₁} {m} {n} (π4₁≤ m) (succ-/≤ n k #terms-1 (λ ()))

  σ : type
  σ = decode-type x₁

  x₂ : ℕ
  x₂ = π4₂ m

  cx₂ : x₂ < n
  cx₂ = <-transʳ {x₂} {m} {n} (π4₂≤ m) (succ-/≤ n k #terms-1 (λ ()))

  t₁ : Tσ Γ
  t₁ = ind x₂ cx₂ {Γ}

  x₃ : ℕ
  x₃ = π4₃ m

  cx₃ : x₃ < n
  cx₃ = <-transʳ {x₃} {m} {n} (π4₃≤ m) (succ-/≤ n k #terms-1 (λ ()))

  t₂ : Tσ Γ
  t₂ = ind x₃ cx₃ {Γ}

  x₄ : ℕ
  x₄ = π4₄ m

  cx₄ : x₄ < n
  cx₄ = <-transʳ {x₄} {m} {n} (π4₄≤ m) (succ-/≤ n k #terms-1 (λ ()))

  t₃ : Tσ Γ
  t₃ = ind x₄ cx₄ {Γ}
-- ν
decode-aux-aux 3 z ind {Γ} = {!!}
-- ƛ
decode-aux-aux k@4 z ind {Γ} = tσ (σ ⇒ τ) (ƛ (Tσ→T τ t₂))
 where
  n : ℕ
  n = succ z

  m : ℕ
  m = (n - k) / #terms

  x₁ : ℕ
  x₁ = π3₁ m

  --cx₁ : x₁ < n
  --cx₁ = <-transʳ {x₁} {m} {n} (π3₁≤ m) (succ-/≤ n k #terms-1 (λ ()))

  σ : type
  σ = decode-type x₁

  x₂ : ℕ
  x₂ = π3₂ m

  --cx₂ : x₂ < n
  --cx₂ = <-transʳ {x₂} {m} {n} (π3₂≤ m) (succ-/≤ n k #terms-1 (λ ()))

  τ : type
  τ = decode-type x₂

  x₃ : ℕ
  x₃ = π3₃ m

  cx₃ : x₃ < n
  cx₃ = <-transʳ {x₃} {m} {n} (π3₃≤ m) (succ-/≤ n k #terms-1 (λ ()))

  t₂ : Tσ (Γ ,, σ)
  t₂ = ind x₃ cx₃ {Γ ,, σ}
-- ·
decode-aux-aux k@5 z ind {Γ} = tσ σ (Tσ→T (τ ⇒ σ) t₁ · Tσ→T τ t₂)
 where
  n : ℕ
  n = succ z

  m : ℕ
  m = (n - k) / #terms

  x₁ : ℕ
  x₁ = π3₁ m

  -- no need
  --cx₁ : x₁ < n
  --cx₁ = <-transʳ {x₁} {m} {n} (π4₁≤ m) (succ-/≤ n k #terms-1 (λ ()))

  σ : type -- return type
  σ = decode-type x₁

  x₂ : ℕ
  x₂ = π4₂ m

  -- no need
  --cx₂ : x₁ < n
  --cx₂ = <-transʳ {x₂} {m} {n} (π4₂≤ m) (succ-/≤ n k #terms-1 (λ ()))

  τ : type -- type of the argument
  τ = decode-type x₂

  x₃ : ℕ
  x₃ = π4₃ m

  cx₃ : x₃ < n
  cx₃ = <-transʳ {x₃} {m} {n} (π4₃≤ m) (succ-/≤ n k #terms-1 (λ ()))

  t₁ : Tσ Γ
  t₁ = ind x₃ cx₃ {Γ}

  x₄ : ℕ
  x₄ = π4₄ m

  cx₄ : x₄ < n
  cx₄ = <-transʳ {x₄} {m} {n} (π4₄≤ m) (succ-/≤ n k #terms-1 (λ ()))

  t₂ : Tσ Γ
  t₂ = ind x₄ cx₄ {Γ}
-- default
decode-aux-aux (succ (succ (succ (succ (succ (succ _)))))) z ind {Γ} = →Tσ Γ

decode-aux : (n : ℕ) → ((m : ℕ) → m < n → {Γ : Cxt} → Tσ Γ) → {Γ : Cxt} → Tσ Γ
decode-aux 0 ind {Γ} = tσ ι Zero
decode-aux n@(succ z) ind {Γ} = decode-aux-aux (n % #terms) z ind

decode : ℕ → {Γ : Cxt} → Tσ Γ
decode = comp-ind-ℕ (λ _ → {Γ : Cxt} → Tσ Γ) decode-aux

Q⟦_⟧ : {Γ : Cxt} {σ : type} → QT Γ σ → 【 Γ 】 → 〖 σ 〗
Q⟦ Zero      ⟧  _ = 0
Q⟦ Succ t    ⟧ xs = succ (Q⟦ t ⟧ xs)
Q⟦ Rec f g t ⟧ xs = rec (Q⟦ f ⟧ xs) (Q⟦ g ⟧ xs) (Q⟦ t ⟧ xs)
Q⟦ ν i       ⟧ xs = xs i
Q⟦ ƛ t       ⟧ xs = λ x → Q⟦ t ⟧ (xs ‚ x)
Q⟦ t · u     ⟧ xs = Q⟦ t ⟧ xs (Q⟦ u ⟧ xs)
Q⟦ Quote t   ⟧ xs = encode t
Q⟦_⟧ {Γ} {σ} (Unquote t) xs = c
 where
  n : ℕ
  n = Q⟦ t ⟧ xs

  s : Tσ Γ
  s = decode n {Γ}

  -- One problem is that σ might not be t's type:
  c : 〖 σ 〗
  c = ⟦ Tσ→T σ s ⟧ xs -- This wouldn't terminate if decode was returning a QT
                      -- Should we instead allow quoting & unquoting T terms?

\end{code}
