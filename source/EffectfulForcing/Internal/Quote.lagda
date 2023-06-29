Currently porting those:
https://github.com/vrahli/opentt/blob/master/encoding2.lagda
https://github.com/vrahli/opentt/blob/master/encoding3.lagda

\begin{code}

{-# OPTIONS --without-K --exact-split --safe --no-sized-types --no-guardedness --auto-inline #-}

module EffectfulForcing.Internal.Quote where

open import MLTT.Spartan  hiding (rec ; _^_ ; _+_)
open import Naturals.Order renaming (_≤ℕ_ to _≤_; _<ℕ_ to _<_)
open import Naturals.Addition using (_+_; succ-right; sum-to-zero-gives-zero; addition-commutativity; zero-right-neutral; zero-left-neutral)
open import Naturals.Properties using (positive-not-zero)
open import EffectfulForcing.MFPSAndVariations.SystemT using (type ; ι ; _⇒_ ; 〖_〗)
open import EffectfulForcing.Internal.SystemT
open import UF.Base using (transport₂ ; transport₃ ; ap₂ ; ap₃)

\end{code}

System T with quoting.

\begin{code}

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

_∧_ : 𝟚 → 𝟚 → 𝟚
₁ ∧ b = b
₀ ∧ b = ₀

infixr 6 _∧_

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

\end{code}

The unpairing function `unpair`:

\begin{code}

unpair : ℕ → ℕ × ℕ
unpair 0 = 0 , 0
unpair (succ n) with unpair n
... | zero   , y = succ y , zero
... | succ x , y = x      , succ y

\end{code}

`p` is `pairing m n`, and we want to return `m`

\begin{code}

π₁ : ℕ → ℕ
π₁ = pr₁ ∘ unpair

\end{code}

p is (pairing m n), and we want to return n

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
π3₂ n = pr₁ (unpair (pr₂ (unpair n)))

\end{code}

The third projection from a triple.

\begin{code}

pairing3→₃ : (n : ℕ) → ℕ
pairing3→₃ n = pr₂ (unpair (pr₂ (unpair n)))

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

pairing-s0 : (x : ℕ) → pair (succ x , 0) ＝ succ (pair (0 , x))
pairing-s0 x = {!!}

pairing-xs : (x y : ℕ) → pair (x , succ y) ＝ succ (pair (succ x , y))
pairing-xs x y = {!!}

＝pair : {A : 𝓤 ̇ } {B : 𝓥 ̇ } {a₁ a₂ : A} {b₁ b₂ : B} → a₁ ＝ a₂ → b₁ ＝ b₂ → (a₁ , b₁) ＝ (a₂ , b₂)
＝pair {_} {_} {A} {B} {a₁} {a₂} {b₁} {b₂} refl refl = refl

＝pair→ : {A : 𝓤 ̇ } {B : 𝓥 ̇ } {a₁ a₂ : A} {b₁ b₂ : B} → (a₁ , b₁) ＝ (a₂ , b₂) → (a₁ ＝ a₂) × (b₁ ＝ b₂)
＝pair→ {_} {_} {A} {B} {a₁} {a₂} {b₁} {b₂} refl = refl , refl

unpair-pairing-aux : (p : ℕ × ℕ) (n : ℕ) → pair p ＝ n → unpair n ＝ p
unpair-pairing-aux (x , y) 0 h = ＝pair ((pr₁ (pair-zero-means-both-components-zero x y h)) ⁻¹) ((pr₂ (pair-zero-means-both-components-zero x y h)) ⁻¹)
unpair-pairing-aux (x , 0) (succ n) h with x
... | 0 = 𝟘-elim (positive-not-zero n (h ⁻¹))
... | succ x
 with unpair-pairing-aux (0 , x) n
... | z with unpair n
... | 0 , b = ap (λ k → succ k , 0) (pr₂ (＝pair→ (z (succ-injective ((pairing-s0 x) ⁻¹ ∙ h)))))
... | succ a , b = 𝟘-elim {! (¬succ＝0 a (pr₁ (＝pair→ (z (succ-injective ((pairing-s0 x) ⁻¹ ∙ h)))))) !}
unpair-pairing-aux (x , succ y) (succ n) h with unpair-pairing-aux (succ x , y) n
... | z with unpair n
... | 0 , b = 𝟘-elim {! (¬succ＝0 x ((pr₁ (＝pair→ (z (succ-injective ((pairing-xs x y) ⁻¹ ∙ h))))) ⁻¹)) !}
... | succ a , b =
 ＝pair
  (succ-injective (pr₁ (＝pair→ (z (succ-injective ((pairing-xs x y) ⁻¹ ∙ h))))))
  (ap succ (pr₂ (＝pair→ (z (succ-injective ((pairing-xs x y) ⁻¹ ∙ h))))))

unpair-pairing : (p : ℕ × ℕ) → unpair (pair p) ＝ p
unpair-pairing p = unpair-pairing-aux p (pair p) refl

pairing→₁-pairing : (x₁ x₂ : ℕ) → π₁ (pair (x₁ , x₂)) ＝ x₁
pairing→₁-pairing x₁ x₂ = ap pr₁ (unpair-pairing (x₁ , x₂))

＝pairing→₁ : {x₁ x₂ : ℕ} → x₁ ＝ x₂ → π₁ x₁ ＝ π₁ x₂
＝pairing→₁ {x₁} {x₂} refl = refl

pairing→₂-pairing : (x₁ x₂ : ℕ) → π₂ (pair (x₁ , x₂)) ＝ x₂
pairing→₂-pairing x₁ x₂ = ap pr₂ (unpair-pairing (x₁ , x₂))

＝pairing→₂ : {x₁ x₂ : ℕ} → x₁ ＝ x₂ → π₂ x₁ ＝ π₂ x₂
＝pairing→₂ {x₁} {x₂} refl = refl

π3₁-pairing3 : (x₁ x₂ x₃ : ℕ) → π3₁ (pair₃ (x₁ , x₂ , x₃)) ＝ x₁
π3₁-pairing3 x₁ x₂ x₃ = ap pr₁ (unpair-pairing (x₁ , pair (x₂ , x₃)))

＝π3₁ : {x₁ x₂ : ℕ} → x₁ ＝ x₂ → π3₁ x₁ ＝ π3₁ x₂
＝π3₁ {x₁} {x₂} refl = refl

π3₂-pairing3 : (x₁ x₂ x₃ : ℕ) → π3₂ (pair₃ (x₁ , x₂ , x₃)) ＝ x₂
π3₂-pairing3 x₁ x₂ x₃ =
 ap (λ k → pr₁ (unpair (pr₂ k))) (unpair-pairing (x₁ , pair (x₂ , x₃)))
 ∙ ap pr₁ (unpair-pairing (x₂ , x₃))

＝π3₂ : {x₁ x₂ : ℕ} → x₁ ＝ x₂ → π3₂ x₁ ＝ π3₂ x₂
＝π3₂ {x₁} {x₂} refl = refl

pairing3→₃-pairing3 : (x₁ x₂ x₃ : ℕ) → pairing3→₃ (pair₃ (x₁ , x₂ , x₃)) ＝ x₃
pairing3→₃-pairing3 x₁ x₂ x₃ =
 ap (λ k → pr₂ (unpair (pr₂ k))) (unpair-pairing (x₁ , pair (x₂ , x₃)))
 ∙ ap pr₂ (unpair-pairing (x₂ , x₃))

＝pairing3→₃ : {x₁ x₂ : ℕ} → x₁ ＝ x₂ → pairing3→₃ x₁ ＝ pairing3→₃ x₂
＝pairing3→₃ {x₁} {x₂} refl = refl

pairing-inj : (p q : ℕ × ℕ) → pair p ＝ pair q → p ＝ q
pairing-inj p q h =
  (((unpair-pairing p) ⁻¹) ∙ h1) ∙ (unpair-pairing q)
  where
    h1 : unpair (pair p) ＝ unpair (pair q)
    h1 = ap unpair h

unpair＝ : (n : ℕ) → Σ x ꞉ ℕ , Σ y ꞉ ℕ , unpair n ＝ (x , y)
unpair＝ n with unpair n
... | x , y = x , y , refl

fst-unpair＝ : (n x y : ℕ) → unpair n ＝ (x , y) → pr₁ (unpair n) ＝ x
fst-unpair＝ n x y u = ap pr₁ u

snd-unpair＝ : (n x y : ℕ) → unpair n ＝ (x , y) → pr₂ (unpair n) ＝ y
snd-unpair＝ n x y u = ap pr₂ u

pairing-unpair : (n : ℕ) → pair (unpair n) ＝ n
pairing-unpair 0 = refl
pairing-unpair (succ n) with unpair＝ n
... | succ x , y , p = {!!} --rewrite p = →s＝s (trans h1 (pairing-unpair n))
  where
    h1 : y + succ ((y + x) + sum-up-to (y + x)) ＝ pair (unpair n)
    h1 with unpair n
    ... | a , b = {!!}
... | 0 , y , p = {!!} --rewrite p = →s＝s (trans h1 (pairing-unpair n))
  where
    h1 : y + sum-up-to y ＝ pair (unpair n)
    h1 with unpair n
    ... | a , b = ap (λ k → y + sum-up-to k) (zero-right-neutral y ⁻¹) ∙ ap₂ (λ i j → pair (i , j)) (pr₁ (＝pair→ p) ⁻¹) (pr₂ (＝pair→ p) ⁻¹)

unpair-inj : (n m : ℕ) → unpair n ＝ unpair m → n ＝ m
unpair-inj n m h =
  (((pairing-unpair n) ⁻¹) ∙ h1) ∙ (pairing-unpair m)
  where
    h1 : pair (unpair n) ＝ pair (unpair m)
    h1 = ap pair h

+assoc-aux : (x y : ℕ) → x + x + (y + y) ＝ y + x + (y + x)
+assoc-aux x y = {!!}
{-
  rewrite +-comm y x
        | sym (+-assoc (x + y) x y)
        | +-assoc x y x
        | +-comm y x
        | sym (+-assoc x x y)
        | sym (+-assoc (x + x) y y)  = refl
-}

{-
pairing-spec-aux : (n x y : ℕ) → n ＝ y + x → pair (x , y) * 2 ＝ y * 2 + n * suc n
pairing-spec-aux 0 x y h rewrite fst (+＝0→ y x (sym h)) | snd (+＝0→ y x (sym h)) = refl
pairing-spec-aux (suc n) 0 0 ()
pairing-spec-aux (suc n) (suc x) 0 h
  rewrite *-distribʳ-+ 2 x (sum-up-to x)
        | sym (pairing-x0 x)
        | pairing-spec-aux n x 0 (suc-injective h)
        | suc-injective h
        | *-comm x 2
        | +0 x
        | *-suc x (suc x)
        | +-assoc x x (x * suc x)
  = refl
pairing-spec-aux (suc n) x (suc y) h
  rewrite *-distribʳ-+ 2 y (suc (y + x + sum-up-to (y + x)))
        | +-comm y x
        | +-assoc x y (sum-up-to (x + y))
        | *-distribʳ-+ 2 x (y + sum-up-to (x + y))
        | +-comm x y
        | pairing-spec-aux n x y (suc-injective h)
        | suc-injective h
        | *-suc (y + x) (suc (y + x))
        | *-comm x 2
        | *-comm y 2
        | +0 y
        | +0 x
        | sym (+-assoc (y + x) (y + x) ((y + x) * suc (y + x)))
        | sym (+-assoc (x + x) (y + y) ((y + x) * suc (y + x)))
        | +assoc-aux x y = refl
-}

{-
pairing-spec : (x y : ℕ) → pair (x , y) * 2 ＝ y * 2 + (y + x) * suc (y + x)
pairing-spec x y = pairing-spec-aux (y + x) x y refl
-}

{-
2∣+* : (x : ℕ) → 2 ∣ (x + x * x)
2∣+* 0 = divides 0 refl
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
-}

→＝+ₗ : {a b c : ℕ} → a ＝ b → a + c ＝ b + c
→＝+ₗ {a} {b} {c} refl = refl

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
m≤m*m : (m : ℕ) → m ≤ m * m
m≤m*m 0 = ≤-refl
m≤m*m (suc m) = m≤m*n (suc m) (_≤_.s≤s _≤_.z≤n)
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

#cons : ℕ
#cons = 8

#cons-1 : ℕ
#cons-1 = 7

encode : {Γ : Cxt} {σ : type} → QT Γ σ → ℕ
encode {Γ} {.ι} Zero = 0
encode {Γ} {.ι} (Succ t) = {!1 + encode t * #cons!}
encode {Γ} {σ} (Rec t t₁ t₂) = {!!}
encode {Γ} {σ} (ν i) = {!!}
encode {Γ} {σ ⇒ τ} (ƛ t) = {!!}
encode {Γ} {σ} (t · t₁) = {!!}
encode {Γ} {.ι} (Quote t) = {!!}
encode {Γ} {σ} (Unquote t) = {!!}

\end{code}
