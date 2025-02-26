-- Martin Escardo and Paulo Oliva 2011

{-# OPTIONS --no-termination-check --without-K --exact-split #-}

-- We use the Berardi-Bezem-Coquand functional to realize the J-Shift
-- (and hence the K-Shift in another module).

module Pigeon.J-Shift-BBC where

open import Pigeon.JK-Monads
open import Pigeon.Logic
open import Pigeon.LogicalFacts
open import Pigeon.Naturals


J-∀-shift-bbc : {R : Ω} {A : ℕ → Ω} →
-------------

      (∀(n : ℕ) → J(A n)) → J(∀(n : ℕ) → A n)

J-∀-shift-bbc {R} {A} ε = bbc
  where
   bbc : J {R} (∀(n : ℕ) → A n)
   bbc p i = ε i (λ x → J-K bbc (p ∘ mapsto {A} i x))
