{-# OPTIONS --without-K #-}

module Iff where

open import lib.Base public
open import lib.types.Sigma public

_⇔_ : ∀ {j₁ j₂} → Set j₁ → Set j₂ → Set (lmax j₁ j₂)
A ⇔ B = (A → B) × (B → A)
