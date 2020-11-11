{-# OPTIONS --without-K #-}

open import Agda.Primitive
-- open import Relation.Binary.PropositionalEquality

-- open import lib.Equivalence
open import HoTT

module idemequivs where



module _ {i} {j} {A : Set i} {B : Set j} where

{-
  record is-equiv (f : A → B) : Set (i ⊔ j)
    where
    field
      left-inv : B → A
      right-inv : B → A
      left-eq : (a : A) → left-inv (f a) ≡ a
      right-eq : (b : B) → f (right-inv b) ≡ b
      
module _ {i} where

  is-prop : (A : Set i) → Set i
  is-prop A = (a₀ a₁ : A) → a₀ ≡ a₁
-}



record Semicat i j : Set (lsuc (i ⊔ j)) where
  field
    Ob    : Set i
    Hom   : Ob → Ob → Set j
    _∘_   : ∀ {X Y Z} → Hom Y Z → Hom X Y → Hom X Z
    assoc : ∀ {X Y Z W}{f : Hom X Y}{g : Hom Y Z}{h : Hom Z W}
            → (h ∘ g) ∘ f ≡ (h ∘ (g ∘ f)) 

open Semicat

module _ {i j} (C : Semicat i j) where

  is-idem : {X : Ob C} → (Hom C X X) → Set {!!}
  is-idem f = (_∘_ C f f) ≡ f
  
  isIdentity : {X Y : Ob C} → Hom C X Y → Set j
  isIdentity = {!!}


--isIdentity : ∀ {i j} → (C : Semicat i j) → {X Y : Hom C} → ?
--isIdentity = ?
