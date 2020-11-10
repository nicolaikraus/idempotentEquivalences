{-# OPTIONS --without-K #-}

{-

Goal of this file: "having identities" as proposition.

-}

module Identities where

open import HoTT public

record SemiCat {j} : Type (lsucc j) where
  infixr 40 _⋄_
  field
    Ob  : Type j
    Hom : Ob → Ob → Type j
    _⋄_ : ∀ {x y z} → Hom y z → Hom x y → Hom x z
    ass : ∀ {x y z w} {f : Hom z w} {g : Hom y z} {h : Hom x y}
        → (f ⋄ g) ⋄ h == f ⋄ (g ⋄ h)

-- for the rest of this file, we assume that C is a given "wild" semicategory.
module _ {j} {C : SemiCat {j}} where
  open SemiCat C

  -- maybe need to reformulate this as Σ-type??
  record has-standard-identities : Type j where
    field
      id : {x : Ob} → Hom x x
      idl : {x y : Ob} {f : Hom x y} → id ⋄ f == f
      idr : {y z : Ob} {g : Hom y z} → g ⋄ id == g


  module _ {y : Ob} (i : Hom y y) where

    is-left-neutral = {x : Ob} (f : Hom x y) → i ⋄ f == f
    is-right-neutral = {z : Ob} (g : Hom y z) → g ⋄ i == g
    is-standard-id = is-left-neutral × is-right-neutral

  has-standard-ids = (x : Ob) → Σ (Hom x x) is-standard-id

  -- the point is that "having standard identities" is ok if Hom x y is a set.

  -- NOT a prop
  is-idempotent : {x : Ob} (f : Hom x x) → Type j
  is-idempotent f = f ⋄ f == f

  -- a prop
  -- aka "is neutral"
  is-eqv : {x y : Ob} (g : Hom x y) → Type j
  is-eqv {x} {y} g =   ((z : Ob) → is-equiv λ (h : Hom y z) → h ⋄ g)
                     × ((w : Ob) → is-equiv λ (f : Hom w x) → g ⋄ f)

  is-idpt-eqv : {x : Ob} (i : Hom x x) → Type j
  is-idpt-eqv i = is-idempotent i × is-eqv i

  has-idempot-eqvs = (x : Ob) → Σ (Hom x x) is-idpt-eqv

--  record has-idempot-eqv : Type i where
--    field
--      i : {x : Ob}

  -- auxiliary lemma
--  unapply-eqv : {x y}



  module idpt+eqv→std {y : Ob} (i : Hom y y) (idpt+eqv : is-idpt-eqv i) where

    idpt = fst idpt+eqv
    eqv = snd idpt+eqv
    
    left-neutral : is-left-neutral i
    left-neutral f = w/o-i
      where
        with-i : i ⋄ (i ⋄ f) == i ⋄ f
        with-i =
          i ⋄ (i ⋄ f)
            =⟨ ! ass ⟩
          (i ⋄ i) ⋄ f
            =⟨ ap (λ g → g ⋄ f) idpt ⟩
          i ⋄ f
            =∎
        w/o-i : i ⋄ f == f
        w/o-i = is-equiv.g
                  (ap-is-equiv {f = λ g → i ⋄ g} (snd eqv _) (i ⋄ f) f)
                  with-i

    -- a copy. Shortened it.
    right-neutral : is-right-neutral i
    right-neutral g =
      is-equiv.g
        (ap-is-equiv (fst eqv _) (g ⋄ i) g)
        (ass ∙ ap (λ f → g ⋄ f) idpt)

  module _ {y : Ob} (i : Hom y y) (std-id : is-standard-id i) where

    l-ntrl = fst std-id
    r-ntrl = snd std-id

    eqv : is-eqv i
    eqv = (λ z → is-eq (λ g → g ⋄ i) (λ h → h) r-ntrl r-ntrl)
          ,
          λ x → is-eq (λ f → i ⋄ f) (λ h → h) l-ntrl l-ntrl

    idpt : is-idempotent i
    idpt = l-ntrl i

  -- NOW, we have everything up to Lemma 15. Fix notation. Clean up.

  idpt+eqv→std-id : ∀{y} → (i : Hom y y) → is-idpt-eqv i → is-standard-id i
  idpt+eqv→std-id i idpt+eqv = idpt+eqv→std.left-neutral i idpt+eqv , idpt+eqv→std.right-neutral i idpt+eqv
