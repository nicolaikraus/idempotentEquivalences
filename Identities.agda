{- Nicolai Kraus
-}

{-# OPTIONS --without-K #-}

module Identities where
open import HoTT public
open import Iff public

{-  A *wild semicategory*, sometimes also known as 
    a *(wild) semigroupoid*, consists of:
      - Ob: a type of objects;
      - Hom: a type family of morphisms (for increased
             generality possibly in another universe
             than Ob, but it doesn't matter)
      - and an associative binary operation _⋄_.
    This is of course just a "category without
    identities". Note that we do NOT ask for set-
    truncation!
-}

record SemiCat {j₁ j₂} : Type (lsucc (lmax j₁ j₂)) where
  infixr 40 _⋄_
  field
    Ob  : Type j₁
    Hom : Ob → Ob → Type j₂
    _⋄_ : ∀ {x y z} → Hom y z → Hom x y → Hom x z
    ass : ∀ {x y z w} {f : Hom z w} {g : Hom y z} {h : Hom x y}
        → (f ⋄ g) ⋄ h == f ⋄ (g ⋄ h)

{-  For the rest of this file, we assume that C is a 
    given fixed "wild" semicategory. This means we work
    inside a module which fixes C.
-}

module _ {j₁ j₂} {C : SemiCat {j₁} {j₂}} where
  open SemiCat C

  j = lmax j₁ j₂

  {- A "standard identity" is a morphism which is left and right
     neutral. This is the normal, well-known definition. -}

  module _ {y : Ob} (i : Hom y y) where
    is-left-neutral = {x : Ob} (f : Hom x y) → i ⋄ f == f
    is-right-neutral = {z : Ob} (g : Hom y z) → g ⋄ i == g
    is-standard-id = is-left-neutral × is-right-neutral

  has-standard-ids = (x : Ob) → Σ (Hom x x) is-standard-id

  {- The problem with these identities is that "having standard
     identities" is not a propositional property: it is structure,
     i.e. C can have standard identities in multiple different ways.
     This makes "having standard identities" ill-behaved, as 
     demonstrated in TODO of the paper TODO.

     We now develop a better alternative definition of identities,
     namely *idempotent equivalences*, and this will lead to a
     propositional property.
  -}

  is-idempotent : {x : Ob} (f : Hom x x) → Type j₂
  is-idempotent f = f ⋄ f == f
  {- Note: "being idempotent" is not necessarily a proposition
     (as 'Hom x x' might not be a set). -}

  is-eqv : {x y : Ob} (g : Hom x y) → Type j
  is-eqv {x} {y} g =   ((z : Ob) → is-equiv λ (h : Hom y z) → h ⋄ g)
                     × ((w : Ob) → is-equiv λ (f : Hom w x) → g ⋄ f)
  {- Note: "being an equivalence" is a proposition (inherited property
     from equivalences of types). -}

  is-idpt+eqv : {x : Ob} (i : Hom x x) → Type j
  is-idpt+eqv i = is-idempotent i × is-eqv i
  {- Note: "being idempotent and an equivalence" is not a proposition.
     E.g. in the wild semicategory of types and functions, the identity
     on the circle S¹ is an idempotent equivalence in ℤ-many ways. -}

  has-idempot-eqvs = (x : Ob) → Σ (Hom x x) is-idpt+eqv
  {- "Having idempotent equivalences" *is* a proposition, but this is
     non-trivial and will be shown later! -}

  {- First, we show that an idempotent equivalence is also a standard
     identity -}
  module idpt+eqv→std {y : Ob} (i : Hom y y) (idpt+eqv : is-idpt+eqv i) where

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

    -- A copy; shortened version of the above proof.
    right-neutral : is-right-neutral i
    right-neutral g =
      is-equiv.g
        (ap-is-equiv (fst eqv _) (g ⋄ i) g)
        (ass ∙ ap (λ f → g ⋄ f) idpt)


  

  {- Next, we show that a standard identity is an idempotent equivalence. -}
  module std→idpt+eqv {y : Ob} (i : Hom y y) (std-id : is-standard-id i) where

    l-ntrl = fst std-id
    r-ntrl = snd std-id

    eqv : is-eqv i
    eqv = (λ z → is-eq (λ g → g ⋄ i) (λ h → h) r-ntrl r-ntrl)
          ,
          λ x → is-eq (λ f → i ⋄ f) (λ h → h) l-ntrl l-ntrl

    idpt : is-idempotent i
    idpt = l-ntrl i

  {- Now, we have everything in place to state Lemma 15 of TODO.
     Iff (⇔) just means "maps in both directions". -}

  idpt+eqv⇔std : ∀{y} → (i : Hom y y) → is-idpt+eqv i ⇔ is-standard-id i
  idpt+eqv⇔std i = (⇒ , ⇐)
    where
      ⇒ : is-idpt+eqv i → is-standard-id i
      ⇒ p = idpt+eqv→std.left-neutral i p , idpt+eqv→std.right-neutral i p
      ⇐ : is-standard-id i → is-idpt+eqv i
      ⇐ p = std→idpt+eqv.idpt i p , std→idpt+eqv.eqv i p

  {- Idempotent equivalences are unique: Corollary 16 -}

  idpt+eqv-unique : ∀{y} → (i₁ i₂ : Hom y y) → is-idpt+eqv i₁ → is-idpt+eqv i₂ → i₁ == i₂
  idpt+eqv-unique i₁ i₂ p₁ p₂ =
    i₁
      =⟨ ! (idpt+eqv→std.right-neutral i₂ p₂ i₁) ⟩
    i₁ ⋄ i₂
      =⟨ idpt+eqv→std.left-neutral i₁ p₁ i₂ ⟩
    i₂
      =∎

  {- Given an equivalence, we can define an idempotent equivalence. -}

  module _ {x y} (e : Hom x y) (p : is-eqv e) where

    I : Hom x x
    I = is-equiv.g (snd p x) e

    l-ntrl : is-left-neutral I
    l-ntrl = {!!}


    r-ntrl : is-right-neutral I
    r-ntrl = ?
