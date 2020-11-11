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

  -- A very simple observation:
  -- Any left-neutral endomorphism is idempotent.
  left-neutral→idempotent : ∀{y} (f : Hom y y) → is-left-neutral f → is-idempotent f
  left-neutral→idempotent f l-ntrl = l-ntrl f
  -- (Of course, the same is true for right-neutral endomorphisms.)

  {- Next, we show that a standard identity is an idempotent equivalence. -}
  module std→idpt+eqv {y : Ob} (i : Hom y y) (std-id : is-standard-id i) where

    l-ntrl = fst std-id
    r-ntrl = snd std-id

    eqv : is-eqv i
    eqv = (λ z → is-eq (λ g → g ⋄ i) (λ h → h) r-ntrl r-ntrl)
          ,
          λ x → is-eq (λ f → i ⋄ f) (λ h → h) l-ntrl l-ntrl

    idpt : is-idempotent i
    idpt = left-neutral→idempotent i l-ntrl

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

  -- A useful lemma: equivalences satisfy 2-out-of-3 (we only show one specific instance)

  eqv-2-out-of-3 : ∀{x y z} (f : Hom x y) (g : Hom y z)
    → is-eqv g → is-eqv (g ⋄ f) → is-eqv f
  eqv-2-out-of-3 f g (p₁ , p₂) (q₁ , q₂) = {!!} , {!!}


  {- Given an equivalence, we can define an idempotent equivalence. -}

  module I {y z} (e : Hom y z) (p : is-eqv e) where

    e⁻¹⋄- : ∀{x} → Hom x z → Hom x y
    e⁻¹⋄- = is-equiv.g (snd p _)

    e⋄- : ∀{x} → Hom x y → Hom x z
    e⋄- = _⋄_ e

    I : Hom y y
    I = e⁻¹⋄- e

    -- Easy: I right neutral for e
    e⋄I : e ⋄ I == e
    e⋄I = is-equiv.f-g (snd p _) e

    -- Also easy (but more work): I left neutral in general
    l-ntrl : is-left-neutral I
    l-ntrl f =
      I ⋄ f
        =⟨ ! (is-equiv.g-f (snd p _) _) ⟩
      e⁻¹⋄- (e⋄- (I ⋄ f))
        =⟨ ap e⁻¹⋄- (! ass) ⟩
      e⁻¹⋄- ((e ⋄ I) ⋄ f)
        =⟨ ap (λ g → e⁻¹⋄- (g ⋄ f)) e⋄I ⟩
      e⁻¹⋄- (e ⋄ f)
        =⟨ is-equiv.g-f (snd p _) _ ⟩
      f
        =∎

--    r-ntrl : is-right-neutral I
--    r-ntrl = {!!}

    -- solution via 2-out-of-3
    I-is-idpt+eqv : is-idpt+eqv I
    I-is-idpt+eqv = left-neutral→idempotent
      I l-ntrl ,
      eqv-2-out-of-3 I e p (transport is-eqv (! e⋄I) p)

  {- If an endomorphism e is an equivalence, its idempotence is equivalent to its equality to I(e).
     TODO Lemma 19.
  -}
  module e-vs-I {y : Ob} (e : Hom y y) (p : is-eqv e) where
    open I
  
    e-I-idpt : (e == I e p) ≃ is-idempotent e
    e-I-idpt = --  {!ap-equiv (e⋄- e p , ?) e (I e p)!} --  {!ap-equiv {f = e⋄- e p} ? e (I e p)!} -- {!!}
      e == I e p
        ≃⟨ ap-equiv (e⋄- e p , snd p _) e (I e p) ⟩
      e ⋄ e == e ⋄ I e p
        ≃⟨ transport (λ expr → (e ⋄ e == e ⋄ I e p) ≃ (e ⋄ e == expr)) (e⋄I e p) (ide _) ⟩ 
      e ⋄ e == e
        ≃⟨ ide _ ⟩
      is-idempotent e
        ≃∎


  -- now the main theorem (Thm 17), namely that "having idempotent equivalences" is a proposition.

  module uniqueness-of-idpt+eqv (y : Ob) (i₀ : Hom y y) (idpt+eqv : is-idpt+eqv i₀) where

    idpt = fst idpt+eqv
    eqv = snd idpt+eqv

    idpt-to-=i₀ =
      Σ (Hom y y) (λ i → is-idpt+eqv i)
        ≃⟨ {!!} ⟩
      Σ (Hom y y) (λ i → is-idempotent i × is-eqv i)
        ≃⟨ {!!} ⟩
      {!!}
        ≃⟨ {!!} ⟩
      {!!}
        ≃⟨ {!!} ⟩
      {!!}
        ≃⟨ {!!} ⟩
      {!!}
        ≃∎
        


  {-  
  module idpt+eqv→std {y : Ob} (i : Hom y y) (idpt+eqv : is-idpt+eqv i) where

    idpt = fst idpt+eqv
    eqv = snd idpt+eqv
-}
  having-idpt+eqv-is-prop : is-prop has-idempot-eqvs
  having-idpt+eqv-is-prop = {!Σ-emap-r!}


