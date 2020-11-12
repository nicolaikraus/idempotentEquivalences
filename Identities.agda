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

  is-idpt : {x : Ob} (f : Hom x x) → Type j₂
  is-idpt f = f ⋄ f == f
  {- Note: "being idempotent" is not necessarily a proposition
     (as 'Hom x x' might not be a set). -}

  is-eqv : {x y : Ob} (g : Hom x y) → Type j
  is-eqv {x} {y} g =   ((z : Ob) → is-equiv λ (h : Hom y z) → h ⋄ g)
                     × ((w : Ob) → is-equiv λ (f : Hom w x) → g ⋄ f)
  {- Note: "being an equivalence" is a proposition (inherited property
     from equivalences of types). -}

  is-idpt+eqv : {x : Ob} (i : Hom x x) → Type j
  is-idpt+eqv i = is-idpt i × is-eqv i
  {- Note: "being idempotent and an equivalence" is not a proposition.
     E.g. in the wild semicategory of types and functions, the identity
     on the circle S¹ is an idempotent equivalence in ℤ-many ways. -}

  has-idpt-eqvs = (x : Ob) → Σ (Hom x x) is-idpt+eqv
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
  left-neutral→idempotent : ∀{y} (f : Hom y y) → is-left-neutral f → is-idpt f
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

    idpt : is-idpt i
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

{-
  -- We first show this for "real" equivalences between types
  equiv-2-out-of-3 : ∀ {j₁ j₂ j₃} {X : Type j₁} {Y : Type j₂} {Z : Type j₃}
    (f : X → Y) (g : Y → Z) (h : X → Z)
    → h == g ∘ f
    → is-equiv g → is-equiv h → is-equiv f
  equiv-2-out-of-3 = {!!}
-}

  eqv-2-out-of-3 : ∀{w x y} (f : Hom w x) (g : Hom x y)
    → is-eqv g → is-eqv (g ⋄ f) → is-eqv f
  eqv-2-out-of-3 {w} {x} {y} f g (p₁ , p₂) (q₁ , q₂) =
    {!λ v → f⋄-is-eqv!}
    ,
    λ _ → f⋄-is-eqv
      where
      f⋄- : {v : Ob} → Hom v w → Hom v x
      f⋄- = λ h → f ⋄ h
      g⁻¹⋄- : {v : Ob} → Hom v y → Hom v x
      g⁻¹⋄- = is-equiv.g {f = λ h → g ⋄ h} (p₂ _)
      gf⋄- : {v : Ob} → Hom v w → Hom v y
      gf⋄- = λ h → (g ⋄ f) ⋄ h
      eq : ∀{v} → g⁻¹⋄- {v} ∘ gf⋄- == f⋄- {v}
      eq {v} = λ= (λ h →
        (g⁻¹⋄- ∘ gf⋄-) h
          =⟨ idp ⟩
        g⁻¹⋄- ((g ⋄ f) ⋄ h)
          =⟨ ap g⁻¹⋄- ass ⟩
        g⁻¹⋄- (g ⋄ (f ⋄ h))
          =⟨ is-equiv.g-f (p₂ _) (f ⋄ h)  ⟩
        (f ⋄ h)
          =⟨ idp ⟩
        f⋄- h
          =∎
        )
      g⁻¹⋄-equiv : ∀{v} → is-equiv (g⁻¹⋄- {v})
      g⁻¹⋄-equiv {v} = is-equiv-inverse (p₂ _)
      f⋄-is-eqv : ∀{v} → is-equiv (f⋄- {v})
      f⋄-is-eqv {v} = transport is-equiv eq (g⁻¹⋄-equiv ∘ise q₂ _)
      
      
      -⋄f : {y : Ob} → Hom x y → Hom w y
      -⋄f = λ h → h ⋄ f
      -⋄g⁻¹ : {z : Ob} → Hom x z → Hom y z
      -⋄g⁻¹ = is-equiv.g (p₁ _)
      -⋄gf : {z : Ob} → Hom y z → Hom w z
      -⋄gf = λ h → h ⋄ (g ⋄ f)
      eq' : ∀{z} → -⋄gf {z} ∘ -⋄g⁻¹ == -⋄f {z}
      eq' {z} = λ= (λ h →
        (-⋄g⁻¹ h) ⋄ (g ⋄ f)
          =⟨ ! ass ⟩
        ((-⋄g⁻¹ h) ⋄ g) ⋄ f
          =⟨ ap (λ k → k ⋄ f) (is-equiv.f-g (p₁ _) _) ⟩
        h ⋄ f
          =∎
        )

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
  
    e-I-idpt : (e == I e p) ≃ is-idpt e
    e-I-idpt =
      e == I e p
        ≃⟨ ap-equiv (e⋄- e p , snd p _) e (I e p) ⟩
      e ⋄ e == e ⋄ I e p
        ≃⟨ transport (λ expr → (e ⋄ e == e ⋄ I e p) ≃ (e ⋄ e == expr)) (e⋄I e p) (ide _) ⟩ 
      e ⋄ e == e
        ≃⟨ ide _ ⟩
      is-idpt e
        ≃∎


  -- now the main theorem (Thm 17), namely that "having idempotent equivalences" is a proposition.

  module unique (y : Ob) (i₀ : Hom y y) (idpt+eqv₀ : is-idpt+eqv i₀) where

    open I
    open e-vs-I
    
    idpt₀ = fst idpt+eqv₀
    eqv₀ = snd idpt+eqv₀

    idpt-to-=i₀ =
      Σ (Hom y y) (λ i → is-idpt+eqv i)
        ≃⟨ ide {i = j} _ ⟩ -- unfolding, does nothing
      Σ (Hom y y) (λ i → is-idpt i × is-eqv i)
        ≃⟨ Σ-emap-r --{A = Hom y y}
                    --{B = λ i → is-idpt i × is-eqv i}
                    --{C = λ i → is-eqv i × is-idpt i}
                    (λ i → ×-comm) ⟩
      Σ (Hom y y) (λ i → Σ (is-eqv i) λ eqv → (is-idpt i))
        ≃⟨ Σ-emap-r (λ i → Σ-emap-r λ eqv → e-I-idpt i eqv ⁻¹) ⟩
      Σ (Hom y y) (λ i → Σ (is-eqv i) λ eqv → i == I i eqv)
        ≃⟨ Σ-emap-r (λ i → Σ-emap-r λ p → coe-equiv
             (ap (λ i' → (i == i')) (idpt+eqv-unique (I i p) i₀ (I-is-idpt+eqv i p) idpt+eqv₀))) ⟩ 
      Σ (Hom y y) (λ i → Σ (is-eqv i) λ _ → i == i₀)
        ≃⟨ Σ-emap-r (λ i → ×-comm) ⟩
      Σ (Hom y y) (λ i → Σ (i == i₀) λ _ → (is-eqv i))
        ≃⟨ Σ-assoc ⁻¹ ⟩
      (Σ (Σ (Hom y y) (λ i → (i == i₀))) λ ip → (is-eqv (fst ip)))
        ≃⟨ Σ-emap-l {A = Unit} {B = Σ (Hom y y) λ i → (i == i₀)} (λ ip → (is-eqv (fst ip))) (contr-equiv-Unit (pathto-is-contr i₀) ⁻¹) ⁻¹ ⟩
      (Σ Unit λ _ → is-eqv i₀)
        ≃⟨ Σ₁-Unit ⟩
      is-eqv i₀
        ≃⟨ contr-equiv-Unit (inhab-prop-is-contr eqv₀) ⟩ -- proof that is-eqv is prop is inferred!
      Unit
        ≃∎

    -- in other words: the type of idempotent equivalences on y is contractible (note that the module assumes an idempotent equivalence).
    unique-idpt+eqv : is-contr (Σ (Hom y y) (λ i → is-idpt+eqv i))
    unique-idpt+eqv = equiv-preserves-level (idpt-to-=i₀ ⁻¹)

  -- therefore: "having idempotent equivalences" is a propositional property of the wild semicategory C.
  -- Theorem 17
  having-idpt+eqv-is-prop : is-prop has-idpt-eqvs
  having-idpt+eqv-is-prop = inhab-to-contr-is-prop λ idpt+eqvs →
    WeakFunext.weak-λ= λ y → unique.unique-idpt+eqv y (fst(idpt+eqvs y)) (snd(idpt+eqvs y)) 
