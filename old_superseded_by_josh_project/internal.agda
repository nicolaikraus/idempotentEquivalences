{-# OPTIONS --without-K #-}

module internal where

open import Agda.Primitive
open import Data.Nat hiding (_≥_)
open import Data.Bool
open import Relation.Binary.PropositionalEquality

-- uip : {A : Set} (a b : A) (p q : a ≡ b) → p ≡ q
-- uip a .a refl refl = {!!}

record TT i : Set (lsuc i) where
  field

    -- a category
    Con : Set i
    Sub : Con → Con → Set i
    id : {Γ : Con} → Sub Γ Γ
    _∘_ : {Γ Δ Θ : Con} → Sub Δ Θ → Sub Γ Δ → Sub Γ Θ
    idl : {Γ Δ : Con} {f : Sub Γ Δ} → id ∘ f ≡ f
    idr : {Γ Δ : Con} {f : Sub Γ Δ} → f ∘ id ≡ f
    assoc : {Γ Δ Θ Ω : Con} {f : Sub Γ Δ} {g : Sub Δ Θ} {h : Sub Θ Ω} → (h ∘ g) ∘ f ≡ h ∘ (g ∘ f)

    -- a presheaf
    Ty : Con → Set i
    _[_]T : {Γ Δ : Con} → Ty Δ → Sub Γ Δ → Ty Γ
    idT : {Γ : Con} (A : Ty Γ) → A [ id ]T ≡ A
    ∘T : {Γ Δ Θ : Con} {f : Sub Γ Δ} {g : Sub Δ Θ} {A : Ty Θ} → A [ g ]T [ f ]T ≡ A [ g ∘ f ]T

    -- a (co/contravariant?) presheaf on the category of elements of Ty
    Tm : (Γ : Con) → Ty Γ → Set i
    _[_]t : {Γ Δ : Con} {A : Ty Δ} → Tm Δ A → (f : Sub Γ Δ) → Tm Γ (A [ f ]T)
--    idt : {Γ : Con} {A : Ty Γ} → 
    -- TODO

    -- concrete elements:


    -- contexts:
    ● : Con
    _,_ : (Γ : Con) → Ty Γ → Con


    -- substitutions:
    pi1 : ∀ {Γ A} → Sub (Γ , A) Γ -- {Γ : Con} {A : Ty Γ} → Sub (Γ , A) Γ

    -- terms:
    pi2 : ∀ {Γ A} → Tm (Γ , A) (A [ pi1 ]T) -- maybe I should stick to alten-ambrus...

    -- types:
    Unit : {Γ : Con} → Ty Γ
    -- Nat : {Γ : Con} → Ty Γ
    Pi : {Γ : Con} (A : Ty Γ) → Ty (Γ , A) → Ty Γ
    U : {Γ : Con} → Ty Γ
    El : {Γ : Con} → Tm Γ U → Ty Γ

    ⋆ : {Γ : Con} → Tm Γ Unit

-- open TT    

set-based : {i : Level} (tt : TT i) → Set _
set-based tt = (Γ : TT.Con tt) (A : TT.Ty tt Γ) (x y : TT.Tm tt Γ A) (p q : x ≡ y) → p ≡ q


module semisimpl {i : Level} (tt : TT i) (s : set-based tt) where

  Con = TT.Con tt
  Sub = TT.Sub tt
  id = TT.id tt
  _∘_ = TT._∘_ tt
  idl = TT.idl tt
  idr = TT.idr tt
  assoc = TT.assoc tt

  Ty = TT.Ty tt
  _[_]T = TT._[_]T tt
  idT = TT.idT tt
  ∘T = TT.∘T tt
  
  Tm = TT.Tm tt
  _[_]t = TT._[_]t tt

  ● = TT.● tt
  _,_ = TT._,_ tt
  pi1 = TT.pi1 tt
  Unit = TT.Unit tt
  Pi = TT.Pi tt
  U = TT.U tt
  El = TT.El tt

  _⇒_ : {Γ : Con} (A B : Ty Γ) → Ty Γ
  A ⇒ B = Pi A (B [ pi1 ]T)

  SS : ℕ → Con

  {- explanation: 
     n is the "base" (max shape with base n is Δⁿ)
     k is the "height" (the maximum level used by the shape)
     j is the "fill", i.e. the number of cells on level k; can be anything from 0 to 'n choose k'. -}

  record shape : Set where
--    inductive
--    constructor _,_,_
    field
      height : ℕ
      base : ℕ
      fill : ℕ

  open shape
  
  curryshape : ∀ {i} {A : shape → Set i} → ((k n j : ℕ) → A ( record { height = k ; base = n ; fill = j })) → (s : shape) → A s
  curryshape F s = {!!} -- F (height s) (base s) (fill s)

  test : ℕ → ℕ → ℕ → shape
  test n k j = record { height = {!!} ; base = {!!} ; fill = {!!} } --  shape { ? ; ? ; ? }

  record R : Set where
    field
      a : ℕ
      b : ℕ
      c : ℕ

--  testtest : (x : R) → x ≡ record { a = R.a x ; b = R.b x ; c = R.c x }
--  testtest x = refl


  Sk : (k n j : ℕ) → Ty (SS k)

  SS zero = ●
  SS (suc i) = (SS i) , (Pi (Sk i (suc i) (suc i)) U)

  binom : ℕ → ℕ → ℕ
  binom n k = {!!}

  -- ALL OF THE FOLLOWING NEED TO BE DEFINED IN THE SAME WAY AS SKELETON!
  -- given shape k,n,j; we want the skeleton chosen by j' (where j' encodes a subset of the base n)
  calc-height : (k n j : ℕ) → (j' : ℕ) → ℕ
  calc-height zero n j j' = zero
  calc-height (suc k) n zero j' = calc-height k n (binom n k) j'
  calc-height k n (suc j) j' = calc-height k n j j' -- MAYBE WRONG? basically: if 

  calc-base : (k n j : ℕ) → (j' : ℕ) → ℕ
  calc-base zero n j j' = zero
  calc-base (suc k) n j j' = {!!}

--  calc-fill : (k n j : ℕ) → (j' : ℕ) → ℕ
--  calc-fill = ?

  -- given shape k,n,j, and j' encoding a subset of n as above: does going from j to j+1 increas the fill of the sub-shape?
  check : (k n j : ℕ) → (j' : ℕ) → Bool
  check = {!!}

  calc-fill : (k n j : ℕ) → (j' : ℕ) → ℕ
  calc-fill k n j j' = {!!} -- if check k n j j' then {!!} else {!!}

  data _≥_ : ℕ → ℕ → Set where
    start : {n : ℕ} → n ≥ n
    next : {n k : ℕ} → n ≥ k → suc n ≥ k

  lemma : (k n j : ℕ) → (j' : ℕ) → k ≥ calc-height k n j j'
  lemma = {!!}

  subs : {n k : ℕ}→ n ≥ k → Sub (SS n) (SS k)
  subs start = id
  subs (next p) = subs p ∘ pi1

{-
  -- CAVEAT: HUGE SIMPLIFICATION POSSIBLE: function which calculates subskeleton can be external!
  Sksub : (k n j : ℕ) → (j' : ℕ) → Tm (SS k) ((Sk k n j) ⇒ ((Sk (calc-height k n j j') (calc-base k n j j') (calc-fill k n j j')) [ subs (lemma k n j j') ]T))
  Sksub zero n j j' = {!!}
  Sksub (suc k) n zero j' = {!!}
  Sksub (suc k) n (suc j) j' = {!!}
-}




  Sk zero n j = Unit
  Sk (suc k) n zero = _[_]T (Sk k n (binom n k)) pi1 
  Sk k n (suc j) = -- here: suc j encodes the new thing. WE NEED SIGMA!
    {!!}












