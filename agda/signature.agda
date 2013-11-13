module signature where

open import Coinduction
open import Function
open import Data.Empty
open import Data.Unit
open import Data.Product
open import Data.Sum
open import Data.Nat
open import Data.List
open import Data.Maybe renaming (Maybe to _*)
open import Category.Functor

open import Relation.Binary.PropositionalEquality

open RawFunctor ⦃...⦄

record Signature : Set₁ where
  constructor _▷_
  field
    Label : Set
    ∣_∣ : Label → List ℕ

open Signature ⦃...⦄

-- postulate _**_ : Set → ℕ → Set

_**_ : Set → ℕ → Set
V ** zero = V
V ** (suc n) = (V *) ** n

**-map : ∀ {V W n} → (V → W) → V ** n → W ** n
**-map {n = zero}  f t = f t
**-map {n = suc n} f t = **-map {n = n} (_<$>_ f) t

-- TermList′ : (Set → Set) → Set → List ℕ → Set
-- TermList′ F V [] = ⊤
-- TermList′ F V (n ∷ l) = ∞ (F (V ** n)) × TermList′ F V l

data TermList′ (F : Set → Set) (V : Set) : List ℕ → Set where
  [] : TermList′ F V []
  _∷_ : ∀ {n l} → ∞ (F (V ** n)) → TermList′ F V l → TermList′ F V (n ∷ l)

mutual
  data CoTerm (Σ : Signature) (V : Set) : Set where
    _∷_ : (s : Label) → TermList Σ V ∣ s ∣ → CoTerm Σ V
  data TermList (Σ : Signature) (V : Set) : List ℕ → Set where
    [] : TermList Σ V []
    _∷_ : ∀ {n l} → ∞ (CoTerm Σ (V ** n)) → TermList Σ V l → TermList Σ V (n ∷ l)

  data CoTerm′ (Σ : Signature) (V : Set) : Set where
    _∷_ : (s : Label) → TermList′ (CoTerm′ Σ) V ∣ s ∣ → CoTerm′ Σ V

module _ {Σ} where

  mutual
    CoTerm-map : ∀ {V W} → (V → W) → CoTerm Σ V → CoTerm Σ W
    CoTerm-map f (s ∷ x) = s ∷ TermList-map f x

    TermList-map : ∀ {l V W} → (V → W) → TermList Σ V l → TermList Σ W l
    TermList-map f []                = []
    TermList-map f (_∷_ {n = n} x t) = ?
--(♯ (CoTerm-map (**-map {n = n} f) (♭ x))) ∷ TermList-map f t


  CoTerm-map′ : ∀ {V W} → (V → W) → CoTerm′ Σ V → CoTerm′ Σ W
  CoTerm-map′ f (s ∷ x) = s ∷ {!!}
