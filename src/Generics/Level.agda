{-# OPTIONS --safe --without-K #-}

module Generics.Level where

open import Level using (Level; Setω; Lift; lift; _⊔_) renaming (zero to lzero; suc to lsuc) public
open import Relation.Binary.PropositionalEquality using (_≡_; refl)

variable
  ℓ ℓ' ℓ'' ℓ''' ℓ′ ℓ′′ ℓ′′′ ℓᵈ ℓᵉ ℓⁱ ℓʲ ℓᵏ ℓˣ ℓʸ : Level

record Liftω {a} (A : Set a) : Setω where
  constructor lift
  field lower : A

open Liftω public

-- Synonyms

0ℓ 1ℓ 2ℓ : Level
0ℓ = lzero
1ℓ = lsuc 0ℓ
2ℓ = lsuc 1ℓ

rewriteLevel : ∀ {ℓ ℓ'} → ℓ ≡ ℓ' → Set ℓ → Set ℓ'
rewriteLevel refl X = X

infix 4 _⊑_ -- Type `\squb=` to get `⊑`
_⊑_ : Level → Level → Set
ℓ₁ ⊑ ℓ₂ = ℓ₁ ⊔ ℓ₂ ≡ ℓ₂

levelOfType : ∀ {a} → Set a → Level
levelOfType {a} _ = a

levelOfTerm : ∀ {a} {A : Set a} → A → Level
levelOfTerm {a} _ = a
