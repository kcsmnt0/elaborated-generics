{-# OPTIONS --safe --with-K #-}

module Generics.SimpleContainer where

open import Generics.Description
open import Generics.Level
open import Generics.Telescope

open import Data.Bool using (Bool)
open import Data.List.Relation.Unary.All using (All)
open import Data.Sum as Sum using (inj₁; inj₂)
open import Data.Unit using (⊤)
open import Function using (const)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; trans; cong)

private variable
  cb  : ConB
  cbs : ConBs

SCᵇ : ConB → Set
SCᵇ = All Sum.[ const Bool , const ⊤ ]

scConB : Level → (cb : ConB) → SCᵇ cb → ConB
scConB ℓ []            _           = []
scConB ℓ (inj₁ ℓ' ∷ cb) (false ∷ s) = inj₁ ℓ' ∷ scConB ℓ cb s
scConB ℓ (inj₁ ℓ' ∷ cb) (true  ∷ s) = inj₁ ℓ' ∷ inj₁ ℓ ∷ scConB ℓ cb s
scConB ℓ (inj₂ rb ∷ cb) (_     ∷ s) = inj₂ rb ∷ scConB ℓ cb s

hasEl? : Level → (cb : ConB) → SCᵇ cb → Level
hasEl? ℓ []           _           = lzero
hasEl? ℓ (inj₁ _ ∷ cb) (false ∷ s) = hasEl? ℓ cb s
hasEl? ℓ (inj₁ _ ∷ cb) (true  ∷ s) = ℓ ⊔ hasEl? ℓ cb s
hasEl? ℓ (inj₂ _ ∷ cb) (_     ∷ s) = hasEl? ℓ cb s

hasEl?-bound : (ℓ : Level) (cb : ConB) (sb : SCᵇ cb) {ℓ' : Level}
             → ℓ ⊑ ℓ' → hasEl? ℓ cb sb ⊑ ℓ'
hasEl?-bound ℓ []           []           ℓ⊑ℓ' = refl
hasEl?-bound ℓ (inj₁ _ ∷ cb) (false ∷ sb) ℓ⊑ℓ' = hasEl?-bound ℓ cb sb ℓ⊑ℓ'
hasEl?-bound ℓ (inj₁ _ ∷ cb) (true  ∷ sb) ℓ⊑ℓ' = trans (cong (ℓ ⊔_)
                                               (hasEl?-bound ℓ cb sb ℓ⊑ℓ')) ℓ⊑ℓ'
hasEl?-bound ℓ (inj₂ _ ∷ cb) (_     ∷ sb) ℓ⊑ℓ' = hasEl?-bound ℓ cb sb ℓ⊑ℓ'

hasEl?-dist-⊔ : (ℓ ℓ' : Level) (cb : ConB) (sb : SCᵇ cb)
              → hasEl? (ℓ ⊔ ℓ') cb sb ≡ hasEl? ℓ cb sb ⊔ hasEl? ℓ' cb sb
hasEl?-dist-⊔ ℓ ℓ' []           []           = refl
hasEl?-dist-⊔ ℓ ℓ' (inj₁ _ ∷ cb) (false ∷ sb) = hasEl?-dist-⊔ ℓ ℓ' cb sb
hasEl?-dist-⊔ ℓ ℓ' (inj₁ _ ∷ cb) (true  ∷ sb) = cong (ℓ ⊔ ℓ' ⊔_) (hasEl?-dist-⊔ ℓ ℓ' cb sb)
hasEl?-dist-⊔ ℓ ℓ' (inj₂ _ ∷ cb) (_     ∷ sb) = hasEl?-dist-⊔ ℓ ℓ' cb sb

SCᶜ : {I : Set ℓⁱ} (D : ConD I cb) → SCᵇ cb → Set ℓ → Setω
SCᶜ (ι i  ) _           X = Liftω ⊤
SCᶜ (σ A D) (false ∷ s) X = (a : A) → SCᶜ (D a) s X
SCᶜ (σ A D) (true  ∷ s) X = Σωω[ _ ∈ (_ ,ℓ A) ≡ω ((_ ,ℓ X) ⦂ω Σℓ[ ℓ ] Set ℓ) ]
                           ((a : A) → SCᶜ (D a) s X)
SCᶜ (ρ D E) (_     ∷ s) X = SCᶜ E s X

SCᶜˢ : {I : Set ℓⁱ} → ConDs I cbs → All SCᵇ cbs → Set ℓᵉ → Setω
SCᶜˢ []            ss  E = Liftω ⊤
SCᶜˢ (D ∷ Ds) (s ∷ ss) E = Σωω[ _ ∈ SCᶜ D s E ] SCᶜˢ Ds ss E

record SC (D : PDataD) : Setω where
  field
    {elevel} : Level
    El  : ⟦ PDataD.Param D ⟧ᵗ → Set elevel
    pos : All SCᵇ (PDataD.struct D)
    coe : (ps : ⟦ PDataD.Param D ⟧ᵗ) → SCᶜˢ (PDataD.applyP D ps) pos (El ps)

SCᵈ : DataD → Setω
SCᵈ D = ∀ {ℓs} → SC (DataD.applyL D ℓs)
