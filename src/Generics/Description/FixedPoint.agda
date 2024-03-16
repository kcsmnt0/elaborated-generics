{-# OPTIONS --safe --without-K #-}

module Generics.Description.FixedPoint where

open import Generics.Description
open import Generics.Level
open import Generics.Telescope

data μ (D : DataD)
       (ℓs : DataD.Levels D)
       (ps : ⟦ PDataD.Param (DataD.applyL D ℓs) ⟧ᵗ)
     : let Dᵖ = DataD.applyL D ℓs
       in  ⟦ PDataD.Index Dᵖ ps ⟧ᵗ → Set (PDataD.dlevel Dᵖ) where
  con : let Dᵖ = DataD.applyL D ℓs in ∀ {is}
      → rewriteLevel (level-pre-fixed-point Dᵖ)
          (Lift (PDataD.dlevel Dᵖ) (⟦ D ⟧ᵈ (μ D ℓs ps) is))
      → μ D ℓs ps is
