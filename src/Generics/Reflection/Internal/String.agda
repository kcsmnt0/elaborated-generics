{-# OPTIONS --safe --without-K #-}

module Generics.Reflection.Internal.String where

open import Data.Bool using (Bool; true; false; if_then_else_; _∧_)
open import Data.Char using (Char; isDigit; toℕ)
open import Data.List using (List; []; _∷_; length; take; reverse)
open import Data.Maybe using (Maybe; nothing; just; maybe)
open import Data.Nat using (ℕ; zero; suc; _+_; _∸_; _*_; _<ᵇ_)
open import Data.String using (String; toList; fromList; _++_)
open import Function using (_∘_; case_of_)

import Data.Nat.Show as Nat

lenLeadingNat : List Char → ℕ
lenLeadingNat [] = 0
lenLeadingNat (x ∷ xs) =
  if isDigit x then suc (lenLeadingNat xs) else 0

-- toNat : Char → Maybe Nat
-- toNat c = let n = C.primCharToNat c
--            in if (47 <ᵇ n) ∧ (n <ᵇ 58) then
--                 just (n ∸ 48)
--               else
--                 nothing

trailingNatʳ : List Char → Maybe ℕ
trailingNatʳ [] = nothing
trailingNatʳ (x ∷ xs) using n ← toℕ x with (47 <ᵇ toℕ x) ∧ (toℕ x <ᵇ 58)
… | true =
      case trailingNatʳ xs of λ where
        (just m) → just (m * 10 + n)
        nothing → just n
… | false = nothing

trailingNat = trailingNatʳ ∘ reverse
lenTrailingNat = lenLeadingNat ∘ reverse

removeTrailingNat : List Char → List Char
removeTrailingNat cs = take (length cs ∸ lenTrailingNat cs) cs

increase : String → String
increase s =
  let cs = toList s in
    case trailingNat cs of λ where
      (just x) → (fromList (removeTrailingNat cs)) ++ Nat.show (suc x)
      nothing  → s ++ "1"
