{-# OPTIONS --safe --without-K #-}

module Generics.Reflection.Internal.Eq where

open import Generics.Reflection.Internal.Core

open import Agda.Builtin.Reflection
open import Data.Bool using (Bool; true; false; _∧_)
open import Data.List using (List; []; _∷_)
open import Data.Product using (_,_)

import Data.Char as Char
import Data.Float as Float
import Data.Nat as Nat
import Data.String as String
import Data.Word64 as Word64

private variable
  A : Set _

eqVisibility : (x y : Visibility) → Bool
eqVisibility visible   visible   = true
eqVisibility hidden    hidden    = true
eqVisibility instance′ instance′ = true
eqVisibility _         _         = false

eqRelevance : (x y : Relevance) → Bool
eqRelevance relevant   relevant   = true
eqRelevance irrelevant irrelevant = true
eqRelevance _          _          = false

eqQuantity : (x y : Quantity) → Bool
eqQuantity quantity-0 quantity-0 = true
eqQuantity quantity-ω quantity-ω = true
eqQuantity _          _          = false

eqName : (x y : Name) → Bool
eqName = primQNameEquality

eqMeta : (x y : Meta) → Bool
eqMeta = primMetaEquality

eqModality : (x y : Modality) → Bool
eqModality (modality r q) (modality r₁ q₁) =
  (eqRelevance r r₁) ∧ (eqQuantity q q₁)

eqArgInfo : (x y : ArgInfo) → Bool
eqArgInfo (arg-info v r) (arg-info v₁ r₁) =
  (eqVisibility v v₁) ∧ (eqModality r r₁)

eqArg : ((x y : A) → Bool) → (x y : Arg A) → Bool
eqArg eqA (arg i x) (arg i₁ x₁) =
  (eqArgInfo i i₁) ∧ (eqA x x₁)

eqAbs : ((x y : A) → Bool) → (x y : Abs A) → Bool
eqAbs eqA (abs s x) (abs s₁ x₁) = (s String.== s₁) ∧ (eqA x x₁)


eqLiteral : (x y : Literal) → Bool
eqLiteral (nat n)    (nat m)    = m Nat.≡ᵇ n
eqLiteral (word64 n) (word64 m) = n Word64.== m
eqLiteral (float x)  (float y)  = x Float.≡ᵇ y
eqLiteral (char c)   (char d)   = c Char.== d
eqLiteral (string s) (string t) = s String.== t
eqLiteral (name x)   (name y)   = eqName x y -- x Char.== y
eqLiteral (meta x)   (meta y)   = eqMeta x y
eqLiteral _          _          = false

eqTerm   : (x y : Term)    → Bool
eqPat    : (x y : Pattern) → Bool
eqSort   : (x y : Sort)    → Bool
eqClause : (x y : Clause)  → Bool
  
eqArgTerm : (x y : Arg Term) → Bool
eqArgTerm (arg i x) (arg i₁ x₁) = (eqArgInfo i i₁) ∧ eqTerm x x₁

eqAbsTerm : (x y : Abs Term) → Bool
eqAbsTerm (abs s x) (abs s₁ x₁) = (s String.== s₁) ∧ eqTerm x x₁

eqTel    : (x y : Telescope) → Bool
eqTel []       []       = true
eqTel ((x , a) ∷ xs) ((y , b) ∷ ys) = (x String.== y) ∧ eqArgTerm a b ∧ eqTel xs ys
eqTel _        _        = false

eqArgPat : (x y : Arg Pattern) → Bool
eqArgPat (arg i x) (arg i₁ x₁) = (eqArgInfo i i₁) ∧ eqPat x x₁

eqArgs : (x y : Args Term) → Bool
eqArgs []       []       = true
eqArgs (x ∷ xs) (y ∷ ys) = eqArgTerm x y ∧ eqArgs xs ys
eqArgs _        _        = false

eqPats : (x y : Args Pattern) → Bool
eqPats []       []       = true
eqPats (x ∷ xs) (y ∷ ys) = eqArgPat x y ∧ eqPats xs ys
eqPats _        _        = false

eqClauses : (x y : Clauses) → Bool
eqClauses []       []       = true
eqClauses (x ∷ xs) (y ∷ ys) = eqClause x y ∧ eqClauses xs ys
eqClauses _        _        = false

eqTerm (var x args)      (var x₁ args₁)      = (x Nat.≡ᵇ x₁) ∧ eqArgs args args₁
eqTerm (con c args)      (con c₁ args₁)      = eqName c c₁ ∧ eqArgs args args₁
eqTerm (def f args)      (def f₁ args₁)      = eqName f f₁ ∧ eqArgs args args₁
eqTerm (lam v t)         (lam v₁ t₁)         = eqVisibility v v₁ ∧ eqAbsTerm t t₁
eqTerm (pat-lam cs args) (pat-lam cs₁ args₁) = eqClauses cs cs₁ ∧ eqArgs args args₁
eqTerm (pi a b)          (pi a₁ b₁)          = eqArgTerm a a₁ ∧ eqAbsTerm b b₁
eqTerm (agda-sort s)     (agda-sort s₁)      = eqSort s s₁
eqTerm (lit l)           (lit l₁)            = eqLiteral l l₁
eqTerm (meta x args)     (meta x₁ args₁)     = eqMeta x x₁ ∧ eqArgs args args₁
eqTerm unknown           unknown             = true
eqTerm _                 _                   = false

eqSort (set t)     (set t₁)     = eqTerm t t₁
eqSort (lit n)     (lit n₁)     = n Nat.≡ᵇ n₁
eqSort (prop t)    (prop t₁)    = eqTerm t t₁
eqSort (propLit n) (propLit n₁) = n Nat.≡ᵇ n₁
eqSort (inf n)     (inf n₁)     = n Nat.≡ᵇ n₁
eqSort unknown     unknown      = true
eqSort _           _            = false

eqPat (con c ps) (con c₁ ps₁) = eqName c c₁ ∧ eqPats ps ps₁
eqPat (dot t)    (dot t₁)     = eqTerm t t₁
eqPat (var x)    (var x₁)     = x Nat.≡ᵇ x₁
eqPat (lit l)    (lit l₁)     = eqLiteral l l₁
eqPat (proj f)   (proj f₁)    = eqName f f₁
eqPat (absurd x) (absurd x₁)  = x Nat.≡ᵇ x₁
eqPat _          _            = false

eqClause (clause tel ps t)      (clause tel₁ ps₁ t₁)     = eqTel tel tel₁ ∧ eqPats ps ps₁ ∧ eqTerm t t₁
eqClause (absurd-clause tel ps) (absurd-clause tel₁ ps₁) = eqTel tel tel₁ ∧ eqPats ps ps₁
eqClause _                      _                        = false

eqErrorPart : ErrorPart → ErrorPart → Bool
eqErrorPart (strErr s)  (strErr t)  = s String.== t
eqErrorPart (termErr t) (termErr u) = eqTerm t u
eqErrorPart (nameErr x) (nameErr y) = eqName x y
eqErrorPart _           _           = false
