{-# OPTIONS --safe --without-K #-}

module Generics.Reflection.Internal.Tactic where

open import Generics.Reflection.Internal.Core
open import Generics.Reflection.Internal.Term

import Generics.Internal.Error as Err

open import Data.Bool using (Bool; true; false)
open import Data.Nat using (ℕ; zero; suc)
open import Data.List using (List; []; _∷_; [_]; drop)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Data.String using (String; _++_)
open import Data.Unit using (⊤)
open import Function using (_∘_; _$_)
open import Level using (Level; Setω)
open import Reflection.AST.Show
open import Reflection.TCM
open import Reflection.TCM.Syntax

import Data.List.Effectful as List
import Reflection.TCM.Effectful as TCM

private variable
  ℓ ℓ′ : Level
  A : Set ℓ

dprint = debugPrint "meta" 5

give : Term → Tactic
give v = λ hole → unify hole v

define : Arg Name → Type → Clauses → TC ⊤
define f a cs = declareDef f a >> defineFun (unArg f) cs

define! : Arg Type → Clauses → TC Name
define! (arg i a) cs = do
  f ← freshName "_"
  define (arg i f) a cs
  pure f

extend*Context : Telescope → TC A → TC A
extend*Context []              m = m
extend*Context ((s , a) ∷ tel) m = extendContext s a (extend*Context tel m)

_onClause_ : (Term → TC Term) → Clause → TC Clause
f onClause (tel ⊢ ps `= t) = do
  u ← extend*Context tel (f t)
  pure $ tel ⊢ ps `= u
f onClause cl = pure cl

_onClauses_ : (Term → TC Term) → Clauses → TC Clauses
_onClauses_ f = List.TraversableA.mapA TCM.applicative (f onClause_)

checkClauses : Clauses → Type → TC Clauses
checkClauses cls `A = do
  pat-lam₀ cls ← checkType (pat-lam₀ cls) `A
    where _ → Err.IMPOSSIBLE
  pure cls
  
quoteTC! : A → TC Term
quoteTC! a = withNormalisation true (quoteTC a)

quoteωTC! : {A : Setω} → A → TC Term
quoteωTC! a = withNormalisation true (quoteωTC a)

newMeta! : TC Term
newMeta! = newMeta unknown

typeErrorS : String → TC A
typeErrorS s = typeError (strErr s ∷ [])

blockOnMeta! : Meta → TC A
blockOnMeta! x = commitTC >>= λ _ → blockOnMeta x

inferNormalisedType : Term → TC Type
inferNormalisedType t = withNormalisation true (inferType t)

formatErrorPart : ErrorPart → TC String
formatErrorPart = formatErrorParts ∘ [_]

defineUnify : Arg String → Type → Term → Term → TC Name
defineUnify (arg i ns) ty tm hole = do
  n ← freshName ns
  declareDef (arg i n) ty
  defineFun n [ [] ⊢ [] `= tm ]

  unify hole (def₀ n)

  pure n
  
evalTC : TC A → Tactic
evalTC {A = A} c hole = do
  v  ← c
  `v ← quoteTC v
  `A ← quoteTC A
  checkedHole ← checkType hole `A
  unify checkedHole `v

macro
  evalT : TC A → Tactic
  evalT = evalTC

-- Typed version of extendContext
exCxtT : String → ArgInfo → (B : Set ℓ)
  → (Type → B → TC A) → TC A
exCxtT s i B f = do
  `B ← quoteTC! B
  extendContext s (arg i `B) do
    x ← unquoteTC {A = B} (var₀ 0)
    f `B x

getConTelescope : Name → (pars : ℕ) → TC Telescope
-- getConTelescope c pars = drop pars ∘ proj₁ ∘ (coerce'_to (Telescope × Type)) <$> getType c
getConTelescope c pars = drop pars ∘ proj₁ ∘ typeToTelescope <$> getType c

getAbsName : {A : Set ℓ} {B : A → Set ℓ′} → ((x : A) → B x) → TC String
getAbsName f = quoteTC! f >>= λ { (lam visible (abs s _)) → pure s ; t → Err.notλ t }

getAbsNameω : {A : Set ℓ} {B : A → Setω} → ((x : A) → B x) → TC String
getAbsNameω f = quoteωTC! f >>= λ { (lam visible (abs s _)) → pure s ; t → Err.notλ t }

getFunction : Name → TC (Type × Clauses)
getFunction d = do
  function cs ← getDefinition d
    where t → Err.notFun d
  t ← getType d
  pure $ t , cs

getDataDefinition : Name → TC (ℕ × Names)
getDataDefinition d = do
  data-type pars cs ← getDefinition d
    where _ → Err.notData (def₀ d)
  pure $ pars , cs

getTelescope : Name → TC (Telescope × Type)
getTelescope s = ⦇ typeToTelescope (getType s) ⦈

macro
  getTelescopeT : Name → Tactic
  getTelescopeT s = evalTC $ getTelescope s

getSetLevel : Type → TC Term
getSetLevel (agda-sort (set t)) = pure t
getSetLevel (`Set n) = quoteTC (fromℕ n)
  where 
    fromℕ : ℕ → Level
    fromℕ zero = Level.zero
    fromℕ (suc n) = Level.suc (fromℕ n)
getSetLevel (def (quote Set) []) = pure (quoteTerm Level.zero)
getSetLevel (def (quote Set) (arg _ x ∷ [])) = pure x
getSetLevel t = quoteTC t >>= λ t →
                  typeError [ strErr $ showTerm t ++ " level error!" ]


-- Rename names in a telescope to the first letter of the given type,
-- if no name is given
renameUnderscore : Telescope → TC Telescope
renameUnderscore []        = pure []
renameUnderscore (("_" , x@(arg visible-relevant-ω `A)) ∷ as) = do
  s ← formatErrorPart $ termErr `A
  -- let s = ⇑ [ maybe′ toLower 'x' $ head (⇑ s ⦂ List Char) ]
  extendContext s x $ (("x" , x) ∷_) <$> renameUnderscore as
renameUnderscore (a@(s , x) ∷ as) = extendContext s x $ a ∷_ <$> renameUnderscore as
