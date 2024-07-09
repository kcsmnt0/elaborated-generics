{-# OPTIONS --without-K --safe #-}

module Generics.Internal.Error where

open import Generics.Reflection.Internal.Core

open import Data.List using (List; []; _∷_; [_])
open import Function using (_$_)
open import Reflection.AST.Show using (showTerm)

private variable
  A : Set _

notEndIn : ErrorPart → ErrorPart → TC A
notEndIn s n = typeError (strErr "Type of"
                       ∷ s
                       ∷ strErr "does not end in "
                       ∷ n
                       ∷ [])

#idxNotMatch : TC A
#idxNotMatch = typeError [ strErr "number of indices doesn't match." ]

notλ : Term → TC A
notλ t = typeError $ strErr (showTerm t) ∷ strErr " cannot be reduced further to a λ-abstraction" ∷ []

notDef : Term → TC A
notDef t = typeError $ termErr t ∷ strErr " is not a definition." ∷ []

notApp : Term → TC A
notApp t = typeError $ termErr t ∷ strErr " is not an application witha name." ∷ []

notFun : Name → TC A
notFun d = typeError $ nameErr d ∷ [ strErr " is not a function." ]

notData : Term → TC A
notData t = typeError $ termErr t ∷ [ strErr " is not a datatype." ]

IMPOSSIBLE : TC A
IMPOSSIBLE = typeError $ [ strErr "An impossible event occurs." ]

IMPOSSIBLE-term : Term → TC A
IMPOSSIBLE-term t = typeError $ termErr t ∷ [ strErr " should not occur" ]
