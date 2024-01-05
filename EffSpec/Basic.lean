import Std

import Lean
import Lean.Elab.Tactic

import Init.Control.Lawful
import Mathlib.Tactic.HelpCmd
import Mathlib.Tactic.convert

import Aesop

open Lean.Meta Lean.Elab.Tactic

namespace Basic

-- provide a simple/default m-Algebra for certain monads
class AutoMAlgebra (m : Type → Type) where
    autoAlg : m a → a

def handleM [Functor m] (mAlgebra : m b → b) (f : a → b) : m a → b := mAlgebra ∘ Functor.map f

-- handleM specialized to a monad result, for better type inference
def handleMW {m w : Type → Type} [Functor m] (mAlgebra : m (w b) → w b) (f : a → w b) : m a → w b := mAlgebra ∘ Functor.map f

-- note that if you have [AutoMAlgebra m] then you can just use autoAlg.
-- This provides a path using [Monad m] instead.
def joinM {m : Type → Type} [Monad m] : m (m a) → m a := fun c => c >>= id

end Basic
