import Mathlib.Tactic.HelpCmd
import Mathlib.Tactic.convert

import EffSpec.Effect

open Effect

def hello := "world"

inductive OneOp : Type where
| One : OneOp

def OneEffect : Effect :=
    {
        op := OneOp
        result := fun _ => Nat
    }

def OneEffQ (c : OneEffect.op) (o : OneEffect.result c) : Prop :=
    match c with
    | .One => let o' : Nat := o; o' < 3
