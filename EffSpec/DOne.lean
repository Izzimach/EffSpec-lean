--
-- The (almost) simplest possible dijkstra monad built using a simple stateless monad and an observation into PureSpec.
-- Mostly for instructional purposes.
--
import Std

import Aesop

import EffSpec.Basic
import Effspec.DMonad


open DMonad

@[aesop safe default]
inductive OneEff (a : Type) : Type where
| One : a → OneEff a

@[aesop norm unfold]
def bindOneEff (m : OneEff a) (f : a → OneEff b) : OneEff b :=
    match m with
    | .One x => f x

instance : Monad OneEff where
    pure := OneEff.One
    bind := bindOneEff

@[aesop norm]
theorem bindOneEffPure (m : OneEff a) (f : a → OneEff b) : m >>= f = f (m.1) := by rfl

@[aesop norm unfold]
def oneObs {a : Type} : OneEff a → PureSpec a
| .One x => fun post => post x

instance : @OrderedRelation OneEff PureSpec _ _ oneObs where
    weaken := fun r₁ r₂ => ∀ post, r₂ post → r₁ post
    weakenRfl := by simp
    weakenTrans := by intros _x A B C f₁ f₂ post
                      exact f₁ post ∘ f₂ post
    weakenPure := by unfold oneObs pure Applicative.toPure Monad.toApplicative instMonadOneEff instMonadPureSpec
                     simp
                     unfold retPureSpec
                     simp
    weakenBind := by intros a b m₁ m₂ w₁ w₂
                     unfold PureSpec oneObs
                     simp
                     unfold bindOneEff bind Monad.toBind instMonadPureSpec
                     simp
                     unfold bindPureSpec
                     intros r₁ r₂ post h
                     apply r₂
                     apply r₁ (fun x => w₂ x post)
                     exact h


-- A simple dijkstra monad with a simple  monad (OneEff) and PureSpec for the spec
def DOne : (a : Type) → PureSpec a → Type := PreR OneEff PureSpec oneObs

-- just re-use ret/bind from PreR
instance : DMonad DOne where
    retD := @DMonad.retD PureSpec _ (PreR OneEff PureSpec oneObs) _
    bindD := @DMonad.bindD PureSpec _ (PreR OneEff PureSpec oneObs) _


-- a basic "program" in DOne
open DMonad in
def somestuff :=
    show DOne Nat _ from
        retD 9 >>w retD 6

-- Alternate version where we bind the monads and THEN apply oneObs observation
-- We can manually write the desired specification but we also have to prove it manually. Maybe aesop will be helpful here
def somestuff2 : DOne Nat (pure 8) :=
        let m : OneEff Nat := pure 9 >>= fun _=> pure 8
        PreR.mk m (by unfold pure Applicative.toPure Monad.toApplicative instMonadPureSpec OrderedRelation.weaken
                      unfold oneObs
                      simp
                      unfold pure Applicative.toPure Monad.toApplicative instMonadOneEff retPureSpec bindOneEff
                      simp
                      unfold instOrderedRelationOneEffPureSpecInstMonadOneEffInstMonadPureSpecTypeOneObs
                      simp)


def runDOne (dm : DOne a w) (post : a → Prop) : w post → PSigma post :=
    match dm with
    | ⟨.One x, rel⟩ => fun pre => PSigma.mk x (rel post pre)

def x := runDOne somestuff (fun a => a > 3)

#check x (by simp; unfold pure Applicative.toPure Monad.toApplicative instMonadPureSpec; simp; unfold retPureSpec; simp [Nat.succ_lt_succ, Nat.lt.step])

macro "weakenSpec" : tactic => `(tactic | {simp; unfold pure Applicative.toPure Monad.toApplicative instMonadPureSpec; simp; unfold retPureSpec; simp; simp [Nat.succ_lt_succ, Nat.lt.step]})

-- A macro to run a DOne program. This macro tries to automatically prove/generate the required precondition computed from
-- the provided postcondition.
macro "runDM" prog:term ">!" post:term : term => `(runDOne $prog $post (by weakenSpec))

#check runDM somestuff >! (fun a => a > 4)
