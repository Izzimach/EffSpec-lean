import Std

import Lean
import Lean.Elab.Tactic

import Init.Control.Lawful
--import Mathlib.Tactic.HelpCmd
import Mathlib.Tactic.convert
import Mathlib.Logic.Function.Basic

import Aesop

import EffSpec.DMonad

open DMonad

open Lean.Meta Lean.Elab.Tactic

structure Effect : Type 1 where
    op : Type
    result : op → Type

namespace Effect

-- standard freer monad
inductive Eff (e : Effect) (a : Type) : Type where
| Pure : a → Eff e a
| Step : (c : e.op) → (e.result c → Eff e a) → Eff e a

def genOp (e : Effect) (c : e.op) : Eff e (e.result c) := .Step c .Pure

def mapEff (f : a → b) : Eff e a → Eff e b
| .Pure x => .Pure (f x)
| .Step c next => .Step c (fun o => mapEff f (next o))

instance : Functor (Eff e) where
    map := mapEff


def seqEff (f : Eff e (a → b)) (m : Unit → Eff e a) : Eff e b :=
    match f with
    | .Pure g => mapEff g (m ())
    | .Step c next => .Step c (fun o => seqEff (next o) m)

instance : Applicative (Eff e) where
    pure := .Pure
    seq := seqEff


instance : LawfulFunctor (Eff e) where
    map_const := by intros a b; rfl
    id_map := by intros a x
                 unfold Functor.map instFunctorEff; simp; unfold mapEff
                 induction x with
                 | Pure h => simp
                 | Step c next h => unfold mapEff; simp; funext x; exact h x
    comp_map := by intros a b g f h x
                   unfold Functor.map instFunctorEff Function.comp; simp; unfold mapEff
                   induction x <;> unfold mapEff
                   simp; simp; rename_i h; funext x; exact h x

instance : LawfulApplicative (Eff e) where
    seqLeft_eq := by intros a b x y
                     unfold SeqLeft.seqLeft Seq.seq Function.const Applicative.toSeqLeft Applicative.toSeq instApplicativeEff
                     simp; unfold seqEff Function.const; simp
    seqRight_eq := by intros a b x y
                      unfold SeqRight.seqRight Seq.seq Function.const Applicative.toSeqRight Applicative.toSeq instApplicativeEff
                      simp; unfold seqEff Function.const; simp
    pure_seq := by intros a b g x
                   unfold Seq.seq pure Functor.map Applicative.toSeq Applicative.toPure Applicative.toFunctor instApplicativeEff
                   simp; unfold seqEff instFunctorEff
                   rfl
    map_pure := by intros a b f x
                   unfold pure Functor.map Applicative.toPure Applicative.toFunctor instApplicativeEff
                   simp; unfold instFunctorEff mapEff
                   rfl
    seq_pure := by intros a b g x
                   unfold Seq.seq pure Functor.map Applicative.toSeq Applicative.toFunctor Applicative.toPure instApplicativeEff
                   simp; unfold seqEff instFunctorEff
                   induction g with
                   | Pure x => simp; unfold mapEff; rfl
                   | Step c next h => unfold seqEff mapEff; simp; funext x; exact h x
    seq_assoc := by intros a b x m g h
                    unfold Seq.seq Applicative.toSeq Function.comp Functor.map Applicative.toFunctor instApplicativeEff
                    simp; unfold seqEff instFunctorEff mapEff
                    induction m with
                    | Pure x =>
                        induction h with
                        | Pure y =>
                            simp; unfold seqEff mapEff
                            induction g with
                            | Pure z => unfold mapEff; simp
                            | Step e next₃ h₃ =>
                                simp
                                unfold mapEff seqEff;
                                funext o; exact h₃ o
                        | Step d next₂ h₂ =>
                            simp
                            unfold seqEff mapEff; simp
                            funext o; apply h₂ o
                    | Step c next₁ h₁ =>
                        induction h with
                        | Pure y =>
                            simp_all
                            induction g with
                            | Pure z =>
                                unfold seqEff mapEff
                                unfold seqEff mapEff; simp
                                unfold seqEff mapEff at h₁; simp at h₁
                                funext o; rw [h₁ o]
                            | Step e next₃ h₃ =>
                                unfold seqEff mapEff; simp
                                unfold seqEff mapEff at h₁; simp at h₁
                                funext o; apply h₃ o
                                intros a1
                                apply congrFun (h₁ a1)
                        | Step d next₂ h₂ =>
                            simp_all
                            unfold seqEff mapEff; simp
                            unfold seqEff mapEff at h₁; simp at h₁
                            funext o; apply h₂ o
                            intros a1
                            apply congrFun (h₁ a1)



def bindEff (m : Eff e a) (f : a → Eff e b) : Eff e b :=
    match m with
    | .Pure x => f x
    | .Step c next => .Step c (fun o => bindEff (next o) f)

instance : Monad (Eff e) where
    bind := bindEff

instance : LawfulMonad (Eff e) where
    bind_pure_comp := by unfold bind Monad.toBind instMonadEff
                         simp; unfold bindEff; intros a b f x
                         induction x with
                         | Pure a => simp; rw [←LawfulApplicative.map_pure]; rfl
                         | Step c next h =>
                            simp; unfold Functor.map Applicative.toFunctor instApplicativeEff
                            simp; unfold instFunctorEff mapEff
                            simp; unfold bindEff
                            funext o; apply h o
    bind_map := by unfold bind Monad.toBind instMonadEff Seq.seq Applicative.toSeq instApplicativeEff
                   simp; unfold bindEff seqEff
                   intros a b f x_1
                   induction f with
                   | Pure a => rfl
                   | Step c next h =>
                        simp; unfold bindEff seqEff
                        funext o; apply h o
    pure_bind := by unfold bind Monad.toBind instMonadEff; simp; unfold bindEff; simp
    bind_assoc := by intros a b c x f g
                     unfold bind Monad.toBind instMonadEff bindEff; simp
                     induction x with
                     | Pure a =>
                        unfold bindEff
                        induction f a with
                        | Pure b => simp
                        | Step e next h₂ =>
                            unfold bindEff; simp
                            funext o; apply h₂ o
                     | Step d next h₁ =>
                        unfold bindEff; simp
                        funext o; apply h₁ o

-- standard "algebraic effect" algebra
def EffAlgebra (e : Effect) (a : Type) : Type := (c : e.op) → (e.result c → a) → a

def handleEff (h : EffAlgebra e b) (f : a → b) : Eff e a → b
| .Pure x => f x
| .Step c next => h c (fun o => handleEff h f (next o))

-- spec containing pre/post conditions for a given effect
structure effSpec (e : Effect) : Type where
    pre : e.op → Prop
    post : (c : e.op) → e.result c → Prop

-- Eff algebra for props
def propEff (e : Effect) (Q : effSpec e) : Eff e Prop → Prop
| .Pure p => p
| .Step c next => Q.pre c ∧ ∀ (o : e.result c), Q.post c o → propEff e Q (next o)

-- map Eff to a PureSpec
def effToPureSpec (e : Effect) (Q : effSpec e) : Eff e a → PureSpec a :=
    fun m post => propEff e Q (Functor.map post m)

-- handler mapping to an effSpec
def effSpecHandler (e : Effect) (Q : effSpec e) := (c : e.op) → Q.pre c → PSigma (fun (o : e.result c) => Q.post c o)


-- to build a PreR using a relation `Eff e a → PureSpec a` we need an `OrderedRelation`
instance {e : Effect} {Q : effSpec e} : OrderedRelation (Eff e) PureSpec (effToPureSpec e Q) where
    weaken := fun rm w => ∀ post, w post → rm post
    weakenRfl := fun A => by simp
    weakenTrans := fun a b post => a post ∘ b post
    weakenPure := by intros a x post
                     unfold effToPureSpec Functor.map instFunctorEff mapEff propEff
                     unfold pure Applicative.toPure Monad.toApplicative instMonadPureSpec
                     simp; unfold retPureSpec
                     intros; assumption
    weakenBind := by intros a b m₁ m₂ w₁ w₂
                     unfold effToPureSpec propEff Functor.map instFunctorEff
                     simp; unfold bind Monad.toBind instMonadEff instMonadPureSpec bindPureSpec bindEff
                     simp;
                     induction m₁ with
                     | Pure a =>
                        intros p₁ p₂ post wpost
                        simp_all
                        apply p₂ a post
                        apply p₁ (fun x => w₂ x post)
                        exact wpost
                     | Step c next h =>
                        intros p₁ p₂ post wpost
                        simp_all
                        unfold bindEff mapEff propEff; simp
                        unfold mapEff propEff at p₁; simp at p₁
                        apply And.intro
                        let pz := p₁ (fun x => w₂ x post) wpost
                        exact pz.1
                        intro o qpost
                        apply h o
                        intro post w1post
                        let pz := p₁ post w1post
                        apply pz.2 o qpost
                        exact wpost


-- a Dijkstra monad built on the free monad `Eff` with some effect `e` and a pure-only spec
def pureDEff (e : Effect) (Q : effSpec e) : (a : Type) → PureSpec a → Type :=
    PreR (Eff e) PureSpec (effToPureSpec e Q)

-- a handler for a Dijkstra monad built on `Eff`
def DEHandleOp (e : Effect) (Q : effSpec e) := (c : e.op) → Q.pre c → @PSigma (e.result c) (Q.post c)

def handleDEEff2aux
                {A B : Type}
                {mpost : A → Prop}
                {R : B → Prop}
                (m : Eff e A)
                (pf : @OrderedRelation.weaken (Eff e) PureSpec _ _ (effToPureSpec e Q) _ A (effToPureSpec e Q m) (fun (post : A → Prop) => ∀ o, mpost o → post o))
                (f : (x : A) → mpost x → PSigma R)
                (handleOp : DEHandleOp e Q)
                : PSigma R :=
    match m with
    | .Pure x => f x (pf mpost (by simp))
    | .Step c next => by
        let y' := pf mpost (by simp)
        unfold effToPureSpec propEff Functor.map instFunctorEff mapEff at y'
        simp at y'
        let ⟨r, fp⟩ := handleOp c y'.left
        exact handleDEEff2aux
                (next r)
                (by let pf' : @OrderedRelation.weaken (Eff e) PureSpec _ _ (fun {a} => effToPureSpec e Q) _ _ (effToPureSpec e Q (next r)) (effToPureSpec e Q (Eff.Step c next)) :=
                                         by unfold OrderedRelation.weaken instOrderedRelationEffPureSpecInstMonadEffInstMonadPureSpecTypeEffToPureSpec
                                            simp
                                            intros post wpre
                                            unfold effToPureSpec propEff Functor.map instFunctorEff mapEff at wpre
                                            unfold effToPureSpec propEff Functor.map instFunctorEff mapEff
                                            simp_all
                                            cases h : (next r)
                                            let hx := wpre.right r fp
                                            rw [h] at hx
                                            unfold propEff mapEff at hx
                                            exact hx
                                            let hx := wpre.right r fp
                                            rw [h] at hx
                                            unfold propEff mapEff at hx
                                            simp at hx
                                            simp_all
                    apply OrderedRelation.weakenTrans pf' pf)
            f handleOp


def handleDEEff2 {mpost : A → Prop} (m : pureDEff e Q A (fun (post : A → Prop) => ∀ o, mpost o → post o))
                 (f : (x : A) → mpost x → PSigma R)
                 (handleOp : DEHandleOp e Q)
                 : PSigma R :=
    match m with | ⟨c,pf⟩ => handleDEEff2aux c pf f handleOp


end Effect
