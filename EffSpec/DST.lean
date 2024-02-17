--
-- Dijkstra monad built around a State Monad
--

import Lean.Elab.Tactic
import Aesop

import Mathlib.Tactic.HelpCmd

import EffSpec.DMonad

open DMonad

def StateSpec (s a : Type) : Type := (a × s → Prop) → s → Prop

instance : Functor (StateSpec s) where
    map := fun f w post => w (fun ⟨a,s⟩ => post ⟨f a, s⟩)

instance : LawfulFunctor (StateSpec s) where
    map_const := by intro a b; rfl
    id_map := by intro a x; rfl
    comp_map := by aesop

def bindStateSpec {s a b : Type} (w₁ : StateSpec s a) (w₂ : a → StateSpec s b) : StateSpec s b :=
    fun post s₀ => w₁ (fun ⟨x,s₁⟩ => w₂ x post s₁) s₀

instance : Monad (StateSpec s) where
    pure := fun x post s => post ⟨x,s⟩
    bind := bindStateSpec

instance : LawfulMonad (StateSpec s) where
    pure_seq := by intro a b g x; rfl
    pure_bind := by intro a b x f; rfl
    bind_map := by intro a b f x; rfl
    bind_assoc := by intro a b y x f g; rfl
    bind_pure_comp := by intro a b f x; rfl
    seqLeft_eq := by intro a b x y; rfl
    seqRight_eq := by intro a b x y; rfl



-- effect observations
def stateObs (s : Type) {a : Type} : StateM s a → StateSpec s a :=
    fun m post s => post (m s)

instance {s : Type} : OrderedRelation (StateM s) (StateSpec s) (stateObs s) where
    weaken := fun r₁ r₂ => ∀ post s, r₂ post s → r₁ post s
    weakenRfl := by simp
    weakenTrans := by intros _x A B C f₁ f₂ post s
                      exact f₁ post s ∘ f₂ post s
    weakenPure := by intros a x post s₁
                     unfold stateObs pure Applicative.toPure Monad.toApplicative instMonadStateSpec StateT.instMonadStateT
                     simp
                     unfold StateT.pure pure Applicative.toPure Monad.toApplicative Id.instMonadId
                     simp
    weakenBind := by intros a b m₁ m₂ w₁ w₂ mrel frel
                     unfold stateObs
                     unfold stateObs at mrel
                     unfold stateObs at frel
                     simp_all
                     intros post s1
                     unfold Bind.bind Monad.toBind instMonadStateSpec
                     simp
                     unfold bindStateSpec StateT.instMonadStateT
                     simp
                     unfold StateT.bind
                     simp
                     intro h
                     have hm := mrel (fun x => w₂ x.fst post x.snd)
                     have hf := fun x => frel x post
                     apply hf
                     apply hm
                     exact h

-- state monad with spec
/-structure DST (s a : Type) (w : StateSpec s a) : Type where
    (c : StateM s a) (p : ∀ (post : a × s → Prop) s₀, w post s₀ → post (c s₀))
-/
def DST (s : Type) : (a :Type) → StateSpec s a → Type := PreR (StateM s) (StateSpec s) (stateObs s)

instance : DMonad (DST s) where
    retD := @DMonad.retD (StateSpec s) _ (PreR (StateM s) (StateSpec s)  (stateObs s)) _
    bindD := @DMonad.bindD (StateSpec s) _ (PreR (StateM s) (StateSpec s)  (stateObs s)) _

def getDST : DST s s (fun post s₀ => post ⟨s₀,s₀⟩) :=
    PreR.mk
        (fun s => ⟨s,s⟩)
        (by unfold OrderedRelation.weaken stateObs instOrderedRelationStateMStateSpecInstMonadStateTIdInstMonadIdInstMonadStateSpecTypeStateObs
            simp)

def putDST (x : s) : DST s Unit (fun post _ => post ⟨(),x⟩) :=
    PreR.mk
        (fun _s => ⟨(),x⟩)
        (by unfold OrderedRelation.weaken stateObs instOrderedRelationStateMStateSpecInstMonadStateTIdInstMonadIdInstMonadStateSpecTypeStateObs
            simp)

#check DMonad.retD "argh"
#reduce (putDST 3) >>w DMonad.retD 4

def prog := show DST Nat String _ from putDST 4 >>w DMonad.retD "argh"

def runDST {s : Type} {w : StateSpec s a} (m : DST s a w) (post : a × s → Prop) (s₀ : s) : w post s₀ → PSigma post :=
    fun pre =>
        let compute := m.m s₀
        let pf : post compute := by apply m.rel post s₀; exact pre
        PSigma.mk compute pf

#reduce runDST prog (fun s => s.2 < 5) 2 _

macro "autosolve" : tactic =>
    `(tactic | aesop (add norm unfold bindStateSpec,
                          norm unfold bind,
                          norm unfold Monad.toBind,
                          norm unfold instMonadStateSpec,
                          safe apply Nat.succ_lt_succ,
                          safe apply Nat.zero_lt_succ))


--set_option trace.aesop true

def y := runDST prog (fun ⟨_a,s⟩ => s < 5) 3 (by autosolve)

def h : 2 < 5 := by apply Nat.lt_add_of_pos_left; apply Nat.zero_lt_succ

#reduce y
#check y

macro "goProg" prog:term "," post:term "," state:term : term => `(runDST $prog $post $state (by autosolve))


#check goProg prog, (fun (s : String × Nat) => s.2 < 5), 3
