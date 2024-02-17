-- Dijkstra monad with ghost state. In essence the specification is over state that isn't
-- used in the actual running program. This Ghost State represents some sort of state that isn't
-- normally available in the runtime, such as I/O, mutexes, other hosts/programs, etc.
import Lean.Elab.Tactic
import Aesop

import Mathlib.Tactic.HelpCmd

import EffSpec.Effect
import EffSpec.DMonad

open Effect DMonad

def GhostState (s a : Type) : Type := s → a × s

instance : Functor (GhostState s) where
    map := fun f m v => let ⟨a,v'⟩ := m v
                        ⟨f a, v'⟩

instance : LawfulFunctor (GhostState s) where
    map_const := by intro a b; rfl
    id_map := by intro a x; rfl
    comp_map := by aesop

def retGhostState {s a : Type} : a → GhostState s a := fun x s => ⟨x,s⟩

def bindGhostState {s a b : Type} (m : GhostState s a) (f : a → GhostState s b) : GhostState s b :=
    fun v => let ⟨x,v'⟩ := m v
             f x v'

instance : Monad (GhostState s) where
    pure := retGhostState
    bind := bindGhostState

instance : LawfulMonad (GhostState s) where
    pure_seq := by intro a b g x; rfl
    pure_bind := by intro a b x f; rfl
    bind_map := by intro a b f x; rfl
    bind_assoc := by intro a b y x f g; rfl
    bind_pure_comp := by intro a b f x; rfl
    seqLeft_eq := by intro a b x y; rfl
    seqRight_eq := by intro a b x y; rfl


def GhostSpec (s a : Type) : Type := (a × s → Prop) → s → Prop

instance : Functor (GhostSpec s) where
    map := fun f w post => w (fun ⟨a,s⟩ => post ⟨f a, s⟩)

instance : LawfulFunctor (GhostSpec s) where
    map_const := by intro a b; rfl
    id_map := by intro a x; rfl
    comp_map := by aesop

def retGhostSpec {s a : Type} : a → GhostSpec s a :=
    fun x post s => post ⟨x,s⟩

def bindGhostSpec {s a b : Type} (w₁ : GhostSpec s a) (w₂ : a → GhostSpec s b) : GhostSpec s b :=
    fun post s₀ => w₁ (fun ⟨x,s₁⟩ => w₂ x post s₁) s₀

instance : Monad (GhostSpec s) where
    pure := retGhostSpec
    bind := bindGhostSpec

instance : LawfulMonad (GhostSpec s) where
    pure_seq := by intro a b g x; rfl
    pure_bind := by intro a b x f; rfl
    bind_map := by intro a b f x; rfl
    bind_assoc := by intro a b y x f g; rfl
    bind_pure_comp := by intro a b f x; rfl
    seqLeft_eq := by intro a b x y; rfl
    seqRight_eq := by intro a b x y; rfl


-- mapping from the commands of a specific effect to state monads
def ghostOpObs (e : Effect) (s : Type) : Type 1 := (a : Type) → Eff e a → GhostState s a

class WeakenOpObs (obs : ghostOpObs e state) where
    pureObs {a : Type} {x : a} {s : state} : obs a (.Pure x) s = ⟨x,s⟩
    bindObs {a b : Type} {s : state} {m₁ : Eff e a} {m₂ : a → Eff e b} : obs b (m₁ >>= m₂) s = (obs a m₁ >>= fun x => obs b (m₂ x)) s

-- effect observations
def ghostStateObs (s : Type) (a : Type) : GhostState s a → GhostSpec s a :=
    fun m post s => post (m s)

def ghostEffObs (e : Effect) (s : Type) (a : Type) : Type := Eff e a → GhostSpec s a

def composeGhostObs (e : Effect) (state : Type) (opObs : ghostOpObs e state) (a : Type) : Eff e a → GhostSpec state a :=
    ghostStateObs state a ∘ opObs a



instance {state : Type} {opObs : ghostOpObs e state} [WeakenOpObs opObs] : OrderedRelation (Eff e) (GhostSpec state) (fun {a : Type} => composeGhostObs e state opObs a) where
    weaken := fun r₁ r₂ => ∀ post s, r₂ post s → r₁ post s
    weakenRfl := by simp
    weakenTrans := by intros _x A B C f₁ f₂ post s
                      exact f₁ post s ∘ f₂ post s
    weakenPure := by intros a x post s₁
                     unfold composeGhostObs ghostStateObs pure Applicative.toPure Monad.toApplicative
                     unfold instMonadGhostSpec instMonadEff
                     simp
                     unfold retGhostSpec instApplicativeEff
                     simp
                     rw [@WeakenOpObs.pureObs e state opObs]
                     simp
    weakenBind := by intros a b m₁ m₂ w₁ w₂ mrel frel
                     unfold composeGhostObs ghostStateObs
                     unfold composeGhostObs ghostStateObs at mrel
                     unfold composeGhostObs ghostStateObs at frel
                     simp_all
                     intros post s
                     rw [@WeakenOpObs.bindObs e state opObs _]
                     unfold Bind.bind Monad.toBind instMonadGhostSpec instMonadGhostState
                     simp_all
                     unfold bindGhostSpec bindGhostState
                     simp
                     intro  h
                     apply frel
                     apply mrel (fun x => w₂ x.fst post x.snd)
                     exact h



inductive StateEff (state : Type) : Type where
| Put : state → StateEff state
| Get : StateEff state

def StateEffect (state : Type) : Effect :=
    {
        op := StateEff state
        result := fun e => match e with
                           | .Put s => Unit
                           | .Get => state
    }

def StateEffObs (state : Type) (a : Type) : Eff (StateEffect state) a → GhostState state a
| .Pure x => fun s => ⟨x,s⟩
| .Step .Get next => fun s => StateEffObs state a (next s) s
| .Step (.Put s') next => fun _ => StateEffObs state a (next ()) s'

instance {state : Type} : WeakenOpObs (StateEffObs state) where
    pureObs := by unfold StateEffObs; simp
    bindObs := by intros a b s m₁ m₂
                  unfold StateEffObs bind Monad.toBind instMonadGhostState instMonadEff
                  simp_all
                  unfold bindEff joinEff mapEff
                  induction m₁ generalizing s
                  unfold bindGhostState
                  simp
                  rename_i c next ih
                  simp_all
                  cases c
                  simp_all
                  rename_i s'
                  conv => {rhs; arg 1; unfold StateEffObs; {}}
                  conv => {lhs; unfold StateEffObs joinEff mapEff}
                  simp_all
                  rfl
                  simp_all
                  conv => {rhs; arg 1; unfold StateEffObs; {}}
                  conv => {lhs; unfold StateEffObs joinEff mapEff}
                  simp_all
                  rfl


def prepostStateM (s a : Type) (pre : s → Prop) (post : a × s → Prop) : Type :=
    PSigma pre → PSigma post

def wpt (s a : Type) (pre : s → Prop) (post : a × s → Prop) := (PSigma post → Prop) → PSigma pre → Prop

def toWPT (s a : Type) {pre : s → Prop} {post : a×s → Prop} (pp : prepostStateM s a pre post) : wpt s a pre post :=
    --fun post0 v => pre v ∧ ∀ a v2, post ⟨a,v2⟩ → post0 ⟨a,v2⟩
    fun post0 s0 => post0 <| pp s0

def bindwpt {s a b: Type} {pre1 pre2 : s → Prop} {post1 : a × s → Prop} {post2 : b × s → Prop}
    (m : wpt s a pre1 post1)
    (f : a → wpt s b pre2 post2)
    : wpt s b (fun v => pre1 v ∧ ∀ a, post1 ⟨a,v⟩ → pre2 v) post2 :=
      fun post0 pf0 =>
          let m2 := m _
          _



def prog1P : prepostStateM Nat Unit (fun s => s < 3) (fun x => x.2 < 5) :=
    fun ⟨s,pf⟩ => PSigma.mk ⟨(),s+1⟩ (by simp; apply Nat.succ_lt_succ; apply Nat.lt_trans pf (show 3<4 by simp))

def bindPrepost {s a b: Type} {pre1 pre2 : s → Prop} {post1 : a × s → Prop} {post2 : b × s → Prop}
    (m : prepostStateM s a pre1 post1)
    (f : a → prepostStateM s b pre2 post2)
    : prepostStateM s b (fun v₁ => pre1 v₁ ∧ ∀ (v₂ :s) (x : a), post1 ⟨x,v₂⟩ → pre2 v₂)
                        (fun x => post2 x ∧ ∃ z, post1 z)
    :=
    fun ⟨v₁,pf₁⟩ =>
        let ⟨z,pz⟩ := m ⟨v₁,pf₁.1⟩
        let pf₂ := pf₁.2 z.2 z.1 pz
        let q := f z.1 ⟨z.2,pf₂⟩
        PSigma.mk q.1 (by apply And.intro
                          exact q.2
                          exact Exists.intro z pz)


def prog1 : prepostStateM Nat Unit (fun x => True) (fun z => z.2 < 3):=
  fun ⟨s,pf⟩ => PSigma.mk ⟨(),2⟩ (by simp)

def prog2 : prepostStateM Nat Unit (fun x => x < 3) (fun z => z.2 < 4) :=
  fun ⟨s,pf⟩ => PSigma.mk ⟨(),s⟩ (by simp; apply Nat.lt_trans pf (show 3<4 by simp))

#check bindPrepost prog1 (fun x => prog2)

def prog1spec (n : Nat) : ∀s, s < n → ∃ s₂, s₂ = (prog1 s).2 ∧ s₂ < n + 1 := by
    intros s h
    let s₂ := s + 1
    exact Exists.intro s₂ (by unfold prog1
                              simp
                              apply Nat.succ_lt_succ
                              exact h)

def prog2spec (n : Nat) : ∀s, s < n → (prog2 s).2 < n := by
    intros s h
    unfold prog2
    simp_all

def p12spec (n : Nat) (h : n > 0) : ∃ s, s < n := Exists.intro 0 (Nat.zero_lt_of_ne_zero <| Nat.ne_of_gt h)
def pxxspec : ∀ (s : Nat), ∃ (h : 0 <= s), True := by intros s; simp

#check @Exists.elim _ _ (1 < 2) (p12spec 1 (by simp)) (prog1spec 1)

-- spec containing pre/post conditions for a given effect
structure effGhostSpec (e : Effect) (s : Type) : Type where
    pre : e.op → s → Prop
    post : (c : e.op) → s → (e.result c × s) → Prop

-- Eff algebra for props
def propEffGhost (e : Effect) (s : Type) (Q : effGhostSpec e s) : Eff e (s → Prop) → s → Prop
| .Pure p => p
| .Step c next => fun s₁ => Q.pre c s₁ ∧ ∀ (o : e.result c) (s₂ : s), Q.post c s₁ ⟨o,s₂⟩ → propEffGhost e s Q (next o) s₂

-- map Eff to a PureSpec
def effToGhostSpec (e : Effect) (s : Type) (Q : effGhostSpec e s) : Eff e a → GhostSpec s a :=
    fun m post => propEffGhost e s Q (mapEff (fun a s => post ⟨a,s⟩) m)

-- handler mapping to an effSpec
def effSpecHandler (e : Effect) (Q : effGhostSpec e s) := (c : e.op) → (s₁ : s) → Q.pre c s₁ → PSigma (fun (r : e.result c × s) => Q.post c s₁ r)

instance {e : Effect} {Q : effGhostSpec e s} : OrderedRelation (Eff e) (GhostSpec s) (effToGhostSpec e s Q) where
    weaken := fun rm w => ∀ post s, w post s → rm post s
    weakenRfl := fun A => by simp
    weakenTrans := fun a b post s => a post s ∘ b post s
    weakenPure := by intros a x post
                     unfold effToGhostSpec mapEff
                     unfold pure Applicative.toPure Monad.toApplicative instMonadGhostSpec
                     simp; unfold retGhostSpec
                     intros; assumption
    weakenBind := by intros a b m₁ m₂ w₁ w₂
                     unfold effToGhostSpec
                     intros mrel frel
                     unfold bind Monad.toBind instMonadEff instMonadGhostSpec bindGhostSpec bindEff
                     simp_all;
                     induction m₁ with
                     | Pure a =>
                        intros post state w1post
                        simp_all
                        apply frel a post state
                        apply mrel (fun x => w₂ x.1 post x.snd)
                        exact w1post
                     | Step c next ih =>
                        intros post s₁ w1post
                        simp_all
                        unfold bindEff mapEff propEffGhost
                        simp_all
                        apply And.intro
                        let pz := mrel (fun x => w₂ x.1 post x.2) s₁ w1post
                        exact pz.1
                        intro o s₂ qpost
                        apply frel
                        apply ih o _
                        --let pz := fun post s wpost => (p₁ post s wpost).2 o s
                        let pz := (mrel (fun x => (w₂ x.1 post x.2)) s₁ w1post).2 o s₂ qpost
                        unfold propEffGhost mapEff at pz
                        simp at pz
                        {}





def Dec3Nat := ∀ s₁ s₂, s₁ > 3 → s₂ = s₁ - 1

def Dec3Pre := ∃ s, s > 3
