import Lean.Elab.Tactic
import Aesop

import Mathlib.Tactic.HelpCmd

import EffSpec.DMonad
import EffSpec.Effect

open Effect

-- spec for a monad that accumulates a history of commands
def HistSpec (cmd a : Type) : Type := (a × List cmd → Prop) → (List cmd → Prop)

def mapHistSpec (f : a → b) (m : HistSpec cmd a) : HistSpec cmd b :=
    fun post log => m (fun x => post ⟨f x.1, x.2⟩) log

instance : Functor (HistSpec cmd) where
    map := mapHistSpec

/-
-- intuitive  HistSpec monad. We don't use this in favor of the accumulator version in the next section
def bindHistSpec {op a b : Type} (w₁ : HistSpec op a) (w₂ : a → HistSpec op b) : HistSpec op b :=
    fun post log => w₁ (fun ⟨x,log'⟩ => w₂ x post log') log

instance : Monad (HistSpec op) where
    pure := fun x post log => post ⟨x,log⟩
    bind := bindHistSpec

inductive IOHist (op a : Type) : HistSpec op a → Type 1 where
| Pure : (x : a) → (∀ post log, w post log → post ⟨x,log⟩) → IOHist op a w
| Step : (c : op) → (next : IOHist op a w₁) → (∀ post log, w₂ post log → w₁ post (log ++ [c])) → IOHist op a w₂

def retIOHist {a : Type} (x : a) : IOHist IOOp a (fun post log => post ⟨x,log⟩) :=
    IOHist.Pure x (by simp)

def ioCmd {op : Type} (o : op) : IOHist op Unit (fun post log => post ⟨(), log ++ [o]⟩) :=
    let pr := @IOHist.Pure op Unit (fun post log => post ⟨(),log⟩) () (by simp)
    IOHist.Step o pr (by simp)

def ioProg := show IOHist IOOp Unit _ from ioCmd (IOOp.Write "argh")

def bindIOHist {op a b : Type} {w₁ : HistSpec op a} (m : IOHist op a w₁) {w₂ : a → HistSpec op b}
    (f : (x : a) → IOHist op b (w₂ x))
    : IOHist op b (bindHistSpec w₁ w₂) :=
        match m with
        | .Pure x p =>
            match f x with
            | .Pure y p₂ => IOHist.Pure y (by unfold bindHistSpec
                                              simp
                                              intros post log h
                                              apply p₂
                                              revert h
                                              apply p)
            | .Step c next p₂ =>
                IOHist.Step c next (by unfold bindHistSpec
                                       simp
                                       rename_i w₃
                                       intros post log h
                                       apply p₂
                                       revert h
                                       apply p)
        | .Step c next p =>
                IOHist.Step
                    c
                    (bindIOHist next f)
                    (by rename_i w₃
                        unfold bindHistSpec
                        simp
                        intros post log
                        apply p (fun x => w₂ x.fst post x.snd))
-/


def pureHistSpecAccumulate {op a : Type} (x : a) : HistSpec op a :=
    fun post log => post ⟨x,[]⟩

-- the HistSpec bind that accumulates history
def bindHistSpecAccumulate {cmd a b : Type} (w₁ : HistSpec cmd a) (w₂ : a → HistSpec cmd b) : HistSpec cmd b :=
    fun post log => w₁ (fun ⟨x,log'⟩ => w₂ x (fun ⟨y,log''⟩ => post ⟨y,log' ++ log''⟩) (log ++ log')) log

instance : Monad (HistSpec cmd) where
    pure := pureHistSpecAccumulate
    bind := bindHistSpecAccumulate

-- relation to map from an Effect (Freer) monad to a HistSpec
def effHistObs (e : Effect) {a : Type} (ea : EffAlgebra e Prop) (f : a → Prop) : Eff e a → HistSpec (e.op) Prop
| .Pure x => pure x
| .Step c next => ea c next

-- alternative IOHist what applies postconditions only to the log of the local command
inductive IOHist2 (op a : Type) : HistSpec op a → Type 1 where
| Pure : (x : a) → (p : ∀ post log, w post log → post ⟨x,[]⟩) → IOHist2 op a w
| Step : (c : op) → (next : IOHist2 op a w₂) → (p : ∀ post log, w post log → bindHistSpecAccumulate (fun post log => post ⟨(), [c]⟩) (fun _ => w₂) post log) → IOHist2 op a w

/-
 For the .Step constructor w₁ is implied here as:
    - w₁ = fun post log => post ⟨(),[c]⟩
 and we'll take w to be a composition of w₁ and w₂:
    - w = bindHistSpecAccumulate w₁ w₂
 we'll beta-reduce w₁ in the expression for `bindHistSpecAccumulate w₁ w₂`:
    - fun post log => w₁ (fun ⟨x,log'⟩ => w₂ x (fun ⟨y,log''⟩ => post ⟨y, log' ++ log''⟩) (log ++ log')) log
    - fun post log =>                    w₂ () (fun ⟨y,log''⟩ => post ⟨y, [c] ++ log''⟩) (log ++ [c]))
 from this we can figure out what the postcondition proof `p` is for .Step
-/

def retIOHist2 {a : Type} (x : a) : IOHist2 IOOp a (pureHistSpecAccumulate x) :=
    IOHist2.Pure x (by unfold pureHistSpecAccumulate; simp)

def ioCmd2 {op : Type} (o : op) : IOHist2 op Unit (fun post log => post ⟨(), [o]⟩) :=
    let z := fun post log => post ⟨(),[]⟩
    let w : ∀ post log, z post log → post ⟨(),[]⟩ := by simp
    let pr := (@IOHist2.Pure op Unit z () w)
    IOHist2.Step o pr (by unfold bindHistSpecAccumulate; simp)

def ioProg2 := show IOHist2 IOOp Unit _ from ioCmd2 (IOOp.Write "argh")

def bindIOHist2 {op a b : Type} {w₁ : HistSpec op a} (m : IOHist2 op a w₁) {w₂ : a → HistSpec op b}
    (f : (x : a) → IOHist2 op b (w₂ x))
    : IOHist2 op b (bindHistSpecAccumulate w₁ w₂) :=
    match m with
    | .Pure x p₁ =>
        match f x with
        | .Pure y p₂ => IOHist2.Pure y (by unfold bindHistSpecAccumulate
                                           simp
                                           intros post log h
                                           let p₃ := p₁ (fun x => w₂ x.fst (fun x_1 => post (x_1.fst, x.snd ++ x_1.snd)) (log ++ x.snd)) log
                                           simp at p₃
                                           apply p₂ (fun x => post x) log
                                           apply p₃
                                           exact h)
        | .Step c next p₂ =>
            IOHist2.Step c next (by unfold bindHistSpecAccumulate
                                    rename_i w₃
                                    simp
                                    intros post log h
                                    unfold bindHistSpecAccumulate at p₂
                                    simp at p₂
                                    let p₃ := p₁ (fun x => w₂ x.fst (fun x_1 => post (x_1.fst, x.snd ++ x_1.snd)) (log ++ x.snd)) log
                                    simp at p₃
                                    apply p₂
                                    apply p₃
                                    exact h)

    | .Step c next p₁ =>
        IOHist2.Step c
                     (bindIOHist2 next f)
                     (by unfold bindHistSpecAccumulate
                         simp
                         rename_i w₃
                         intros post log
                         let p₃ := p₁ (fun x => w₂ x.fst (fun x_1 => post (x_1.fst, x.snd ++ x_1.snd)) (log ++ x.snd)) log
                         simp at p₃
                         apply p₃)


syntax term ">>=i" term : term
syntax term ">>i" term : term

macro_rules
| `($a >>=i $b) => `(bindIOHist2 $a $b)
| `($a >>i $b) => `(bindIOHist2 $a (fun _ => $b))

#check retIOHist2 "argh"
#reduce (ioCmd2 IOOp.Read) >>i ioCmd2 (IOOp.Write "argh")

def preHist (_ : IOHist2 op a w) (post : a × List op → Prop) : List op → Prop := w post

def prog2 := show IOHist2 IOOp Nat _ from
    ioCmd2 (IOOp.Write "argh")
    >>i ioCmd2 IOOp.Read
    >>i retIOHist2 4

def run2 (pg : IOHist2 IOOp a w) (post : a × List IOOp → Prop) (log : List IOOp) (p : (w post) log) : IO (PSigma post) :=
    match pg with
    | .Pure x p₁ => pure <| PSigma.mk ⟨x,[]⟩ (by apply p₁ post log; exact p)
    | .Step c next p₁ => do
        let _ ← match c with
                | .Read => pure ()
                | .Write s => IO.println s
        let ⟨⟨x,log⟩,pf⟩ ←
            run2 next
                 (fun x => post (x.fst, c :: x.snd))
                 (log ++ [c])
                 (by unfold bindHistSpecAccumulate at p₁
                     simp at p₁
                     apply p₁ post log
                     exact p) -- could code golf this proof but let's keep it for clarity
        pure <| PSigma.mk ⟨x, c :: log⟩ pf

#check run2 (ioCmd2 <| IOOp.Write "blargh") (fun ⟨(),log⟩ => log.length >= 1) []

macro "weakenhist" : tactic => `(tactic | {first | unfold pureHistSpecAccumulate bindHistSpecAccumulate; simp | simp})

def y2 := run2 (ioCmd2 <| IOOp.Read) (fun ⟨(),log⟩ => log.contains IOOp.Read) [] (by weakenhist)
def y3 := run2 prog2 (fun ⟨x,log⟩ => log.length > 1) [] (by unfold pureHistSpecAccumulate bindHistSpecAccumulate; simp)

-- this fails since it does not contain a Read op
--def y3 := run2 (ioCmd2 <| IOOp.Write "argh") (fun ⟨(),log⟩ => log.contains IOOp.Read) [] (by weakenhist)

#check y2

-- macro which starts with an empty log and attempts to provide the precondition automatically
macro "goProg2" prog:term ">!" post:term : term => `(run2 $prog $post [] (by weakenhist))

def y4 := goProg2 prog2 >! (fun ⟨_,log⟩ => log.length > 1)

#eval y4 >>= fun ⟨a,b⟩ => pure a

def mapW [Monad w] (l : List a) (f : a → w b) : w (List b) :=
    match l with
    | .nil => pure []
    | .cons h t => do
        let h' ← f h
        mapW t f >>= (fun t' => pure <| h' :: t')

def mapD (l : List a) (w : a → HistSpec IOOp b) (f : (x : a) → IOHist2 IOOp b (w x)) : IOHist2 IOOp (List b) (mapW l w) :=
    match l with
    | .nil => retIOHist2 []
    | .cons h t =>
        f h
        >>=i fun y => mapD t w f
        >>=i fun ys => retIOHist2 <| y :: ys


class ForSpec (w : HistSpec IOOp Unit) where
    fromRet : ∀ (post : Unit × List IOOp → Prop) (log : List IOOp), w post log → post ((), [])
    joinSpec : IOHist2 IOOp Unit (bindHistSpecAccumulate w fun x => w) → IOHist2 IOOp Unit w

instance : ForSpec (fun post log => post ⟨(),[]⟩) where
    fromRet := by simp
    joinSpec := by unfold bindHistSpecAccumulate
                   simp
                   apply id

def for_in (r : List Nat) (body : Nat → IOHist2 IOOp Unit w) [ForSpec w] : IOHist2 IOOp Unit w :=
    match r with
    | .nil => IOHist2.Pure () ForSpec.fromRet
    | .cons h t => ForSpec.joinSpec <| body h >>i for_in t body


structure algOP (m : Type → Type) (I O : Type) (a : Type) where
    (cmd : I) (next : O → m a)

def genOP (m : Type → Type) [Monad m] (I O : Type) (i : I) : algOP m I O O :=
    {
        cmd := i,
        next := pure
    }


-- standard freer monad
inductive FreerD (op : Type) (a : Type) where
| Pure : a → FreerD op a
| Step : (c : op) → (Unit → FreerD op a) → FreerD op a

-- freer effect observation for HistSpec
def histFreer : FreerD op a → HistSpec op a
| .Pure x => fun post log => post ⟨x,[]⟩
| .Step c next => fun post log => bindHistSpecAccumulate (fun post log => post ⟨(), [c]⟩) (fun x => histFreer (next x)) post log

-- wat
def joinW (w : HistSpec op (HistSpec op a)) : HistSpec op a := bindHistSpecAccumulate w (fun w' => w')

#check joinW ∘ histFreer



structure FreePre (obs : (x : Type) → FreerD op x → HistSpec op x) (a : Type) (w : HistSpec op a) : Type where
    (m : FreerD op a) (pf : ∀ post log, w post log → obs a m post log)

structure DMon (op a : Type)
    (w : HistSpec op a) (c : IOHist2 op a w)

structure FreerW (op : Type) (obs : (x : Type) → FreerD op x → HistSpec op x) (a : Type) : Type where
    (m : FreerD op a) (w : HistSpec op a) (pf : ∀ post log, w post log → obs a m post log)

def histFreer0 (a : Type) : FreerD op a → HistSpec op a := fun x => histFreer x

def opwa (c : op) (w : Unit → HistSpec op a) : HistSpec op a := joinW (histFreer (FreerD.Step c (fun u => FreerD.Pure (w u))))

def obswa (c : op) (w : Unit → HistSpec op a) (obs : (x : Type) → FreerD op x → HistSpec op x): HistSpec op a := joinW (obs (HistSpec op a) (FreerD.Step c (fun u => FreerD.Pure (w u))))


def opDa (c :op) (next : Unit → IOHist2 op a (w ())) : IOHist2 op a (opwa c w) :=
    IOHist2.Step c (next ()) (by delta opwa bindHistSpecAccumulate joinW; simp; delta bindHistSpecAccumulate histFreer; simp)

def opPre {op : Type} {w : Unit → HistSpec op a} (c : op) (next : Unit → FreePre histFreer0 a (w ())) : FreePre histFreer0 a (opwa c w) :=
    FreePre.mk
        (FreerD.Step c (fun o => (next o).m))
        (by unfold opwa joinW bindHistSpecAccumulate histFreer0 histFreer
            conv in (fun x => histFreer _) => {unfold histFreer}
            unfold bindHistSpecAccumulate
            simp
            intros post log
            apply (next ()).pf)

def purePre {op : Type} (x : a) : @FreePre op histFreer0 a (fun post log => post ⟨x,[]⟩) :=
    FreePre.mk (FreerD.Pure x) (by unfold histFreer0 histFreer; simp)


def handleFreerD {op A B : Type} (m : FreerD op A) (a : op → (Unit → FreerD op B) → FreerD op B) (f : A → FreerD op B) : FreerD op B :=
    match m with
    | .Pure x => f x
    | .Step c next => a c (fun _ => handleFreerD (next ()) a f)

def handleHistSpec {op A B : Type} (m : HistSpec op A) (a : HistSpec op B → B) (f : A → B) : B := a (mapHistSpec m f)

/-
def handlePre {obs : (x : Type) → FreerD op x → HistSpec op x}
              (c₁ : FreePre obs A w₁)
              (hw : op → (Unit → HistSpec op B) → HistSpec op B)
              (hdop : (c : op) → (next : Unit → FreePre obs B (w o)) → FreePre obs B (hw c w))
              (c₂ : (a : A) → FreePre obs B (w₂ a))
              : FreePre obs B (handleHistSpec w₁ joinW w₂) :=
    FreePre.mk (handleFreerD c₁.m (fun op n => (hdop op n).m) (fun x => c₂ x)) _
-/
