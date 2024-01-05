import Std

import Lean
import Lean.Elab.Tactic

import Init.Control.Lawful

import Aesop

import EffSpec.Basic





--
-- Dijkstra monad class - from "Dijkastra Monads for All", Kenji Maillard et al.
--

class DMonad {W : Type → Type} [Monad W] (d : (a : Type) → W a → Type) where
    retD : (x : a) → d a (pure x : W a)
    bindD : {w₁ : W a} → {w₂ : a → W b} → (d a w₁) → ((x : a) → d b (w₂ x)) → d b (w₁ >>= w₂)

namespace DMonad


open Lean.Meta Lean.Elab.Tactic

syntax term ">>=w" term : term
syntax term ">>w" term : term

macro_rules
| `($a >>=w $b) => `(DMonad.bindD $a $b)
| `($a >>w $b) => `(DMonad.bindD $a (fun _ => $b))


--
-- some Monad type coercions to make Djkstra monad theorems easier
--

-- `d a w = d a (w >>= pure)`
instance {W : Type → Type} {d : (a : Type) → W a → Type} [Monad W] [LawfulMonad W] {w : W a} : Coe (d a w) (d a (w >>= pure)) where
    coe x := by rw [bind_pure_comp]; simp; exact x

-- `d a w = d a (pure _ >> w)`
instance {W : Type → Type} {d : (a : Type) → W a → Type} {a : Type} [Monad W] [LawfulMonad W] {w : W a} {x : b} : Coe (d a w) (d a (pure x >>= (fun _ => w))) where
    coe x := by rw [pure_bind]; exact x

-- Re-ordering let bindings in the `w` of `d a w`
instance {W : Type → Type} {d : (a : Type) → W a → Type} {a : Type} [Monad W] [LawfulMonad W] {w₁ w₂ w₃ : W a} : Coe (d a (do let _ ← w₁; let _ ← w₂; w₃)) (d a (do let _ ← (do let _ ← w₁; w₂); w₃)) where
    coe x := by simp; exact x

-- Re-ordering monad bindings in the `w` of `d a w`
instance {W : Type → Type} {d : (a : Type) → W a → Type} {a : Type} [Monad W] [LawfulMonad W] {w₁ : W a} {w₂ : a → W b} {w₃ : b → W c} : Coe (d c (w₁ >>= (fun x => w₂ x >>= w₃))) (d c (w₁ >>= w₂ >>= w₃)) where
    coe x := by simp; exact x



open DMonad in
class LawfulDMonad {W : Type → Type} [Monad W] [LawfulMonad W] (d : (a : Type) → W a → Type) [DMonad d] where
    bindPure : (a : Type) → ∀ (w : W a) (m : d a w), bindD m retD = m
    pureBind : (a : Type) → ∀ (x : a) (f : a → d b w), bindD (retD x) f = f x
    bindAssoc : (a b c : Type) → ∀ (w₁ : W a) (w₂ : a → W b) (w₃ : b → W c) (m : d a w₁) (f : (x : a) → d b (w₂ x)) (g : (y : b) → d c (w₃ y)), bindD (bindD m f) g = bindD m (fun x => bindD (f x) g)
-- yikes, here it is written with explicit arguments which is SLIGHLTY more readable:
--        @bindD W _ d _ b c (w₁ >>= w₂) w₃ (@bindD W _ d _ a b w₁ w₂ m f) g = @bindD W _ d _ a c w₁ (fun x => w₂ x >>= w₃) m (fun x => @bindD W _ d _ b c (w₂ x) w₃ (f x) g)


-- For transforming dijkstra monads we need a dependent type:
--   `wMap` defines a map on the specification w, and then
--   `dMap` map on the dijkstra monad that builds on the specification map
structure DMorphism  {W₁ W₂ : Type → Type} [Monad W₁] [Monad W₂] (d₁ : (a : Type) → W₁ a → Type) (d₂ : (a : Type) → W₂ a → Type) : Type 1 where
    (wMap : W₁ a → W₂ a)
    (wMapPure : ∀ {a : Type} (x : a), wMap (@pure W₁ _ a x) = @pure W₂ _ a x)
    (wMapBind : (do let x ← wMap w₁; wMap (w₂ x)) = wMap (w₁ >>=  w₂))
    (dMap : d₁ a w → d₂ a (wMap w))

--
-- some coercions needed for `LawfulDMorphism`
--
-- For some Dijkstra monad morphism `ΘD` we have `d a (pure x) = d a (ΘD.wMap (pure x))`
instance {W₁ W₂ : Type → Type} [Monad W₁] [Monad W₂] {d₁ : (a : Type) → W₁ a → Type} {d₂ : (a : Type) → W₂ a → Type} {dm : @DMorphism W₁ W₂ _ _ d₁ d₂}
    : Coe (d₂ a (pure x)) (d₂ a (dm.wMap (pure x))) where
    coe d := by rw [dm.wMapPure]; exact d

-- `d a (do let _ ← ΘD.wMap w₁; ΘD.wMap w₂) = d a (ΘD.wMap (do let _ ← w₁; w₂))
instance {W₁ W₂ : Type → Type} [Monad W₁] [Monad W₂] {d₁ : (a : Type) → W₁ a → Type} {d₂ : (a : Type) → W₂ a → Type} {dm : @DMorphism W₁ W₂ _ _ d₁ d₂}
    {w₁ : W₁ a} {w₂ : a → W₁ b}
    : Coe (d₂ b (do let x ← dm.wMap w₁; dm.wMap (w₂ x))) (d₂ b (dm.wMap (w₁ >>= w₂))) where
    coe d := by rw [←dm.wMapBind]; exact d


open DMonad DMorphism in
class LawfulDMorphism
      {W₁ W₂ : Type → Type} [Monad W₁] [LawfulMonad W₁] [Monad W₂] [LawfulMonad W₂]
      {d₁ : (a : Type) → W₁ a → Type} {d₂ : (a : Type) → W₂ a → Type} [DMonad d₁] [LawfulDMonad d₁] [DMonad d₂] [LawfulDMonad d₂]
      (dm : DMorphism d₁ d₂)
      where
    pureMorphism : ∀ (ΘD : DMorphism d₁ d₂) (x : a), ΘD.dMap (retD x) = retD x
    bindMorphism : ∀ (ΘD : DMorphism d₁ d₂) (a : Type) (w₁ : W₁ a) (m : d₁ a w₁)  (w₂ : {a : Type} → a → W₁ b) (f : {a : Type} → (x : a) → d₁ b (w₂ x)),
        ΘD.dMap (bindD m f) = bindD (ΘD.dMap m) (fun x => ΘD.dMap (f x))
        --(ΘD.dMap (bindD m f) : d₂ b (wMap ΘD (w₁ >>= w₂))) = (bindD (ΘD.dMap m) (fun x => ΘD.dMap (f x)) : d₂ b (do let x ← ΘD.wMap w₁; ΘD.wMap (w₂ x)))


--
-- "converters" between a monad and dijkstra monad
--

--@[aesop norm unfold]
def MonadRelation (M W : Type → Type) [Monad M] [Monad W] : Type 1 := {a : Type} → M a → W a

-- to built a dijkstra monad using a relation between a computational monad M and specification W
-- we need these properties
class OrderedRelation (M W : Type → Type) [Monad M] [Monad W] (R : {a : Type} → M a → W a) where
    weaken : W a → W a → Prop
    weakenPure : (x : a) → weaken (R (pure x)) (pure x)
    weakenBind : (m₁ : M a) → (m₂ : a → M b) → (w₁ : W a) → (w₂ : a → W b) → weaken (R m₁) w₁ → ((x : a) → weaken (R (m₂ x)) (w₂ x)) → weaken (R (m₁ >>= m₂)) (w₁ >>= w₂)

open OrderedRelation

/- some dijkstra monads built on M/W/R where you specify:
   - M the computational monad
   - W the specification monad
   - R a relation that maps from M to W

   and the Dijkstra monads are built from these.

   Most commonly used should be PreR which additionaly requires that W has
   a PredicateT instance.
-/

structure PreR0 {M W : Type → Type} [Monad M] [Monad W] (R : MonadRelation M W) (a : Type) (w : W a) : Type where
    m : M a
    rel : R m = w

@[aesop unsafe constructors]
structure PreR (M W : Type → Type) [Monad M] [Monad W] (R : MonadRelation M W) [OrderedRelation M W R] (a : Type) (w : W a) : Type where
    m : M a
    rel : @OrderedRelation.weaken M W _ _ R _ a (R m) w

@[aesop unsafe constructors]
structure UnpackD  {W : Type → Type} [Monad W] (D : (a : Type) → W a → Type 1) (A : Type) : Type 1 where
    w : W A
    d : D A w



instance {M W : Type → Type} [Monad M] [Monad W] {R : MonadRelation M W} [OrderedRelation M W R] : DMonad (PreR M W R) where
    retD := fun x => PreR.mk (pure x) (OrderedRelation.weakenPure x)
    bindD := fun m f => by
        rename_i w₁ w₂
        let fComp := fun x => (f x).m
        exact PreR.mk (m.m >>= fComp) (OrderedRelation.weakenBind m.m fComp w₁ w₂ m.rel (fun x => (f x).rel))


#check Function.const

instance {M W : Type → Type}
    [Monad M] [LawfulMonad M]
    [Monad W] [LawfulMonad W]
    {R : MonadRelation M W} [OrderedRelation M W R]
    : LawfulDMonad (PreR M W R) where
    bindPure := by intros a w m
                   unfold bindD retD instDMonadTypePreR; simp!
                   unfold Eq.mpr
                   congr
                   rw [bind_pure_comp]; simp
                   let h₀ : PreR M W (fun {a} => R) a w                    = PreR M W (fun {a} => R) a (w >>= pure)         := by simp
                   let h₁ : PreR M W (fun {a} => R) a w                    = PreR M W (fun {a} => R) a ((fun a => a) <$> w) := by simp
                   let h₂ : PreR M W (fun {a} => R) a ((fun a => a) <$> w) = PreR M W (fun {a} => R) a (w >>= pure)         := by simp
                   let h₄ : HEq ((h₁ : PreR M W (fun {a} => R) a w = PreR M W (fun {a} => R) a ((fun a => a) <$> w)) ▸ m) m := by apply cast_heq
                   let h₅ : ∀ (m : PreR M W (fun {a} => R) a ((fun a => a) <$> w)), HEq (h₂ ▸ m) m                          := by apply cast_heq h₂
                   let h₆ : HEq (h₂ ▸ h₁ ▸ m) m                                                                           := HEq.trans (h₅ _) h₄
                   exact HEq.symm h₆
    pureBind := by intros b w a x f
                   unfold bindD retD instDMonadTypePreR; simp!
                   unfold Eq.mpr
                   congr
                   simp
                   apply HEq.symm
                   apply cast_heq
    bindAssoc := by intros a b c w₁ w₂ w₃ m f g
                    unfold bindD instDMonadTypePreR; simp
                    rw [←heq_iff_eq]
                    apply HEq.symm
                    apply HEq.trans (cast_heq _ _)
                    congr!
                    simp


--
-- the pure specification (in the paper this is called "w_pure")
--
@[aesop norm 50% unfold]
def PureSpec (a : Type) : Type := (a → Prop) → Prop

instance : Functor PureSpec where
    map := fun f v => fun b => v (fun a => b (f a))

instance : LawfulFunctor PureSpec where
    map_const := by intro a b; rfl
    id_map := by intro a x; rfl
    comp_map := by intro a b f g h x; rfl

@[aesop norm 50% unfold]
def retPureSpec {a : Type} (x : a) : PureSpec a :=
    fun post => post x

@[aesop norm 50% unfold]
def bindPureSpec {a b : Type} (w₁ : PureSpec a) (w₂ : a → PureSpec b) : PureSpec b :=
    fun post => w₁ (fun x => (w₂ x) post)

instance : Monad PureSpec where
    pure := retPureSpec
    bind := bindPureSpec

instance : LawfulMonad PureSpec where
    pure_seq := by intro a b g x; rfl
    pure_bind := by intro a b f x; rfl
    bind_assoc := by intro a b g f x y; rfl
    seqLeft_eq := by intro a b x f; rfl
    seqRight_eq := by intro a b x y; rfl
    bind_map := by intro a b f x; rfl
    bind_pure_comp := by intro a b f x; rfl

end DMonad
