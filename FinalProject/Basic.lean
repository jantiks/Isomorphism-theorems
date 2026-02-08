-- This file contains a formalization of the First isomorphism (in Universal algebra) thoerem.
-- First, I want to defie an algebra, for that we start with the definition of a signature

import Mathlib.Data.Quot
import Mathlib.Logic.Function.Basic

universe u v

structure Signature where
  Op : Type u
  arity : Op → ℕ

-- Now, an algebra with a signature \sigma, and ground set A is the interpretations of the functions
-- from the signature, with corresponding arities
structure Algebra (σ : Signature) (A : Type v) where
  interpret : (f : σ.Op) → (Fin (σ.arity f) → A) → A

structure Homomorphism (σ : Signature) {A B : Type _}
  (algA : Algebra σ A) (algB : Algebra σ B) where
  toFun : A → B
  map_op : ∀ (f : σ.Op) (args : Fin (σ.arity f) → A),
    toFun (algA.interpret f args) = algB.interpret f (toFun ∘ args)

-- This is just a syntactic sugar, to not write h.toFun x but h x when h is a homomorphism
instance (σ : Signature) {A B : Type _} (algA : Algebra σ A) (algB : Algebra σ B) :
    CoeFun (Homomorphism σ algA algB) (fun _ => A → B) where
  coe h := h.toFun

-- basically Binary relation takes two arguments and returns Ture or False value.
def BinRelation (A : Type u) := A → A → Prop

-- Congurence here is just an equivalence relation on A that also is closed under the basic opeartions
-- of A, or in other words congurence is a subalgebra of A^2, but I don't want to define
-- a subalgebra and powers of an algebra, since it can get tricky with infinte products
-- (at least that's what I think), so will stick with equiv rel + closoure
-- under the operations definition.
structure Congruence (σ : Signature) {A : Type u} (alg : Algebra σ A) where
  toRel : BinRelation A -- the underlying binary relation
  equiv : Equivalence toRel -- proof that it is an equivalence relation
  compatible : ∀ (f : σ.Op) (args1 args2 : Fin (σ.arity f) → A),
    (∀ i, toRel (args1 i) (args2 i)) →
    toRel (alg.interpret f args1) (alg.interpret f args2)

def kerRel {σ : Signature} {A B : Type _} {algA : Algebra σ A} {algB : Algebra σ B}
  (h : Homomorphism σ algA algB) : BinRelation A :=
  fun x y => h x = h y

-- since kernel of a homomorphism A -> B is actually a congurence relation on the domain algebra A, I will
-- prove it step by step, first that it is a equivalence relation
def kernelIsEquivalence {σ : Signature} {A B : Type _} {algA : Algebra σ A} {algB : Algebra σ B}
  (h : Homomorphism σ algA algB) : Equivalence (kerRel h) where
  refl _ := rfl
  symm hxy := hxy.symm
  trans hxy hyz := hxy.trans hyz


def kernelCongurence {σ : Signature} {A B : Type _} {algA : Algebra σ A} {algB : Algebra σ B}
  (h : Homomorphism σ algA algB) : Congruence σ algA where
  toRel := kerRel h
  equiv := kernelIsEquivalence h
  compatible := by
    intro f args1 args2 h_args
    simp [kerRel] at *
    rw [h.map_op, h.map_op]
    congr 1
    funext i
    exact h_args i

-- using the Lean's Setoid machinary
instance quotientSetoid {σ : Signature} {A : Type u} {alg : Algebra σ A} (Φ : Congruence σ alg) : Setoid A where
  r := Φ.toRel
  iseqv := Φ.equiv

-- We use Quotient.choice to pick representatives, but the 'compatible' property
-- ensures the final result is independent of the choice.
-- Here I use noncomputable since Quotient.choice is noncomputable, since it depends on AOC
noncomputable def QuotientAlgebra {σ : Signature} {A : Type u} (alg : Algebra σ A) (Φ : Congruence σ alg) :
    Algebra σ (Quotient (quotientSetoid Φ)) where
  interpret f args :=
    Quotient.lift (fun (v : Fin (σ.arity f) → A) => Quotient.mk (quotientSetoid Φ) (alg.interpret f v))
      (by
        intro v1 v2 h_equiv
        apply Quotient.sound
        apply Φ.compatible
        intro i
        exact h_equiv i
      )
      (Quotient.choice args)

-- lets define the canonical homomorphism. i.e. f a = class(a), since the quotient is well defined, this
-- is a homomorphism, which sends each element to its equivalence class.
def quotientMap {σ : Signature} {A : Type u} {alg : Algebra σ A} (Φ : Congruence σ alg) :
    Homomorphism σ alg (QuotientAlgebra alg Φ) where
  toFun := Quotient.mk (quotientSetoid Φ)
  map_op f args := by
    simp [QuotientAlgebra]
    apply Quotient.sound
    apply Φ.compatible
    intro i
    change @Setoid.r _ (quotientSetoid Φ) (args i) _
    apply Quotient.exact
    symm
    apply Quotient.out_eq

def inducedFun {σ : Signature} {A B : Type _} {algA : Algebra σ A} {algB : Algebra σ B}
  (h : Homomorphism σ algA algB) : Quotient (quotientSetoid (kernelCongurence h)) → B :=
  Quotient.lift h (fun _ _ h_eq => h_eq)

noncomputable def inducedHomomorphism {σ : Signature} {A B : Type _} {algA : Algebra σ A} {algB : Algebra σ B}
  (h : Homomorphism σ algA algB) :
  Homomorphism σ (QuotientAlgebra algA (kernelCongurence h)) algB where
  toFun := inducedFun h
  map_op := by
    intro f args
    let q_map := quotientMap (kernelCongurence h)

    have h_link : ∀ a, inducedFun h (q_map a) = h a := by
      intro a; rfl

    let v : Fin (σ.arity f) → A := fun i => (args i).out

    have h_args : args = q_map ∘ v := by
      funext i
      dsimp [q_map, quotientMap]
      rw [Quotient.out_eq]

    rw [h_args]
    rw [← q_map.map_op]
    rw [h_link]

    rw [h.map_op]
    apply congr
    rfl

    funext i
    dsimp [Function.comp]
    rw [h_link]
