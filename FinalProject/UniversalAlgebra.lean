-- This file contains a formalization of the First isomorphism (in Universal algebra) thoerem.
-- The theorem I will prove above is as follows:
-- Let A and B be algebras with same signature, let h : A -> B be a surjective homomorphism,
-- then A / ker h is isomorphic to B.
-- First, I want to defie an algebra, for that we start with the definition of a signature

import Mathlib.Data.Quot
import Mathlib.Logic.Function.Basic
import Mathlib.Data.Real.Basic

namespace UniversalAlgebra

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
  mapOp : ∀ (f : σ.Op) (args : Fin (σ.arity f) → A),
    toFun (algA.interpret f args) = algB.interpret f (toFun ∘ args)

-- Since we are proving a theorem which is about isomorphisms,
-- we need to define isomorphism between algebras :)
structure Isomorphism (σ : Signature) (algA : Algebra σ A) (algB : Algebra σ B)
extends Homomorphism σ algA algB where
  bijective : Function.Bijective toFun

-- This is just a syntactic sugar, to not write h.toFun x but h x when h is a homomorphism
instance (σ : Signature) {A B : Type _} (algA : Algebra σ A) (algB : Algebra σ B) :
    CoeFun (Homomorphism σ algA algB) (fun _ => A → B) where
  coe h := h.toFun

-- basically Binary relation takes two arguments and returns Ture or False value.
def BinRelation (A : Type u) := A → A → Prop

-- Congurence here is just an equivalence relation on algebra A that also
-- is closed under the basic opeartions of A, or in other words congurence is a subalgebra
-- of A^2, but I don't want to define a subalgebra and powers of an algebra,
-- since it can get tricky with infinte products (at least that's what I think),
-- so will stick with equiv rel + closoure under the operations definition.
structure Congruence (σ : Signature) {A : Type u} (alg : Algebra σ A) where
  toRel : BinRelation A -- the underlying binary relation
  equiv : Equivalence toRel -- proof that it is an equivalence relation
  compatible : ∀ (f : σ.Op) (args1 args2 : Fin (σ.arity f) → A),
    (∀ i, toRel (args1 i) (args2 i)) →
    toRel (alg.interpret f args1) (alg.interpret f args2)

def kerRel {σ : Signature} {A B : Type _} {algA : Algebra σ A} {algB : Algebra σ B}
  (h : Homomorphism σ algA algB) : BinRelation A :=
  fun x y => h x = h y

-- since kernel of a homomorphism A -> B is actually a congurence relation on
-- the domain algebra A, I will prove it step by step,
-- first that it is a equivalence relation
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
    simp only [kerRel] at *
    rw [h.mapOp, h.mapOp]
    congr 1
    funext i
    exact h_args i

-- using the Lean's Setoid machinary
instance quotientSetoid
{σ : Signature}
{A : Type u}
{alg : Algebra σ A}
(Φ : Congruence σ alg) : Setoid A where
  r := Φ.toRel
  iseqv := Φ.equiv

-- We use Quotient.choice to pick representatives, but the 'compatible' property
-- ensures the final result is independent of the choice.
-- Here I use noncomputable since Quotient.choice is noncomputable, since it depends on AOC
noncomputable def QuotientAlgebra {σ : Signature} {A : Type u}
(alg : Algebra σ A) (Φ : Congruence σ alg) :
    Algebra σ (Quotient (quotientSetoid Φ)) where
  interpret f args :=
    Quotient.lift (fun (v : Fin (σ.arity f) → A) =>
    Quotient.mk (quotientSetoid Φ) (alg.interpret f v))
      (by
        intro v1 v2 hEquiv
        apply Quotient.sound
        apply Φ.compatible
        intro i
        exact hEquiv i
      )
      (Quotient.choice args)

-- lets define the canonical homomorphism. i.e. f a = class(a), since
-- the quotient is well defined, this is a homomorphism which
-- sends each element to its equivalence class.
def quotientMap {σ : Signature} {A : Type u} {alg : Algebra σ A} (Φ : Congruence σ alg) :
    Homomorphism σ alg (QuotientAlgebra alg Φ) where
  toFun := Quotient.mk (quotientSetoid Φ)
  mapOp f args := by
    simp only [QuotientAlgebra]
    apply Quotient.sound
    apply Φ.compatible
    intro i
    change @Setoid.r _ (quotientSetoid Φ) (args i) _
    apply Quotient.exact
    symm
    apply Quotient.out_eq

-- now, I want to define the induced homomorphism form
-- h : A -> B to h' : A/ker(h) -> B as f([a]) -> f(a) ∈ B,
-- First, I just define the induced function, and then prove that it is a homomorphism.
def inducedFun {σ : Signature} {A B : Type _} {algA : Algebra σ A} {algB : Algebra σ B}
  (h : Homomorphism σ algA algB) : Quotient (quotientSetoid (kernelCongurence h)) → B :=
  Quotient.lift h (fun _ _ h_eq => h_eq)

def inducedHomomorphism {σ : Signature} {A B : Type _} {algA : Algebra σ A} {algB : Algebra σ B}
  (h : Homomorphism σ algA algB) :
  Homomorphism σ (QuotientAlgebra algA (kernelCongurence h)) algB where
  toFun := inducedFun h
  mapOp := by
    intro f args
    let qMap := quotientMap (kernelCongurence h)
    have hLink : ∀ a, inducedFun h (qMap a) = h a := by
      intro a; rfl
    let v : Fin (σ.arity f) → A := fun i => (args i).out
    have hArgs : args = qMap ∘ v := by
      funext i
      dsimp [qMap, quotientMap]
      rw [Quotient.out_eq]
    rw [hArgs, ← qMap.mapOp, hLink, h.mapOp]
    apply congr
    · rfl
    · funext i
      dsimp [Function.comp]
      rw [hLink]

theorem inducedInjective {σ : Signature} {A B : Type _} {algA : Algebra σ A} {algB : Algebra σ B}
  (h : Homomorphism σ algA algB) :
  Function.Injective (inducedFun h) := by
  intro q1 q2 heq
  induction q1 using Quotient.inductionOn
  induction q2 using Quotient.inductionOn
  apply Quotient.sound
  exact heq

def firstIsomorphismConstruction {σ : Signature} {A B : Type _}
  {algA : Algebra σ A} {algB : Algebra σ B} (h : Homomorphism σ algA algB)
  (h_surj : Function.Surjective h) :
  Isomorphism σ (QuotientAlgebra algA (kernelCongurence h)) algB := {
    toFun := inducedFun h,
    mapOp := (inducedHomomorphism h).mapOp,
    bijective := ⟨inducedInjective h, by
      intro b
      obtain ⟨a, ha⟩ := h_surj b
      use Quotient.mk (quotientSetoid (kernelCongurence h)) a
      exact ha
    ⟩
  }

theorem firstIsomorphismTheorem {σ : Signature} {A B : Type _}
  {algA : Algebra σ A} {algB : Algebra σ B} (h : Homomorphism σ algA algB)
  (h_surj : Function.Surjective h) :
  Nonempty (Isomorphism σ (QuotientAlgebra algA (kernelCongurence h)) algB) :=
  ⟨firstIsomorphismConstruction h h_surj⟩

-- Now, lets use the theorem to show that for any algebra A, A/Ker(id) is isomorphic to A.
def idHomomorphism {σ : Signature} {A : Type u} (alg : Algebra σ A) :
    Homomorphism σ alg alg where
  toFun := id
  mapOp _ _ := rfl

theorem idSurjective {A : Type u} : Function.Surjective (@id A) := by
  intro y
  use y
  rfl

theorem quotientIdIsomorphic {σ : Signature} {A : Type u} (alg : Algebra σ A) :
    Nonempty (Isomorphism σ (QuotientAlgebra alg (kernelCongurence (idHomomorphism alg))) alg) :=
  firstIsomorphismTheorem (idHomomorphism alg) idSurjective

end UniversalAlgebra
