-- This file contains a formalization of the First isomorphism (in Universal algebra) thoerem.
-- First, I want to defie an algebra, for that we start with the definition of a signature
universe u v

structure Signature where
  Op : Type u
  arity : Op → ℕ

-- Now, an algebra with a signature sigma, and ground set A is the interpretations of the functions
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

structure Congruence (σ : Signature) {A : Type u} (alg : Algebra σ A) where
  toRel : BinRelation A -- the underlying binary relation
  equiv : Equivalence toRel -- proof that it is an equivalence relation
  compatible : ∀ (f : σ.Op) (args1 args2 : Fin (σ.arity f) → A),
    (∀ i, toRel (args1 i) (args2 i)) →
    toRel (alg.interpret f args1) (alg.interpret f args2)

def kerRel {σ : Signature} {A B : Type _} {algA : Algebra σ A} {algB : Algebra σ B}
  (h : Homomorphism σ algA algB) : BinRelation A :=
  fun x y => h x = h y

-- since kernel if a homomorphism A -> B is actually a congurence relation on the domain algebra A, I will
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
