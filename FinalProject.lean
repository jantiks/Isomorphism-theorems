-- In this file I will apply the first isomorphism theorem on specific groups,
-- namely I will show that (ℝ, +) ≅ (ℝ^{+}, *), where ℝ^{+} = ℝ \ {x ∈ ℝ : x < 0}, and * is the usual multiplication.
--

import FinalProject.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Real.Basic


inductive GroupOp
  | mul | inv | one

def groupArity : GroupOp → ℕ
  | .mul => 2
  | .inv => 1
  | .one => 0

def GroupSignature : UniversalAlgebra.Signature where
  Op := GroupOp
  arity := groupArity

-- The Algebra (ℝ, +)
def RealAddAlgebra : UniversalAlgebra.Algebra GroupSignature ℝ where
  interpret op args :=
    match op with
    | .mul =>
      let a0 : ℝ := args ⟨0, by simp [GroupSignature, groupArity]⟩
      let a1 : ℝ := args ⟨1, by simp [GroupSignature, groupArity]⟩
      a0 + a1
    | .inv =>
      -(args ⟨0, by simp [GroupSignature, groupArity]⟩)
    | .one => 0

-- The Algebra (ℝ^+, *)
def PosReal := {x : ℝ // 0 < x}

noncomputable def RealMulAlgebra : UniversalAlgebra.Algebra GroupSignature PosReal where
  interpret op args :=
    match op with
    | .mul =>
      let x := args ⟨0, by simp [GroupSignature, groupArity]⟩
      let y := args ⟨1, by simp [GroupSignature, groupArity]⟩
      ⟨x.val * y.val, mul_pos x.property y.property⟩
    | .inv =>
      let x := args ⟨0, by simp [GroupSignature, groupArity]⟩
      ⟨x.val⁻¹, inv_pos.mpr x.property⟩
    | .one =>
      ⟨1, one_pos⟩

noncomputable def expHom :
UniversalAlgebra.Homomorphism GroupSignature RealAddAlgebra RealMulAlgebra where
  toFun x := ⟨Real.exp x, Real.exp_pos x⟩
  mapOp f args := by
    cases f
    · apply Subtype.ext
      simp [RealMulAlgebra, RealAddAlgebra, Real.exp_add]
    · apply Subtype.ext
      simp only [RealMulAlgebra, RealAddAlgebra]
      exact Real.exp_neg (args ⟨0, by simp [GroupSignature, groupArity]⟩)
    · apply Subtype.ext
      simp [RealMulAlgebra, RealAddAlgebra]

lemma expSurjective : Function.Surjective expHom.toFun := by
  intro a
  use Real.log a.val
  apply Subtype.ext
  simp only [expHom]
  apply Real.exp_log a.prop

theorem RealIsomorphism :
    Nonempty (UniversalAlgebra.Isomorphism GroupSignature
      (UniversalAlgebra.QuotientAlgebra RealAddAlgebra (UniversalAlgebra.kernelCongurence expHom))
      RealMulAlgebra) :=
  UniversalAlgebra.firstIsomorphismTheorem expHom expSurjective
