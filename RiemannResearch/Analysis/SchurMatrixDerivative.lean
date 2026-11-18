import RiemannResearch.Analysis.GramLogarithmicDerivative
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.Abel
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.LinearAlgebra.Matrix.SchurComplement

/-!
# First variation of a finite Schur complement

The two moving regression coefficients disappear from the derivative. Only
the variation of the original Gram applied to the fixed screened columns
remains. The proof differentiates the actual inverse normal equations.
-/

noncomputable section
open Filter
open scoped BigOperators Topology
namespace RiemannResearch.Analysis.SchurMatrixDerivative
variable {ι κ ν : Type*} [Fintype ι] [Fintype κ] [Fintype ν]
variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]

private theorem mul_entries {A : 𝕜 → Matrix ι κ 𝕜} {B : 𝕜 → Matrix κ ν 𝕜}
    {dA : Matrix ι κ 𝕜} {dB : Matrix κ ν 𝕜} {s : 𝕜}
    (ha : ∀ i j, HasDerivAt (fun u => A u i j) (dA i j) s)
    (hb : ∀ i j, HasDerivAt (fun u => B u i j) (dB i j) s) (i : ι) (j : ν) :
    HasDerivAt (fun u => (A u * B u) i j) ((dA * B s + A s * dB) i j) s := by
  simpa only [Matrix.mul_apply, Matrix.add_apply, ← Finset.sum_add_distrib, Pi.mul_apply] using
    HasDerivAt.fun_sum (fun k (_ : k ∈ Finset.univ) => (ha i k).mul (hb k j))

variable [DecidableEq ι]

private theorem inv_entry_diff {A : 𝕜 → Matrix ι ι 𝕜} {s : 𝕜}
    (ha : ∀ i j, DifferentiableAt 𝕜 (fun u => A u i j) s) (hu : (A s).det ≠ 0) (i j : ι) :
    DifferentiableAt 𝕜 (fun u => (A u)⁻¹ i j) s := by
  let U := fun u => (A u).updateRow j (Pi.single i 1)
  have hd (a b : ι) : DifferentiableAt 𝕜 (fun u => U u a b) s := by
    by_cases he : a = j
    · subst a
      simpa only [U, Matrix.updateRow_self] using
        (differentiableAt_const (c := (Pi.single i (1:𝕜) : ι → 𝕜) b) (x := s))
    · simpa only [U, Matrix.updateRow_ne he] using ha a b
  have hD := (GramLogarithmicDerivative.det_hasDerivAt (fun a b => (ha a b).hasDerivAt)).differentiableAt
  have hU := (GramLogarithmicDerivative.det_hasDerivAt (fun a b => (hd a b).hasDerivAt)).differentiableAt
  apply ((hD.inv hu).mul hU).congr_of_eventuallyEq
  filter_upwards [] with u
  simp only [Matrix.inv_def, Ring.inverse_eq_inv, Matrix.smul_apply, smul_eq_mul,
    Matrix.adjugate_apply, U, Pi.mul_apply, Pi.inv_apply]

theorem inv_entries {A : 𝕜 → Matrix ι ι 𝕜} {dA : Matrix ι ι 𝕜} {s : 𝕜}
    (ha : ∀ i j, HasDerivAt (fun u => A u i j) (dA i j) s) (hu : (A s).det ≠ 0) (i j : ι) :
    HasDerivAt (fun u => (A u)⁻¹ i j) ((-((A s)⁻¹ * dA * (A s)⁻¹)) i j) s := by
  let X := fun u => (A u)⁻¹
  let dX : Matrix ι ι 𝕜 := fun a b => deriv (fun u => X u a b) s
  have hx (a b : ι) : HasDerivAt (fun u => X u a b) (dX a b) s :=
    (inv_entry_diff (fun a b => (ha a b).differentiableAt) hu a b).hasDerivAt
  have hz : dX * A s + X s * dA = 0 := by
    ext a b
    have heq : (fun u => (X u * A u) a b) =ᶠ[𝓝 s] (fun _ => (1 : Matrix ι ι 𝕜) a b) := by
      filter_upwards [(GramLogarithmicDerivative.det_hasDerivAt ha).continuousAt.eventually_ne hu] with u h
      change ((A u)⁻¹ * A u) a b = _
      rw [Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr h)]
    exact ((mul_entries hx ha a b).congr_of_eventuallyEq heq.symm).unique (hasDerivAt_const _ _)
  have he : dX * A s = -(X s * dA) := eq_neg_of_add_eq_zero_left hz
  have he' : dX = -(X s * dA * X s) := by
    calc
      _ = dX * (A s * X s) := by
        change _ = dX * (A s * (A s)⁻¹)
        rw [Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hu), Matrix.mul_one]
      _ = _ := by rw [← Matrix.mul_assoc, he, Matrix.neg_mul]
  exact he' ▸ hx i j

/-- A screened bilinear form applied to a perturbation of all four blocks. -/
def variation (M E : Matrix (ι ⊕ κ) (ι ⊕ κ) 𝕜) : Matrix κ κ 𝕜 :=
  let X := M.toBlocks₁₁⁻¹ * M.toBlocks₁₂
  let Y := M.toBlocks₂₁ * M.toBlocks₁₁⁻¹
  E.toBlocks₂₂ - E.toBlocks₂₁ * X - Y * (E.toBlocks₁₂ - E.toBlocks₁₁ * X)

theorem schur_entries {M : 𝕜 → Matrix (ι ⊕ κ) (ι ⊕ κ) 𝕜} {dM : Matrix (ι ⊕ κ) (ι ⊕ κ) 𝕜}
    {s : 𝕜} (hm : ∀ i j, HasDerivAt (fun u => M u i j) (dM i j) s)
    (hu : (M s).toBlocks₁₁.det ≠ 0) (i j : κ) :
    HasDerivAt (fun u => ((M u).toBlocks₂₂ - (M u).toBlocks₂₁ *
      (M u).toBlocks₁₁⁻¹ * (M u).toBlocks₁₂) i j) (variation (M s) dM i j) s := by
  let A := fun u => (M u).toBlocks₁₁
  let B := fun u => (M u).toBlocks₁₂
  let C := fun u => (M u).toBlocks₂₁
  have hA (a b) : HasDerivAt (fun u => A u a b) (dM.toBlocks₁₁ a b) s := hm (.inl a) (.inl b)
  have hB (a b) : HasDerivAt (fun u => B u a b) (dM.toBlocks₁₂ a b) s := hm (.inl a) (.inr b)
  have hC (a b) : HasDerivAt (fun u => C u a b) (dM.toBlocks₂₁ a b) s := hm (.inr a) (.inl b)
  have hh := (hm (.inr i) (.inr j)).sub
    (mul_entries (mul_entries hC (inv_entries hA hu)) hB i j)
  have hmat : dM.toBlocks₂₂ - ((dM.toBlocks₂₁ * (A s)⁻¹ +
      C s * -((A s)⁻¹ * dM.toBlocks₁₁ * (A s)⁻¹)) * B s +
      C s * (A s)⁻¹ * dM.toBlocks₁₂) = variation (M s) dM := by
    unfold variation
    simp only [A, B, C, Matrix.mul_neg, Matrix.neg_mul, Matrix.add_mul, Matrix.mul_sub,
      Matrix.mul_assoc]
    abel
  exact hh.congr_deriv (congrFun (congrFun hmat i) j)

end RiemannResearch.Analysis.SchurMatrixDerivative
