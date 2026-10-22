import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Abel

/-!
# Mean normalization preserves the approximation subspace

Source: `RH_Contracting_Evolution_and_Arithmetic_Repair_2026-09-08.md`,
Section 4. A single mean-one legal vector normalizes any other legal vector.
This is independent of an arithmetic reconstruction theorem.
-/

namespace RiemannResearch.Analysis.MeanNormalization

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def normalize (ℓ : E →L[ℝ] ℝ) (v G : E) : E := G + (1 - ℓ G) • v

theorem normalize_mean (ℓ : E →L[ℝ] ℝ) (v G : E) (hv : ℓ v = 1) :
    ℓ (normalize ℓ v G) = 1 := by
  simp [normalize, map_add, map_smul, hv]

theorem normalize_mem (V : Submodule ℝ E) (ℓ : E →L[ℝ] ℝ) (v G : E)
    (hv : v ∈ V) (hG : G ∈ V) : normalize ℓ v G ∈ V :=
  V.add_mem hG (V.smul_mem _ hv)

/-- Exact normalization defect; its coefficient is the mean of the original
approximation error. -/
theorem normalize_sub (ℓ : E →L[ℝ] ℝ) (v G y : E) (hy : ℓ y = 1) :
    normalize ℓ v G - y = (G - y) - ℓ (G - y) • v := by
  rw [normalize, map_sub, hy, sub_smul, one_smul, sub_smul, one_smul]
  abel

theorem norm_normalize_sub_le (ℓ : E →L[ℝ] ℝ) (v G y : E) (hy : ℓ y = 1) :
    ‖normalize ℓ v G - y‖ ≤ (1 + ‖ℓ‖ * ‖v‖) * ‖G - y‖ := by
  rw [normalize_sub ℓ v G y hy]
  calc
    ‖(G - y) - ℓ (G - y) • v‖ ≤ ‖G - y‖ + ‖ℓ (G - y) • v‖ :=
      norm_sub_le _ _
    _ = ‖G - y‖ + ‖ℓ (G - y)‖ * ‖v‖ := by rw [norm_smul]
    _ ≤ ‖G - y‖ + (‖ℓ‖ * ‖G - y‖) * ‖v‖ :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_right (ℓ.le_opNorm _) (norm_nonneg _))
    _ = (1 + ‖ℓ‖ * ‖v‖) * ‖G - y‖ := by ring

theorem norm_normalize_sub_le_of_mean_norm_le_one
    (ℓ : E →L[ℝ] ℝ) (v G y : E) (hy : ℓ y = 1) (hℓ : ‖ℓ‖ ≤ 1) :
    ‖normalize ℓ v G - y‖ ≤ (1 + ‖v‖) * ‖G - y‖ := by
  apply (norm_normalize_sub_le ℓ v G y hy).trans
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  have h := mul_le_mul_of_nonneg_right hℓ (norm_nonneg v)
  nlinarith

end RiemannResearch.Analysis.MeanNormalization
