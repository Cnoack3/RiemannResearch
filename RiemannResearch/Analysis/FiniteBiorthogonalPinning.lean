import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Continuous finite biorthogonal pinning

Source: user-requested continuation of the Ramanujan dual structure,
23 October 2026. A fixed finite biorthogonal system gives an explicit
continuous coordinate repair. The exact energy identity precedes the
uniform operator-norm estimate; no mixed energy is suppressed.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.Analysis.FiniteBiorthogonalPinning

variable {ι E : Type*} [Fintype ι]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def repair (v : ι → E) (L : ι → E →L[ℝ] ℝ) : E →L[ℝ] E :=
  ∑ i, (L i).smulRight (v i)

theorem repair_apply (v : ι → E) (L : ι → E →L[ℝ] ℝ) (x : E) :
    repair v L x = ∑ i, L i x • v i := by
  simp [repair]

theorem repair_coordinate [DecidableEq ι] (v : ι → E) (L : ι → E →L[ℝ] ℝ)
    (hdual : ∀ i j, L i (v j) = if i = j then 1 else 0) (x : E) (i : ι) :
    L i (repair v L x) = L i x := by
  simp [repair_apply, map_sum, map_smul, hdual]

theorem repair_idempotent [DecidableEq ι] (v : ι → E) (L : ι → E →L[ℝ] ℝ)
    (hdual : ∀ i j, L i (v j) = if i = j then 1 else 0) (x : E) :
    repair v L (repair v L x) = repair v L x := by
  calc
    _ = ∑ i, L i (repair v L x) • v i := repair_apply v L _
    _ = ∑ i, L i x • v i := by simp_rw [repair_coordinate v L hdual]
    _ = _ := (repair_apply v L x).symm

/-- Pin the chosen coordinates to those of an arbitrary target. -/
def pinTo (v : ι → E) (L : ι → E →L[ℝ] ℝ) (target x : E) : E :=
  x + repair v L (target - x)

theorem pinTo_coordinate [DecidableEq ι] (v : ι → E) (L : ι → E →L[ℝ] ℝ)
    (hdual : ∀ i j, L i (v j) = if i = j then 1 else 0) (target x : E) (i : ι) :
    L i (pinTo v L target x) = L i target := by
  rw [pinTo, map_add, repair_coordinate v L hdual, map_sub]
  ring

/-- At an orthogonal baseline the complete repair cost is an added norm square. -/
theorem pinTo_error_exact (v : ι → E) (L : ι → E →L[ℝ] ℝ) (target x : E)
    (horth : ∀ i, inner ℝ (target - x) (v i) = 0) :
    ‖target - pinTo v L target x‖ ^ 2 =
      ‖target - x‖ ^ 2 + ‖repair v L (target - x)‖ ^ 2 := by
  have he : target - pinTo v L target x =
      (target - x) - repair v L (target - x) := by
    simp only [pinTo]
    abel
  have hz : inner ℝ (target - x) (repair v L (target - x)) = 0 := by
    rw [repair_apply, inner_sum]
    simp only [inner_smul_right, horth, mul_zero, Finset.sum_const_zero]
  rw [he, norm_sub_sq_real, hz]
  ring

/-- A fixed finite repair costs at most a fixed multiple of the original error. -/
theorem pinTo_error_le (v : ι → E) (L : ι → E →L[ℝ] ℝ) (target x : E)
    (horth : ∀ i, inner ℝ (target - x) (v i) = 0) :
    ‖target - pinTo v L target x‖ ^ 2 ≤
      (1 + ‖repair v L‖ ^ 2) * ‖target - x‖ ^ 2 := by
  rw [pinTo_error_exact v L target x horth]
  have h := (repair v L).le_opNorm (target - x)
  have hs : ‖repair v L (target - x)‖ ^ 2 ≤
      ‖repair v L‖ ^ 2 * ‖target - x‖ ^ 2 := by
    simpa only [mul_pow] using
      (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mpr h
  nlinarith

end RiemannResearch.Analysis.FiniteBiorthogonalPinning
