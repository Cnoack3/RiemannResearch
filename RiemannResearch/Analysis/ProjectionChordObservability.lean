import RiemannResearch.Analysis.FiniteHilbertGram
import RiemannResearch.Analysis.ProjectionSourceImprovement
import RiemannResearch.LinearAlgebra.FiniteHilbertSchur
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

/-!
# Signed chord screening and source-specific observability

Source: user-provided argument,
RH_Global_Approximation_and_Resonance_Blind_Patterns_Handoff_2026-09-16(1).md,
Sections 23, 25--27. The source supports the statements and proof strategy.

All Gram and innovation identities below keep their signed mixed terms.
The finite-family gain theorem allows dependent or redundant columns.
Its synthesis bound and positive-charge bound are explicit hypotheses;
neither the arithmetic Bessel conjecture nor RH is asserted.

Concrete consumer: RH.TwoThreeChordObservability.
-/

open scoped BigOperators
noncomputable section
namespace RiemannResearch.Analysis.ProjectionChordObservability
open RiemannResearch.Analysis.ProjectionSourceImprovement
open RiemannResearch.Analysis.ProjectionCompression
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

theorem chord_gram (x₀ x₁ y₀ y₁ : H) :
    inner ℝ (x₁ - x₀) (y₁ - y₀) =
      inner ℝ x₁ y₁ - inner ℝ x₁ y₀ -
        inner ℝ x₀ y₁ + inner ℝ x₀ y₀ := by
  simp only [inner_sub_left, inner_sub_right]
  ring

variable (P : Submodule ℝ H) [P.HasOrthogonalProjection]

theorem screened_chord_source (b x y : H) :
    inner ℝ (ProjectionSourceImprovement.residual P b) (ProjectionSourceImprovement.residual P (y-x)) =
      inner ℝ (ProjectionSourceImprovement.residual P b) y - inner ℝ (ProjectionSourceImprovement.residual P b) x := by
  rw [residual_inner, inner_sub_right]

theorem screened_chord_gram (x₀ x₁ y₀ y₁ : H) :
    inner ℝ (ProjectionSourceImprovement.residual P (x₁-x₀)) (ProjectionSourceImprovement.residual P (y₁-y₀)) =
      (inner ℝ x₁ y₁ - inner ℝ x₁ y₀ -
        inner ℝ x₀ y₁ + inner ℝ x₀ y₀) -
      inner ℝ (P.starProjection (x₁-x₀)) (P.starProjection (y₁-y₀)) := by
  rw [ProjectionSourceImprovement.residual, ProjectionSourceImprovement.residual, RiemannResearch.LinearAlgebra.inner_residualized_eq_schur,
    chord_gram]

theorem residual_charge (b : H) :
    inner ℝ (ProjectionSourceImprovement.residual P b) b = ‖ProjectionSourceImprovement.residual P b‖^2 := by
  rw [← residual_inner P b b, real_inner_self_eq_norm_sq]

theorem residual_zero_of_charge_zero (b : H)
    (h : inner ℝ (ProjectionSourceImprovement.residual P b) b = 0) : ProjectionSourceImprovement.residual P b = 0 := by
  rw [residual_charge] at h
  exact norm_eq_zero.mp (by nlinarith [norm_nonneg (ProjectionSourceImprovement.residual P b)])

theorem residual_charge_pos (b : H) (h : ProjectionSourceImprovement.residual P b ≠ 0) :
    0 < inner ℝ (ProjectionSourceImprovement.residual P b) b := by
  rw [residual_charge]
  exact sq_pos_of_ne_zero (norm_ne_zero_iff.mpr h)

theorem annihilator_source_invariant (e q z : H) (t : ℝ)
    (hq : inner ℝ q z = 0) :
    inner ℝ (e+t • q) z = inner ℝ e z := by
  simp [inner_add_left, real_inner_smul_left, hq]

variable {ι : Type*} [Fintype ι]

def source (b : H) (u : ι → H) (i : ι) : ℝ :=
  inner ℝ (ProjectionSourceImprovement.residual P b) (u i)

def sourceSquare (b : H) (u : ι → H) : ℝ :=
  ∑ i, (source P b u i)^2

theorem sourceSquare_nonneg (b : H) (u : ι → H) : 0 ≤ sourceSquare P b u := by
  exact Finset.sum_nonneg (fun i _ => sq_nonneg _)

theorem source_synthesis (b : H) (u : ι → H) (c : ι → ℝ) :
    inner ℝ (ProjectionSourceImprovement.residual P b) (Fintype.linearCombination ℝ u c) =
      ∑ i, c i * source P b u i := by
  simp only [Fintype.linearCombination_apply, inner_sum, real_inner_smul_right, source]

theorem screened_synthesis_le_raw (u : ι → H) (c : ι → ℝ) :
    ‖ProjectionSourceImprovement.residual P (Fintype.linearCombination ℝ u c)‖^2 ≤
      ‖Fintype.linearCombination ℝ u c‖^2 := by
  have h := projection_pythagoras P (Fintype.linearCombination ℝ u c)
  change _ = _ + ‖ProjectionSourceImprovement.residual P (Fintype.linearCombination ℝ u c)‖^2 at h
  nlinarith [sq_nonneg ‖P.starProjection (Fintype.linearCombination ℝ u c)‖]

theorem sourceSquare_refit_lower (b : H) (u : ι → H) {C : ℝ}
    (hC : 0 < C)
    (hbound : ∀ c : ι → ℝ,
      ‖ProjectionSourceImprovement.residual P (Fintype.linearCombination ℝ u c)‖^2 ≤ C * ∑ i, (c i)^2) :
    sourceSquare P b u / C ≤ ‖ProjectionSourceImprovement.residual P b‖^2 -
      ‖b - (P.starProjection b + (1/C) •
        ProjectionSourceImprovement.residual P (Fintype.linearCombination ℝ u (source P b u)))‖^2 := by
  rw [refit_gain_exact, source_synthesis]
  have hid : (∑ i, source P b u i * source P b u i) = sourceSquare P b u := by
    simp only [sourceSquare, pow_two]
  rw [hid]
  have hn := hbound (source P b u)
  change _ ≤ C * sourceSquare P b u at hn
  have hmul := mul_le_mul_of_nonneg_left hn (sq_nonneg (1/C))
  have he : 2*(1/C)*sourceSquare P b u -
      (1/C)^2*(C*sourceSquare P b u) = sourceSquare P b u/C := by
    field_simp [ne_of_gt hC]
    ring
  nlinarith

variable (W : Submodule ℝ H) [W.HasOrthogonalProjection]

theorem projection_error_le (b y : H) (hy : y ∈ W) :
    ‖ProjectionSourceImprovement.residual W b‖^2 ≤ ‖b-y‖^2 := by
  have he := refit_pythagoras W b y 0 hy
  have hz : ProjectionSourceImprovement.residual W (0 : H) = 0 := by simp [ProjectionSourceImprovement.residual]
  simp only [add_zero, hz, sub_zero, map_zero] at he
  nlinarith [sq_nonneg ‖W.starProjection b-y‖]

theorem gain_ge_sourceSquare (hPW : P ≤ W) (b : H) (u : ι → H)
    (hu : ∀ i, u i ∈ W) {C : ℝ} (hC : 0 < C)
    (hbound : ∀ c : ι → ℝ,
      ‖Fintype.linearCombination ℝ u c‖^2 ≤ C * ∑ i, (c i)^2) :
    sourceSquare P b u/C ≤ ‖ProjectionSourceImprovement.residual P b‖^2 - ‖ProjectionSourceImprovement.residual W b‖^2 := by
  have hs := sourceSquare_refit_lower P b u hC
    (fun c => (screened_synthesis_le_raw P u c).trans (hbound c))
  have hm : Fintype.linearCombination ℝ u (source P b u) ∈ W := by
    rw [Fintype.linearCombination_apply]
    exact W.sum_mem (fun i _ => W.smul_mem _ (hu i))
  have hy := refit_mem P W hPW b _ hm (1/C)
  have he := projection_error_le W b _ hy
  linarith

/-- Conditional research reduction: both covariance and actual-source charge
are supplied as hypotheses, not proved by this declaration. -/
theorem gain_ge_charge (hPW : P ≤ W) (b : H) (u : ι → H)
    (hu : ∀ i, u i ∈ W) {C c : ℝ} (hC : 0 < C)
    (hbound : ∀ a : ι → ℝ,
      ‖Fintype.linearCombination ℝ u a‖^2 ≤ C * ∑ i, (a i)^2)
    (hcharge : c * ‖ProjectionSourceImprovement.residual P b‖^2 ≤ sourceSquare P b u) :
    c * ‖ProjectionSourceImprovement.residual P b‖^2 / C ≤ ‖ProjectionSourceImprovement.residual P b‖^2 - ‖ProjectionSourceImprovement.residual W b‖^2 :=
  (div_le_div_of_nonneg_right hcharge hC.le).trans
    (gain_ge_sourceSquare P W hPW b u hu hC hbound)

theorem innovation_source (b z : H) :
    inner ℝ (ProjectionSourceImprovement.residual W b) z =
      inner ℝ (ProjectionSourceImprovement.residual P b) z -
        inner ℝ (W.starProjection b - P.starProjection b) z := by
  simp only [ProjectionSourceImprovement.residual, inner_sub_left]
  ring

theorem nested_residual_orthogonal (hPW : P ≤ W) (b : H) :
    inner ℝ (ProjectionSourceImprovement.residual W b) (W.starProjection b-P.starProjection b) = 0 :=
  Submodule.starProjection_inner_eq_zero b _ (W.sub_mem
    (Submodule.starProjection_apply_mem W b) (hPW (Submodule.starProjection_apply_mem P b)))

theorem innovation_energy (hPW : P ≤ W) (b : H) :
    ‖ProjectionSourceImprovement.residual P b‖^2 - ‖ProjectionSourceImprovement.residual W b‖^2 =
      ‖W.starProjection b-P.starProjection b‖^2 := by
  have h : ProjectionSourceImprovement.residual P b = ProjectionSourceImprovement.residual W b +
      (W.starProjection b-P.starProjection b) := by unfold ProjectionSourceImprovement.residual; abel
  rw [h, RiemannResearch.LinearAlgebra.TwoChannelCancellation.norm_add_sq,
    nested_residual_orthogonal P W hPW]
  ring

end RiemannResearch.Analysis.ProjectionChordObservability

/-! Section 24's one-chord gain is an immediate singleton specialization. -/
namespace RiemannResearch.Analysis.ProjectionChordObservability
open RiemannResearch.Analysis.ProjectionSourceImprovement
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable (P W : Submodule ℝ H) [P.HasOrthogonalProjection] [W.HasOrthogonalProjection]

theorem gain_ge_single_correlation (hPW : P ≤ W) (b z : H) (hz : z ∈ W)
    {C : ℝ} (hC : 0 < C) (hcost : ‖z‖^2 ≤ C) :
    (inner ℝ (residual P b) z)^2/C ≤
      ‖residual P b‖^2-‖residual W b‖^2 := by
  have hbound (a : Unit → ℝ) :
      ‖Fintype.linearCombination ℝ (fun _ : Unit => z) a‖^2 ≤
        C*∑ i : Unit, (a i)^2 := by
    simp only [Fintype.linearCombination_apply, Fintype.sum_unique,
      norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]
    nlinarith [mul_le_mul_of_nonneg_left hcost (sq_nonneg (a ()))]
  have h := gain_ge_sourceSquare P W hPW b (fun _ : Unit => z)
    (fun _ => hz) hC hbound
  simpa only [sourceSquare, source, Fintype.sum_unique] using h

end RiemannResearch.Analysis.ProjectionChordObservability
