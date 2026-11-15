import RiemannResearch.RH.CoupledResidualFiniteHead
import RiemannResearch.RH.ThresholdHilbertTail
import RiemannResearch.RH.ExactHeadResidualTail
import Mathlib.Tactic.Linarith

/-!
# Cauchy--Schwarz tail intervals for the actual signed sources

Source: continuation of the user-provided signed-head detection catalog,
14 November 2026. The primary identity keeps the signed tail correlation.
Its Cauchy--Schwarz radius improves the arithmetic-mean radius of the
sum/difference certificate. Every source, floor, and energy is the actual
two-seed Pareto object. No arithmetic source lower bound is asserted.
-/

noncomputable section
open Filter
open scoped BigOperators Topology
namespace RiemannResearch.RH.Pareto.CoupledResidual

def finiteSourceCenter (M p : ℕ) (hp : 0 < p) (K : ℕ) : ℝ :=
  sourceMain M p hp -
    ∑ n ∈ Finset.range K, error M n * sourceDilation M p hp n

def sourceTailRadius (M p : ℕ) (hp : 0 < p) (K : ℕ) : ℝ :=
  ‖hilbertTailShift (error M) K‖ * ‖hilbertTailShift (sourceDilation M p hp) K‖

/-- Exact signed head/tail decomposition, before applying an estimate. -/
theorem source_tail_correlation_identity (M p : ℕ) (hp : 0 < p) (K : ℕ) :
    source M p hp = finiteSourceCenter M p hp K -
      inner ℝ (hilbertTailShift (error M) K)
        (hilbertTailShift (sourceDilation M p hp) K) := by
  rw [source_residual_identity, hilbertTailShift_inner_sub_head]
  dsimp only [finiteSourceCenter, sourceMain, sourceDilation]
  ring

theorem sourceTailRadius_nonneg (M p : ℕ) (hp : 0 < p) (K : ℕ) :
    0 ≤ sourceTailRadius M p hp K := mul_nonneg (norm_nonneg _) (norm_nonneg _)

/-- The squared radius uses only complete energies and finite observations. -/
theorem sourceTailRadius_sq (M p : ℕ) (hp : 0 < p) (K : ℕ) :
    (sourceTailRadius M p hp K)^2 =
      (distance M - coordinateHeadEnergy (error M) K) *
      ((p:ℝ)*distance (2*M/p) -
        coordinateHeadEnergy (sourceDilation M p hp) K) := by
  rw [sourceTailRadius, mul_pow, hilbertTailShift_norm_sq, hilbertTailShift_norm_sq]
  simp only [sourceDilation, hilbertDilation_norm_sq, distance, coordinateHeadEnergy]

theorem source_cauchy_interval (M p : ℕ) (hp : 0 < p) (K : ℕ) :
    finiteSourceCenter M p hp K - sourceTailRadius M p hp K ≤ source M p hp ∧
      source M p hp ≤ finiteSourceCenter M p hp K + sourceTailRadius M p hp K := by
  have hc := abs_real_inner_le_norm (hilbertTailShift (error M) K)
    (hilbertTailShift (sourceDilation M p hp) K)
  change |inner ℝ (hilbertTailShift (error M) K)
    (hilbertTailShift (sourceDilation M p hp) K)| ≤ sourceTailRadius M p hp K at hc
  obtain ⟨hl, hu⟩ := abs_le.mp hc
  have hi := source_tail_correlation_identity M p hp K
  constructor <;> linarith only [hi, hl, hu]

/-- Original lower endpoint, expressed with its exact arithmetic-mean radius. -/
theorem finiteSourceLower_eq_tailCenter (M p : ℕ) (hp : 0 < p) (K : ℕ) :
    finiteSourceLower M p hp K = finiteSourceCenter M p hp K -
      (‖hilbertTailShift (error M) K‖^2 +
        ‖hilbertTailShift (sourceDilation M p hp) K‖^2)/2 := by
  have ht := hilbertTailShift_norm_sq (error M - sourceDilation M p hp) K
  have he : hilbertTailShift (error M - sourceDilation M p hp) K =
      hilbertTailShift (error M) K - hilbertTailShift (sourceDilation M p hp) K := by
    apply Subtype.ext
    rfl
  rw [he, norm_sub_sq_real] at ht
  change _ = _ - coordinateHeadEnergy (error M - sourceDilation M p hp) K at ht
  linarith only [ht, source_lower_tail_identity M p hp K,
    source_tail_correlation_identity M p hp K]

theorem finiteSourceUpper_eq_tailCenter (M p : ℕ) (hp : 0 < p) (K : ℕ) :
    finiteSourceUpper M p hp K = finiteSourceCenter M p hp K +
      (‖hilbertTailShift (error M) K‖^2 +
        ‖hilbertTailShift (sourceDilation M p hp) K‖^2)/2 := by
  have ht := hilbertTailShift_norm_sq (error M + sourceDilation M p hp) K
  have he : hilbertTailShift (error M + sourceDilation M p hp) K =
      hilbertTailShift (error M) K + hilbertTailShift (sourceDilation M p hp) K := by
    apply Subtype.ext
    rfl
  rw [he, norm_add_sq_real] at ht
  change _ = _ - coordinateHeadEnergy (error M + sourceDilation M p hp) K at ht
  linarith only [ht, source_upper_tail_identity M p hp K,
    source_tail_correlation_identity M p hp K]

theorem sourceTailRadius_le_arithmetic_mean (M p : ℕ) (hp : 0 < p) (K : ℕ) :
    sourceTailRadius M p hp K ≤
      (‖hilbertTailShift (error M) K‖^2 +
        ‖hilbertTailShift (sourceDilation M p hp) K‖^2)/2 := by
  dsimp only [sourceTailRadius]
  nlinarith [sq_nonneg (‖hilbertTailShift (error M) K‖ -
    ‖hilbertTailShift (sourceDilation M p hp) K‖)]

/-- Distance of the sharper certified interval from zero. -/
def cauchySourceMagnitude (M p : ℕ) (hp : 0 < p) (K : ℕ) : ℝ :=
  max 0 (|finiteSourceCenter M p hp K| - sourceTailRadius M p hp K)

theorem cauchySourceMagnitude_nonneg (M p : ℕ) (hp : 0 < p) (K : ℕ) :
    0 ≤ cauchySourceMagnitude M p hp K := le_max_left _ _

theorem finiteSourceMagnitude_le_cauchy (M p : ℕ) (hp : 0 < p) (K : ℕ) :
    finiteSourceMagnitude M p hp K ≤ cauchySourceMagnitude M p hp K := by
  have hr := sourceTailRadius_le_arithmetic_mean M p hp K
  have hm := le_max_right (0:ℝ)
    (|finiteSourceCenter M p hp K| - sourceTailRadius M p hp K)
  change _ ≤ cauchySourceMagnitude M p hp K at hm
  unfold finiteSourceMagnitude
  apply max_le (cauchySourceMagnitude_nonneg M p hp K)
  apply max_le
  · rw [finiteSourceLower_eq_tailCenter]
    linarith only [hm, hr, le_abs_self (finiteSourceCenter M p hp K)]
  · rw [finiteSourceUpper_eq_tailCenter]
    linarith only [hm, hr, neg_le_abs (finiteSourceCenter M p hp K)]

theorem cauchySourceMagnitude_le_abs (M p : ℕ) (hp : 0 < p) (K : ℕ) :
    cauchySourceMagnitude M p hp K ≤ |source M p hp| := by
  obtain ⟨hl, hu⟩ := source_cauchy_interval M p hp K
  apply max_le (abs_nonneg _)
  by_cases hc : 0 ≤ finiteSourceCenter M p hp K
  · rw [abs_of_nonneg hc]
    exact hl.trans (le_abs_self _)
  · rw [abs_of_nonpos (le_of_not_ge hc)]
    linarith only [hu, neg_le_abs (source M p hp)]

/-- Quantitative truncation loss: twice the tail radius suffices. -/
theorem cauchySourceMagnitude_lower (M p : ℕ) (hp : 0 < p) (K : ℕ) :
    |source M p hp| - 2*sourceTailRadius M p hp K ≤
      cauchySourceMagnitude M p hp K := by
  have hc := abs_real_inner_le_norm (hilbertTailShift (error M) K)
    (hilbertTailShift (sourceDilation M p hp) K)
  have ha := abs_sub (finiteSourceCenter M p hp K)
    (inner ℝ (hilbertTailShift (error M) K) (hilbertTailShift (sourceDilation M p hp) K))
  rw [← source_tail_correlation_identity] at ha
  change _ ≤ sourceTailRadius M p hp K at hc
  have hm := le_max_right (0:ℝ)
    (|finiteSourceCenter M p hp K| - sourceTailRadius M p hp K)
  change _ ≤ cauchySourceMagnitude M p hp K at hm
  linarith only [hc, ha, hm]

theorem cauchySourceMagnitude_tendsto (M p : ℕ) (hp : 0 < p) :
    Tendsto (cauchySourceMagnitude M p hp) atTop (𝓝 |source M p hp|) :=
  tendsto_of_tendsto_of_tendsto_of_le_of_le (finiteSourceMagnitude_tendsto M p hp)
    tendsto_const_nhds (finiteSourceMagnitude_le_cauchy M p hp)
    (cauchySourceMagnitude_le_abs M p hp)

def cauchySourceSquare (M K : ℕ) : ℝ :=
  (cauchySourceMagnitude M 2 (by omega) K)^2 +
    (cauchySourceMagnitude M 3 (by omega) K)^2

theorem finiteSourceSquare_le_cauchy (M K : ℕ) :
    finiteSourceSquare M K ≤ cauchySourceSquare M K := by
  apply add_le_add
  · exact (sq_le_sq₀ (finiteSourceMagnitude_nonneg M 2 (by omega) K)
      (cauchySourceMagnitude_nonneg M 2 (by omega) K)).mpr
        (finiteSourceMagnitude_le_cauchy M 2 (by omega) K)
  · exact (sq_le_sq₀ (finiteSourceMagnitude_nonneg M 3 (by omega) K)
      (cauchySourceMagnitude_nonneg M 3 (by omega) K)).mpr
        (finiteSourceMagnitude_le_cauchy M 3 (by omega) K)

theorem cauchySourceSquare_le_sourceSquare (M K : ℕ) :
    cauchySourceSquare M K ≤ sourceSquare M := by
  have h2 := (sq_le_sq₀ (cauchySourceMagnitude_nonneg M 2 (by omega) K)
    (abs_nonneg (source M 2 (by omega)))).mpr
      (cauchySourceMagnitude_le_abs M 2 (by omega) K)
  have h3 := (sq_le_sq₀ (cauchySourceMagnitude_nonneg M 3 (by omega) K)
    (abs_nonneg (source M 3 (by omega)))).mpr
      (cauchySourceMagnitude_le_abs M 3 (by omega) K)
  simpa only [cauchySourceSquare, sourceSquare, sq_abs] using add_le_add h2 h3

theorem cauchySourceSquare_le_trace_gain (M K : ℕ) :
    cauchySourceSquare M K ≤ trace M * gain M := by
  have h2 := interscale_source_sq M 2 (by omega)
  have h3 := interscale_source_sq M 3 (by omega)
  have h := cauchySourceSquare_le_sourceSquare M K
  norm_num only [Nat.cast_ofNat] at h2 h3
  dsimp only [sourceSquare, trace] at h ⊢
  nlinarith

theorem cauchySourceSquare_tendsto (M : ℕ) :
    Tendsto (cauchySourceSquare M) atTop (𝓝 (sourceSquare M)) := by
  change Tendsto (fun K => (cauchySourceMagnitude M 2 (by omega) K)^2 +
    (cauchySourceMagnitude M 3 (by omega) K)^2) _ _
  simpa only [sourceSquare, sq_abs] using
    ((cauchySourceMagnitude_tendsto M 2 (by omega)).pow 2).add
      ((cauchySourceMagnitude_tendsto M 3 (by omega)).pow 2)

end RiemannResearch.RH.Pareto.CoupledResidual
