import Mathlib.MeasureTheory.Measure.AbsolutelyContinuous
import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed
import Mathlib.MeasureTheory.Measure.Regular
import Mathlib.Tactic.GCongr

/-!
# Continuous-test domination gives a common measure class

Source: user-provided manuscript `Prime_Phases_Agenda_Proof_Attempts.tex`,
Corollary `newdistinctregularity`.

This file formalizes both the weak-limit passage for nonnegative bounded
continuous tests and the regular approximation giving mutual absolute
continuity. The zeta-specific multiplicity-square budget and Haar weak-limit
provider remain open formalization obligations. No equality of limit laws
is inferred from mutual absolute continuity.
-/

open Filter Set MeasureTheory Topology BoundedContinuousFunction
open scoped Topology ENNReal NNReal MeasureTheory

namespace MeasureTheory.Measure

variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
  [BorelSpace X] [HasOuterApproxClosed X]
  {μ ν : Measure X} [IsFiniteMeasure μ] [IsFiniteMeasure ν]

/-- The continuous upper sampling bound passes to every closed set. -/
theorem closed_upper_bound_of_continuous_tests {C : ℝ≥0∞} (hC : C ≠ ∞)
    (hupper : ∀ f : X →ᵇ ℝ≥0,
      (∫⁻ x, f x ∂ν) ≤ C * (∫⁻ x, f x ∂μ))
    {F : Set X} (hF : IsClosed F) : ν F ≤ C * μ F := by
  have hm := HasOuterApproxClosed.tendsto_lintegral_apprSeq hF μ
  have hn := HasOuterApproxClosed.tendsto_lintegral_apprSeq hF ν
  exact le_of_tendsto_of_tendsto hn (ENNReal.Tendsto.const_mul hm (Or.inr hC))
    (Eventually.of_forall fun n => hupper (hF.apprSeq n))

/-- The square of the closed-set approximation is another closed-set approximation. -/
private theorem tendsto_lintegral_apprSeq_sq {F : Set X} (hF : IsClosed F)
    (σ : Measure X) [IsFiniteMeasure σ] :
    Tendsto (fun n => ∫⁻ x, ((hF.apprSeq n x : ℝ≥0∞) ^ 2) ∂σ)
      atTop (𝓝 (σ F)) := by
  have hs := HasOuterApproxClosed.tendsto_apprSeq hF
  rw [tendsto_pi_nhds] at hs
  have hs2 : Tendsto (fun n x => ((hF.apprSeq n) ^ 2) x) atTop
      (𝓝 (F.indicator (fun _ => (1 : ℝ≥0)))) := by
    apply tendsto_pi_nhds.mpr
    intro x
    by_cases hx : x ∈ F
    · simpa [hx, BoundedContinuousFunction.pow_apply] using (hs x).pow 2
    · simpa [hx, BoundedContinuousFunction.pow_apply] using (hs x).pow 2
  have hb : ∀ n x, ((hF.apprSeq n) ^ 2) x ≤ (1 : ℝ≥0) := by
    intro n x
    have hx := HasOuterApproxClosed.apprSeq_apply_le_one hF n x
    calc
      _ = hF.apprSeq n x * hF.apprSeq n x := by simp [pow_two]
      _ ≤ 1 * 1 := mul_le_mul' hx hx
      _ = 1 := one_mul _
  simpa only [BoundedContinuousFunction.pow_apply, ENNReal.coe_pow] using
    measure_of_cont_bdd_of_tendsto_indicator σ hF.measurableSet
      (fun n => (hF.apprSeq n) ^ 2) hb hs2

/-- The continuous quadratic sampling bound passes to every closed set. -/
theorem closed_quadratic_bound_of_continuous_tests {C : ℝ≥0∞} (hC : C ≠ ∞)
    (hlower : ∀ f : X →ᵇ ℝ≥0,
      (∫⁻ x, f x ∂μ) ^ 2 ≤ C * (∫⁻ x, (f x : ℝ≥0∞) ^ 2 ∂ν))
    {F : Set X} (hF : IsClosed F) : (μ F) ^ 2 ≤ C * ν F := by
  have hm := HasOuterApproxClosed.tendsto_lintegral_apprSeq hF μ
  have hn := tendsto_lintegral_apprSeq_sq hF ν
  exact le_of_tendsto_of_tendsto (ENNReal.Tendsto.pow hm)
    (ENNReal.Tendsto.const_mul hn (Or.inr hC))
    (Eventually.of_forall fun n => hlower (hF.apprSeq n))

/-- Continuous-test upper and quadratic lower domination have exactly the same
    null sets after regular approximation. -/
theorem mutual_absoluteContinuity_of_continuous_tests
    [T2Space X] [InnerRegular μ] [InnerRegular ν] {C : ℝ≥0∞} (hC : C ≠ ∞)
    (hupper : ∀ f : X →ᵇ ℝ≥0,
      (∫⁻ x, f x ∂ν) ≤ C * (∫⁻ x, f x ∂μ))
    (hlower : ∀ f : X →ᵇ ℝ≥0,
      (∫⁻ x, f x ∂μ) ^ 2 ≤ C * (∫⁻ x, (f x : ℝ≥0∞) ^ 2 ∂ν)) :
    (ν ≪ μ) ∧ (μ ≪ ν) := by
  constructor
  · apply AbsolutelyContinuous.mk
    intro s hs hμ
    rw [hs.measure_eq_iSup_isCompact ν]
    simp only [ENNReal.iSup_eq_zero]
    intro K hKs hK
    have hμK : μ K = 0 := measure_mono_null hKs hμ
    exact le_antisymm (by simpa [hμK] using
      closed_upper_bound_of_continuous_tests hC hupper hK.isClosed) bot_le
  · apply AbsolutelyContinuous.mk
    intro s hs hν
    rw [hs.measure_eq_iSup_isCompact μ]
    simp only [ENNReal.iSup_eq_zero]
    intro K hKs hK
    have hνK : ν K = 0 := measure_mono_null hKs hν
    have hsq : (μ K) ^ 2 = 0 := le_antisymm (by simpa [hνK] using
      closed_quadratic_bound_of_continuous_tests hC hlower hK.isClosed) bot_le
    exact sq_eq_zero_iff.mp hsq

/-- The finite sampling inequalities pass through actual continuous-test weak
    limits, then give the common measure class. This is independent of how
    either empirical law is constructed. -/
theorem mutual_absoluteContinuity_of_weak_test_limits
    [T2Space X] [InnerRegular μ] [InnerRegular ν] (P Q : ℕ → Measure X)
    {C : ℝ≥0∞} (hC : C ≠ ∞)
    (hP : ∀ f : X →ᵇ ℝ≥0, Tendsto (fun n => ∫⁻ x, f x ∂P n)
      atTop (𝓝 (∫⁻ x, f x ∂μ)))
    (hQ : ∀ f : X →ᵇ ℝ≥0, Tendsto (fun n => ∫⁻ x, f x ∂Q n)
      atTop (𝓝 (∫⁻ x, f x ∂ν)))
    (hupper : ∀ n (f : X →ᵇ ℝ≥0),
      (∫⁻ x, f x ∂Q n) ≤ C * (∫⁻ x, f x ∂P n))
    (hlower : ∀ n (f : X →ᵇ ℝ≥0),
      (∫⁻ x, f x ∂P n) ^ 2 ≤ C * (∫⁻ x, (f x : ℝ≥0∞) ^ 2 ∂Q n)) :
    (ν ≪ μ) ∧ (μ ≪ ν) := by
  apply mutual_absoluteContinuity_of_continuous_tests hC
  · intro f
    exact le_of_tendsto_of_tendsto (hQ f)
      (ENNReal.Tendsto.const_mul (hP f) (Or.inr hC))
      (Eventually.of_forall fun n => hupper n f)
  · intro f
    have hQsq : Tendsto (fun n => ∫⁻ x, (f x : ℝ≥0∞) ^ 2 ∂Q n)
        atTop (𝓝 (∫⁻ x, (f x : ℝ≥0∞) ^ 2 ∂ν)) := by
      have hpoint (x : X) : (((f ^ 2) x : ℝ≥0) : ℝ≥0∞) =
          (f x : ℝ≥0∞) ^ 2 := by
        change (((f x) ^ 2 : ℝ≥0) : ℝ≥0∞) = _
        exact ENNReal.coe_pow (f x) 2
      have hsq := hQ (f ^ 2)
      simp_rw [hpoint] at hsq
      exact hsq
    exact le_of_tendsto_of_tendsto (ENNReal.Tendsto.pow (hP f))
      (ENNReal.Tendsto.const_mul hQsq (Or.inr hC))
      (Eventually.of_forall fun n => hlower n f)

end MeasureTheory.Measure
