import RiemannResearch.RH.FiniteDyadicDefect
import RiemannResearch.RH.MobiusCoefficientStabilization
import RiemannResearch.RH.ThresholdHilbertDilation
import RiemannResearch.Analysis.ExhaustiveProjectionWalk
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import RiemannResearch.RH.ParetoSignedSchurRemainder
import RiemannResearch.Analysis.CorrelationNormalizedCorrection
import RiemannResearch.Analysis.ResidualEndpointFeedback
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Finite first-coordinate Gram bound

Source: user-requested backwards RH verification, 13 October 2026.
These conditional deductions are independently formalized, without a novelty claim.
No missing arithmetic bound is asserted.
-/

noncomputable section
open Filter
open scoped Topology
namespace RiemannResearch.RH.Pareto.CoefficientStabilization
open RiemannResearch.RH.ArithmeticCumulative
open RiemannResearch.Analysis.ExhaustiveWalk
set_option backward.isDefEq.respectTransparency false

theorem doubleDilation_inner_firstPoint (f : ThresholdHilbert) :
    inner ℝ (doubleDilation f) (paretoPointHilbert 0) = 0 := by
  rw [paretoPoint_zero_inner]
  change (1 / 2 : ℝ) *
    hilbertSequence (hilbertDilation 2 (by decide) f) 1 = 0
  rw [hilbertDilation_sequence]
  simp [dilation]

theorem remove_firstPoint_norm_sq (f : ThresholdHilbert) :
    ‖f - hilbertSequence f 1 • paretoPointHilbert 0‖ ^ 2 =
      ‖f‖ ^ 2 - (hilbertSequence f 1)^2 / 2 := by
  rw [norm_sub_sq_real, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs,
    paretoPoint_zero_norm_sq, inner_smul_right, paretoPoint_zero_inner]
  ring

/-- Once the upper cutoff contains the dilation of the lower projection,
both residuals can be paired through their first-site error. -/
theorem residual_inner_doubleDilation_of_le (k n : ℕ) (hn : doubleStage k ≤ n) :
    inner ℝ (projectionResidual n)
        (doubleDilation (projectionResidual k)) =
      2 * energy n - hilbertSequence (projectionResidual n) 1 := by
  have hlegal := doubleDilation_mem_double
    ((finiteSpace k).starProjection_apply_mem hilbertOne)
  have horth := projectionResidual_inner_mem n _
    (walkSpan_mono residueAtom id hn hlegal)
  change inner ℝ (projectionResidual n)
    (doubleDilation (projection k)) = 0 at horth
  have h := congrArg (fun f => inner ℝ (projectionResidual n) f)
    firstPoint_eq_dilation_difference
  rw [paretoPoint_zero_inner, inner_sub_right, inner_smul_right,
    projectionResidual_inner_one] at h
  change (1 / 2 : ℝ) * hilbertSequence (projectionResidual n) 1 =
    energy n - (1 / 2 : ℝ) *
      inner ℝ (projectionResidual n) (doubleDilation hilbertOne) at h
  rw [show projectionResidual k = hilbertOne - projection k from rfl,
    map_sub, inner_sub_right, horth, sub_zero]
  linarith

/-- The cross-scale identity at the first admissible upper stage. -/
theorem residual_doubleStage_inner_doubleDilation (n : ℕ) :
    inner ℝ (projectionResidual (doubleStage n))
        (doubleDilation (projectionResidual n)) =
      2 * energy (doubleStage n) -
        hilbertSequence (projectionResidual (doubleStage n)) 1 :=
  residual_inner_doubleDilation_of_le n (doubleStage n) le_rfl

/-- Removing the first site from the upper residual sharpens the cross-scale
Gram inequality for every admissible pair of cutoffs. -/
theorem finite_endpoint_gram_of_le (k n : ℕ) (hn : doubleStage k ≤ n) :
    (energy n -
        hilbertSequence (projectionResidual n) 1 / 2)^2 ≤
      (energy k / 2) * (energy n -
        (hilbertSequence (projectionResidual n) 1)^2 / 2) := by
  let a := hilbertSequence (projectionResidual n) 1
  let r := projectionResidual n
  let v := doubleDilation (projectionResidual k)
  have hip : inner ℝ (paretoPointHilbert 0) v = 0 := by
    rw [real_inner_comm]
    exact doubleDilation_inner_firstPoint (projectionResidual k)
  have hpair : inner ℝ r v = 2 * energy n - a :=
    residual_inner_doubleDilation_of_le k n hn
  have hnorm : ‖v‖ ^ 2 = 2 * energy k := by
    change ‖hilbertDilation 2 (by decide) (projectionResidual k)‖ ^ 2 = _
    calc
      _ = 2 * ‖projectionResidual k‖ ^ 2 := by
        simpa using hilbertDilation_norm_sq 2 (by decide) (projectionResidual k)
      _ = _ := rfl
  have hremove : ‖r - a • paretoPointHilbert 0‖ ^ 2 =
      energy n - a^2 / 2 := remove_firstPoint_norm_sq r
  have hcs := RiemannResearch.Analysis.CorrelationCorrection.inner_sq_le
    (r - a • paretoPointHilbert 0) v
  rw [inner_sub_left, real_inner_smul_left, hip, mul_zero, sub_zero,
    hpair, hremove, hnorm] at hcs
  change (energy n - a / 2)^2 ≤
    (energy k / 2) * (energy n - a^2 / 2)
  nlinarith

/-- The endpoint Gram inequality at the first admissible upper stage. -/
theorem finite_endpoint_gram (n : ℕ) :
    (energy (doubleStage n) -
        hilbertSequence (projectionResidual (doubleStage n)) 1 / 2)^2 ≤
      (energy n / 2) * (energy (doubleStage n) -
        (hilbertSequence (projectionResidual (doubleStage n)) 1)^2 / 2) :=
  finite_endpoint_gram_of_le n (doubleStage n) le_rfl

theorem finite_endpoint_energy_le_one (n : ℕ) : energy n ≤ 1 := by
  have hz : energy 0 = 1 := by
    simp [energy, walkError, walkSpan, hilbertOne_norm_sq]
  have h := energy_antitone (Nat.zero_le n)
  rwa [hz] at h

/-- Conditional finite drop. The first-coordinate upper bound is the open
arithmetic hypothesis; it is not provided by the Gram inequality. -/
theorem finite_endpoint_quadratic_drop (n : ℕ)
    (ha : hilbertSequence (projectionResidual (doubleStage n)) 1 ≤
      (2 - Real.sqrt 2) * energy n) :
    energy (doubleStage n) ≤
      energy n - ((4 * Real.sqrt 2 - 5) / 7) * (energy n)^2 := by
  exact RiemannResearch.Analysis.ResidualEndpointFeedback.quadratic_drop_of_endpoint
    (energy (doubleStage n)) (energy n)
    (hilbertSequence (projectionResidual (doubleStage n)) 1)
    (sq_nonneg _) (finite_endpoint_energy_le_one n) ha (finite_endpoint_gram n)

/-- Conditional cofinal endpoint criterion, allowing an additive error that
tends to zero. This theorem does not assert the endpoint bound itself. -/
theorem riemannHypothesis_of_cofinal_endpoint_feedback (e : ℕ → ℝ)
    (he : Tendsto e atTop (𝓝 0))
    (hbound : ∀ B : ℕ, ∃ n : ℕ, B ≤ n ∧
      hilbertSequence (projectionResidual (doubleStage n)) 1 ≤
        (2 - Real.sqrt 2) * energy n + e n) :
    RiemannHypothesis := by
  choose k hk hendpoint using hbound
  have hk' : Tendsto k atTop atTop := tendsto_atTop_mono hk tendsto_id
  have hd : Tendsto doubleStage atTop atTop :=
    tendsto_atTop_mono (fun n => by dsimp [doubleStage]; omega) tendsto_id
  have hL1 : limitEnergy ≤ 1 :=
    le_of_tendsto_of_tendsto energy_tendsto tendsto_const_nhds
      (Eventually.of_forall finite_endpoint_energy_le_one)
  have hs0 : 0 ≤ Real.sqrt (2 : ℝ) := Real.sqrt_nonneg 2
  have hs2 : (Real.sqrt (2 : ℝ))^2 = 2 := Real.sq_sqrt (by norm_num)
  have hc0 : 0 < 2 - Real.sqrt (2 : ℝ) := by nlinarith
  have hc1 : 2 - Real.sqrt (2 : ℝ) < 1 := by nlinarith
  have hroot : (2 - Real.sqrt (2 : ℝ))^2 - 4 * (2 - Real.sqrt 2) + 2 = 0 := by
    nlinarith
  have hz := RiemannResearch.Analysis.ResidualEndpointFeedback.limit_zero_of_endpoint
    (fun j => energy (doubleStage (k j)))
    (fun j => energy (k j))
    (fun j => hilbertSequence (projectionResidual (doubleStage (k j))) 1)
    (fun j => e (k j)) limitEnergy (2 - Real.sqrt 2)
    (sq_nonneg _) hL1 hc0 hc1 hroot
    ((energy_tendsto.comp hd).comp hk') (energy_tendsto.comp hk') (he.comp hk')
    (fun j => sq_nonneg _) hendpoint (fun j => finite_endpoint_gram (k j))
  exact riemannHypothesis_of_limitCoefficients
    (limitCoefficients_eq_mobius_iff_residual_zero.mpr
      (limitResidual_zero_iff_energy_zero.mpr hz))

end RiemannResearch.RH.Pareto.CoefficientStabilization
