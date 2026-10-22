import RiemannResearch.RH.OptimalProjectionDilationGaps
import RiemannResearch.RH.MobiusCoefficientStabilization
import RiemannResearch.RH.MobiusResidualFirstCoordinate
import RiemannResearch.RH.ThresholdHilbertDilation
import RiemannResearch.Analysis.CorrelationNormalizedCorrection
import RiemannResearch.Analysis.ExhaustiveProjectionWalk
import RiemannResearch.Analysis.ProjectionCompressionDefect
import RiemannResearch.Analysis.AdjacentGainContraction
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Actual two-dilation innovations and their adjacent-scale audit

Source: user-requested backwards RH verification, 13 October 2026.
These conditional deductions are independently formalized, without a novelty claim.
No missing arithmetic bound is asserted.
-/

noncomputable section
open Filter
open scoped Topology BigOperators

namespace RiemannResearch.RH.Pareto.CoefficientStabilization.OptimalDilationInnovation
open RiemannResearch.Analysis.ExhaustiveWalk
open RiemannResearch.Analysis.AdjacentGainContraction
open RiemannResearch.Analysis.CorrelationCorrection

set_option backward.isDefEq.respectTransparency false

def tripleStage (n : ℕ) : ℕ := 3 * n + 2

theorem le_tripleStage (n : ℕ) : n ≤ tripleStage n := by
  unfold tripleStage
  omega

theorem hilbertDilation_mem_triple {n : ℕ} {x : ThresholdHilbert}
    (hx : x ∈ finiteSpace n) (m : ℕ) (hm : 0 < m) (hm3 : m ≤ 3) :
    hilbertDilation m hm x ∈ finiteSpace (tripleStage n) := by
  classical
  obtain ⟨a, rfl⟩ := finiteSpace_expansion n x hx
  change hilbertDilationContinuous m hm (∑ i : Fin n, a i • residueAtom i.val) ∈ _
  rw [map_sum]
  apply (finiteSpace (tripleStage n)).sum_mem
  intro i hi
  rw [map_smul]
  apply (finiteSpace (tripleStage n)).smul_mem
  change hilbertDilation m hm (residueAtom i.val) ∈ _
  rw [hilbertDilation_residueAtom]
  apply (finiteSpace (tripleStage n)).sub_mem
  · apply (finiteSpace (tripleStage n)).smul_mem
    apply normalizedResidueHilbert_mem_finiteSpace
    have hiN : i.val + 2 ≤ n + 1 := by omega
    have hmul := Nat.mul_le_mul hm3 hiN
    simp only [tripleStage]
    nlinarith
  · apply (finiteSpace (tripleStage n)).smul_mem
    apply normalizedResidueHilbert_mem_finiteSpace
    simp only [tripleStage]
    omega

def floorDilatedProjection (n m : ℕ) (hm : 0 < m) : ThresholdHilbert :=
  (1 / (m : ℝ)) • hilbertDilation m hm (projection n)

def innovation (n m : ℕ) (hm : 0 < m) : ℝ :=
  inner ℝ (projectionResidual n) (floorDilatedProjection n m hm)

def twoSource (n : ℕ) : ℝ :=
  2 * (innovation n 2 (by decide)) ^ 2 +
    3 * (innovation n 3 (by decide)) ^ 2

theorem projection_norm_sq (n : ℕ) : ‖projection n‖ ^ 2 = 1 - energy n := by
  have h := RiemannResearch.Analysis.ProjectionCompression.projection_pythagoras
    (finiteSpace n) hilbertOne
  change ‖hilbertOne‖ ^ 2 = ‖projection n‖ ^ 2 + energy n at h
  rw [hilbertOne_norm_sq] at h
  linarith

theorem floorDilatedProjection_norm_sq (n m : ℕ) (hm : 0 < m) :
    ‖floorDilatedProjection n m hm‖ ^ 2 = (1 - energy n) / m := by
  have hm0 : (m : ℝ) ≠ 0 := by positivity
  rw [floorDilatedProjection, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs,
    hilbertDilation_norm_sq, projection_norm_sq]
  field_simp <;> ring

theorem floorDilatedProjection_mem (n m : ℕ) (hm : 0 < m) (hm3 : m ≤ 3) :
    floorDilatedProjection n m hm ∈ finiteSpace (tripleStage n) :=
  (finiteSpace (tripleStage n)).smul_mem _
    (hilbertDilation_mem_triple ((finiteSpace n).starProjection_apply_mem hilbertOne)
      m hm hm3)

/-- Exact signed correlation, before applying Cauchy--Schwarz. -/
theorem innovation_eq_increment_inner (n m : ℕ) (hm : 0 < m) (hm3 : m ≤ 3) :
    innovation n m hm = inner ℝ (projection (tripleStage n) - projection n)
      (floorDilatedProjection n m hm) := by
  have h := nested_correlation (finiteSpace n) (finiteSpace (tripleStage n))
    hilbertOne (floorDilatedProjection n m hm)
    (floorDilatedProjection_mem n m hm hm3)
  exact h

/-- Unconditional finite gain from one actual legal column. -/
theorem innovation_gain (n m : ℕ) (hm : 0 < m) (hm3 : m ≤ 3) :
    (m : ℝ) * (innovation n m hm) ^ 2 ≤
      (energy n - energy (tripleStage n)) * (1 - energy n) := by
  have h := nested_correlation_sq_le (finiteSpace n) (finiteSpace (tripleStage n))
    (walkSpan_mono residueAtom id (le_tripleStage n)) hilbertOne
    (floorDilatedProjection n m hm) (floorDilatedProjection_mem n m hm hm3)
  change (innovation n m hm) ^ 2 ≤
    (energy n - energy (tripleStage n)) * ‖floorDilatedProjection n m hm‖ ^ 2 at h
  rw [floorDilatedProjection_norm_sq] at h
  have hm0 : (m : ℝ) ≠ 0 := by positivity
  calc
    _ ≤ (m : ℝ) *
        ((energy n - energy (tripleStage n)) * ((1 - energy n) / m)) :=
      mul_le_mul_of_nonneg_left h (Nat.cast_nonneg m)
    _ = _ := by field_simp <;> ring

/-- Both signed innovations are retained through their squared values. -/
theorem twoSource_gain (n : ℕ) :
    twoSource n ≤ 2 * (energy n - energy (tripleStage n)) * (1 - energy n) := by
  have h2 := innovation_gain n 2 (by decide) (by decide)
  have h3 := innovation_gain n 3 (by decide) (by decide)
  norm_num at h2 h3
  unfold twoSource
  linarith

/-- Conditional arithmetic estimate implies a quadratic decrease. -/
theorem quadratic_drop (n : ℕ) (η : ℝ)
    (hlower : η * (energy n) ^ 2 ≤ twoSource n) :
    energy (tripleStage n) ≤ energy n - (η / 2) * (energy n) ^ 2 := by
  have hsource := twoSource_gain n
  have he : 0 ≤ energy n := by change 0 ≤ ‖projectionResidual n‖ ^ 2; positivity
  have hmono := energy_antitone (le_tripleStage n)
  have hp : 0 ≤ (energy n - energy (tripleStage n)) * energy n :=
    mul_nonneg (sub_nonneg.mpr hmono) he
  nlinarith

/-- Conditional research reduction. No lower-bound provider is proved here. -/
theorem riemannHypothesis_of_cofinal_twoSource (η : ℝ) (hη : 0 < η)
    (hlower : ∀ B : ℕ, ∃ n : ℕ, B ≤ n ∧ η * (energy n) ^ 2 ≤ twoSource n) :
    RiemannHypothesis := by
  choose n hn hsource using hlower
  have hn' : Tendsto n atTop atTop := tendsto_atTop_mono hn tendsto_id
  have ht : Tendsto tripleStage atTop atTop :=
    tendsto_atTop_mono le_tripleStage tendsto_id
  have hleft : Tendsto (fun k : ℕ => (η / 2) * (energy (n k)) ^ 2)
      atTop (𝓝 ((η / 2) * limitEnergy ^ 2)) :=
    tendsto_const_nhds.mul ((energy_tendsto.comp hn').pow 2)
  have hright : Tendsto
      (fun k : ℕ => energy (n k) - energy (tripleStage (n k))) atTop (𝓝 0) := by
    simpa only [sub_self, Function.comp_def] using
      (energy_tendsto.comp hn').sub ((energy_tendsto.comp ht).comp hn')
  have hle : (η / 2) * limitEnergy ^ 2 ≤ 0 :=
    le_of_tendsto_of_tendsto hleft hright (Eventually.of_forall (fun k => by
      have h := quadratic_drop (n k) η (hsource k)
      linarith))
  have hη2 : 0 < η / 2 := by linarith
  have hsq : limitEnergy ^ 2 ≤ 0 :=
    (mul_le_mul_iff_right₀ hη2).mp (by simpa using hle)
  have hzsq : limitEnergy ^ 2 = 0 := le_antisymm hsq (sq_nonneg limitEnergy)
  have hz : limitEnergy = 0 := sq_eq_zero_iff.mp hzsq
  exact riemannHypothesis_of_limitCoefficients
    (limitCoefficients_eq_mobius_iff_residual_zero.mpr
      (limitResidual_zero_iff_energy_zero.mpr hz))

/-- A quartic source estimate implies a quartic energy decrease. The displayed
lower bound is an arithmetic hypothesis, not a result of the geometric argument. -/
theorem quartic_drop (n : ℕ) (η : ℝ)
    (hlower : η * (energy n) ^ 4 ≤ twoSource n) :
    energy (tripleStage n) ≤ energy n - (η / 2) * (energy n) ^ 4 := by
  have hsource := twoSource_gain n
  have he : 0 ≤ energy n := by change 0 ≤ ‖projectionResidual n‖ ^ 2; positivity
  have hmono := energy_antitone (le_tripleStage n)
  have hp : 0 ≤ (energy n - energy (tripleStage n)) * energy n :=
    mul_nonneg (sub_nonneg.mpr hmono) he
  nlinarith

/-- Conditional alternative with the weaker quartic-source hypothesis.
No arithmetic provider for this cofinal lower bound is asserted. -/
theorem riemannHypothesis_of_cofinal_quarticSource (η : ℝ) (hη : 0 < η)
    (hlower : ∀ B : ℕ, ∃ n : ℕ, B ≤ n ∧ η * (energy n) ^ 4 ≤ twoSource n) :
    RiemannHypothesis := by
  choose n hn hsource using hlower
  have hn' : Tendsto n atTop atTop := tendsto_atTop_mono hn tendsto_id
  have ht : Tendsto tripleStage atTop atTop :=
    tendsto_atTop_mono le_tripleStage tendsto_id
  have hleft : Tendsto (fun k : ℕ => (η / 2) * (energy (n k)) ^ 4)
      atTop (𝓝 ((η / 2) * limitEnergy ^ 4)) :=
    tendsto_const_nhds.mul ((energy_tendsto.comp hn').pow 4)
  have hright : Tendsto
      (fun k : ℕ => energy (n k) - energy (tripleStage (n k))) atTop (𝓝 0) := by
    simpa only [sub_self, Function.comp_def] using
      (energy_tendsto.comp hn').sub ((energy_tendsto.comp ht).comp hn')
  have hle : (η / 2) * limitEnergy ^ 4 ≤ 0 :=
    le_of_tendsto_of_tendsto hleft hright (Eventually.of_forall (fun k => by
      have h := quartic_drop (n k) η (hsource k)
      linarith))
  have hη2 : 0 < η / 2 := by linarith
  have hnonneg : 0 ≤ limitEnergy := by change 0 ≤ ‖limitResidual‖ ^ 2; positivity
  have hz : limitEnergy = 0 := by
    by_contra hnz
    have hpos : 0 < limitEnergy := lt_of_le_of_ne hnonneg (Ne.symm hnz)
    have hprod : 0 < (η / 2) * limitEnergy ^ 4 := mul_pos hη2 (pow_pos hpos 4)
    linarith
  exact riemannHypothesis_of_limitCoefficients
    (limitCoefficients_eq_mobius_iff_residual_zero.mpr
      (limitResidual_zero_iff_energy_zero.mpr hz))

end RiemannResearch.RH.Pareto.CoefficientStabilization.OptimalDilationInnovation

noncomputable section
open scoped Topology BigOperators
open Filter

namespace RiemannResearch.RH.Pareto.CoefficientStabilization.OptimalDilationInnovation
open RiemannResearch.Analysis.ExhaustiveWalk
open RiemannResearch.Analysis.AdjacentGainContraction
open RiemannResearch.Analysis.CorrelationCorrection

set_option backward.isDefEq.respectTransparency false

theorem floorDilatedProjection_sub (n k m : ℕ) (hm : 0 < m) :
    floorDilatedProjection k m hm - floorDilatedProjection n m hm =
      (1 / (m : ℝ)) • hilbertDilation m hm (projection k - projection n) := by
  unfold floorDilatedProjection
  change (1 / (m : ℝ)) • (hilbertDilationContinuous m hm) (projection k) -
      (1 / (m : ℝ)) • (hilbertDilationContinuous m hm) (projection n) =
    (1 / (m : ℝ)) • (hilbertDilationContinuous m hm) (projection k - projection n)
  rw [map_sub, smul_sub]

/-- Exact transported increment norm, with the previous full-energy decrease. -/
theorem column_increment_norm_sq (n m : ℕ) (hm : 0 < m) :
    ‖floorDilatedProjection (tripleStage n) m hm - floorDilatedProjection n m hm‖ ^ 2 =
      (energy n - energy (tripleStage n)) / m := by
  have hm0 : (m : ℝ) ≠ 0 := by positivity
  rw [floorDilatedProjection_sub, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs,
    hilbertDilation_norm_sq, projection_gap_sq (le_tripleStage n)]
  field_simp <;> ring

/-- Exact signed pairing with both adjacent projection increments retained. -/
theorem innovation_two_gap_identity (n m : ℕ) (hm : 0 < m) (hm3 : m ≤ 3) :
    innovation (tripleStage n) m hm =
      inner ℝ (projection (tripleStage (tripleStage n)) - projection (tripleStage n))
        (floorDilatedProjection (tripleStage n) m hm - floorDilatedProjection n m hm) := by
  have hold := floorDilatedProjection_mem n m hm hm3
  have hz := projectionResidual_inner_mem (tripleStage n)
    (floorDilatedProjection n m hm) hold
  have hmem : floorDilatedProjection (tripleStage n) m hm -
      floorDilatedProjection n m hm ∈ finiteSpace (tripleStage (tripleStage n)) :=
    (finiteSpace (tripleStage (tripleStage n))).sub_mem
      (floorDilatedProjection_mem (tripleStage n) m hm hm3)
      (walkSpan_mono residueAtom id (le_tripleStage (tripleStage n)) hold)
  have hc := nested_correlation (finiteSpace (tripleStage n))
    (finiteSpace (tripleStage (tripleStage n))) hilbertOne
    (floorDilatedProjection (tripleStage n) m hm - floorDilatedProjection n m hm) hmem
  calc
    _ = inner ℝ (projectionResidual (tripleStage n))
        (floorDilatedProjection (tripleStage n) m hm - floorDilatedProjection n m hm) := by
      rw [inner_sub_right, hz, sub_zero]
      rfl
    _ = _ := hc

/-- The actual source is controlled by the product of two adjacent gains. -/
theorem innovation_adjacent_gain (n m : ℕ) (hm : 0 < m) (hm3 : m ≤ 3) :
    (m : ℝ) * (innovation (tripleStage n) m hm) ^ 2 ≤
      (energy n - energy (tripleStage n)) *
        (energy (tripleStage n) - energy (tripleStage (tripleStage n))) := by
  have hc := inner_sq_le
    (projection (tripleStage (tripleStage n)) - projection (tripleStage n))
    (floorDilatedProjection (tripleStage n) m hm - floorDilatedProjection n m hm)
  rw [projection_gap_sq (le_tripleStage (tripleStage n)), column_increment_norm_sq] at hc
  rw [innovation_two_gap_identity n m hm hm3]
  have hm0 : (m : ℝ) ≠ 0 := by positivity
  calc
    _ ≤ (m : ℝ) *
        ((energy (tripleStage n) - energy (tripleStage (tripleStage n))) *
          ((energy n - energy (tripleStage n)) / m)) :=
      mul_le_mul_of_nonneg_left hc (Nat.cast_nonneg m)
    _ = _ := by field_simp <;> ring

theorem twoSource_adjacent_gain (n : ℕ) :
    twoSource (tripleStage n) ≤
      2 * (energy n - energy (tripleStage n)) *
        (energy (tripleStage n) - energy (tripleStage (tripleStage n))) := by
  have h2 := innovation_adjacent_gain n 2 (by decide) (by decide)
  have h3 := innovation_adjacent_gain n 3 (by decide) (by decide)
  norm_num at h2 h3
  unfold twoSource
  linarith

/-- A at a middle stage already forces a fixed decrease from the previous stage. -/
theorem previous_stage_contraction (n : ℕ) (η : ℝ) (hη : 0 < η)
    (hlower : η * (energy (tripleStage n)) ^ 2 ≤ twoSource (tripleStage n)) :
    energy (tripleStage n) ≤ (2 / (η + 2)) * energy n := by
  apply middle_contraction_of_adjacent_gains (energy n) (energy (tripleStage n))
    (energy (tripleStage (tripleStage n))) η hη
  · change 0 ≤ ‖projectionResidual (tripleStage n)‖ ^ 2
    positivity
  · change 0 ≤ ‖projectionResidual (tripleStage (tripleStage n))‖ ^ 2
    positivity
  · exact energy_antitone (le_tripleStage n)
  · exact hlower.trans (twoSource_adjacent_gain n)

theorem two_stage_contraction (n : ℕ) (η : ℝ) (hη : 0 < η)
    (hlower : η * (energy (tripleStage n)) ^ 2 ≤ twoSource (tripleStage n)) :
    energy (tripleStage (tripleStage n)) ≤ (2 / (η + 2)) * energy n :=
  (energy_antitone (le_tripleStage (tripleStage n))).trans
    (previous_stage_contraction n η hη hlower)

def geometricStage (n : ℕ) : ℕ → ℕ
  | 0 => n
  | k + 1 => tripleStage (geometricStage n k)

theorem geometricStage_conductor (n k : ℕ) :
    geometricStage n k + 1 = 3 ^ k * (n + 1) := by
  induction k with
  | zero => simp [geometricStage]
  | succ k ih =>
    simp only [geometricStage, tripleStage, pow_succ]
    nlinarith [ih]

/-- Every-scale A entails genuine geometric decay, not merely a quadratic rate. -/
theorem every_scale_geometric_bound (n : ℕ) (η : ℝ) (hη : 0 < η)
    (hlower : ∀ k : ℕ,
      η * (energy (geometricStage n (k + 1))) ^ 2 ≤ twoSource (geometricStage n (k + 1)))
    (k : ℕ) :
    energy (geometricStage n k) ≤ (2 / (η + 2)) ^ k * energy n := by
  have hq : 0 ≤ (2 : ℝ) / (η + 2) := by positivity
  induction k with
  | zero => simp [geometricStage]
  | succ k ih =>
    have hstep := previous_stage_contraction (geometricStage n k) η hη (hlower k)
    calc
      _ ≤ (2 / (η + 2)) * energy (geometricStage n k) := hstep
      _ ≤ (2 / (η + 2)) * ((2 / (η + 2)) ^ k * energy n) :=
        mul_le_mul_of_nonneg_left ih hq
      _ = _ := by rw [pow_succ]; ring


end RiemannResearch.RH.Pareto.CoefficientStabilization.OptimalDilationInnovation
