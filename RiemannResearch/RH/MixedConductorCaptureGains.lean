import RiemannResearch.RH.ScreenedPrimePowerTelescope
import RiemannResearch.RH.ConductorProjectionChain

/-!
# Relative gains for the mixed-conductor projection of centered parity

Source: the fixed-conductor saturation question for the Pareto packet space.
The denominator in each relative gain is the remaining *centered* energy.
A common multiple of the conductors gives a strictly positive contribution
at every finite stage. The norm identity therefore gives an exact product
and a nonsummability criterion for this particular mixed dictionary.
-/

noncomputable section
open Filter
open scoped BigOperators Topology

namespace RiemannResearch.RH.Pareto.PrimePowerSchur.CaptureGains
open CoefficientStabilization

/-- The fixed datum whose approximation by mixed packets is at issue. -/
def centeredParity : ThresholdHilbert :=
  ramanujanPacketHilbert 2 - Real.log 2 • hilbertOne

/-- The complete squared Pareto error at the mixed cutoff. -/
def deficit (B : ℕ) : ℝ := ‖finiteScreening B centeredParity‖ ^ 2

/-- The squared norm of the actual change of mixed projection. -/
def gain (A B : ℕ) : ℝ :=
  ‖(mixedSpace (Finset.Icc 2 B)).starProjection (ramanujanPacketHilbert 2) -
    (mixedSpace (Finset.Icc 2 A)).starProjection (ramanujanPacketHilbert 2)‖ ^ 2

theorem project_centeredParity (B : ℕ) :
    (mixedSpace (Finset.Icc 2 B)).starProjection centeredParity =
      (mixedSpace (Finset.Icc 2 B)).starProjection (ramanujanPacketHilbert 2) := by
  rw [centeredParity, map_sub, map_smul, (Submodule.starProjection_apply_eq_zero_iff _).mpr
    (one_mem_mixed_orthogonal _), smul_zero, sub_zero]

theorem centeredParity_norm_sq :
    ‖centeredParity‖ ^ 2 = Real.log 2 - (Real.log 2) ^ 2 := by
  have hmean : inner ℝ (ramanujanPacketHilbert 2) hilbertOne = Real.log 2 := by
    rw [hilbert_inner_one, hilbertSequence_ramanujanPacketHilbert, paretoMean_ramanujanPacket,
      ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two]
    norm_num
  rw [centeredParity, norm_sub_sq_real, real_inner_smul_right, hmean,
    ramanujanPacketHilbert_two_norm_sq, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs,
    hilbertOne_norm_sq]
  ring

/-- The capture plus its deficit is exactly the variance of parity. -/
theorem deficit_add_capture (B : ℕ) :
    deficit B + ‖(mixedSpace (Finset.Icc 2 B)).starProjection (ramanujanPacketHilbert 2)‖ ^ 2 =
      Real.log 2 - (Real.log 2) ^ 2 := by
  let K := mixedSpace (Finset.Icc 2 B)
  have ho := (K.mem_orthogonal _).mp (K.sub_starProjection_mem_orthogonal centeredParity)
    _ (K.starProjection_apply_mem centeredParity)
  rw [inner_sub_right, real_inner_self_eq_norm_sq, sub_eq_zero, real_inner_comm] at ho
  rw [← project_centeredParity, deficit, finiteScreening_apply, norm_sub_sq_real]
  change ‖centeredParity‖ ^ 2 - 2 * inner ℝ centeredParity (K.starProjection centeredParity) +
    ‖K.starProjection centeredParity‖ ^ 2 + ‖K.starProjection centeredParity‖ ^ 2 = _
  rw [ho, centeredParity_norm_sq]
  ring

/-- All mixed fits vanish on a common multiple, where the centered target equals
minus log 2. This supplies a positive error before every finite gain division. -/
theorem common_multiple_floor (B L : ℕ) (hL : 0 < L) (h2 : 2 ∣ L)
    (hdiv : ∀ q ∈ mixedConductors (Finset.Icc 2 B), q ∣ L) :
    positiveWeight L * (Real.log 2) ^ 2 ≤ deficit B := by
  let K := mixedSpace (Finset.Icc 2 B)
  have hc := mixedSpace_evaluation_eq_zero_of_common_multiple _ L hdiv
    (K.starProjection_apply_mem centeredParity)
  have hz : anchoredEvaluationCLM L (ramanujanPacketHilbert 2) = 0 := by
    rw [anchoredEvaluationCLM_apply, hilbertSequence_ramanujanPacketHilbert,
      ramanujanPacket_eq_zero_of_dvd h2]
  have h1 : anchoredEvaluationCLM L hilbertOne = 1 := by
    rw [anchoredEvaluationCLM_apply, hilbertOne_sequence]
    simp [zeroAnchor, hL.ne']
  have he : hilbertSequence (finiteScreening B centeredParity) L = -Real.log 2 := by
    rw [← anchoredEvaluationCLM_apply, finiteScreening_apply, map_sub, hc, sub_zero,
      centeredParity, map_sub, map_smul, hz, h1, smul_eq_mul, mul_one, zero_sub]
  rw [deficit, hilbert_norm_weighted_sq]
  have h := (hilbertSequence_square_summable (finiteScreening B centeredParity)).sum_le_tsum
    ({L} : Finset ℕ) (fun k _ => mul_nonneg (positiveWeight_nonneg k) (sq_nonneg _))
  simpa only [Finset.sum_singleton, he, neg_sq] using h

theorem deficit_pos (B : ℕ) : 0 < deficit B := by
  let L := 2 * (B + 1).factorial
  have hL : 0 < L := Nat.mul_pos (by decide) (Nat.factorial_pos _)
  have hdiv (q : ℕ) (hq : q ∈ mixedConductors (Finset.Icc 2 B)) : q ∣ L := by
    obtain ⟨lo, hi⟩ := Finset.mem_Icc.mp (Finset.mem_filter.mp hq).1
    exact dvd_mul_of_dvd_right (Nat.dvd_factorial (by omega) (by omega)) 2
  have hw : 0 < positiveWeight L := by
    have hLR : (0 : ℝ) < L := by exact_mod_cast hL
    unfold positiveWeight
    positivity
  exact (mul_pos hw (sq_pos_of_pos (Real.log_pos (by norm_num)))).trans_le
    (common_multiple_floor B L hL (dvd_mul_right 2 _) hdiv)

/-- This identity also applies to a block of new mixed conductors. -/
theorem deficit_step {A B : ℕ} (h : A ≤ B) : deficit A = deficit B + gain A B := by
  simpa only [deficit, gain, project_centeredParity] using
    finiteScreening_energy_split A B h centeredParity

def relativeGain (B : ℕ) : ℝ := gain B (B + 1) / deficit B

theorem relativeGain_bounds (B : ℕ) : 0 ≤ relativeGain B ∧ relativeGain B < 1 := by
  refine ⟨div_nonneg (sq_nonneg _) (deficit_pos B).le, (div_lt_one (deficit_pos B)).mpr ?_⟩
  linarith [deficit_step (Nat.le_succ B), deficit_pos (B + 1)]

theorem deficit_recurrence (B : ℕ) : deficit (B + 1) = deficit B * (1 - relativeGain B) := by
  have h := deficit_step (Nat.le_succ B)
  unfold relativeGain
  field_simp [(deficit_pos B).ne']
  nlinarith

theorem deficit_product (N : ℕ) :
    deficit N = deficit 0 * ∏ B ∈ Finset.range N, (1 - relativeGain B) :=
  Analysis.ResidualGain.recurrence_eq_mul_product deficit_recurrence N

/-- The complete mixed-conductor saturation criterion in terms of relative
gains of actual finite fits. Their nonsummability is the arithmetic input. -/
theorem fixed_capture_saturation_iff_relativeGain_not_summable :
    Tendsto (fun B : ℕ => ‖(mixedSpace (Finset.Icc 2 B)).starProjection
        (ramanujanPacketHilbert 2)‖ ^ 2) atTop (𝓝 (Real.log 2 - (Real.log 2) ^ 2)) ↔
      ¬ Summable relativeGain := by
  have he (B : ℕ) := deficit_add_capture B
  let τ := Real.log 2 - (Real.log 2) ^ 2
  have hsub (B : ℕ) : τ - ‖(mixedSpace (Finset.Icc 2 B)).starProjection
      (ramanujanPacketHilbert 2)‖ ^ 2 = deficit B := by dsimp [τ]; linarith [he B]
  have hrev (B : ℕ) : τ - deficit B = ‖(mixedSpace (Finset.Icc 2 B)).starProjection
      (ramanujanPacketHilbert 2)‖ ^ 2 := by dsimp [τ]; linarith [he B]
  rw [← Analysis.ResidualGain.residual_tendsto_zero_iff_not_summable (deficit_pos 0)
    (fun n => (relativeGain_bounds n).1) (fun n => (relativeGain_bounds n).2) deficit_recurrence]
  constructor
  · intro h
    have hh := (tendsto_const_nhds (x := τ)).sub h
    simpa only [hsub, sub_self, τ] using hh
  · intro h
    have hh := (tendsto_const_nhds (x := τ)).sub h
    simpa only [hrev, sub_zero, τ] using hh

theorem riemannHypothesis_of_mixed_relativeGain_not_summable (h : ¬ Summable relativeGain) :
    RiemannHypothesis :=
  riemannHypothesis_of_fixed_capture_saturation
    (fixed_capture_saturation_iff_relativeGain_not_summable.mpr h)

/-- Any proposed direction in the enlarged mixed window tests the actual
projection increment. Its signed correlation uses only the old residual. -/
theorem correlation_sq_le_gain_mul_norm_sq (A B : ℕ) (y : ThresholdHilbert)
    (hy : y ∈ mixedSpace (Finset.Icc 2 B)) :
    (inner ℝ y (finiteScreening A centeredParity)) ^ 2 ≤ gain A B * ‖y‖ ^ 2 := by
  let K := mixedSpace (Finset.Icc 2 B)
  let p := K.starProjection centeredParity
  let t := (mixedSpace (Finset.Icc 2 A)).starProjection centeredParity
  have hperp : inner ℝ y (centeredParity - p) = 0 :=
    (K.mem_orthogonal _).mp (K.sub_starProjection_mem_orthogonal centeredParity) y hy
  have hsplit : finiteScreening A centeredParity = (centeredParity - p) + (p - t) := by
    change centeredParity - t = _
    abel
  rw [hsplit, inner_add_right, hperp, zero_add]
  have h := (sq_le_sq₀ (abs_nonneg _) (mul_nonneg (norm_nonneg y) (norm_nonneg (p - t)))).mpr
    (abs_real_inner_le_norm y (p - t))
  rw [sq_abs, mul_pow] at h
  simpa only [p, t, K, project_centeredParity, gain, mul_comm] using h

/-- A lower bound on each relative gain computable from a proposed direction.
The value is zero for a zero test vector. -/
def correlationShare (B : ℕ) (y : ThresholdHilbert) : ℝ :=
  (inner ℝ y (finiteScreening B centeredParity)) ^ 2 / ‖y‖ ^ 2 / deficit B

theorem correlationShare_le_relativeGain (B : ℕ) (y : ThresholdHilbert)
    (hy : y ∈ mixedSpace (Finset.Icc 2 (B + 1))) : correlationShare B y ≤ relativeGain B := by
  unfold correlationShare relativeGain
  apply div_le_div_of_nonneg_right _ (deficit_pos B).le
  by_cases hz : y = 0
  · subst y
    simp [gain]
  · exact (div_le_iff₀ (sq_pos_of_pos (norm_pos_iff.mpr hz))).mpr
      (correlation_sq_le_gain_mul_norm_sq B (B + 1) y hy)

/-- It suffices to find actual mixed test directions with divergent relative
squared correlation. No inverse Gram matrix for the enlarged window enters. -/
theorem riemannHypothesis_of_mixed_correlation_shares
    (y : ℕ → ThresholdHilbert) (hy : ∀ B, y B ∈ mixedSpace (Finset.Icc 2 (B + 1)))
    (h : ¬ Summable (fun B => correlationShare B (y B))) : RiemannHypothesis := by
  apply riemannHypothesis_of_mixed_relativeGain_not_summable
  intro hs
  apply h
  exact Summable.of_nonneg_of_le (fun B => div_nonneg
    (div_nonneg (sq_nonneg _) (sq_nonneg _)) (deficit_pos B).le)
    (fun B => correlationShare_le_relativeGain B (y B) (hy B)) hs

end RiemannResearch.RH.Pareto.PrimePowerSchur.CaptureGains
