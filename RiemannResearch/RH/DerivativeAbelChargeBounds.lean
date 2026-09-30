import RiemannResearch.RH.DerivativeMobiusCRT
import RiemannResearch.RH.MobiusPrimitiveCharge

/-!
# Signed divisor Abel charge: vanishing endpoint and sharp comparison threshold

Source: user-directed continuation from 4557e290, 30 September 2026, using
DerivativeCRT.correctionPrimitive_eq_divisor_sum and the previously checked
complete conductor-one CRT cancellation. The latter supplies no charge sign
and is not reproved.

The primary finite identities retain the endpoint, signed divisor primitives,
first-site charge, cross terms, and both dyadic square remainders. The actual
Abel endpoint is proved to vanish using the bounded normalized primitive
kernel and strong convergence of the optimizer. This leaves a single signed
harmonic primitive sum with its exact potentially nonzero limit.

The cofinal sign provider and every strict-fraction comparison are CONDITIONAL
RESEARCH REDUCTIONS. No provider, Li positivity, Weil positivity, or RH proof
is asserted. The full residual square remains in the finite lower estimate.
-/

noncomputable section
open Filter
open scoped Topology BigOperators
namespace RiemannResearch.RH.Pareto.CoefficientStabilization

/-- The complete finite residual square converges to the first residual charge. -/
theorem finiteDyadicSquare_tendsto_firstCoordinate :
    Tendsto finiteDyadicSquare atTop (𝓝 (hilbertSequence limitResidual 1)) := by
  have hf : Tendsto projectionResidual atTop (𝓝 limitResidual) := by
    change Tendsto (fun n => hilbertOne - projection n) atTop
      (𝓝 (hilbertOne - limitProjection))
    exact tendsto_const_nhds.sub projection_tendsto
  have hd := (doubleDilation.continuous.tendsto limitResidual).comp hf
  have h := ((hf.sub (hd.const_smul (1 - Real.sqrt 2 / 2))).norm.pow 2).const_mul
    (1 + Real.sqrt 2 / 2)
  rw [CorrectionTail.firstCoordinate_eq_dyadicFactor_energy]
  change Tendsto (fun n => (1 + Real.sqrt 2 / 2) *
      ‖projectionResidual n - (1 - Real.sqrt 2 / 2) •
        doubleDilation (projectionResidual n)‖^2) atTop
    (𝓝 ((1 + Real.sqrt 2 / 2) *
      ‖limitResidual - (1 - Real.sqrt 2 / 2) • doubleDilation limitResidual‖^2))
  simpa only [Function.comp_def] using h

end RiemannResearch.RH.Pareto.CoefficientStabilization

namespace RiemannResearch.RH.Pareto
namespace CoefficientStabilization.DerivativeCompatibility
open GramMobiusCorrection
open RiemannResearch.Analysis.SignedAbel

theorem correctionPrimitive_eq_charge_prefix (n K : ℕ) (hK : K ≤ n) :
    primitive (correctionCoefficient n) K =
      ∑ m ∈ Finset.Icc 2 (K + 1), mobiusDifferenceCLM m (projectionResidual n) := by
  induction K with
  | zero => simp [primitive]
  | succ K ih =>
    have hKn : K < n := by omega
    have hc : correctionCoefficient n K =
        mobiusDifferenceCLM (K + 2) (projectionResidual n) := by
      simp only [correctionCoefficient, dif_pos hKn]
      rw [correctionVector_apply, correction_eq_residual_coordinate n (K + 2) (by omega)]
      rfl
    rw [show primitive (correctionCoefficient n) (K + 1) =
      primitive (correctionCoefficient n) K + correctionCoefficient n K by
        simp only [primitive, Finset.sum_range_succ]]
    rw [ih (by omega), hc]
    conv_rhs => rw [Finset.sum_Icc_succ_top (by omega)]

/-- Exact endpoint formula, with the first-site term retained. -/
theorem correctionPrimitive_normalized_exact (n K : ℕ) (hK : K ≤ n) :
    primitive (correctionCoefficient n) K / ((K + 2 : ℕ) : ℝ) =
      (((K + 1 : ℕ) : ℝ) / ((K + 2 : ℕ) : ℝ)) *
        inner ℝ (primitiveChargeRiesz (K + 1)) (projectionResidual n) -
      hilbertSequence (projectionResidual n) 1 / ((K + 2 : ℕ) : ℝ) := by
  have hfirst : mobiusDifferenceCLM 1 (projectionResidual n) =
      hilbertSequence (projectionResidual n) 1 := by
    simp [mobiusDifferenceCLM_apply, mobiusDifference]
  have hu : ({1} : Finset ℕ) ∪ Finset.Icc 2 (K + 1) = Finset.Icc 1 (K + 1) := by
    ext m
    simp only [Finset.mem_union, Finset.mem_singleton, Finset.mem_Icc]
    omega
  have hd : Disjoint ({1} : Finset ℕ) (Finset.Icc 2 (K + 1)) := by simp
  have hi := primitiveChargeRiesz_inner (K + 1) (projectionResidual n)
  rw [← hu, Finset.sum_union hd] at hi
  simp only [Finset.sum_singleton, hfirst] at hi
  rw [correctionPrimitive_eq_charge_prefix n K hK]
  have h1 : ((K + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  have h2 : ((K + 2 : ℕ) : ℝ) ≠ 0 := by positivity
  rw [hi]
  field_simp [h1, h2]
  ring

/-- Unconditional o(1) endpoint for the actual moving optimizer. -/
theorem correctionPrimitive_endpoint_tendsto_zero :
    Tendsto (fun n => primitive (correctionCoefficient n) n / ((n + 2 : ℕ) : ℝ))
      atTop (𝓝 0) := by
  have hf : Tendsto projectionResidual atTop (𝓝 limitResidual) := by
    change Tendsto (fun n => hilbertOne - projection n) atTop
      (𝓝 (hilbertOne - limitProjection))
    exact tendsto_const_nhds.sub projection_tendsto
  have hinner := primitiveChargeRiesz_inner_moving_tendsto_zero
    (fun n => n + 1) (tendsto_add_atTop_nat 1) projectionResidual limitResidual hf
  have hratio : Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ) / ((n + 2 : ℕ) : ℝ))
      atTop (𝓝 1) := by
    have hinv : Tendsto (fun n : ℕ => (((n + 2 : ℕ) : ℝ))⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp
        (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 2))
    have he (n : ℕ) : ((n + 1 : ℕ) : ℝ) / ((n + 2 : ℕ) : ℝ) =
        1 - (((n + 2 : ℕ) : ℝ))⁻¹ := by
      have h2 : ((n + 2 : ℕ) : ℝ) ≠ 0 := by positivity
      push_cast
      field_simp
      ring
    simpa only [he, sub_zero] using tendsto_const_nhds.sub hinv
  have heval : Tendsto (fun n => hilbertSequence (projectionResidual n) 1) atTop
      (𝓝 (hilbertSequence limitResidual 1)) := by
    simpa only [Function.comp_def, anchoredEvaluationCLM_apply] using
      ((anchoredEvaluationCLM 1).continuous.tendsto limitResidual).comp hf
  have hsmall : Tendsto (fun n => hilbertSequence (projectionResidual n) 1 /
      ((n + 2 : ℕ) : ℝ)) atTop (𝓝 0) := by
    have hinv : Tendsto (fun n : ℕ => (((n + 2 : ℕ) : ℝ))⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp
        (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 2))
    simpa only [div_eq_mul_inv, mul_zero] using heval.mul hinv
  have ht := (hratio.mul hinner).sub hsmall
  simp only [mul_zero, sub_zero] at ht
  exact ht.congr' (Eventually.of_forall (fun n =>
    (correctionPrimitive_normalized_exact n n le_rfl).symm))


/-- The finite signed divisor primitive; no absolute divisor masses are used. -/
def correctionDivisorPrimitive (n K : ℕ) : ℝ :=
  ∑ j ∈ Finset.range K, ∑ d ∈ (j + 2).divisors,
    (ArithmeticFunction.moebius ((j + 2) / d) : ℝ) *
      hilbertSequence (derivativeResidual n) d

theorem correctionDivisorPrimitive_eq (n K : ℕ) (hK : K ≤ n) :
    correctionDivisorPrimitive n K = primitive (correctionCoefficient n) K :=
  (correctionPrimitive_eq_divisor_sum n K hK).symm

def signedDivisorPrimitiveSum (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range n, correctionDivisorPrimitive n (k + 1) /
    (((k + 2 : ℕ) : ℝ) * ((k + 3 : ℕ) : ℝ))

/-- Complete finite charge: endpoint and all signed primitives remain together. -/
theorem reciprocalCorrectionAbel_eq_divisor_endpoint_sum (n : ℕ) :
    reciprocalCorrectionAbel n =
      correctionDivisorPrimitive n n / ((n + 2 : ℕ) : ℝ) +
        signedDivisorPrimitiveSum n := by
  unfold reciprocalCorrectionAbel signedDivisorPrimitiveSum
  rw [correctionDivisorPrimitive_eq n n le_rfl]
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  rw [correctionDivisorPrimitive_eq n (k + 1) (by
    have := Finset.mem_range.mp hk
    omega)]

theorem reciprocalCorrectionAbel_tendsto_full_square :
    Tendsto reciprocalCorrectionAbel atTop
      (𝓝 (-((2 - Real.sqrt 2) * limitEnergy + (Real.sqrt 2 / 2) *
        ‖limitResidual - (Real.sqrt 2 / 2) • doubleDilation limitResidual‖ ^ 2))) := by
  have he : reciprocalCorrectionAbel = reciprocalCorrection := by
    funext n
    rw [reciprocalCorrectionAbel_eq_moment,
      correctionReciprocalMoment_eq_reciprocalCorrection]
  rw [he]
  exact reciprocalCorrection_tendsto_full_remainder

theorem signedDivisorPrimitiveSum_tendsto_full_square :
    Tendsto signedDivisorPrimitiveSum atTop
      (𝓝 (-((2 - Real.sqrt 2) * limitEnergy + (Real.sqrt 2 / 2) *
        ‖limitResidual - (Real.sqrt 2 / 2) • doubleDilation limitResidual‖ ^ 2))) := by
  have he : Tendsto (fun n => correctionDivisorPrimitive n n /
      ((n + 2 : ℕ) : ℝ)) atTop (𝓝 0) := by
    have heq (n : ℕ) : correctionDivisorPrimitive n n =
        primitive (correctionCoefficient n) n := correctionDivisorPrimitive_eq n n le_rfl
    simpa only [heq] using correctionPrimitive_endpoint_tendsto_zero
  have ht := reciprocalCorrectionAbel_tendsto_full_square.sub he
  simp only [sub_zero] at ht
  apply ht.congr'
  exact Eventually.of_forall (fun n => by
    dsimp only
    rw [reciprocalCorrectionAbel_eq_divisor_endpoint_sum]
    ring)

/-- Both complete dyadic squares and both energy endpoints survive in the charge identity. -/
theorem reciprocalCorrectionAbel_doubleStage_full_squares (b : ℕ) :
    reciprocalCorrectionAbel (doubleStage b) =
      mobiusReciprocalSum (doubleStage b + 1) -
        (2 - Real.sqrt 2) * energy (doubleStage b) -
        (Real.sqrt 2 / 2) * finiteDyadicResidualRemainder (doubleStage b) +
        (Real.sqrt 2 / 2) * (energy b - energy (doubleStage (doubleStage b)) -
          finiteDyadicIncrementRemainder b) := by
  have h := reciprocalCorrection_add_dyadicSquare_sub_mobius (doubleStage b)
  rw [← correctionReciprocalMoment_eq_reciprocalCorrection,
    ← reciprocalCorrectionAbel_eq_moment,
    finiteDyadicSquare_eq_energy_add_remainder,
    finiteDyadicDefect_eq_energy_drop_sub_remainder] at h
  linarith

theorem reciprocalCorrectionAbel_centered_two_gap_sq (b : ℕ) :
    (reciprocalCorrectionAbel (doubleStage b) +
      finiteDyadicSquare (doubleStage b) -
      mobiusReciprocalSum (doubleStage b + 1))^2 ≤
        2 * (energy b - energy (doubleStage b)) *
          (energy (doubleStage b) - energy (doubleStage (doubleStage b))) := by
  rw [reciprocalCorrectionAbel_eq_moment,
    correctionReciprocalMoment_eq_reciprocalCorrection,
    reciprocalCorrection_add_dyadicSquare_sub_mobius]
  exact finiteDyadicDefect_two_gap_sq b

theorem reciprocalCorrectionAbel_doubleStage_lower (b : ℕ) :
    mobiusReciprocalSum (doubleStage b + 1) -
      finiteDyadicSquare (doubleStage b) -
      Real.sqrt (2 * (energy b - energy (doubleStage b)) *
        (energy (doubleStage b) - energy (doubleStage (doubleStage b)))) ≤
      reciprocalCorrectionAbel (doubleStage b) := by
  have hs := reciprocalCorrectionAbel_centered_two_gap_sq b
  have hpos : 0 ≤ 2 * (energy b - energy (doubleStage b)) *
      (energy (doubleStage b) - energy (doubleStage (doubleStage b))) :=
    (sq_nonneg _).trans hs
  have hbound : |reciprocalCorrectionAbel (doubleStage b) +
      finiteDyadicSquare (doubleStage b) -
      mobiusReciprocalSum (doubleStage b + 1)| ≤
      Real.sqrt (2 * (energy b - energy (doubleStage b)) *
        (energy (doubleStage b) - energy (doubleStage (doubleStage b)))) := by
    apply (sq_le_sq₀ (abs_nonneg _) (Real.sqrt_nonneg _)).mp
    rw [sq_abs, Real.sq_sqrt hpos]
    exact hs
  have hl := (abs_le.mp hbound).1
  linarith


/-- CONDITIONAL RESEARCH REDUCTION: one signed harmonic average, no termwise positivity. -/
theorem signedDivisorPrimitiveSum_cofinal_iff_residual_zero :
    (∀ ε : ℝ, 0 < ε → ∃ᶠ n : ℕ in atTop,
      -ε < signedDivisorPrimitiveSum n) ↔ limitResidual = 0 := by
  have ht : Tendsto signedDivisorPrimitiveSum atTop
      (𝓝 (-hilbertSequence limitResidual 1)) := by
    simpa only [firstCoordinate_eq_energy_add_dyadicRemainder] using
      signedDivisorPrimitiveSum_tendsto_full_square
  constructor
  · intro h
    apply firstCoordinate_zero_iff_residual_zero.mp
    by_contra hz
    have hp : 0 < hilbertSequence limitResidual 1 :=
      lt_of_le_of_ne firstCoordinate_nonneg (Ne.symm hz)
    have he : ∀ᶠ n : ℕ in atTop, signedDivisorPrimitiveSum n <
        -(hilbertSequence limitResidual 1 / 2) :=
      ht.eventually_lt_const (by linarith)
    obtain ⟨n, hn, hn'⟩ :=
      ((h (hilbertSequence limitResidual 1 / 2) (by positivity)).and_eventually he).exists
    linarith
  · intro hz ε hε
    rw [firstCoordinate_zero_iff_residual_zero.mpr hz, neg_zero] at ht
    exact (ht.eventually_const_lt (by linarith)).frequently

theorem riemannHypothesis_of_signedDivisorPrimitiveSum_cofinal
    (h : ∀ ε : ℝ, 0 < ε → ∃ᶠ n : ℕ in atTop,
      -ε < signedDivisorPrimitiveSum n) : RiemannHypothesis := by
  apply riemannHypothesis_of_fixedMismatch_limits
  exact fixedMismatch_limits_iff_residual_zero.mpr
    (signedDivisorPrimitiveSum_cofinal_iff_residual_zero.mp h)

theorem correctionPrimitive_normalized_square (n K : ℕ) (hK : K ≤ n) :
    (primitive (correctionCoefficient n) K / ((K + 2 : ℕ) : ℝ))^2 =
      ((((K + 1 : ℕ) : ℝ) / ((K + 2 : ℕ) : ℝ)) *
        inner ℝ (primitiveChargeRiesz (K + 1)) (projectionResidual n))^2 -
      2 * ((((K + 1 : ℕ) : ℝ) / ((K + 2 : ℕ) : ℝ)) *
        inner ℝ (primitiveChargeRiesz (K + 1)) (projectionResidual n)) *
        (hilbertSequence (projectionResidual n) 1 / ((K + 2 : ℕ) : ℝ)) +
      (hilbertSequence (projectionResidual n) 1 / ((K + 2 : ℕ) : ℝ))^2 := by
  rw [correctionPrimitive_normalized_exact n K hK]
  ring

theorem correctionPrimitive_normalized_centered_sq_le (n K : ℕ) (hK : K ≤ n) :
    (primitive (correctionCoefficient n) K / ((K + 2 : ℕ) : ℝ) +
      hilbertSequence (projectionResidual n) 1 / ((K + 2 : ℕ) : ℝ))^2 ≤
      196 * ((((K + 1 : ℕ) : ℝ) / ((K + 2 : ℕ) : ℝ)))^2 * energy n := by
  have h := (abs_real_inner_le_norm (primitiveChargeRiesz (K + 1))
    (projectionResidual n)).trans
      (mul_le_mul_of_nonneg_right (primitiveChargeRiesz_norm_le (K + 1)) (norm_nonneg _))
  have hs := mul_self_le_mul_self (abs_nonneg _) h
  have hi : (inner ℝ (primitiveChargeRiesz (K + 1)) (projectionResidual n))^2 ≤
      196 * energy n := by
    change _ ≤ 196 * ‖projectionResidual n‖^2
    nlinarith [sq_abs (inner ℝ (primitiveChargeRiesz (K + 1)) (projectionResidual n))]
  rw [correctionPrimitive_normalized_exact n K hK, sub_add_cancel, mul_pow]
  exact (mul_le_mul_of_nonneg_left hi (sq_nonneg _)).trans_eq (by ring)


theorem reciprocalCorrectionAbel_centered_tendsto_zero :
    Tendsto (fun n => reciprocalCorrectionAbel n + finiteDyadicSquare n)
      atTop (𝓝 0) := by
  have ht : Tendsto reciprocalCorrectionAbel atTop
      (𝓝 (-hilbertSequence limitResidual 1)) := by
    simpa only [firstCoordinate_eq_energy_add_dyadicRemainder] using
      reciprocalCorrectionAbel_tendsto_full_square
  simpa only [neg_add_cancel] using ht.add finiteDyadicSquare_tendsto_firstCoordinate

/-- Sharp signed comparison boundary: any fixed strict improvement over coefficient one
is equivalent to residual zero; coefficient one itself is established unconditionally. -/
theorem reciprocalCorrectionAbel_strict_fraction_cofinal_iff_residual_zero
    (θ : ℝ) (hθ : θ < 1) :
    (∀ ε : ℝ, 0 < ε → ∃ᶠ n : ℕ in atTop,
      -ε < reciprocalCorrectionAbel n + θ * finiteDyadicSquare n) ↔
        limitResidual = 0 := by
  have ha : Tendsto reciprocalCorrectionAbel atTop
      (𝓝 (-hilbertSequence limitResidual 1)) := by
    simpa only [firstCoordinate_eq_energy_add_dyadicRemainder] using
      reciprocalCorrectionAbel_tendsto_full_square
  have ht : Tendsto (fun n => reciprocalCorrectionAbel n + θ * finiteDyadicSquare n)
      atTop (𝓝 (-(1 - θ) * hilbertSequence limitResidual 1)) := by
    have h := ha.add (finiteDyadicSquare_tendsto_firstCoordinate.const_mul θ)
    have he : -hilbertSequence limitResidual 1 + θ * hilbertSequence limitResidual 1 =
        -(1 - θ) * hilbertSequence limitResidual 1 := by ring
    rw [he] at h
    exact h
  constructor
  · intro h
    apply firstCoordinate_zero_iff_residual_zero.mp
    by_contra hz
    have hp : 0 < hilbertSequence limitResidual 1 :=
      lt_of_le_of_ne firstCoordinate_nonneg (Ne.symm hz)
    have hε : 0 < (1 - θ) * hilbertSequence limitResidual 1 / 2 := by positivity
    have he : ∀ᶠ n : ℕ in atTop, reciprocalCorrectionAbel n + θ * finiteDyadicSquare n <
        -((1 - θ) * hilbertSequence limitResidual 1 / 2) :=
      ht.eventually_lt_const (by nlinarith)
    obtain ⟨n, hn, hn'⟩ :=
      ((h ((1 - θ) * hilbertSequence limitResidual 1 / 2) hε).and_eventually he).exists
    linarith
  · intro hz ε hε
    rw [firstCoordinate_zero_iff_residual_zero.mpr hz, mul_zero] at ht
    exact (ht.eventually_const_lt (by linarith)).frequently

end CoefficientStabilization.DerivativeCompatibility

end RiemannResearch.RH.Pareto
