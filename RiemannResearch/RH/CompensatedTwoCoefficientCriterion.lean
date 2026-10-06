import RiemannResearch.RH.OptimalTwoCoefficientCriterion
import RiemannResearch.RH.ResidueGramModeIdentities

/-!
# Actual compensated optimal-coefficient criterion

Source: user-provided `FixedGramAdjointContinuation20261006.md`, equations
(31)--(36). The complete finite Gram coefficient bridge is the existing
`coefficient_eq_inverseGram_logarithmicSource`. Every conductor from 2 through
n+1 participates in `coefficient n`; no prime-only truncation is made.

The cofinal arithmetic lower bound remains an explicit hypothesis. The exact
limiting completed square and first-coordinate rigidity prove its equivalence
with the actual canonical residual vanishing. The RH implication is conditional
on that arithmetic bound. The final full RH equivalence additionally exposes
the current RH-to-target-membership formalization gap as `hTarget`.

-/

noncomputable section
open Filter
open scoped Topology
namespace RiemannResearch.RH.Pareto.CoefficientStabilization
open RiemannResearch.RH.ArithmeticCumulative

set_option backward.isDefEq.respectTransparency false

/-- The complete square for the actual scaled dyadic operator D=2S. -/
def twoThreeCompleted (x : ThresholdHilbert) : ThresholdHilbert :=
  (6 : ℝ) • x - (13 / 2 : ℝ) • doubleDilation x +
    (3 : ℝ) • doubleDilation (doubleDilation x)

@[simp] theorem twoThreeCompleted_zero : twoThreeCompleted 0 = 0 := by
  simp [twoThreeCompleted]

/-- Both dyadic terms vanish at physical site one. -/
theorem twoThreeCompleted_firstCoordinate (x : ThresholdHilbert) :
    hilbertSequence (twoThreeCompleted x) 1 = 6 * hilbertSequence x 1 := by
  unfold twoThreeCompleted
  rw [doubleDilation_twice]
  simp only [hilbertSequence_add, hilbertSequence_sub, hilbertSequence_smul,
    Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul,
    doubleDilation, hilbertDilationContinuous_apply, hilbertDilation_sequence]
  norm_num [dilation, hilbertSequence_zero]

/-- Equation (31), using actual full-norm optimal projection coefficients. -/
def twoThreeCompensated (n : ℕ) : ℝ :=
  3 * coefficient n 2 + coefficient n 3 - 4 + (23 / 24 : ℝ) * energy n

def twoThreeCompensatedLimit : ℝ :=
  3 * limitCoefficient 2 + limitCoefficient 3 - 4 +
    (23 / 24 : ℝ) * limitEnergy

/-- The statistic uses the inverse of the complete stage Gram matrix and its
exact energy defect, retaining every composite conductor. -/
theorem twoThreeCompensated_eq_full_inverseGram (n : ℕ) (hn : 2 ≤ n) :
    twoThreeCompensated n =
      3 * ((IntegerDPP.fullGram n)⁻¹.mulVec (logarithmicSource n)) ⟨0, by omega⟩ +
      ((IntegerDPP.fullGram n)⁻¹.mulVec (logarithmicSource n)) ⟨1, by omega⟩ - 4 +
      (23 / 24 : ℝ) * (1 - dotProduct (logarithmicSource n)
        ((IntegerDPP.fullGram n)⁻¹.mulVec (logarithmicSource n))) := by
  have h0 := coefficient_eq_inverseGram_logarithmicSource n ⟨0, by omega⟩
  have h1 := coefficient_eq_inverseGram_logarithmicSource n ⟨1, by omega⟩
  unfold twoThreeCompensated
  rw [energy_eq_one_sub_mode_sum, ← logarithmic_inverseGram_eq_mode_sum]
  simp only [Nat.zero_add, Nat.reduceAdd] at h0 h1
  rw [h0, h1]

/-- The substantive arithmetic assertion in equation (33), still Open. -/
def TwoThreeCompensatedCofinal : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ N : ℕ,
    ∃ n : ℕ, max N 2 ≤ n ∧ -ε < twoThreeCompensated n

theorem twoThreeCompensated_tendsto :
    Tendsto twoThreeCompensated atTop (𝓝 twoThreeCompensatedLimit) := by
  change Tendsto
    (fun n => 3 * coefficient n 2 + coefficient n 3 - 4 +
      (23 / 24 : ℝ) * energy n) atTop
    (𝓝 (3 * limitCoefficient 2 + limitCoefficient 3 - 4 +
      (23 / 24 : ℝ) * limitEnergy))
  exact (twoThreeCoefficients_tendsto.sub tendsto_const_nhds).add
    (energy_tendsto.const_mul (23 / 24 : ℝ))

/-- The full norm-square remainder survives compensation exactly. -/
theorem twoThreeCompensatedLimit_square_identity :
    twoThreeCompensatedLimit =
      -(1 / 12 : ℝ) * ‖twoThreeCompleted limitResidual‖ ^ 2 := by
  have hs := twoThreeLimit_square_identity
  change 4 - 3 * limitCoefficient 2 - limitCoefficient 3 =
    (1 / 12 : ℝ) * ‖twoThreeCompleted limitResidual‖ ^ 2 +
      (23 / 24 : ℝ) * limitEnergy at hs
  unfold twoThreeCompensatedLimit
  linarith

theorem twoThreeCompensatedLimit_nonpos : twoThreeCompensatedLimit ≤ 0 := by
  rw [twoThreeCompensatedLimit_square_identity]
  have hn := sq_nonneg ‖twoThreeCompleted limitResidual‖
  linarith

/-- Actual canonical residual rigidity, with no leakage-energy provider. -/
theorem twoThreeCompensatedLimit_zero_iff_residual_zero :
    twoThreeCompensatedLimit = 0 ↔ limitResidual = 0 := by
  constructor
  · intro hz
    have hs := twoThreeCompensatedLimit_square_identity
    have hn := sq_nonneg ‖twoThreeCompleted limitResidual‖
    have hsq : ‖twoThreeCompleted limitResidual‖ ^ 2 = 0 := by
      linarith
    have hvec : twoThreeCompleted limitResidual = 0 :=
      norm_eq_zero.mp (sq_eq_zero_iff.mp hsq)
    apply firstCoordinate_zero_iff_residual_zero.mp
    have hhead := congrArg (fun y : ThresholdHilbert => hilbertSequence y 1) hvec
    rw [twoThreeCompleted_firstCoordinate] at hhead
    have hzero : hilbertSequence (0 : ThresholdHilbert) 1 = 0 := by
      exact congrFun (hilbertSequenceLinear.map_zero) 1
    rw [hzero] at hhead
    linarith
  · intro hr
    rw [twoThreeCompensatedLimit_square_identity, hr, twoThreeCompleted_zero]
    simp

private theorem compensated_limit_nonneg_of_cofinal
    (hc : TwoThreeCompensatedCofinal) : 0 ≤ twoThreeCompensatedLimit := by
  by_contra h
  have hL : twoThreeCompensatedLimit < 0 := lt_of_not_ge h
  have hε : 0 < -twoThreeCompensatedLimit / 2 := by linarith
  have hev : ∀ᶠ n in atTop,
      twoThreeCompensated n < twoThreeCompensatedLimit / 2 :=
    twoThreeCompensated_tendsto.eventually_lt_const (by linarith)
  obtain ⟨N, hN⟩ := eventually_atTop.1 hev
  obtain ⟨n, hn, hfn⟩ := hc (-twoThreeCompensatedLimit / 2) hε N
  have hnn : N ≤ n := le_trans (le_max_left N 2) hn
  have hupper := hN n hnn
  linarith

/-- The compensated arithmetic provider is exactly residual-zero. It is not
proved here that either side holds. -/
theorem twoThreeCompensated_cofinal_iff_residual_zero :
    TwoThreeCompensatedCofinal ↔ limitResidual = 0 := by
  constructor
  · intro hc
    apply twoThreeCompensatedLimit_zero_iff_residual_zero.mp
    exact le_antisymm twoThreeCompensatedLimit_nonpos
      (compensated_limit_nonneg_of_cofinal hc)
  · intro hr ε hε N
    have hzero := twoThreeCompensatedLimit_zero_iff_residual_zero.mpr hr
    have ht : Tendsto twoThreeCompensated atTop (𝓝 0) := by
      simpa only [hzero] using twoThreeCompensated_tendsto
    have hev : ∀ᶠ n in atTop, -ε < twoThreeCompensated n :=
      ht.eventually_const_lt (by linarith)
    obtain ⟨M, hM⟩ := eventually_atTop.1 hev
    exact ⟨max M (max N 2), le_max_right _ _, hM _ (le_max_left _ _)⟩

theorem twoThreeCompensated_cofinal_iff_energy_zero :
    TwoThreeCompensatedCofinal ↔ limitEnergy = 0 :=
  twoThreeCompensated_cofinal_iff_residual_zero.trans
    limitResidual_zero_iff_energy_zero

theorem twoThreeCompensated_cofinal_iff_one_mem_closedSpace :
    TwoThreeCompensatedCofinal ↔ hilbertOne ∈ closedSpace :=
  twoThreeCompensated_cofinal_iff_energy_zero.trans limitEnergy_zero_iff_mem

/-- Conditional research reduction. Open: provide the displayed cofinal
arithmetic lower bound for the complete optimal coefficients. -/
theorem riemannHypothesis_of_twoThreeCompensated_cofinal
    (hc : TwoThreeCompensatedCofinal) : RiemannHypothesis := by
  apply riemannHypothesis_of_limitCoefficients
  exact limitCoefficients_eq_mobius_iff_residual_zero.mpr
    (twoThreeCompensated_cofinal_iff_residual_zero.mp hc)

/-- The reverse RH-to-density implication remains an explicit structural
formalization hypothesis, matching the current repository's Mellin tests. -/
theorem riemannHypothesis_iff_twoThreeCompensated_cofinal
    (hTarget : RiemannHypothesis → hilbertOne ∈ closedSpace) :
    RiemannHypothesis ↔ TwoThreeCompensatedCofinal := by
  constructor
  · intro hRH
    apply twoThreeCompensated_cofinal_iff_one_mem_closedSpace.mpr
    exact hTarget hRH
  · exact riemannHypothesis_of_twoThreeCompensated_cofinal

/-! ## Exact finite signed enlargement bridge -/

def twoThreeResidual (n : ℕ) : ThresholdHilbert := hilbertOne - projection n

def twoThreeDyadicEnlargement (n : ℕ) : ℝ :=
  inner ℝ (twoThreeResidual n) (doubleDilation (projection n))

def twoThreeDyadicEnlargementTwice (n : ℕ) : ℝ :=
  inner ℝ (twoThreeResidual n) (doubleDilation (doubleDilation (projection n)))

theorem twoThreeResidual_norm_sq (n : ℕ) :
    ‖twoThreeResidual n‖ ^ 2 = energy n := rfl

theorem twoThreeResidual_inner_projection (n : ℕ) :
    inner ℝ (twoThreeResidual n) (projection n) = 0 := by
  rw [real_inner_comm]
  exact ((finiteSpace n).mem_orthogonal _).mp
    (Submodule.sub_starProjection_mem_orthogonal hilbertOne) _
    ((finiteSpace n).starProjection_apply_mem hilbertOne)

private theorem twoThreeRiesz_inner_coefficient (x : ThresholdHilbert) :
    inner ℝ x ((-3 : ℝ) • mobiusRieszHilbert 2 - mobiusRieszHilbert 3) =
      3 * coefficientCLM 2 x + coefficientCLM 3 x := by
  have h2 : inner ℝ x (mobiusRieszHilbert 2) = mobiusDifferenceCLM 2 x := by
    rw [real_inner_comm]
    exact mobiusRieszHilbert_inner 2 x
  have h3 : inner ℝ x (mobiusRieszHilbert 3) = mobiusDifferenceCLM 3 x := by
    rw [real_inner_comm]
    exact mobiusRieszHilbert_inner 3 x
  simp only [inner_sub_right, real_inner_smul_right]
  rw [h2, h3]
  simp only [coefficientCLM, neg_apply]
  ring

/-- The exact finite coefficient charge, paired with its actual dyadic
polynomial Riesz vector. -/
theorem twoThreeResidual_charge (n : ℕ) :
    inner ℝ (twoThreeResidual n)
      ((14 : ℝ) • hilbertOne - (13 : ℝ) • doubleDilation hilbertOne +
        (3 : ℝ) • doubleDilation (doubleDilation hilbertOne)) =
      4 - 3 * coefficient n 2 - coefficient n 3 := by
  rw [← twoThreeRiesz_eq_dilation]
  unfold twoThreeResidual
  rw [inner_sub_left, twoThreeRiesz_inner_coefficient,
    twoThreeRiesz_inner_coefficient]
  have h2 : coefficientCLM 2 hilbertOne = 1 := by
    simp only [coefficientCLM, neg_apply, mobius_coordinate_one 2 (by decide)]
    norm_num [ArithmeticFunction.moebius_apply_prime Nat.prime_two]
  have h3 : coefficientCLM 3 hilbertOne = 1 := by
    simp only [coefficientCLM, neg_apply, mobius_coordinate_one 3 (by decide)]
    norm_num [ArithmeticFunction.moebius_apply_prime Nat.prime_three]
  rw [h2, h3]
  change 3 * 1 + 1 - (3 * coefficient n 2 + coefficient n 3) = _
  ring

/-- Equation (36) with its full completed-square remainder. The two signed
enlargement terms are retained; no finite-space invariance is assumed. -/
theorem twoThreeResidual_finite_square_identity (n : ℕ) :
    4 - 3 * coefficient n 2 - coefficient n 3 =
      (1 / 12 : ℝ) * ‖twoThreeCompleted (twoThreeResidual n)‖ ^ 2 +
      (23 / 24 : ℝ) * energy n -
      13 * twoThreeDyadicEnlargement n + 3 * twoThreeDyadicEnlargementTwice n := by
  have hc := twoThreeResidual_charge n
  have he : hilbertOne = twoThreeResidual n + projection n := by
    unfold twoThreeResidual
    abel
  have hp := twoThreeResidual_inner_projection n
  have hs := doubleDilation_square_identity (twoThreeResidual n)
  change inner ℝ (twoThreeResidual n)
    ((14 : ℝ) • twoThreeResidual n - (13 : ℝ) • doubleDilation (twoThreeResidual n) +
      (3 : ℝ) • doubleDilation (doubleDilation (twoThreeResidual n))) =
    (1 / 12 : ℝ) * ‖twoThreeCompleted (twoThreeResidual n)‖ ^ 2 +
      (23 / 24 : ℝ) * ‖twoThreeResidual n‖ ^ 2 at hs
  rw [he] at hc
  simp only [map_add, smul_add, inner_add_right, inner_sub_right,
    real_inner_smul_right] at hc hs
  rw [hp] at hc
  rw [twoThreeResidual_norm_sq] at hs
  unfold twoThreeDyadicEnlargement twoThreeDyadicEnlargementTwice
  linarith

/-- Exact compensated finite statistic: both signed enlargement terms remain
alongside the negative full norm square. D=2S gives +26δ_n-12δ₂,n. -/
theorem twoThreeCompensated_finite_square_identity (n : ℕ) :
    twoThreeCompensated n =
      -(1 / 12 : ℝ) * ‖twoThreeCompleted (twoThreeResidual n)‖ ^ 2 +
      13 * twoThreeDyadicEnlargement n - 3 * twoThreeDyadicEnlargementTwice n := by
  have hs := twoThreeResidual_finite_square_identity n
  unfold twoThreeCompensated
  linarith

end RiemannResearch.RH.Pareto.CoefficientStabilization
