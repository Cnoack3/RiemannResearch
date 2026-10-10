import RiemannResearch.Analysis.WeightedMellinTopologyTargets
import RiemannResearch.RH.AnnularLatticeBounds
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.Tactic.FieldSimp

/-!
# Weighted energy of the actual annular lattice correction

The complete signed lattice correction is O(x^(-2)), with the sharp
pointwise coefficient 10/27 supplied by AnnularLatticeBounds. Its actual
raw function belongs to every H_a with a > -2, with an explicit norm
envelope. This is independent of RH and removes the lattice term from
the still-open infinite arithmetic membership problem.

Measurability uses the exact Bernoulli quotient for x >= 1 and the exact
empty-cutoff formula below 1. No measurability or energy provider is assumed.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set Filter
open scoped Topology

namespace RiemannResearch.Analysis.WeightedMellinTopology
open MeasureTheory.WeightedMellin
open RiemannResearch.RH
open RiemannResearch.RH.AnnularPrimePair

theorem annularBernoulliCubic_measurable :
    Measurable annularBernoulliCubic := by
  unfold annularBernoulliCubic
  exact ((measurable_id.pow_const 3).sub
    (measurable_const.mul (measurable_id.pow_const 2))).add
    (measurable_id.div_const 2)

theorem annularLatticeNumerator_measurable :
    Measurable annularLatticeNumerator := by
  have h0 := annularBernoulliCubic_measurable.comp measurable_id.fract
  have h2 := annularBernoulliCubic_measurable.comp
    (measurable_id.div_const (2 : ℝ)).fract
  have h4 := annularBernoulliCubic_measurable.comp
    (measurable_id.div_const (4 : ℝ)).fract
  have h8 := annularBernoulliCubic_measurable.comp
    (measurable_id.div_const (8 : ℝ)).fract
  exact ((h0.neg.add (measurable_const.mul h2)).sub
    (measurable_const.mul h4)).add (measurable_const.mul h8)

/-- Measurability of the actual variable-cutoff correction, globally. -/
theorem actualLatticeCorrection_measurable :
    Measurable actualLatticeCorrection := by
  have he : actualLatticeCorrection = (Ici (1 : ℝ)).piecewise
      (fun x => annularLatticeNumerator x / (3 * x ^ 2))
      (fun x => -(7 / 64 : ℝ) * x) := by
    funext x
    by_cases hx : x ∈ Ici (1 : ℝ)
    · simp only [Set.piecewise, if_pos hx]
      exact annularLatticeFinite_eq_bernoulli
        (lt_of_lt_of_le zero_lt_one hx)
    · simp only [Set.piecewise, if_neg hx]
      have hf : Nat.floor x = 0 := Nat.floor_eq_zero.mpr (lt_of_not_ge hx)
      simp [actualLatticeCorrection, indices, annularLatticeFinite, hf]
  rw [he]
  exact (annularLatticeNumerator_measurable.div
    (measurable_const.mul (measurable_id.pow_const 2))).piecewise
    measurableSet_Ici (measurable_const.mul measurable_id)

def actualAnnularLatticeVector : ℝ → ℂ :=
  fun x => (actualLatticeCorrection x : ℂ)

theorem actualAnnularLatticeVector_measurable :
    Measurable actualAnnularLatticeVector :=
  Complex.continuous_ofReal.measurable.comp actualLatticeCorrection_measurable

theorem actualAnnularLatticeVector_norm_le {x : ℝ} (hx : 0 < x) :
    ‖actualAnnularLatticeVector x‖ ≤ 10 / (27 * x ^ 2) := by
  simpa only [actualAnnularLatticeVector, Complex.norm_real, Real.norm_eq_abs,
    actualLatticeCorrection, indices] using annularLatticeFinite_abs_le hx

theorem actualAnnularLatticeVector_density_le (a : ℝ)
    {x : ℝ} (hx : 0 < x) :
    ‖actualAnnularLatticeVector x‖ ^ 2 * x ^ (-(2 * a) - 1) ≤
      (100 / 729 : ℝ) * x ^ (-(2 * a) - 5) := by
  have hb := actualAnnularLatticeVector_norm_le hx
  have hb0 : 0 ≤ 10 / (27 * x ^ 2) := by positivity
  have hs : ‖actualAnnularLatticeVector x‖ ^ 2 ≤
      (10 / (27 * x ^ 2)) ^ 2 := by
    simpa only [pow_two] using mul_le_mul hb hb
      (norm_nonneg (actualAnnularLatticeVector x)) hb0
  have hp : x ^ (-(2 * a) - 5) =
      (x ^ 4)⁻¹ * x ^ (-(2 * a) - 1) := by
    rw [show -(2 * a) - 5 = (-4 : ℝ) + (-(2 * a) - 1) by ring,
      Real.rpow_add hx, Real.rpow_neg hx.le, Real.rpow_ofNat]
  calc
    _ ≤ (10 / (27 * x ^ 2)) ^ 2 * x ^ (-(2 * a) - 1) :=
      mul_le_mul_of_nonneg_right hs (Real.rpow_nonneg hx.le _)
    _ = (100 / 729 : ℝ) * x ^ (-(2 * a) - 5) := by
      rw [hp]
      field_simp [ne_of_gt hx]
      ring

/-- The sharp pointwise lattice bound gives unconditional infinite-vector
membership throughout a > -2. -/
theorem actualAnnularLatticeVector_Ha {a : ℝ} (ha : -2 < a) :
    Ha a actualAnnularLatticeVector := by
  have hp : IntegrableOn
      (fun x : ℝ => (100 / 729 : ℝ) * x ^ (-(2 * a) - 5)) (Ioi 1) :=
    (integrableOn_Ioi_rpow_of_lt (by linarith : -(2 * a) - 5 < -1)
      (by norm_num : (0 : ℝ) < 1)).const_mul (100 / 729)
  refine ⟨actualAnnularLatticeVector_measurable, hp.mono' ?_ ?_⟩
  · exact ((actualAnnularLatticeVector_measurable.norm.pow_const 2).mul
      (measurable_id.pow_const (-(2 * a) - 1))).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    have hx0 : 0 < x := lt_trans zero_lt_one hx
    rw [Real.norm_eq_abs, abs_of_nonneg
      (mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hx0.le _))]
    exact actualAnnularLatticeVector_density_le a hx0

/-- An explicit complete infinite-tail norm envelope, independent of RH. -/
theorem actualAnnularLatticeVector_normSquared_le {a : ℝ} (ha : -2 < a) :
    normSquared a actualAnnularLatticeVector ≤
      100 / (729 * (2 * a + 4)) := by
  have hp : IntegrableOn
      (fun x : ℝ => (100 / 729 : ℝ) * x ^ (-(2 * a) - 5)) (Ioi 1) :=
    (integrableOn_Ioi_rpow_of_lt (by linarith : -(2 * a) - 5 < -1)
      (by norm_num : (0 : ℝ) < 1)).const_mul (100 / 729)
  calc
    _ ≤ ∫ x in Ioi (1 : ℝ), (100 / 729 : ℝ) * x ^ (-(2 * a) - 5) := by
      apply integral_mono_ae (actualAnnularLatticeVector_Ha ha).2 hp
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
      exact actualAnnularLatticeVector_density_le a (lt_trans zero_lt_one hx)
    _ = 100 / (729 * (2 * a + 4)) := by
      rw [integral_const_mul, integral_Ioi_rpow_of_lt
        (by linarith : -(2 * a) - 5 < -1) (by norm_num : (0 : ℝ) < 1),
        Real.one_rpow]
      rw [show -(2 * a) - 5 + 1 = -(2 * a + 4) by ring]
      field_simp [ne_of_gt (by linarith : 0 < 2 * a + 4)]

theorem finiteEnergy_neg {f : ℝ → ℂ} {s : ℝ}
    (hf : FiniteEnergy f s) : FiniteEnergy (fun x => -f x) s := by
  refine ⟨hf.1.neg, hf.2.congr ?_⟩
  exact Filter.Eventually.of_forall (fun x => by simp only [norm_neg])

/-- The actual centered arithmetic vector, with all von Mangoldt prime powers. -/
def actualCenteredAnnularVector : ℝ → ℂ := fun x => (actualCentered x : ℂ)

theorem actualCenteredAnnularVector_eq_prime_sub_lattice :
    actualCenteredAnnularVector =
      fun x => actualAnnularVector x - actualAnnularLatticeVector x := by
  funext x
  have h := actualPrimeSignal_eq_centered_add_lattice x
  change (actualCentered x : ℂ) =
    (actualPrimeSignal x : ℂ) - (actualLatticeCorrection x : ℂ)
  rw [← Complex.ofReal_sub]
  exact congrArg (fun y : ℝ => (y : ℂ))
    (show actualCentered x = actualPrimeSignal x - actualLatticeCorrection x by
      linarith)

/-- Since the exact lattice correction has finite energy, arithmetic
membership is equivalent for the two actual centerings at every a > -2. -/
theorem actualCentered_Ha_iff_actualPrimeSignal_Ha {a : ℝ} (ha : -2 < a) :
    Ha a actualCenteredAnnularVector ↔ Ha a actualAnnularVector := by
  have hδ := actualAnnularLatticeVector_Ha ha
  rw [actualCenteredAnnularVector_eq_prime_sub_lattice]
  constructor
  · intro hc
    have h := finiteEnergy_sub hc (finiteEnergy_neg hδ)
    simpa only [sub_neg_eq_add, sub_add_cancel] using h
  · intro hp
    exact finiteEnergy_sub hp hδ

/-- The lattice Mellin correction is analytic beyond the entire critical
strip, throughout Re(z) > -2. -/
theorem actualAnnularLatticeVector_transform_analyticAt {z : ℂ}
    (hz : -2 < z.re) :
    AnalyticAt ℂ (transform actualAnnularLatticeVector) z := by
  exact transform_analyticAt
    (actualAnnularLatticeVector_Ha
      (a := (z.re - 2) / 2) (by linarith)) (by linarith)

/-- Optimize the exact weighted evaluation inequality over a. -/
theorem actualAnnularLatticeVector_transform_norm_sq_le {z : ℂ}
    (hz : -2 < z.re) :
    ‖transform actualAnnularLatticeVector z‖ ^ 2 ≤
      100 / (729 * (z.re + 2) ^ 2) := by
  let a : ℝ := (z.re - 2) / 2
  have ha : -2 < a := by dsimp [a]; linarith
  have haz : a < z.re := by dsimp [a]; linarith
  have hn := actualAnnularLatticeVector_normSquared_le ha
  have he := evaluation_norm_sq_le (actualAnnularLatticeVector_Ha ha) haz
  have hd : 0 < 2 * (z.re - a) := by linarith
  calc
    _ ≤ normSquared a actualAnnularLatticeVector / (2 * (z.re - a)) := he
    _ ≤ (100 / (729 * (2 * a + 4))) / (2 * (z.re - a)) :=
      div_le_div_of_nonneg_right hn hd.le
    _ = 100 / (729 * (z.re + 2) ^ 2) := by
      dsimp [a]
      have h1 : 2 * ((z.re - 2) / 2) + 4 = z.re + 2 := by ring
      have h2 : 2 * (z.re - (z.re - 2) / 2) = z.re + 2 := by ring
      rw [h1, h2]
      field_simp [ne_of_gt (by linarith : 0 < z.re + 2)]

/-- Uniform evaluation at every positive-real-part coordinate, hence at all
nontrivial zero coordinates once their standard strip data is supplied. -/
theorem actualAnnularLatticeVector_transform_uniform_norm_sq_le {z : ℂ}
    (hz : 0 < z.re) :
    ‖transform actualAnnularLatticeVector z‖ ^ 2 ≤ (25/729:ℝ) := by
  have he := actualAnnularLatticeVector_transform_norm_sq_le (by linarith : -2 < z.re)
  have hd : 0 < 729 * (z.re + 2)^2 := by positivity
  have hs : 4 ≤ (z.re + 2)^2 := by nlinarith [sq_nonneg z.re]
  apply he.trans
  apply (div_le_iff₀ hd).mpr
  nlinarith

end RiemannResearch.Analysis.WeightedMellinTopology
