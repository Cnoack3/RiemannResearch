import RiemannResearch.Analysis.MontgomeryReconstructedGapTests
import RiemannResearch.Analysis.ActualZeroCollisionDensity
import RiemannResearch.Analysis.SineGaussianMoment
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Order.LiminfLimsup
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Gaussian tests for singleton ordinates and simple critical-line zeros

The Gaussian factorial moment counts ordered pairs of distinct occurrence labels,
including pairs at a common ordinate. The outer precision limit is taken after
the height limsup. Source: user-provided one-sided Gaussian criterion.
-/

noncomputable section
open Filter MeasureTheory Zeta23
open scoped Topology BigOperators ENNReal

namespace RiemannResearch.Analysis.ActualZeroOrdinate
open ActualZeroCollisionCertificate OrdinateCollisionCertificate

/-- Gaussian factorial moment of all actual occurrences, at the physical unfolding. -/
def gaussianFactorialMoment (a T : ℝ) : ℝ :=
  ∫ x, Real.exp (-a * x ^ 2) ∂(factorialGapMeasure T (Real.log T / (2 * Real.pi)))

theorem gaussianFactorialMoment_eq_sum (a T : ℝ) :
    gaussianFactorialMoment a T =
      (∑ p : Copies T, ∑ q ∈ Finset.univ.erase p,
        Real.exp (-a * ((Real.log T / (2 * Real.pi)) *
          (copyOrdinate T p - copyOrdinate T q)) ^ 2)) / (Ncount 0 T : ℝ) :=
  (integral_factorialGapMeasure T _ _).2

/-- The positive integer powers are the tests in the countable sine-law criterion. -/
theorem gaussianFactorialMoment_eq_weight_power (n : ℕ) (T : ℝ) :
    gaussianFactorialMoment n T = ∫ x, GaussianGapTests.weight x ^ n
      ∂(factorialGapMeasure T (Real.log T / (2 * Real.pi))) := by
  unfold gaussianFactorialMoment GaussianGapTests.weight
  apply integral_congr_ae
  refine ae_of_all _ fun x => ?_
  change Real.exp (-(n : ℝ) * x ^ 2) = Real.exp (-(x ^ 2)) ^ n
  rw [← Real.exp_nat_mul]
  congr 1
  ring

/-- The exact part of the factorial Gaussian supported away from equal ordinates. -/
def unequalOrdinateGaussianMoment (a T : ℝ) : ℝ := by
  classical
  exact (∑ p : Copies T, ∑ q ∈ Finset.univ.erase p,
    if copyOrdinate T p = copyOrdinate T q then 0 else
      Real.exp (-a * ((Real.log T / (2 * Real.pi)) *
        (copyOrdinate T p - copyOrdinate T q)) ^ 2)) / (Ncount 0 T : ℝ)

/-- Exact split into the equal-ordinate atom and the remaining Gaussian mass. -/
theorem gaussianFactorialMoment_split (a T : ℝ) :
    gaussianFactorialMoment a T =
      (occurrenceExcess (copyOrdinate T) : ℝ) / (Ncount 0 T : ℝ) +
        unequalOrdinateGaussianMoment a T := by
  classical
  rw [gaussianFactorialMoment_eq_sum, unequalOrdinateGaussianMoment, ← add_div]
  congr 1
  unfold occurrenceExcess
  simp only [Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun p _ => ?_
  let g := fun q : Copies T =>
    if p ≠ q ∧ copyOrdinate T p = copyOrdinate T q then (1 : ℝ) else 0
  have hz : g p = 0 := by simp [g]
  rw [← Finset.sum_erase Finset.univ hz, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun q hq => ?_
  have hne := (Finset.ne_of_mem_erase hq).symm
  by_cases ht : copyOrdinate T p = copyOrdinate T q <;> simp [g, hne, ht]

/-- The finite collision bound in total ordinate multiplicities. -/
theorem ordinateMultiplicity_excess_le_gaussian (a T : ℝ) :
    ((∑ τ ∈ actualOrdinateSupport T,
      actualOrdinateMultiplicity T τ * (actualOrdinateMultiplicity T τ - 1) : ℕ) : ℝ) /
      (Ncount 0 T : ℝ) ≤ gaussianFactorialMoment a T := by
  have hp : 0 ≤ unequalOrdinateGaussianMoment a T := by
    unfold unequalOrdinateGaussianMoment
    apply div_nonneg _ (Nat.cast_nonneg _)
    exact Finset.sum_nonneg fun p _ => Finset.sum_nonneg fun q _ => by
      split <;> positivity
  rw [gaussianFactorialMoment_split, occurrenceExcess_eq_multiplicityExcess]
  exact le_add_of_nonneg_right hp

/-- Number of distinct-label ordered pairs in the closed symmetric unfolded window. -/
def nearCollisionPairCount (T δ : ℝ) : ℕ := by
  classical
  exact ∑ p : Copies T, ((Finset.univ.erase p).filter fun q =>
    |(Real.log T / (2 * Real.pi)) * (copyOrdinate T p - copyOrdinate T q)| ≤ δ).card

/-- Exponential majorant for all near collisions, including exact ties and both endpoints. -/
theorem nearCollisionPairCount_le_gaussian (T : ℝ) {a δ : ℝ} (ha : 0 ≤ a) (hδ : 0 ≤ δ) :
    (nearCollisionPairCount T δ : ℝ) / (Ncount 0 T : ℝ) ≤
      Real.exp (a * δ ^ 2) * gaussianFactorialMoment a T := by
  classical
  let d (p q : Copies T) := (Real.log T / (2 * Real.pi)) * (copyOrdinate T p - copyOrdinate T q)
  rw [gaussianFactorialMoment_eq_sum, ← mul_div_assoc]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
  simp only [nearCollisionPairCount, Nat.cast_sum, Finset.mul_sum]
  refine Finset.sum_le_sum fun p _ => ?_
  change (((Finset.univ.erase p).filter fun q => |d p q| ≤ δ).card : ℝ) ≤ _
  calc
    _ = ∑ q ∈ Finset.univ.erase p, if |d p q| ≤ δ then (1 : ℝ) else 0 := by
      rw [← Finset.sum_filter]; simp
    _ ≤ _ := by
      refine Finset.sum_le_sum fun q _ => ?_
      change (if |d p q| ≤ δ then (1 : ℝ) else 0) ≤
        Real.exp (a * δ ^ 2) * Real.exp (-a * (d p q) ^ 2)
      rw [← Real.exp_add]
      split_ifs with h
      · apply Real.one_le_exp_iff.mpr
        have hs := (sq_le_sq₀ (abs_nonneg (d p q)) hδ).2 h
        rw [sq_abs] at hs
        nlinarith only [mul_le_mul_of_nonneg_left hs ha]
      · exact (Real.exp_pos _).le

/-- Increasing the Gaussian precision decreases the contribution of every pair. -/
theorem gaussianFactorialMoment_antitone (T : ℝ) :
    Antitone (fun a : ℝ => gaussianFactorialMoment a T) := by
  intro a b hab
  unfold gaussianFactorialMoment
  apply integral_mono (integral_factorialGapMeasure T _ _).1 (integral_factorialGapMeasure T _ _).1
  intro x
  exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (neg_le_neg hab) (sq_nonneg x))

/-- The unbounded height limsup is allowed to take the value infinity. -/
def gaussianHeightLimsup (n : ℕ) : ℝ≥0∞ :=
  limsup (fun T : ℝ => ENNReal.ofReal (gaussianFactorialMoment n T)) atTop

/-- Cofinal precision and eventual height quantifiers for the one-sided condition. -/
theorem gaussian_liminf_limsup_eq_zero_iff :
    liminf gaussianHeightLimsup atTop = 0 ↔
      ∀ ε : ℝ≥0∞, 0 < ε → ∀ k : ℕ, ∃ n ≥ k,
        ∀ᶠ T : ℝ in atTop, ENNReal.ofReal (gaussianFactorialMoment n T) < ε := by
  constructor
  · intro h ε hε k
    have hf : ∃ᶠ n in atTop, gaussianHeightLimsup n < ε :=
      frequently_lt_of_liminf_lt (h := h.trans_lt hε)
    obtain ⟨n, hn, hlt⟩ := frequently_atTop.1 hf k
    exact ⟨n, hn, eventually_lt_of_limsup_lt hlt⟩
  · intro h
    by_contra hn
    obtain ⟨ε, hε, hlt⟩ := exists_between (pos_iff_ne_zero.mpr hn)
    have hf : ∃ᶠ n in atTop, gaussianHeightLimsup n ≤ ε := by
      apply frequently_atTop.2
      intro k
      obtain ⟨n, hn, hT⟩ := h ε hε k
      exact ⟨n, hn, limsup_le_of_le (h := hT.mono fun _ ht => ht.le)⟩
    exact (not_le_of_gt hlt) (liminf_le_of_frequently_le' hf)

/-- For each tolerance it suffices to control one positive integer precision.
Monotonicity makes every larger precision eligible for the same height bound. -/
theorem gaussian_liminf_eq_zero_iff_one_precision :
    liminf gaussianHeightLimsup atTop = 0 ↔
      ∀ ε : ℝ, 0 < ε → ∃ n : ℕ, 0 < n ∧ ∀ᶠ T : ℝ in atTop, gaussianFactorialMoment n T < ε := by
  rw [gaussian_liminf_limsup_eq_zero_iff]
  constructor
  · intro h ε hε
    obtain ⟨n, hn, hT⟩ := h (ENNReal.ofReal ε) (ENNReal.ofReal_pos.mpr hε) 1
    exact ⟨n, hn, hT.mono fun _ ht => (ENNReal.ofReal_lt_ofReal_iff hε).1 ht⟩
  · intro h ε hε k
    by_cases ht : ε = ⊤
    · exact ⟨k, le_rfl, Eventually.of_forall fun _ => ht ▸ ENNReal.ofReal_lt_top⟩
    have hp := ENNReal.toReal_pos hε.ne' ht
    obtain ⟨n, _, hT⟩ := h ε.toReal hp
    refine ⟨max n k, le_max_right _ _, ?_⟩
    filter_upwards [hT] with T hT
    rw [← ENNReal.ofReal_toReal ht]
    exact (ENNReal.ofReal_lt_ofReal_iff hp).2
      ((gaussianFactorialMoment_antitone T (Nat.cast_le.mpr (le_max_left n k))).trans_lt hT)

/-- Density-zero ordered ties under one-sided smallness, with the actual occurrence normalizer. -/
theorem collisionExcess_density_zero_of_gaussian_liminf
    (h : liminf gaussianHeightLimsup atTop = 0) :
    Tendsto (fun T : ℝ => (occurrenceExcess (copyOrdinate T) : ℝ) / (Ncount 0 T : ℝ))
      atTop (𝓝 0) := by
  apply tendsto_order.2
  constructor
  · intro b hb
    exact Eventually.of_forall fun T => hb.trans_le (by positivity)
  · intro ε hε
    obtain ⟨n, _, hn⟩ := gaussian_liminf_limsup_eq_zero_iff.mp h
      (ENNReal.ofReal ε) (ENNReal.ofReal_pos.mpr hε) 1
    filter_upwards [hn] with T hT
    apply lt_of_le_of_lt _ ((ENNReal.ofReal_lt_ofReal_iff hε).mp hT)
    rw [occurrenceExcess_eq_multiplicityExcess]
    exact ordinateMultiplicity_excess_le_gaussian n T

/-- Density one jointly for analytic simplicity and critical-line location, and
density one for heights occupied by a single occurrence, both divided by N(T). -/
theorem density_one_of_gaussian_liminf (h : liminf gaussianHeightLimsup atTop = 0) :
    Tendsto (fun T : ℝ => (simpleCriticalCount T : ℝ) / (Ncount 0 T : ℝ)) atTop (𝓝 1) ∧
    Tendsto (fun T : ℝ => (singletonOrdinateCount T : ℝ) / (Ncount 0 T : ℝ)) atTop (𝓝 1) := by
  have hE := collisionExcess_density_zero_of_gaussian_liminf h
  have hprod := (tendsto_const_nhds (x := (1 : ℝ)) |>.add hE).mul tendsto_count_div_mainTerm
  have hc : Tendsto (fun T : ℝ => (actualCollision T : ℝ) /
      (T * Real.log T / (2 * Real.pi))) atTop (𝓝 1) := by
    apply (show Tendsto _ atTop (𝓝 (1 : ℝ)) from
      by simpa only [add_zero, mul_one] using hprod).congr'
    filter_upwards [eventually_count_pos] with T hN
    have hN' : (Ncount 0 T : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
    have hid := occurrenceCollision_eq_card_add_excess (copyOrdinate T)
    rw [card_copies] at hid
    change (1 + _ / _) * (_ / _) = (occurrenceCollision (copyOrdinate T) : ℝ) / _
    rw [hid, Nat.cast_add]
    field_simp [hN']
  have hs := (density_one_of_collision_limit hc).1
  refine ⟨hs, ?_⟩
  have hl := (hs.const_mul 3 |>.sub (tendsto_const_nhds (x := (1 : ℝ)))).div_const 2
  have hlo : Tendsto (fun T : ℝ => (3 * ((simpleCriticalCount T : ℝ) / (Ncount 0 T : ℝ)) - 1) / 2)
      atTop (𝓝 1) := by convert hl using 1; norm_num
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo tendsto_const_nhds
  · filter_upwards [eventually_count_pos] with T hN
    have hp : 0 < (Ncount 0 T : ℝ) := by exact_mod_cast hN
    have hh : 3 * (simpleCriticalCount T : ℝ) ≤
        (Ncount 0 T : ℝ) + 2 * (singletonOrdinateCount T : ℝ) := by
      exact_mod_cast three_mul_simpleCriticalCount_le T
    field_simp [hp.ne']
    linarith
  · apply Eventually.of_forall
    intro T
    apply div_le_one_of_le₀ _ (Nat.cast_nonneg _)
    exact_mod_cast (Finset.card_filter_le ..).trans
      ((Finset.card_image_le).trans_eq (by simp only [Finset.card_univ, card_copies]) :
        (actualOrdinateSupport T).card ≤ Ncount 0 T)

/-- The sine reference measure in the Gaussian gap-test theorem has this Lebesgue integral. -/
theorem sineFactorialGapMeasure_gaussian (a : ℝ) :
    (∫ x, Real.exp (-a * x ^ 2) ∂sineFactorialGapMeasure) =
      ∫ x : ℝ, Real.exp (-a * x ^ 2) * (1 - Real.sinc (Real.pi * x) ^ 2) := by
  have hpos (x : ℝ) : 0 ≤ 1 - Real.sinc (Real.pi * x) ^ 2 := by
    have hs := (sq_le_sq₀ (abs_nonneg (Real.sinc (Real.pi * x))) zero_le_one).2
      (Real.abs_sinc_le_one _)
    rw [sq_abs] at hs
    linarith
  rw [sineFactorialGapMeasure, integral_withDensity_eq_integral_toReal_smul (by fun_prop)
    (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
  apply integral_congr_ae
  refine ae_of_all _ fun x => ?_
  change (ENNReal.ofReal (1 - Real.sinc (Real.pi * x) ^ 2)).toReal • Real.exp (-a * x ^ 2) = _
  rw [smul_eq_mul, ENNReal.toReal_ofReal (hpos x), mul_comm]

/-- A one-sided model upper estimate gives cubic suppression at the corresponding
width. The arbitrarily small slack is taken after fixing the positive precision. -/
theorem nearCollision_cubic_of_sine_gaussian_upper {a : ℝ} (ha : 0 < a)
    (h : ∀ ε : ℝ, 0 < ε → ∀ᶠ T : ℝ in atTop, gaussianFactorialMoment a T ≤
      (∫ x, Real.exp (-a * x ^ 2) ∂sineFactorialGapMeasure) + ε) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ T : ℝ in atTop,
      (nearCollisionPairCount T (1 / Real.sqrt a) : ℝ) / (Ncount 0 T : ℝ) ≤
        (Real.exp 1 * Real.pi ^ (5 / 2 : ℝ) / 6) * (1 / Real.sqrt a) ^ 3 + ε := by
  intro ε hε
  have hs : 0 < Real.sqrt a := Real.sqrt_pos.mpr ha
  have hscale : a * (1 / Real.sqrt a) ^ 2 = 1 := by
    rw [div_pow, Real.sq_sqrt ha.le]
    field_simp
  have hpow : a ^ (3 / 2 : ℝ) = (Real.sqrt a) ^ 3 := by
    rw [show (3 / 2 : ℝ) = (1 / 2 : ℝ) * (3 : ℕ) by norm_num, Real.rpow_mul ha.le,
      Real.rpow_natCast, ← Real.sqrt_eq_rpow]
  have hmodel := GaussianGapTests.sine_gaussian_moment_le ha
  rw [← sineFactorialGapMeasure_gaussian] at hmodel
  filter_upwards [h (ε / Real.exp 1) (div_pos hε (Real.exp_pos _))] with T hT
  calc
    _ ≤ Real.exp 1 * gaussianFactorialMoment a T := by
      simpa only [hscale] using nearCollisionPairCount_le_gaussian T ha.le (one_div_pos.mpr hs).le
    _ ≤ Real.exp 1 * (Real.pi ^ (5 / 2 : ℝ) / (6 * a ^ (3 / 2 : ℝ)) + ε / Real.exp 1) :=
      mul_le_mul_of_nonneg_left (hT.trans (add_le_add hmodel le_rfl)) (Real.exp_nonneg _)
    _ = _ := by rw [hpow]; field_simp

/--
info: 'RiemannResearch.Analysis.ActualZeroOrdinate.density_one_of_gaussian_liminf' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms density_one_of_gaussian_liminf

/--
info: 'RiemannResearch.Analysis.ActualZeroOrdinate.nearCollision_cubic_of_sine_gaussian_upper' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms nearCollision_cubic_of_sine_gaussian_upper

end RiemannResearch.Analysis.ActualZeroOrdinate
