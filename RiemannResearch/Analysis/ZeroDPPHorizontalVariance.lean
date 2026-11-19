import RiemannResearch.Probability.ZeroOrdinateDPPSampling
import RiemannResearch.Probability.DeterminantalFiberMarks
import RiemannResearch.Analysis.ActualZeroInghamHorizontalEnergy
import RiemannResearch.RH.HorizontalEnergyCriterion
import Mathlib.Probability.Moments.Variance
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Horizontal displacement as variance under the zero-label DPP

Every dictionary gives positive inclusion probabilities and a kernel that is
constant on ordinate fibres. Horizontal reflection centres the displacements
on each fibre. Inverse-square-root inclusion weighting realizes the actual
horizontal energy, with analytic multiplicity, as a variance. For the full
logarithmic dictionary this weight is the square root of the fibre size.

The DPP moment formula follows the discrete correlation identities of Lyons,
https://doi.org/10.1007/s10240-003-0016-0. The unconditional height estimate
uses the repository's Ingham bound based on Chourasiya and Simonič,
https://arxiv.org/abs/2507.15184, Theorem 1.
-/

noncomputable section
open Filter MeasureTheory Zeta23
open scoped BigOperators Topology
namespace RiemannResearch.Analysis.ZeroDPPHorizontal
open ActualZeroOrdinate ActualZeroCollisionCertificate
open RiemannResearch.Probability.DPP RiemannResearch.Probability.DPP.ZeroOrdinateInfinite

/-- Reflection cancels the signed first moment separately at each ordinate. -/
theorem weighted_horizontal_first_moment (T : ℝ) (g : ℝ → ℝ) :
    (∑ c : Copies T, g (copyOrdinate T c) * (c.1.1.re - 1 / 2)) = 0 := by
  let f := fun ρ : ℂ => g ρ.im * (ρ.re - 1 / 2)
  have h := sum_reflect T (fun ρ => (f ρ : ℂ))
  have he (ρ : ℂ) : f (reflect ρ) = -f ρ := by
    simp only [f, reflect_im, reflect_re]
    ring
  simp_rw [he, Complex.ofReal_neg] at h
  simp only [sum_eq_copies, Finset.sum_neg_distrib] at h
  have hsum : (∑ c : Copies T, (f c.1.1 : ℂ)) = 0 := by
    linear_combination -(1 / 2 : ℂ) * h
  have hh := congrArg Complex.re hsum
  simpa only [Complex.re_sum, Complex.ofReal_re, Complex.zero_re, f, copyOrdinate] using hh

private noncomputable def ordinateKernelAt (q : ℕ → ℝ) (s t : ℝ) : ℝ := by
  classical
  exact if hs : ∃ i : Site, ordinate i = s then
    if ht : ∃ j : Site, ordinate j = t then limitingKernel q hs.choose ht.choose else 0 else 0

private theorem sampledKernel_factors (q : ℕ → ℝ) (T : ℝ) (c d : Copies T) :
    limitingKernel q (liftCopy T c) (liftCopy T d) =
      ordinateKernelAt q (copyOrdinate T c) (copyOrdinate T d) := by
  classical
  have h (a : Copies T) : ∃ i : Site, ordinate i = copyOrdinate T a := ⟨liftCopy T a, rfl⟩
  simp only [ordinateKernelAt, dif_pos (h c), dif_pos (h d)]
  have hc : ordinate (liftCopy T c) = ordinate (h c).choose := (h c).choose_spec.symm
  have hd : ordinate (liftCopy T d) = ordinate (h d).choose := (h d).choose_spec.symm
  simp only [limitingKernel, kernelOfSpace, ProjectionDPP.kernel, collision_projection_eq q hc,
    collision_projection_eq q hd]

/-- Centre marks by reflection, with an arbitrary additional real ordinate test. -/
theorem horizontalMark_fiberCentered (T : ℝ) (f : ℝ → ℝ) :
    FiberCentered (copyOrdinate T) (fun c => f (copyOrdinate T c) * (c.1.1.re - 1 / 2)) := by
  intro u
  simpa only [← mul_assoc] using
    weighted_horizontal_first_moment T (fun t => u t * f t)

/-- Signed horizontal displacement, weighted by the inverse square root
of the actual inclusion probability of each label. -/
def horizontalStatistic (q : ℕ → ℝ) (T : ℝ) (f : ℝ → ℝ) : (Site → Bool) → ℝ :=
  normalizedMark (fun x : Site → Bool => {j | x j = true}) (limitingKernel q) (liftCopy T)
    (fun c => f (copyOrdinate T c) * (c.1.1.re - 1 / 2))

/-- On the full logarithmic dictionary the coefficient is explicit. -/
theorem logarithmic_horizontalStatistic (T : ℝ) (f : ℝ → ℝ) :
    horizontalStatistic (fun k => Real.log ((k : ℝ) + 1)) T f =
      linearStatistic (fun x : Site → Bool => {j | x j = true}) (liftCopy T)
        (fun c => Real.sqrt (actualOrdinateMultiplicity T (copyOrdinate T c)) *
          f (copyOrdinate T c) * (c.1.1.re - 1 / 2)) := by
  unfold horizontalStatistic normalizedMark
  congr 1
  funext c
  rw [logarithmic_limitingKernel, if_pos rfl, ordinateFiber_card_liftCopy, Real.sqrt_inv,
    div_eq_mul_inv, inv_inv]
  ring

theorem expected_horizontalStatistic (q : ℕ → ℝ) (T : ℝ) (f : ℝ → ℝ) :
    (∫ x, horizontalStatistic q T f x ∂limitingLaw q) = 0 :=
  (limitingLaw_isDPP q).expected_normalizedMark (liftCopy T) (copyOrdinate T)
    (ordinateKernelAt q) (sampledKernel_factors q T) _ (horizontalMark_fiberCentered T f)

/-- The product moment is the actual horizontal energy against both ordinate
weights, independently of which Fourier frequencies select the labels. -/
theorem horizontalStatistic_product_moment (q : ℕ → ℝ) (T : ℝ) (f g : ℝ → ℝ) :
    (∫ x, horizontalStatistic q T f x * horizontalStatistic q T g x ∂limitingLaw q) =
      ∑ c : Copies T, f (copyOrdinate T c) * g (copyOrdinate T c) * (c.1.1.re - 1 / 2) ^ 2 := by
  unfold horizontalStatistic
  rw [(limitingLaw_isDPP q).normalizedMark_product_moment (liftCopy T) (copyOrdinate T)
    (ordinateKernelAt q) (sampledKernel_factors q T)
    (fun c => limitingKernel_diagonal_pos q (liftCopy T c))
    (fun c => f (copyOrdinate T c) * (c.1.1.re - 1 / 2))
    (fun c => g (copyOrdinate T c) * (c.1.1.re - 1 / 2)) (horizontalMark_fiberCentered T g)]
  apply Finset.sum_congr rfl
  intro c _
  ring

/-- The sum of the cosine and sine cross-moments is the Fourier cosine
transform of the actual horizontal-energy measure at the difference frequency. -/
theorem horizontal_fourier_cross_moment (q : ℕ → ℝ) (T a b : ℝ) :
    (∫ x, horizontalStatistic q T (fun t => Real.cos (a * t)) x *
      horizontalStatistic q T (fun t => Real.cos (b * t)) x ∂limitingLaw q) +
    (∫ x, horizontalStatistic q T (fun t => Real.sin (a * t)) x *
      horizontalStatistic q T (fun t => Real.sin (b * t)) x ∂limitingLaw q) =
      ∑ c : Copies T, Real.cos ((a - b) * copyOrdinate T c) * (c.1.1.re - 1 / 2) ^ 2 := by
  rw [horizontalStatistic_product_moment, horizontalStatistic_product_moment,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro c _
  rw [sub_mul, Real.cos_sub]
  ring

/-- The actual horizontal energy is a DPP variance for every dictionary. -/
theorem variance_horizontalStatistic (q : ℕ → ℝ) (T : ℝ) :
    ProbabilityTheory.variance (horizontalStatistic q T (fun _ => 1)) (limitingLaw q) =
      horizontalEnergy T := by
  let f := fun _ : ℝ => (1 : ℝ)
  have hL : MemLp (horizontalStatistic q T f) 2 (limitingLaw q) :=
    (limitingLaw_isDPP q).linearStatistic_memLp (liftCopy T) _
  rw [ProbabilityTheory.variance_eq_sub hL]
  change (∫ x, (horizontalStatistic q T f x) ^ 2 ∂limitingLaw q) -
    (∫ x, horizontalStatistic q T f x ∂limitingLaw q) ^ 2 = horizontalEnergy T
  rw [expected_horizontalStatistic, zero_pow (by decide), sub_zero]
  simpa only [pow_two, f, one_mul, horizontalEnergy, realSum_eq_copies] using
    horizontalStatistic_product_moment q T f f

/-- The unconditional Ingham height estimate holds simultaneously over all
dictionaries, including dictionaries chosen separately at each height. -/
theorem eventually_variance_le_ingham {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ T : ℝ in atTop, ∀ q : ℕ → ℝ,
      ProbabilityTheory.variance (horizontalStatistic q T (fun _ => 1))
        (limitingLaw q) / (T * horizontalLogRate T) ≤ 9 / (8 * Real.pi) + ε := by
  filter_upwards [eventually_horizontalEnergy_ratio_le_ingham hε] with T ht q
  simpa only [variance_horizontalStatistic] using ht

/-- Cofinal smallness of the absolute variance is equivalent to RH even
when a different frequency dictionary is used at every height. -/
theorem riemannHypothesis_iff_cofinal_variance_small (q : ℝ → ℕ → ℝ) :
    RiemannHypothesis ↔ ∀ ε : ℝ, 0 < ε → ∀ B : ℝ, ∃ T : ℝ, B ≤ T ∧
      ProbabilityTheory.variance (horizontalStatistic (q T) T (fun _ => 1))
        (limitingLaw (q T)) < ε := by
  simpa only [variance_horizontalStatistic] using RH.riemannHypothesis_iff_cofinal_horizontalEnergy_small

/-- Variance for an arbitrary ordinate window or real Fourier weight. -/
theorem variance_horizontalStatistic_weighted (q : ℕ → ℝ) (T : ℝ) (f : ℝ → ℝ) :
    ProbabilityTheory.variance (horizontalStatistic q T f) (limitingLaw q) =
      ∑ c : Copies T, f (copyOrdinate T c) ^ 2 * (c.1.1.re - 1 / 2) ^ 2 := by
  have hL : MemLp (horizontalStatistic q T f) 2 (limitingLaw q) :=
    (limitingLaw_isDPP q).linearStatistic_memLp (liftCopy T) _
  rw [ProbabilityTheory.variance_eq_sub hL]
  change (∫ x, (horizontalStatistic q T f x) ^ 2 ∂limitingLaw q) -
    (∫ x, horizontalStatistic q T f x ∂limitingLaw q) ^ 2 = _
  rw [expected_horizontalStatistic, zero_pow (by decide), sub_zero]
  simpa only [pow_two] using horizontalStatistic_product_moment q T f f

/-- A bounded signed ordinate weight can only reduce the unweighted variance. -/
theorem variance_horizontalStatistic_le (q : ℕ → ℝ) (T : ℝ) (f : ℝ → ℝ)
    (hf : ∀ t, |f t| ≤ 1) :
    ProbabilityTheory.variance (horizontalStatistic q T f) (limitingLaw q) ≤ horizontalEnergy T := by
  rw [variance_horizontalStatistic_weighted, horizontalEnergy, realSum_eq_copies]
  apply Finset.sum_le_sum
  intro c _
  have hh := abs_le.mp (hf (copyOrdinate T c))
  have hs : f (copyOrdinate T c) ^ 2 ≤ 1 := by
    nlinarith only [mul_nonneg (sub_nonneg.mpr hh.2) (show 0 ≤ 1 + f (copyOrdinate T c) by linarith)]
  simpa only [one_mul] using mul_le_mul_of_nonneg_right hs (sq_nonneg (c.1.1.re - 1 / 2))

/-- The unconditional upper tail at the square-root height scale is uniform
over dictionaries and over all bounded ordinate tests. -/
theorem eventually_horizontalStatistic_tail {δ ε : ℝ} (hδ : 0 < δ) (hε : 0 < ε) :
    ∀ᶠ T : ℝ in atTop, ∀ (q : ℕ → ℝ) (f : ℝ → ℝ), (∀ t, |f t| ≤ 1) →
      (limitingLaw q).real {x | δ * Real.sqrt T ≤ |horizontalStatistic q T f x|} ≤
        (9 / (8 * Real.pi) + ε) * horizontalLogRate T / δ ^ 2 := by
  filter_upwards [eventually_horizontalEnergy_ratio_le_ingham hε, eventually_gt_atTop (1 : ℝ),
    Real.tendsto_log_atTop.eventually_gt_atTop (1 : ℝ)] with T ht hT hL q f hf
  have hT₀ : 0 < T := zero_lt_one.trans hT
  have hR : 0 < horizontalLogRate T := div_pos (sq_pos_of_pos (Real.log_pos hL)) (zero_lt_one.trans hL)
  have hS : MemLp (horizontalStatistic q T f) 2 (limitingLaw q) :=
    (limitingLaw_isDPP q).linearStatistic_memLp (liftCopy T) _
  have hcheb := ProbabilityTheory.meas_ge_le_variance_div_sq hS (mul_pos hδ (Real.sqrt_pos.mpr hT₀))
  rw [expected_horizontalStatistic] at hcheb
  simp only [sub_zero] at hcheb
  have hreal := (ENNReal.toReal_mono ENNReal.ofReal_ne_top hcheb)
  rw [ENNReal.toReal_ofReal (div_nonneg (ProbabilityTheory.variance_nonneg _ _) (sq_nonneg _)),
    mul_pow, Real.sq_sqrt hT₀.le] at hreal
  apply hreal.trans
  have hV := variance_horizontalStatistic_le q T f hf
  have hE := (div_le_iff₀ (mul_pos hT₀ hR)).mp ht
  apply (div_le_iff₀ (mul_pos (sq_pos_of_pos hδ) hT₀)).mpr
  calc
    _ ≤ (9 / (8 * Real.pi) + ε) * (T * horizontalLogRate T) := hV.trans hE
    _ = _ := by field_simp [hδ.ne']

/-- In probability at scale sqrt(T), for simultaneous moving frequencies
and moving bounded weights. Each height may carry its own law. -/
theorem moving_horizontalStatistic_tail_tendsto_zero (q : ℝ → ℕ → ℝ) (f : ℝ → ℝ → ℝ)
    (hf : ∀ T t, |f T t| ≤ 1) {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun T : ℝ => (limitingLaw (q T)).real
      {x | δ * Real.sqrt T ≤ |horizontalStatistic (q T) T (f T) x|}) atTop (𝓝 0) := by
  have hu := (horizontalLogRate_tendsto_zero.const_mul (9 / (8 * Real.pi) + 1)).div_const (δ ^ 2)
  simp only [mul_zero, zero_div] at hu
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hu
    (Filter.Eventually.of_forall (fun _ => ENNReal.toReal_nonneg))
    ((eventually_horizontalStatistic_tail hδ zero_lt_one).mono fun T ht => ht (q T) (f T) (hf T))

end RiemannResearch.Analysis.ZeroDPPHorizontal
