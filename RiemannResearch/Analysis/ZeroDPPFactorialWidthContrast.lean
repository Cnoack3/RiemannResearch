import RiemannResearch.Analysis.ZeroDPPWindowLattice
import RiemannResearch.Analysis.MontgomeryDyadicWidthCriterion

/-!
# Half-width tests of the second factorial moment of actual zero counts

The second factorial moment counts ordered pairs of distinct occurrence labels.
The normalized first moment supplies the exact correction between its sine error
and the triangle error. This accounts for multiplicities in the DPP reconstruction
and reduces the open pair-correlation input to a signed factorial-moment contrast.

For background on factorial moments see Daley and Vere-Jones, *An Introduction to
the Theory of Point Processes*, Vol. I, §5.4. The signed dyadic reduction uses
the repository's `MontgomeryDyadicWidthCriterion`.
-/

noncomputable section
open Filter MeasureTheory Set Zeta23
open scoped Topology
namespace RiemannResearch.Analysis.ZeroDPPCorrelation
open ActualZeroOrdinate ActualZeroWindowVariance OrdinateWindowVariance MontgomeryPositiveGap
open RiemannResearch.Probability.DPP.ZeroOrdinateInfinite

/-- The normalized second factorial moment of the multiplicity-weighted sampled windows. -/
def sampledFactorialWindowMoment (x : Site → Bool) (T r : ℝ) : ℝ :=
  let h := r / (Real.log T / (2 * Real.pi))
  (∫ t, sampledWindowCount x T h t * (sampledWindowCount x T h t - 1)) / T

theorem prime_sampledFactorialWindowMoment_eq_ae :
    ∀ᵐ x ∂limitingLaw primeFrequencies, ∀ T r : ℝ, sampledFactorialWindowMoment x T r =
      windowLatticeExcess T (r / (Real.log T / (2 * Real.pi))) 0 := by
  filter_upwards [prime_ordinate_statistics_ae] with x hx
  intro T r
  simp only [sampledFactorialWindowMoment, hx.2.1, windowLatticeExcess, Nat.cast_zero,
    mul_zero, zero_mul, zero_add, one_mul, add_zero, mul_sub, mul_one, sq]

private theorem eventually_triangle_eq_mean_add_windowLatticeExcess (B : ℝ) :
    ∀ᶠ T : ℝ in atTop, ∀ r ∈ Icc 0 B,
      unfoldedWindowEnergy T r = unfoldedWindowMean T r +
        windowLatticeExcess T (r / (Real.log T / (2 * Real.pi))) 0 := by
  filter_upwards [eventually_gt_atTop (1 : ℝ), eventually_unfolded_lattice_identity B,
    eventually_supported_width B] with T hT hI hs
  intro r hr
  obtain ⟨hw, hlow⟩ := hs r hr.1 hr.2
  have hTp := zero_lt_one.trans hT
  have he := actual_triangle_eq_mean_sq_add_variance T _ (unfoldedWindowMean T r) hTp
    hw hlow (by unfold unfoldedWindowMean; field_simp [hTp.ne'])
  change unfoldedWindowEnergy T r = unfoldedWindowMean T r ^ 2 + unfoldedWindowVariance T r at he
  rw [he, hI r hr.1 hr.2 0]
  push_cast
  ring

/-- Factorial-moment error at dyadic width scales, referred to the sine prediction
for ordered distinct occurrence labels. -/
def factorialWidthError (F : ℝ → ℝ → ℝ) (T a b : ℝ) (n : ℕ) : ℝ :=
  ∫ r in a..b, let s := (1/2 : ℝ) ^ n * r
    F T s - (sineWindowEnergy s - s)

/-- The translation average of the ordered distinct-label pair count. -/
def unfoldedFactorialWindowMoment (T r : ℝ) : ℝ :=
  windowLatticeExcess T (r / (Real.log T / (2 * Real.pi))) 0

/-- The signed width error differs from its triangle counterpart by an explicit
finite mean correction. The equality is uniform in the dyadic scale. -/
theorem eventually_dyadicTriangleWidthError_eq_factorial {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    ∀ᶠ T : ℝ in atTop, ∀ n : ℕ, dyadicTriangleWidthError T a b n =
      factorialWidthError unfoldedFactorialWindowMoment T a b n +
        (∫ r in a..b, (1/2 : ℝ)^n * r) * (unfoldedWindowMean T 1 - 1) := by
  filter_upwards [eventually_triangle_eq_mean_add_windowLatticeExcess b,
    eventually_gt_atTop (1 : ℝ)] with T hT ht n
  let scale := (1/2 : ℝ) ^ n
  have hpos : 0 ≤ scale := by positivity
  have hle : scale ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  let tri := fun r : ℝ => unfoldedWindowEnergy T (scale*r) - sineWindowEnergy (scale*r)
  let cor := fun r : ℝ => (scale*r) * (unfoldedWindowMean T 1 - 1)
  have hsc : Continuous (fun r : ℝ => scale * r) := continuous_const.mul continuous_id
  have htint : IntervalIntegrable tri volume a b :=
    ((unfoldedWindowEnergy_mono T ht).comp (fun _ _ h => mul_le_mul_of_nonneg_left h hpos)).intervalIntegrable.sub
      ((continuous_sineWindowEnergy.comp hsc).intervalIntegrable a b)
  have hcint : IntervalIntegrable cor volume a b :=
    (hsc.mul continuous_const).intervalIntegrable a b
  have hfact : factorialWidthError unfoldedFactorialWindowMoment T a b n =
      ∫ r in a..b, tri r - cor r := by
    apply intervalIntegral.integral_congr
    intro r hr
    rw [uIcc_of_le hab] at hr
    have hr0 := ha.trans hr.1
    have hs : scale * r ∈ Icc 0 b :=
      ⟨mul_nonneg hpos hr0, (mul_le_of_le_one_left hr0 hle).trans hr.2⟩
    have hmean : unfoldedWindowMean T (scale*r) = (scale*r) * unfoldedWindowMean T 1 := by
      unfold unfoldedWindowMean
      ring
    dsimp only [tri, cor]
    rw [hT _ hs, hmean]
    unfold unfoldedFactorialWindowMoment
    dsimp only [scale]
    ring
  rw [hfact, intervalIntegral.integral_sub htint hcint]
  have he : (∫ r in a..b, cor r) =
      (∫ r in a..b, scale*r) * (unfoldedWindowMean T 1 - 1) :=
    intervalIntegral.integral_mul_const _ _
  change (∫ r in a..b, tri r) = _
  rw [he]
  ring

/-- A single arithmetic input for the actual factorial window statistic.
Distinct occurrences at the same ordinate remain in the pair count. -/
def FactorialHalfWidthContrasts (F : ℝ → ℝ → ℝ) : Prop :=
  ∀ a b : ℚ, 0 < a → a < b → Tendsto (fun T : ℝ =>
    factorialWidthError F T a b 0 - factorialWidthError F T a b 1) atTop (𝓝 0)

theorem positiveGapPCC_of_factorialHalfWidthContrasts
    (h : FactorialHalfWidthContrasts unfoldedFactorialWindowMoment) : PositiveGapPCC := by
  apply positiveGapPCC_of_rationalHalfWidthContrasts
  intro a b ha hab
  have ha' : (0 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha.le
  have hab' : (a : ℝ) ≤ (b : ℝ) := by exact_mod_cast hab.le
  let c := fun n : ℕ => ∫ r in (a : ℝ)..(b : ℝ), (1/2 : ℝ)^n * r
  have hm : Tendsto (fun T : ℝ => unfoldedWindowMean T 1 - 1) atTop (𝓝 0) := by
    simpa using (unfoldedWindowMean_tendsto 1).sub_const 1
  have hh := (h a b ha hab).add (hm.const_mul (c 0 - c 1))
  simp only [mul_zero, add_zero] at hh
  apply hh.congr'
  filter_upwards [eventually_dyadicTriangleWidthError_eq_factorial ha' hab'] with T hT
  rw [hT 0, hT 1]
  dsimp [c]
  ring

/-- The prime DPP reconstructs these tests on one common event of full measure. -/
theorem factorialHalfWidthContrasts_iff_prime_sampled :
    FactorialHalfWidthContrasts unfoldedFactorialWindowMoment ↔
      ∀ᵐ x ∂limitingLaw primeFrequencies, FactorialHalfWidthContrasts (sampledFactorialWindowMoment x) := by
  have he := prime_sampledFactorialWindowMoment_eq_ae
  constructor
  · intro h
    filter_upwards [he] with x hx
    have hfun : sampledFactorialWindowMoment x = unfoldedFactorialWindowMoment := funext fun T => funext (hx T)
    rwa [hfun]
  · intro h
    obtain ⟨x, hx, hx'⟩ := (he.and h).exists
    have hfun : sampledFactorialWindowMoment x = unfoldedFactorialWindowMoment := funext fun T => funext (hx T)
    rwa [hfun] at hx'
end RiemannResearch.Analysis.ZeroDPPCorrelation
