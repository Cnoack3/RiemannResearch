import RiemannResearch.Analysis.MontgomeryPrimeProbeEnergy
import RiemannResearch.Analysis.OrdinateTriangularIntegral

/-! # Testing the first arithmetic atom with a translated squared sinc

The arithmetic measure is the one in `primeFourierProbe`.  The test below
is nonnegative, takes the value one at the first atom, and has continuum
mass at most the reciprocal bandwidth.
-/

noncomputable section
namespace RiemannResearch.Analysis.MontgomeryPrimeTrace
open MeasureTheory Set MontgomeryPositiveGap
open scoped BigOperators

/-- A translated band-limited test with value one at its centre. -/
def primeProbeAtomTest (q a v : ℝ) : ℝ :=
  Real.sinc (Real.pi * (q * v - q * a)) ^ 2

/-- Frequency representation in the convention of the arithmetic probe. -/
theorem primeProbeAtomTest_eq_triangle {q : ℝ} (hq : 0 < q) (a v : ℝ) :
    primeProbeAtomTest q a v =
      (1 / q) * ∫ u in (-q)..q, (1 - |u| / q) * Real.cos ((2 * Real.pi * (v - a)) * u) := by
  rw [OrdinateCollisionCertificate.triangular_cos_transform hq]
  unfold primeProbeAtomTest OrdinateCollisionCertificate.sincSquared
  rw [show q * (2 * Real.pi * (v - a)) / 2 = Real.pi * (q * v - q * a) by ring]

theorem continuum_primeProbeAtomTest_le {q a : ℝ} (hq : 0 < q) (ha : a ∈ Icc (0 : ℝ) 1) :
    (∫ v in (0 : ℝ)..1, primeProbeAtomTest q a v) ≤ 1 / q := by
  let f : ℝ → ℝ := fun x => Real.sinc (Real.pi * x) ^ 2
  have hc : Continuous f := by dsimp [f]; fun_prop
  have half {x : ℝ} (hx : 0 ≤ x) : (∫ t in (0 : ℝ)..x, f t) ≤ 1/2 := by
    change (∫ t in (0 : ℝ)..x, Real.sinc (Real.pi * t) ^ 2) ≤ _
    rw [primeSineHoleMass_eq]
    linarith only [sineGapMass_lower hx]
  have ev (x : ℝ) : f (-x) = f x := by simp [f]
  have reflect (x : ℝ) : (∫ t in -x..0, f t) = ∫ t in (0 : ℝ)..x, f t := by
    simpa only [ev, neg_zero] using
      (intervalIntegral.integral_comp_neg (a := (0 : ℝ)) (b := x) f).symm
  have hright : 0 ≤ q - q * a := by nlinarith only [mul_nonneg hq.le (sub_nonneg.mpr ha.2)]
  have hl := half (mul_nonneg hq.le ha.1)
  have hr := half hright
  have hmass : (∫ t in -(q*a)..q-q*a, f t) ≤ 1 := by
    rw [← intervalIntegral.integral_add_adjacent_intervals
      (hc.intervalIntegrable (-(q*a)) 0) (hc.intervalIntegrable 0 (q-q*a)), reflect]
    linarith only [hl, hr]
  change (∫ v in (0 : ℝ)..1, f (q * v - q * a)) ≤ 1 / q
  rw [intervalIntegral.integral_comp_mul_sub f hq.ne' (q*a)]
  simp only [mul_zero, zero_sub, mul_one, smul_eq_mul, one_div]
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hmass (inv_nonneg.mpr hq.le)

/-- A first-atom lower bound for the physical-space Fejér test. -/
theorem primeProbeAtomTest_discrepancy_ge {T q : ℝ} (hT : 2 ≤ T) (hq : 0 < q) :
    let a := Real.log 2 / Real.log T
    Real.log 2 / 2 / Real.log T - 1 / q ≤
      (∑ n ∈ Finset.Ioc 0 ⌊T⌋₊, (ArithmeticFunction.vonMangoldt n / (n : ℝ) / Real.log T) *
        primeProbeAtomTest q a (Real.log n / Real.log T)) -
      ∫ v in (0 : ℝ)..1, primeProbeAtomTest q a v := by
  let a := Real.log 2 / Real.log T
  have hlog : 0 < Real.log T := Real.log_pos (by linarith)
  have ha : a ∈ Icc (0 : ℝ) 1 := by
    refine ⟨div_nonneg (Real.log_nonneg (by norm_num)) hlog.le, (div_le_iff₀ hlog).2 ?_⟩
    rw [one_mul]
    exact Real.log_le_log (by norm_num) hT
  have hn : (2 : ℕ) ∈ Finset.Ioc 0 ⌊T⌋₊ :=
    Finset.mem_Ioc.mpr ⟨by decide, Nat.le_floor (by simpa using hT)⟩
  let term (n : ℕ) : ℝ := (ArithmeticFunction.vonMangoldt n / (n : ℝ) / Real.log T) *
    primeProbeAtomTest q a (Real.log n / Real.log T)
  have hterm (n : ℕ) : 0 ≤ term n := mul_nonneg
    (div_nonneg (div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Nat.cast_nonneg n))
      hlog.le) (sq_nonneg _)
  have hsum := Finset.single_le_sum (f := term) (fun n _ => hterm n) hn
  have htwo : term 2 = Real.log 2 / 2 / Real.log T := by
    simp [term, a, primeProbeAtomTest, ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two]
  rw [htwo] at hsum
  exact sub_le_sub hsum (continuum_primeProbeAtomTest_le hq ha)

end RiemannResearch.Analysis.MontgomeryPrimeTrace
