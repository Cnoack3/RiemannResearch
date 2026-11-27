import RiemannResearch.Analysis.MontgomeryPrimeProbeSineKernel
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-! # A resonant Rayleigh witness for the finite atomic prime kernel

The raw finite kernel on Fourier coordinates is a positive Gram matrix on
every tuple. On a growing interval its quadratic form on a single unit
character has quotient at least the weight of the matching atom times the
interval length. This gives a direct obstruction to contraction on the line.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace RiemannResearch.Analysis.MontgomeryPrimeTrace

/-- The interval quadratic form paired with the unnormalized resonant
character at prime-power index m. This character has squared norm B. -/
def primeProbeRayleigh (T B : ℝ) (m : ℕ) : ℝ :=
  let χ (x : ℝ) := Complex.exp (((2*Real.pi*x : ℝ) : ℂ)*Complex.I*((Real.log m/Real.log T : ℝ):ℂ))
  (∫ x in (0:ℝ)..B, ∫ y in (0:ℝ)..B,
      star (χ x) * primeProbeKernel T x y * χ y).re

private theorem continuous_probe_feature (T : ℝ) (n : ℕ) :
    Continuous (fun x => primeProbeFeature T x n) := by
  unfold primeProbeFeature
  fun_prop

/-- Exact sum of squared overlaps against all finite prime features. -/
theorem primeProbeRayleigh_eq {T B : ℝ} (hT : 1 < T) (hB : 0 ≤ B) (m : ℕ) :
    let χ (x : ℝ) := Complex.exp (((2*Real.pi*x : ℝ) : ℂ)*Complex.I*((Real.log m/Real.log T : ℝ):ℂ))
    primeProbeRayleigh T B m = ∑ n ∈ Finset.Ioc 0 ⌊T⌋₊,
      Complex.normSq (∫ x in (0:ℝ)..B, star (χ x)*primeProbeFeature T x n) := by
  let χ (x : ℝ) := Complex.exp (((2*Real.pi*x : ℝ) : ℂ)*Complex.I*((Real.log m/Real.log T : ℝ):ℂ))
  let A (n : ℕ) (x : ℝ) := star (χ x)*primeProbeFeature T x n
  let s := Finset.Ioc 0 ⌊T⌋₊
  have hc (n : ℕ) : Continuous (A n) := by
    have hχ : Continuous χ := by dsimp [χ]; fun_prop
    exact hχ.star.mul (continuous_probe_feature T n)
  have he (x y : ℝ) : star (χ x) * primeProbeKernel T x y * χ y =
      ∑ n ∈ s, A n x * star (A n y) := by
    rw [primeProbeKernel_eq_feature_sum hT, Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro n _
    dsimp only [A]
    rw [star_mul, star_star]
    ring
  have hconj (n : ℕ) : (∫ y in (0:ℝ)..B, star (A n y)) = star (∫ y in (0:ℝ)..B, A n y) := by
    rw [intervalIntegral.integral_of_le hB, intervalIntegral.integral_of_le hB]
    exact integral_conj
  have hinner (x : ℝ) : (∫ y in (0:ℝ)..B, star (χ x)*primeProbeKernel T x y * χ y) =
      ∑ n ∈ s, A n x * star (∫ y in (0:ℝ)..B, A n y) := by
    simp_rw [he]
    rw [intervalIntegral.integral_finsetSum (fun n _ =>
      ((hc n).star.const_mul (A n x)).intervalIntegrable _ _)]
    simp_rw [intervalIntegral.integral_const_mul, hconj]
  change (∫ x in (0:ℝ)..B, ∫ y in (0:ℝ)..B, star (χ x)*primeProbeKernel T x y*χ y).re =
    ∑ n ∈ s, Complex.normSq (∫ x in (0:ℝ)..B, A n x)
  simp_rw [hinner]
  rw [intervalIntegral.integral_finsetSum (fun n _ =>
    ((hc n).mul_const _).intervalIntegrable _ _), Complex.re_sum]
  apply Finset.sum_congr rfl
  intro n _
  rw [intervalIntegral.integral_mul_const, Complex.star_def, Complex.mul_conj, Complex.ofReal_re]

/-- A positive prime atom of mass w gives an interval Rayleigh quotient at
least wB. The test is the character at that very same log-frequency atom. -/
theorem primeProbeRayleigh_lower {T B : ℝ} (hT : 1 < T) (hB : 0 < B) {m : ℕ}
    (hm : m ∈ Finset.Ioc 0 ⌊T⌋₊) :
    (ArithmeticFunction.vonMangoldt m/(m:ℝ)/Real.log T) * B ≤ primeProbeRayleigh T B m / B := by
  let w := ArithmeticFunction.vonMangoldt m/(m:ℝ)/Real.log T
  let χ (x : ℝ) := Complex.exp (((2*Real.pi*x : ℝ) : ℂ)*Complex.I*((Real.log m/Real.log T : ℝ):ℂ))
  have hw : 0 ≤ w := div_nonneg (div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Nat.cast_nonneg _)) (Real.log_pos hT).le
  have hone (x : ℝ) : star (χ x)*primeProbeFeature T x m = (Real.sqrt w : ℂ) := by
    change star (χ x) * ((Real.sqrt w : ℂ) * χ x) = _
    rw [mul_left_comm, Complex.star_def, ← Complex.normSq_eq_conj_mul_self]
    have hnorm : ‖χ x‖ = 1 := by
      dsimp only [χ]
      rw [show (((2*Real.pi*x : ℝ) : ℂ)*Complex.I*((Real.log m/Real.log T : ℝ):ℂ)) =
        (((2*Real.pi*x*(Real.log m/Real.log T) : ℝ) : ℂ)*Complex.I) by push_cast; ring]
      exact Complex.norm_exp_ofReal_mul_I _
    simp [Complex.normSq_eq_norm_sq, hnorm]
  have hrow : Complex.normSq (∫ x in (0:ℝ)..B, star (χ x)*primeProbeFeature T x m) =
      w*B*B := by
    simp_rw [hone]
    rw [intervalIntegral.integral_const]
    simp only [sub_zero, Complex.real_smul, ← Complex.ofReal_mul, Complex.normSq_ofReal]
    calc
      _ = B^2 * (Real.sqrt w)^2 := by ring
      _ = _ := by rw [Real.sq_sqrt hw]; ring
  apply (le_div_iff₀ hB).2
  rw [primeProbeRayleigh_eq hT hB.le]
  change w*B*B ≤ ∑ n ∈ Finset.Ioc 0 ⌊T⌋₊, Complex.normSq (∫ x in (0:ℝ)..B, star (χ x)*primeProbeFeature T x n)
  rw [← hrow]
  exact Finset.single_le_sum (f := fun n => Complex.normSq (∫ x in (0:ℝ)..B, star (χ x)*primeProbeFeature T x n))
    (fun n _ => Complex.normSq_nonneg _) hm

theorem one_lt_primeProbeRayleigh_ratio {T B : ℝ} (hT : 1 < T) (hB : 0 < B) {m : ℕ}
    (hm : m ∈ Finset.Ioc 0 ⌊T⌋₊)
    (hwide : 1 < (ArithmeticFunction.vonMangoldt m/(m:ℝ)/Real.log T)*B) :
    1 < primeProbeRayleigh T B m/B :=
  hwide.trans_le (primeProbeRayleigh_lower hT hB hm)

/-- Every positive finite atom violates a contraction bound on some explicit
bounded interval. Taking B=2/w gives Rayleigh quotient at least two. -/
theorem exists_primeProbeRayleigh_exceeds_one {T : ℝ} (hT : 1 < T) {m : ℕ}
    (hm : m ∈ Finset.Ioc 0 ⌊T⌋₊) (hw : 0 < ArithmeticFunction.vonMangoldt m/(m:ℝ)/Real.log T) :
    ∃ B : ℝ, 0 < B ∧ 1 < primeProbeRayleigh T B m / B := by
  let w := ArithmeticFunction.vonMangoldt m/(m:ℝ)/Real.log T
  have hp : 0 < 2/w := div_pos (by norm_num) hw
  refine ⟨2/w, hp, one_lt_primeProbeRayleigh_ratio hT hp hm ?_⟩
  change 1 < w * (2/w)
  rw [show w * (2/w) = 2 by field_simp [show w ≠ 0 from hw.ne']]
  norm_num

end RiemannResearch.Analysis.MontgomeryPrimeTrace
