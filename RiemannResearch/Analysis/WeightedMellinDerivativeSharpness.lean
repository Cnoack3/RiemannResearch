import RiemannResearch.Analysis.WeightedMellinLogarithmicKernel

/-!
# Sharp higher derivative evaluation constants

Prepared as a mathematical source continuation for coordinator checking.
Current checking evidence and remaining obligations are recorded in
`RiemannResearch/ANNULAR_FORMALIZATION_20261010.md`.
This historical preparation note is not a current verification claim.

The extremizer is an actual raw function in the weighted space, not a
formal kernel symbol. It proves optimality of the coefficient for every
derivative order and every point in the energy half-plane. This generic
extremizer is unrelated to an assertion about the arithmetic vector's
membership; no arithmetic bound or RH hypothesis is supplied.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped ComplexConjugate

namespace MeasureTheory.WeightedMellin

def derivativeExtremizer (s : ℝ) (z : ℂ) (k : ℕ) (x : ℝ) : ℂ :=
  (x : ℂ) ^ ((s : ℂ) - conj z) * (-(Real.log x : ℂ)) ^ k

theorem derivativeExtremizer_energy_integrand (s : ℝ) (z : ℂ) (k : ℕ)
    {x : ℝ} (hx : 1 < x) :
    ‖derivativeExtremizer s z k x‖ ^ 2 * x ^ (-s - 1) =
      (Real.log x) ^ (2 * k) * x ^ (-(2 * z.re - s) - 1) := by
  have hx0 : 0 < x := zero_lt_one.trans hx
  rw [derivativeExtremizer, norm_mul, mul_pow,
    Complex.norm_cpow_eq_rpow_re_of_pos hx0, norm_pow, norm_neg,
    Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.log_nonneg hx.le)]
  simp only [Complex.sub_re, Complex.ofReal_re, Complex.conj_re]
  rw [← Real.rpow_mul_natCast hx0.le, ← pow_mul,
    Nat.mul_comm k 2]
  calc
    _ = (Real.log x) ^ (2 * k) *
        (x ^ ((s - z.re) * 2) * x ^ (-s - 1)) := by ring
    _ = _ := by
      rw [← Real.rpow_add hx0]
      congr 2
      ring

theorem derivativeExtremizer_finiteEnergy (s : ℝ) (z : ℂ) (k : ℕ)
    (hz : s / 2 < z.re) : FiniteEnergy (derivativeExtremizer s z k) s := by
  refine ⟨?_, ?_⟩
  · exact (Complex.continuous_ofReal.measurable.pow_const _).mul
      ((Complex.continuous_ofReal.measurable.comp Real.measurable_log).neg.pow_const k)
  · apply (log_moment_integrable (2 * k)
      (by linarith : 0 < 2 * z.re - s)).congr
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    exact (derivativeExtremizer_energy_integrand s z k hx).symm

theorem derivativeExtremizer_energy (s : ℝ) (z : ℂ) (k : ℕ)
    (hz : s / 2 < z.re) :
    energy (derivativeExtremizer s z k) s =
      ((2 * k).factorial : ℝ) / (2 * z.re - s) ^ (2 * k + 1) := by
  unfold energy
  calc
    _ = ∫ x in Ioi (1 : ℝ),
        (Real.log x) ^ (2 * k) * x ^ (-(2 * z.re - s) - 1) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x hx
      exact derivativeExtremizer_energy_integrand s z k hx
    _ = _ := log_moment_integral (2 * k) (by linarith)

theorem derivativeExtremizer_transform_integrand (s : ℝ) (z : ℂ) (k : ℕ)
    {x : ℝ} (hx : 1 < x) :
    derivativeExtremizer s z k x * (x : ℂ) ^ (-z - 1) *
        (-(Real.log x : ℂ)) ^ k =
      (((Real.log x) ^ (2 * k) * x ^ (-(2 * z.re - s) - 1) : ℝ) : ℂ) := by
  have hx0 : 0 < x := zero_lt_one.trans hx
  have hxc : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hx0.ne'
  have he : ((s : ℂ) - conj z) + (-z - 1) =
      ((-(2 * z.re - s) - 1 : ℝ) : ℂ) := by
    apply Complex.ext <;> simp <;> ring
  have hp : (-(Real.log x : ℂ)) ^ k * (-(Real.log x : ℂ)) ^ k =
      ((Real.log x) ^ (2 * k) : ℝ) := by
    rw [← pow_add, ← two_mul k, pow_mul, neg_sq, ← pow_mul]
    norm_cast
  unfold derivativeExtremizer
  calc
    _ = ((x : ℂ) ^ ((s : ℂ) - conj z) * (x : ℂ) ^ (-z - 1)) *
        ((-(Real.log x : ℂ)) ^ k * (-(Real.log x : ℂ)) ^ k) := by ring
    _ = _ := by
      rw [← Complex.cpow_add _ _ hxc, he, hp, ← Complex.ofReal_cpow hx0.le]
      norm_cast
      ring

theorem derivativeExtremizer_iteratedDeriv (s : ℝ) (z : ℂ) (k : ℕ)
    (hz : s / 2 < z.re) :
    iteratedDeriv k (transform (derivativeExtremizer s z k)) z =
      (((2 * k).factorial : ℝ) / (2 * z.re - s) ^ (2 * k + 1) : ℝ) := by
  rw [iteratedDeriv_transform_eq_logarithmicTransform
    (derivativeExtremizer_finiteEnergy s z k hz) k hz]
  unfold logarithmicTransform
  calc
    _ = ∫ x in Ioi (1 : ℝ),
        (((Real.log x) ^ (2 * k) * x ^ (-(2 * z.re - s) - 1) : ℝ) : ℂ) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x hx
      exact derivativeExtremizer_transform_integrand s z k hx
    _ = _ := by
      have he :
          (∫ x in Ioi (1 : ℝ),
            (((Real.log x) ^ (2 * k) * x ^ (-(2 * z.re - s) - 1) : ℝ) : ℂ)) =
          ((∫ x in Ioi (1 : ℝ),
            (Real.log x) ^ (2 * k) * x ^ (-(2 * z.re - s) - 1) : ℝ) : ℂ) := by
        exact integral_ofReal
      rw [he, log_moment_integral (2 * k) (by linarith)]

/-- No smaller coefficient can bound all genuine finite-energy vectors. -/
theorem iteratedDeriv_transform_coefficient_optimal {s : ℝ} {z : ℂ}
    (hz : s / 2 < z.re) (k : ℕ) {C : ℝ}
    (hC : ∀ f : ℝ → ℂ, FiniteEnergy f s →
      ‖iteratedDeriv k (transform f) z‖ ^ 2 ≤ C * energy f s) :
    ((2 * k).factorial : ℝ) / (2 * z.re - s) ^ (2 * k + 1) ≤ C := by
  have h := hC (derivativeExtremizer s z k)
    (derivativeExtremizer_finiteEnergy s z k hz)
  rw [derivativeExtremizer_iteratedDeriv s z k hz,
    derivativeExtremizer_energy s z k hz] at h
  simp only [Complex.norm_real, Real.norm_eq_abs, sq_abs] at h
  rw [pow_two] at h
  have hK : 0 < ((2 * k).factorial : ℝ) / (2 * z.re - s) ^ (2 * k + 1) := by
    apply div_pos
    · exact_mod_cast Nat.factorial_pos (2 * k)
    · exact pow_pos (by linarith) _
  exact (mul_le_mul_iff_left₀ hK).mp h

end MeasureTheory.WeightedMellin
