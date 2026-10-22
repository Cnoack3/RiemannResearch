import RiemannResearch.RH.FiniteSeedMellinObstruction

/-!
# Explicit error floor for one integer remainder seed

Source: RH_Minimal_Seeds_Canonical_Basis_and_Arithmetic_Charge_20260914.md,
Section 6, equation (6.6). All positive integer dilations are admitted.
-/

namespace RiemannResearch.RH.Pareto
open ArithmeticConductorCommonZeros
noncomputable section

def integerSeedExtraZero (a : ℕ) : ℂ :=
  1 + ((2 * Real.pi / Real.log a : ℝ) : ℂ) * Complex.I

@[simp] theorem integerSeedExtraZero_re (a : ℕ) :
    (integerSeedExtraZero a).re = 1 := by
  simp only [integerSeedExtraZero, Complex.add_re, Complex.mul_re,
    Complex.one_re, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
    Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero]

@[simp] theorem integerSeedExtraZero_im (a : ℕ) :
    (integerSeedExtraZero a).im = 2 * Real.pi / Real.log a := by
  simp only [integerSeedExtraZero, Complex.add_im, Complex.mul_im,
    Complex.one_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re,
    Complex.I_im, mul_one, zero_mul, add_zero, zero_add]

theorem integerSeedExtraZero_ne_one (a : ℕ) (ha : 1 < a) :
    integerSeedExtraZero a ≠ 1 := by
  have hp : 0 < 2 * Real.pi / Real.log a :=
    div_pos Real.two_pi_pos (Real.log_pos (by exact_mod_cast ha))
  intro h
  have he := congrArg Complex.im h
  simp only [integerSeedExtraZero_im, Complex.one_im] at he
  linarith

theorem integerSeedExtraZero_conductor (a : ℕ) (ha : 1 < a) :
    conductorSymbol a (integerSeedExtraZero a) = 0 := by
  have he := conductorSymbol_explicit_zero a ha 1
  norm_num only [Int.cast_one] at he
  have heq : 1 + (1 : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) /
      (Real.log a : ℂ) = integerSeedExtraZero a := by
    unfold integerSeedExtraZero
    push_cast
    ring
  rwa [heq] at he

theorem integerSeedExtraZero_mellin (a : ℕ) (ha : 1 < a) :
    paretoMellin (digitHilbert a 1 (by omega) (by omega)) (integerSeedExtraZero a) = 0 := by
  have ha0 : 0 < a := by omega
  have haC : (a : ℂ) ≠ 0 := by exact_mod_cast ha0.ne'
  have hc := integerSeedExtraZero_conductor a ha
  rw [conductorSymbol_eq_cpow a ha0] at hc
  have hp : (a : ℂ) ^ (1 - integerSeedExtraZero a) = 1 := by
    rw [sub_eq_add_neg, Complex.cpow_add _ _ haC, Complex.cpow_one]
    rw [← sub_eq_zero.mp hc]
    field_simp
  rw [paretoMellin_residue_zeta a ha0 _ (by simp) (integerSeedExtraZero_ne_one a ha),
    hp, sub_self, mul_zero]

/-- The pure seed has a uniform, explicit positive squared-distance floor. -/
theorem integerSeed_explicit_distance_gap (a : ℕ) (ha : 1 < a)
    {f : ThresholdHilbert}
    (hf : f ∈ singleSeedDilationClosure (digitHilbert a 1 (by omega) (by omega))) :
    1 / (1 + (2 * Real.pi / Real.log a)^2) ≤ ‖hilbertOne - f‖^2 := by
  have hb := singleSeedClosure_distance_sq_lower_bound
    (digitHilbert a 1 (by omega) (by omega)) (integerSeedExtraZero a)
    (by norm_num only [integerSeedExtraZero_re]) (integerSeedExtraZero_mellin a ha) hf
  have hn : ‖integerSeedExtraZero a‖^2 = 1 + (2 * Real.pi / Real.log a)^2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply,
      integerSeedExtraZero_re, integerSeedExtraZero_im]
    ring
  simpa only [integerSeedExtraZero_re, hn, mul_one, show (2 : ℝ) - 1 = 1 by norm_num] using hb

end
end RiemannResearch.RH.Pareto
