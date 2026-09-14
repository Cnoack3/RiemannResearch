import RiemannResearch.RH.ArithmeticMellinIdentity
/-!
# Arithmetic Mellin identity throughout the positive half-plane

Source: the user-provided contracting-evolution research report, Section 8,
and CRT packet research, Section 9. This closes ArithmeticMellinIdentityTarget
on the full requested strip 0 < Re(s) < 1, including actual integrability.
The generator formula holds for Re(s) > 0 away from s = 1.
-/
namespace RiemannResearch.RH.Pareto
open MeasureTheory Set
open scoped BigOperators
noncomputable section
theorem arithmetic_generator_integrable_positive (a m : ℕ) (ha : 0 < a) (_hm : 0 < m)
    (s : ℂ) (hs : 0 < s.re) :
    IntegrableOn (fun x : ℝ => (dilation m (residue a) ⌊x⌋₊ : ℂ) *
      (x : ℂ) ^ (-s - 1)) (Ioi 1) := by
  have hmeas : Measurable (fun x : ℝ => (dilation m (residue a) ⌊x⌋₊ : ℂ) *
      (x : ℂ) ^ (-s - 1)) := by
    exact (Complex.continuous_ofReal.measurable.comp
      ((measurable_of_countable (dilation m (residue a))).comp Nat.measurable_floor)).mul
      (Complex.continuous_ofReal.measurable.pow_const (-s - 1))
  have hi := (integrableOn_Ioi_rpow_of_lt
    (by linarith : -s.re - 1 < -1) (by norm_num : (0 : ℝ) < 1)).const_mul
      ((m : ℝ) * (a : ℝ))
  apply hi.mono' hmeas.aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  have hx0 : 0 < x := lt_trans zero_lt_one hx
  have hb : |dilation m (residue a) ⌊x⌋₊| ≤ (m : ℝ) * (a : ℝ) := by
    unfold dilation
    rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg m)]
    exact mul_le_mul_of_nonneg_left (residue_abs_le a _ ha) (Nat.cast_nonneg m)
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    Complex.norm_cpow_eq_rpow_re_of_pos hx0]
  simp only [Complex.sub_re, Complex.neg_re, Complex.one_re]
  exact mul_le_mul_of_nonneg_right hb (Real.rpow_nonneg hx0.le _)
theorem arithmetic_generator_integral_positive (a m : ℕ) (ha : 0 < a) (hm : 0 < m)
    (s : ℂ) (hs : 0 < s.re) (hs1 : s ≠ 1) :
    (∫ x in Ioi (1 : ℝ), (dilation m (residue a) ⌊x⌋₊ : ℂ) *
      (x : ℂ) ^ (-s - 1)) =
      riemannZeta s / s * (m : ℂ) ^ (1 - s) * (1 - (a : ℂ) ^ (1 - s)) := by
  rw [← hilbertDilation_digit_one_sequence a m ha hm, ← paretoMellin_eq_step_integral,
    paretoMellin_dilation, paretoMellin_residue_zeta a ha s hs hs1]
  ring
theorem arithmeticMellinIdentityTarget_proved : ArithmeticMellinIdentityTarget := by
  intro c hc s hs hsupper
  have hs1 : s ≠ 1 := by intro h; simp [h] at hsupper
  have hpositive (p : ℕ × ℕ) (hp : p ∈ c.support) : 0 < p.1 ∧ 0 < p.2 := by
    obtain ⟨ha, hm⟩ := hc p hp
    refine ⟨?_, hm⟩
    rcases ha with ha | ha <;> omega
  have hi (p : ℕ × ℕ) (hp : p ∈ c.support) :
      IntegrableOn (fun x : ℝ => (c p : ℂ) *
        ((dilation p.2 (residue p.1) ⌊x⌋₊ : ℂ) * (x : ℂ) ^ (-s - 1))) (Ioi 1) :=
    (arithmetic_generator_integrable_positive p.1 p.2 (hpositive p hp).1
      (hpositive p hp).2 s hs).const_mul (c p : ℂ)
  have he : (fun x : ℝ => arithmeticStep c x * (x : ℂ) ^ (-s - 1)) =
      fun x : ℝ => ∑ p ∈ c.support, (c p : ℂ) *
        ((dilation p.2 (residue p.1) ⌊x⌋₊ : ℂ) * (x : ℂ) ^ (-s - 1)) := by
    funext x
    simp only [arithmeticStep, arithmeticCombination, Complex.ofReal_sum,
      Complex.ofReal_mul, Finset.sum_mul, mul_assoc]
  rw [he]
  refine ⟨integrable_finsetSum c.support hi, ?_⟩
  rw [integral_finsetSum c.support hi]
  unfold arithmeticMellinSymbol
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p hp
  rw [integral_const_mul,
    arithmetic_generator_integral_positive p.1 p.2 (hpositive p hp).1 (hpositive p hp).2 s hs hs1]
  ring
end
end RiemannResearch.RH.Pareto
