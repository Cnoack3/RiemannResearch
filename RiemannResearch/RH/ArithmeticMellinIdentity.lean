import RiemannResearch.RH.ParetoResidueMellinContinuation
import RiemannResearch.RH.ArithmeticMellinResearchTargets

/-!
# Actual Mellin identity for every finite legal two-seed combination

Source: user-provided argument, RH_CRT_Packet_Research_2026-09-09.md, §9,
equations (45)–(46). The physical Hilbert sequence and every finite coefficient
are retained. Integrability and the arithmetic identity are proved providers.
-/

open scoped BigOperators
namespace RiemannResearch.RH.Pareto
open MeasureTheory Set
noncomputable section

theorem paretoMellin_step_integrable (f : ThresholdHilbert) (s : ℂ)
    (hs : (1 / 2 : ℝ) < s.re) :
    IntegrableOn (fun x : ℝ => (hilbertSequence f ⌊x⌋₊ : ℂ) *
      (x : ℂ) ^ (-s - 1)) (Ioi 1) := by
  apply (paretoMellin_integrable f s hs).congr
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  have hx0 : (x : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr
    (ne_of_gt (lt_trans zero_lt_one hx))
  rw [Complex.cpow_sub (-s) 1 hx0, Complex.cpow_one]
  unfold mellinWeightedStep paretoMellinKernel
  ring

theorem arithmetic_generator_integrable (a m : ℕ) (ha : 0 < a) (hm : 0 < m)
    (s : ℂ) (hs : (1 / 2 : ℝ) < s.re) :
    IntegrableOn (fun x : ℝ => (dilation m (residue a) ⌊x⌋₊ : ℂ) *
      (x : ℂ) ^ (-s - 1)) (Ioi 1) := by
  simpa only [hilbertDilation_digit_one_sequence] using
    paretoMellin_step_integrable
      (hilbertDilation m hm (digitHilbert a 1 ha (by omega))) s hs

theorem arithmetic_generator_integral (a m : ℕ) (ha : 0 < a) (hm : 0 < m)
    (s : ℂ) (hs : (1 / 2 : ℝ) < s.re) (hs1 : s ≠ 1) :
    (∫ x in Ioi (1 : ℝ), (dilation m (residue a) ⌊x⌋₊ : ℂ) *
      (x : ℂ) ^ (-s - 1)) =
      riemannZeta s / s * (m : ℂ) ^ (1 - s) * (1 - (a : ℂ) ^ (1 - s)) := by
  have he := paretoMellin_generator_zeta a m ha hm s hs hs1
  rwa [paretoMellin_eq_step_integral, hilbertDilation_digit_one_sequence] at he

/-- Equation (46) for the actual infinite integral of every legal finite seed. -/
theorem arithmeticMellin_identity (c : ArithmeticCoefficients)
    (hc : ArithmeticCoefficientsLegal c) (ψ : ThresholdHilbert)
    (hψ : hilbertSequence ψ = arithmeticCombination c)
    (s : ℂ) (hs : (1 / 2 : ℝ) < s.re) (hs1 : s ≠ 1) :
    paretoMellin ψ s = riemannZeta s / s * arithmeticMellinSymbol c s := by
  have hpositive (p : ℕ × ℕ) (hp : p ∈ c.support) : 0 < p.1 ∧ 0 < p.2 := by
    obtain ⟨ha, hm⟩ := hc p hp
    refine ⟨?_, hm⟩
    rcases ha with ha | ha <;> omega
  have hi (p : ℕ × ℕ) (hp : p ∈ c.support) :
      IntegrableOn (fun x : ℝ => (c p : ℂ) *
        ((dilation p.2 (residue p.1) ⌊x⌋₊ : ℂ) * (x : ℂ) ^ (-s - 1))) (Ioi 1) :=
    (arithmetic_generator_integrable p.1 p.2 (hpositive p hp).1
      (hpositive p hp).2 s hs).const_mul (c p : ℂ)
  rw [paretoMellin_eq_step_integral]
  calc
    _ = ∫ x in Ioi (1 : ℝ), ∑ p ∈ c.support, (c p : ℂ) *
        ((dilation p.2 (residue p.1) ⌊x⌋₊ : ℂ) * (x : ℂ) ^ (-s - 1)) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x hx
      rw [hψ]
      simp only [arithmeticCombination, Complex.ofReal_sum, Complex.ofReal_mul,
        Finset.sum_mul, mul_assoc]
    _ = ∑ p ∈ c.support, ∫ x in Ioi (1 : ℝ), (c p : ℂ) *
        ((dilation p.2 (residue p.1) ⌊x⌋₊ : ℂ) * (x : ℂ) ^ (-s - 1)) :=
      integral_finset_sum c.support hi
    _ = _ := by
      unfold arithmeticMellinSymbol
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p hp
      rw [integral_const_mul,
        arithmetic_generator_integral p.1 p.2 (hpositive p hp).1 (hpositive p hp).2 s hs hs1]
      ring

end
end RiemannResearch.RH.Pareto
