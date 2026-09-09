import RiemannResearch.Analysis.FiniteExponentialZeros
import RiemannResearch.RH.ArithmeticMellinResearchTargets

/-!
# Nonreal zeros of each fixed finite legal Mellin symbol

Source: user-provided argument, RH_CRT_Packet_Research_2026-09-09.md,
Section 9.2. The proof identifies the actual arithmetic symbol with a finite
exponential polynomial and uses proved phase recurrence and zero persistence.
It makes no claim that the actual Mellin integral has yet been identified
with the arithmetic-zeta product.
-/

namespace RiemannResearch.RH.Pareto
open scoped BigOperators
noncomputable section

/-- Every finite legal symbol has a nonreal zero in the functional continuity
half-plane, including the identically-zero symbol. -/
theorem arithmeticMellinSymbol_exists_nonreal_zero (c : ArithmeticCoefficients)
    (hc : ArithmeticCoefficientsLegal c) :
    ∃ s : ℂ, (1 / 2 : ℝ) < s.re ∧ s.im ≠ 0 ∧ arithmeticMellinSymbol c s = 0 := by
  classical
  let I := c.support
  let a : I ⊕ I → ℂ := Sum.elim (fun p => (c p : ℂ)) (fun p => -(c p : ℂ))
  let freq : I ⊕ I → ℝ := Sum.elim
    (fun p => -Real.log (p.1.2 : ℝ))
    (fun p => -(Real.log (p.1.2 : ℝ) + Real.log (p.1.1 : ℝ)))
  have hrepr (s : ℂ) : Analysis.finiteExponentialPolynomial a freq s =
      arithmeticMellinSymbol c s := by
    unfold Analysis.finiteExponentialPolynomial
    rw [Fintype.sum_sum_type]
    simp only [a, freq, Sum.elim_inl, Sum.elim_inr]
    rw [Finset.sum_coe_sort I (fun p : ℕ × ℕ =>
      (c p : ℂ) * Complex.exp (((-Real.log (p.2 : ℝ) : ℝ) : ℂ) * (s - 1))),
      Finset.sum_coe_sort I (fun p : ℕ × ℕ =>
        -(c p : ℂ) * Complex.exp
          (((-(Real.log (p.2 : ℝ) + Real.log (p.1 : ℝ)) : ℝ) : ℂ) * (s - 1))),
      ← Finset.sum_add_distrib]
    unfold arithmeticMellinSymbol
    apply Finset.sum_congr rfl
    intro p hp
    have hlegal := hc p hp
    have hm : (p.2 : ℂ) ≠ 0 := by exact_mod_cast hlegal.2.ne'
    have ha : (p.1 : ℂ) ≠ 0 := by
      rcases hlegal.1 with he | he <;> rw [he] <;> norm_num
    have hfirst : Complex.exp (((-Real.log (p.2 : ℝ) : ℝ) : ℂ) * (s - 1)) =
        (p.2 : ℂ) ^ (1 - s) := by
      rw [Complex.cpow_def_of_ne_zero hm, ← Complex.natCast_log]
      congr 1
      push_cast
      ring
    have hsecond : Complex.exp
        (((-(Real.log (p.2 : ℝ) + Real.log (p.1 : ℝ)) : ℝ) : ℂ) * (s - 1)) =
        (p.2 : ℂ) ^ (1 - s) * (p.1 : ℂ) ^ (1 - s) := by
      rw [Complex.cpow_def_of_ne_zero hm, Complex.cpow_def_of_ne_zero ha,
        ← Complex.natCast_log, ← Complex.natCast_log, ← Complex.exp_add]
      congr 1
      push_cast
      ring
    rw [hfirst, hsecond]
    ring
  have hone : Analysis.finiteExponentialPolynomial a freq 1 = 0 := by
    rw [hrepr]
    simp [arithmeticMellinSymbol]
  obtain ⟨s, hs, him, hz⟩ := Analysis.finiteExponentialPolynomial_nonreal_zero a freq hone
  exact ⟨s, hs, him, by rwa [hrepr] at hz⟩

end
end RiemannResearch.RH.Pareto
