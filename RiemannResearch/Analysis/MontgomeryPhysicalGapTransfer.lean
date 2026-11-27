import RiemannResearch.Analysis.MontgomeryFejerCertificate

/-!
# The integer precision needed for global simplicity and RH

The forward atom counts all pairs of zero occurrences with the same ordinate.
We extend the fixed-height Fejér certificate to Mathlib's full Riemann
hypothesis together with analytic multiplicity one for every nontrivial zero,
including negative ordinates. The exact arithmetic threshold is two ordered
collisions in excess of the diagonal.

For the density-scale statement compare Goldston, Lee, Schettler and Suriajaya,
*Pair Correlation Conjecture for the zeros of the Riemann zeta-function I*,
§8, https://arxiv.org/abs/2503.15449.
-/

open Filter Zeta23
open scoped ComplexConjugate

namespace RiemannResearch.Analysis.MontgomeryFormFactor

open ActualZeroOrdinate ActualZeroCollisionCertificate

/-- Positive-height criticality and analytic simplicity determine both
properties for all strip zeros, by conjugation and nonvanishing on the
real interval between zero and one. -/
theorem all_cutoffs_critical_simple_iff_global :
    (∀ T : ℝ, ∀ ρ ∈ cutoff T, ρ.re = 1 / 2 ∧ zeroMult ρ = 1) ↔
    RiemannHypothesis ∧ ∀ ρ : ℂ, IsNontrivialZero ρ → zeroMult ρ = 1 := by
  constructor
  · intro hall
    have hglobal (ρ : ℂ) (hz : IsNontrivialZero ρ) :
        ρ.re = 1 / 2 ∧ zeroMult ρ = 1 := by
      rcases lt_trichotomy 0 ρ.im with hi | hi | hi
      · exact hall ρ.im ρ (mem_cutoff.mpr ⟨hz, hi, le_rfl⟩)
      · have he : ρ = (ρ.re : ℂ) := by apply Complex.ext <;> simp [hi.symm]
        exact False.elim (RH.riemannZeta_ofReal_ne_zero ρ.re hz.2.1 hz.2.2.ne
          ((congrArg riemannZeta he).symm.trans hz.1))
      · have hc : IsNontrivialZero (conj ρ) := by
          refine ⟨?_, hz.2.1, hz.2.2⟩
          rw [Zeta23.riemannZeta_conj hz.not_trivial.2, hz.1, map_zero]
        have hci : 0 < (conj ρ).im := by simpa only [Complex.conj_im] using neg_pos.mpr hi
        obtain ⟨hline, hmult⟩ := hall _ _ (mem_cutoff.mpr ⟨hc, hci, le_rfl⟩)
        exact ⟨by simpa only [Complex.conj_re] using hline,
          by simpa only [zeroMult, analyticOrderAt_zeta_conj hz.not_trivial.2] using hmult⟩
    exact ⟨RH.riemannHypothesis_iff_strip_zeros_on_line.mpr
      (fun ρ hz h0 h1 => (hglobal ρ ⟨hz, h0, h1⟩).1), fun ρ hz => (hglobal ρ hz).2⟩
  · rintro ⟨hRH, hs⟩ T ρ hρ
    have hz := (mem_cutoff.mp hρ).1
    exact ⟨RH_implies_on_line hRH hz, hs ρ hz⟩

/-- The first possible positive forward-atom excess is two, so a cofinal
strict inequality below two is equivalent to the global zero statement. -/
theorem frequently_collision_lt_count_add_two_iff_global :
    (∃ᶠ T : ℝ in atTop, actualCollision T < Ncount 0 T + 2) ↔
    RiemannHypothesis ∧ ∀ ρ : ℂ, IsNontrivialZero ρ → zeroMult ρ = 1 := by
  rw [← all_cutoffs_critical_simple_iff_global, frequently_atTop]
  constructor
  · intro h H ρ hρ
    obtain ⟨T, hHT, hsmall⟩ := h H
    have hsum := actualCollision_eq_count_add_excess T
    obtain ⟨k,hk⟩ := actualCollision_sub_count_even T
    have heq : actualCollision T = Ncount 0 T := by omega
    obtain ⟨hz, hpos, hheight⟩ := mem_cutoff.mp hρ
    exact (actualCollision_eq_count_iff T).mp heq ρ
      (mem_cutoff.mpr ⟨hz, hpos, hheight.trans hHT⟩)
  · intro h H
    exact ⟨H, le_rfl, by rw [(actualCollision_eq_count_iff H).mpr (h H)]; omega⟩

/-- An independent form-factor version of the criterion. The bandwidth can
depend on the height, and the normalization is the absolute occurrence count. -/
theorem cofinal_fejer_rh_and_simple_iff :
    (∀ H : ℝ, ∃ T R : ℝ, H ≤ T ∧ 1 < T ∧ 0 < R ∧
       (T * Real.log T / (2 * Real.pi)) * fejerFormFactor T R <
         (Ncount 0 T : ℝ) + 2) ↔
    RiemannHypothesis ∧ ∀ ρ : ℂ, IsNontrivialZero ρ → zeroMult ρ = 1 := by
  rw [← all_cutoffs_critical_simple_iff_global]
  constructor
  · intro h H ρ hρ
    obtain ⟨T,R,hHT,hT,hR,hsmall⟩ := h H
    obtain ⟨hz, hpos, hheight⟩ := mem_cutoff.mp hρ
    exact (fejer_finite_certificate_iff hT).mp ⟨R,hR,hsmall⟩ ρ
      (mem_cutoff.mpr ⟨hz, hpos, hheight.trans hHT⟩)
  · intro h H
    have hT : 1 < max H 2 := lt_of_lt_of_le (by norm_num) (le_max_right H 2)
    obtain ⟨R,hR,hsmall⟩ := (fejer_finite_certificate_iff hT).mpr (h _)
    exact ⟨max H 2, R, le_max_left _ _, hT, hR, hsmall⟩

/-- Even one exceptional zero forces an absolute excess of at least two at
every sufficiently high cutoff. -/
theorem eventually_two_le_collision_excess_of_global_failure
    (h : ¬ (RiemannHypothesis ∧ ∀ ρ : ℂ, IsNontrivialZero ρ → zeroMult ρ = 1)) :
    ∀ᶠ T : ℝ in atTop, Ncount 0 T + 2 ≤ actualCollision T := by
  have hbad := mt frequently_collision_lt_count_add_two_iff_global.mp h
  simpa only [Filter.not_frequently, not_lt] using hbad

end RiemannResearch.Analysis.MontgomeryFormFactor
