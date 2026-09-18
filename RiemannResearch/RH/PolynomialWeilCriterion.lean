import RiemannResearch.RH.FixedWidthWeilDiscrepancy
import RiemannResearch.RH.RiemannHypothesisStrip

/-!
# Conditional polynomial-loss criteria for the actual fixed-width discrepancy

Source: user-provided layer-cake continuation, sections 36--38.
This is a CONDITIONAL research reduction. `FixedWidthLandauDetection h`
is an unresolved formalization obligation (the fixed-width Laplace identity,
noncancellation of zero poles, and Landau's nonnegative-Laplace lemma).
`TwoHatWeilIdentity h` is a separate unresolved analytic identification.
Neither proposition has a provider in this addition. Polynomial lower bounds
are also hypotheses, and their uniform arithmetic proof remains the RH target.
The conclusion is Mathlib's actual RiemannHypothesis, using proved reflection.
-/

namespace RiemannResearch.RH.FixedWidthWeilDiscrepancy

/-- A one-sided polynomial bound excludes every right-half-strip zero,
conditional on the stated actual-discrepancy detection provider. -/
theorem riemannHypothesis_of_discrepancy_polynomial_upper
    (h : ℝ) (hdetect : FixedWidthLandauDetection h)
    (C : ℝ) (hC : 0 ≤ C) (A : ℕ) (R : ℝ)
    (hupper : ∀ x, R ≤ x → hatPrimeDiscrepancy h x ≤ C * (1 + x) ^ A) :
    RiemannHypothesis := by
  have hright (ρ : ℂ) (hz : riemannZeta ρ = 0)
      (h0 : 0 < ρ.re) (h1 : ρ.re < 1) : ρ.re ≤ 1 / 2 := by
    by_contra hn
    obtain ⟨x, _, hxR, hx⟩ := hdetect ρ hz (lt_of_not_ge hn) h1 C hC A R
    exact (not_lt_of_ge (hupper x hxR)) hx
  apply riemannHypothesis_iff_strip_zeros_on_line.mpr
  intro ρ hz h0 h1
  have hb := hright ρ hz h0 h1
  have hr := Zeta23.zeta_reflect_zero ρ ⟨hz, h0, h1⟩
  have hb' := hright (Zeta23.reflect ρ) hr.1 hr.2.1 hr.2.2
  simp only [Zeta23.reflect, Complex.sub_re, Complex.one_re, Complex.conj_re] at hb'
  linarith

/-- The full signed two-hat identity turns polynomial semiboundedness into
the preceding one-sided upper bound. The nonnegative remainder is discarded
only after its sign has been proved from its actual integral definition. -/
theorem riemannHypothesis_of_twoHat_polynomial_lower
    (h : ℝ) (hidentity : TwoHatWeilIdentity h)
    (hdetect : FixedWidthLandauDetection h)
    (C : ℝ) (hC : 0 ≤ C) (A : ℕ) (R : ℝ)
    (hlower : ∀ x, R ≤ x →
      -(C * (1 + x) ^ A) ≤ completedWeilForm (twoHatTest h x)) :
    RiemannHypothesis := by
  let q := completedWeilForm (hatTest h)
  apply riemannHypothesis_of_discrepancy_polynomial_upper h hdetect
    (|q| + C) (add_nonneg (abs_nonneg _) hC) A (max R (max 0 (2 * h + 1)))
  intro x hx
  have hxR : R ≤ x := (le_max_left _ _).trans hx
  have hx0 : 0 ≤ x := (le_max_left 0 (2 * h + 1)).trans
    ((le_max_right R _).trans hx)
  have hxh : 2 * h < x := by
    have hhx : 2 * h + 1 ≤ x := (le_max_right 0 _).trans
      ((le_max_right R _).trans hx)
    linarith
  have hp : 1 ≤ (1 + x) ^ A := one_le_pow₀ (by linarith)
  have hp0 : 0 ≤ (1 + x) ^ A := by positivity
  have hq : q ≤ |q| := le_abs_self _
  have hqmul : |q| ≤ |q| * (1 + x) ^ A := by
    nlinarith [mul_nonneg (abs_nonneg q) (sub_nonneg.mpr hp)]
  have hc := mul_nonneg hC hp0
  have hj := archimedeanHatRemainder_nonneg h x
  have hl := hlower x hxR
  rw [hidentity x hxh] at hl
  change -(C * (1 + x) ^ A) ≤
    2 * q - 2 * hatPrimeDiscrepancy h x - 2 * archimedeanHatRemainder h x at hl
  nlinarith

/-- Any reference energy bounded on the two-hat family can be used in the
polynomial criterion. Its actual boundedness is an explicit premise here. -/
theorem riemannHypothesis_of_twoHat_energy_polynomial_lower
    (h : ℝ) (hidentity : TwoHatWeilIdentity h)
    (hdetect : FixedWidthLandauDetection h)
    (D : (ℝ → ℂ) → ℝ) (B C : ℝ) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (A : ℕ) (R : ℝ)
    (henergy : ∀ x, R ≤ x → D (twoHatTest h x) ≤ B)
    (hlower : ∀ x, R ≤ x → -(C * (1 + x) ^ A) * D (twoHatTest h x) ≤
      completedWeilForm (twoHatTest h x)) : RiemannHypothesis := by
  apply riemannHypothesis_of_twoHat_polynomial_lower h hidentity hdetect
    (C * B) (mul_nonneg hC hB) A (max R 0)
  intro x hx
  have hxR : R ≤ x := (le_max_left _ _).trans hx
  have hx0 : 0 ≤ x := (le_max_right _ _).trans hx
  have hp : 0 ≤ C * (1 + x) ^ A := by positivity
  have hm := mul_le_mul_of_nonneg_left (henergy x hxR) hp
  have hl := hlower x hxR
  nlinarith

end RiemannResearch.RH.FixedWidthWeilDiscrepancy
