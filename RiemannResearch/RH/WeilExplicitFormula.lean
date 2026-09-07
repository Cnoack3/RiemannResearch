import RiemannResearch.RH.WeilExplicitFormula.WeilEF.Main

/-!
# Unconditional compact Weil foundation

The imported proof is the Apache-2.0 development `anthropics/formal-math`,
`zeta23`, commit `fbdc36bbf17d20af3fd0447c6d1a8a02773c9844`.
Only import paths have been relocated. See `WeilExplicitFormula/NOTICE`,
`LICENSE.md`, and `PROVENANCE.md` for the exact scope and attribution.

`zetaZeroConfig.carrier` is exactly the subtype of zeros of Mathlib's
`riemannZeta` with real part strictly between zero and one. `zeroMult` is
`(analyticOrderAt riemannZeta ρ).toNat`, and its positivity/finiteness is
proved in the imported seam. The test transform `paperFT k z` is the
Lebesgue integral of `k u * exp (I * z * u)`; `gammaOf ρ = (ρ - 1/2)/I`.
-/

open Complex MeasureTheory

namespace RiemannResearch.RH.WeilExplicitFormula

noncomputable section

/-- The complete compact-test Weil identity, including absolute convergence,
all prime powers, both pole values, and the actual gamma factor. -/
theorem compact_explicit_formula (k : ℝ → ℂ)
    (hk : ContDiff ℝ 2 k) (hkc : HasCompactSupport k) :
    Summable (fun ρ : Zeta23.zetaZeroConfig.carrier =>
      (Zeta23.zeroMult ρ : ℂ) * Zeta23.paperFT k (Zeta23.gammaOf ρ)) ∧
    (∑' ρ : Zeta23.zetaZeroConfig.carrier,
      (Zeta23.zeroMult ρ : ℂ) * Zeta23.paperFT k (Zeta23.gammaOf ρ)) =
      Zeta23.paperFT k (I / 2) + Zeta23.paperFT k (-I / 2) -
      (∑' n : ℕ,
        ((ArithmeticFunction.vonMangoldt n / Real.sqrt n : ℝ) : ℂ) *
          (k (Real.log n) + k (-Real.log n))) +
      (1 / (2 * Real.pi) : ℂ) * ∫ r : ℝ, Zeta23.paperFT k r *
        (((Complex.digamma (1 / 4 + I * r / 2)).re - Real.log Real.pi : ℝ) : ℂ) :=
  Zeta23.WeilEF.EF_lit_zetaZeroConfig k hk hkc

/-- The unconditional zero-side majorant used in dominated extension
arguments; multiplicities are the actual orders of vanishing of ζ. -/
theorem reciprocal_square_zero_sum_summable :
    Summable (fun ρ : Zeta23.zetaZeroConfig.carrier =>
      (Zeta23.zeroMult ρ : ℝ) / (1 + Complex.normSq (Zeta23.gammaOf ρ))) :=
  Zeta23.WeilEF.zero_sum_inv_sq Zeta23.zetaSeam

/-- The local zero-count estimate already in the compact EF closure. -/
theorem unit_window_zero_count : ∃ A : ℝ, 1 ≤ A ∧ ∀ t : ℝ,
    (Zeta23.Ncount t (t + 1) : ℝ) ≤ A * Real.log (|t| + 3) :=
  Zeta23.RvM.zeta_local_zero_count

end
end RiemannResearch.RH.WeilExplicitFormula
