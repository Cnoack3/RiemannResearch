import RiemannResearch.RH.ParetoResidueMellinArithmetic
import RiemannResearch.RH.ParetoMellinHolomorphic
import Mathlib.Analysis.Analytic.Uniqueness

/-!
# Analytic continuation of the actual residue Mellin identity

Source: user-provided argument, RH_CRT_Packet_Research_2026-09-09.md, §9.
The actual integral and the existing entire conductor L-function agree on
Re(s)>1. Uniqueness extends their product identity to Re(s)>0, retaining the
removable point s=1 throughout the analytic continuation step.
-/

namespace RiemannResearch.RH.Pareto
open Set Filter
noncomputable section

private theorem positiveReHalfPlane_convex : Convex ℝ {s : ℂ | 0 < s.re} := by
  intro x hx y hy a b ha hb hab
  change 0 < (a • x + b • y).re
  simp only [Complex.add_re, Complex.real_smul, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  have hx' : 0 < x.re := hx
  have hy' : 0 < y.re := hy
  by_cases ha0 : a = 0
  · have hb1 : b = 1 := by linarith
    simpa [ha0, hb1] using hy'
  · have hapos : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
    exact add_pos_of_pos_of_nonneg (mul_pos hapos hx') (mul_nonneg hb hy'.le)

theorem paretoMellin_residue_conductor (a : ℕ) [NeZero a]
    (s : ℂ) (hs : 0 < s.re) :
    s * paretoMellin (digitHilbert a 1 (NeZero.pos a) (by omega)) s =
      (a : ℂ) * nymanConductorLFunction a s := by
  let v := digitHilbert a 1 (NeZero.pos a) (by omega)
  have hv : ∀ k, |hilbertSequence v k| ≤ (a : ℝ) := by
    intro k
    simpa [v, hilbertSequence_digitHilbert, digitSequence, residue] using
      residue_abs_le a k (NeZero.pos a)
  have hf : AnalyticOnNhd ℂ (fun z : ℂ => z * paretoMellin v z) {z | 0 < z.re} := by
    intro z hz
    apply Complex.analyticAt_iff_eventually_differentiableAt.mpr
    have he : ∀ᶠ t : ℂ in nhds z, 0 < t.re :=
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds hz
    filter_upwards [he] with t ht
    exact differentiableAt_id.mul (paretoMellin_differentiableAt_of_bounded v hv t ht)
  have hg : AnalyticOnNhd ℂ (fun z => (a : ℂ) * nymanConductorLFunction a z)
      {z : ℂ | 0 < z.re} := by
    intro z hz
    apply Complex.analyticAt_iff_eventually_differentiableAt.mpr
    exact Filter.Eventually.of_forall fun t =>
      (differentiable_nymanConductorLFunction a t).const_mul (a : ℂ)
  have he : (fun z : ℂ => z * paretoMellin v z) =ᶠ[nhds (2 : ℂ)]
      (fun z => (a : ℂ) * nymanConductorLFunction a z) := by
    have hh : ∀ᶠ z : ℂ in nhds (2 : ℂ), 1 < z.re :=
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num)
    filter_upwards [hh] with z hz
    exact paretoMellin_residue_arithmetic a z hz
  exact (hf.eqOn_of_preconnected_of_eventuallyEq hg positiveReHalfPlane_convex.isPreconnected
    (z₀ := (2 : ℂ)) (by norm_num) he).eq_of_mem hs

theorem paretoMellin_residue_zeta (a : ℕ) (ha : 0 < a)
    (s : ℂ) (hs : 0 < s.re) (hs1 : s ≠ 1) :
    paretoMellin (digitHilbert a 1 ha (by omega)) s =
      riemannZeta s / s * (1 - (a : ℂ) ^ (1 - s)) := by
  letI : NeZero a := ⟨ne_of_gt ha⟩
  have hi := paretoMellin_residue_conductor a s hs
  rw [nymanConductorLFunction_eq_conductorZeta,
    ZetaConductorRegularization.conductorZeta_of_ne_one a hs1,
    conductorSymbol_eq_cpow a ha s] at hi
  have ha0 : (a : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt ha
  have hs0 : s ≠ 0 := by intro h; simp [h] at hs
  have hp : (a : ℂ) ^ (1 - s) = (a : ℂ) * (a : ℂ) ^ (-s) := by
    rw [sub_eq_add_neg, Complex.cpow_add _ _ ha0, Complex.cpow_one]
  rw [hp]
  apply (mul_left_cancel₀ hs0)
  rw [hi]
  field_simp <;> ring

theorem paretoMellin_generator_zeta (a m : ℕ) (ha : 0 < a) (hm : 0 < m)
    (s : ℂ) (hs : (1 / 2 : ℝ) < s.re) (hs1 : s ≠ 1) :
    paretoMellin (hilbertDilation m hm (digitHilbert a 1 ha (by omega))) s =
      riemannZeta s / s * (m : ℂ) ^ (1 - s) * (1 - (a : ℂ) ^ (1 - s)) := by
  rw [paretoMellin_dilation, paretoMellin_residue_zeta a ha s (by linarith) hs1]
  ring

end
end RiemannResearch.RH.Pareto
