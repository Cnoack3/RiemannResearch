import RiemannResearch.RH.NymanPeriodicLFunction
import RiemannResearch.RH.ZetaConductorRegularization
import Mathlib.Analysis.Analytic.Uniqueness

/- Source argument: user-provided
RH_Nyman_Weil_Null_Channels_and_Exact_Prime_Compensation_2026-09-07.md,
sections 2–10. The formal statements below specify their exact scope. -/

/-!
# Identification of the actual periodic arithmetic continuation

Source: user-provided argument, equation (4.2) of the Nyman--Weil note.
The equality first follows by an absolutely convergent arithmetic series on
`Re s > 1`; the actual entire providers and the identity theorem extend it to
every complex point, including the removable value at one. No continuation
identity is assumed.
-/

noncomputable section

open Complex Filter
open scoped Topology

namespace RiemannResearch.RH

open ArithmeticConductorCommonZeros ZetaConductorRegularization

theorem conductorSymbol_eq_cpow (n : ℕ) (hn : 0 < n) (s : ℂ) :
    conductorSymbol n s = 1 / (n : ℂ) - (n : ℂ) ^ (-s) := by
  have hnC : (n : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hn
  rw [Complex.cpow_def_of_ne_zero hnC, ← Complex.natCast_log, one_div]
  unfold conductorSymbol
  congr 2
  ring

/-- Both entire constructions represent the same actual arithmetic series. -/
theorem nymanConductorLFunction_eq_conductorZeta (n : ℕ) [NeZero n] :
    nymanConductorLFunction n = conductorZeta n := by
  have hf : AnalyticOnNhd ℂ (nymanConductorLFunction n) Set.univ := by
    intro s _
    apply Complex.analyticAt_iff_eventually_differentiableAt.mpr
    exact Filter.Eventually.of_forall fun t => differentiable_nymanConductorLFunction n t
  have hg : AnalyticOnNhd ℂ (conductorZeta n) Set.univ :=
    fun s _ => analyticAt_conductorZeta n (NeZero.pos n) s
  apply hf.eq_of_eventuallyEq hg (z₀ := (2 : ℂ))
  have hhalf : ∀ᶠ s : ℂ in 𝓝 (2 : ℂ), 1 < s.re :=
    (isOpen_lt continuous_const Complex.continuous_re).mem_nhds (by norm_num)
  filter_upwards [hhalf] with s hs
  have hs1 : s ≠ 1 := by
    intro h
    simp [h] at hs
  rw [nymanConductorLFunction_eq_zeta_cpow n hs,
    conductorZeta_of_ne_one n hs1, conductorSymbol_eq_cpow n (NeZero.pos n) s]

/-- The periodic arithmetic continuation has the computed removable value. -/
@[simp] theorem nymanConductorLFunction_one (n : ℕ) [NeZero n] :
    nymanConductorLFunction n 1 = (Real.log n : ℂ) / n := by
  rw [nymanConductorLFunction_eq_conductorZeta, conductorZeta_one]

/-- All actual zeta-zero multiplicities are preserved by either conductor
throughout the open critical strip. -/
theorem analyticOrderAt_nymanConductorLFunction (n : ℕ) [NeZero n]
    (hn : 1 < n) (s : ℂ) (hs : s.re ≠ 1) :
    analyticOrderAt (nymanConductorLFunction n) s = analyticOrderAt riemannZeta s := by
  rw [nymanConductorLFunction_eq_conductorZeta]
  exact analyticOrderAt_conductorZeta_of_re_ne_one n hn s hs

/-- The pair of actual entire periodic arithmetic functions has exactly the
zeta zeros, with the polar point removed explicitly. -/
theorem nymanConductorLFunction_two_three_common_zero_iff (s : ℂ) :
    (nymanConductorLFunction 2 s = 0 ∧ nymanConductorLFunction 3 s = 0) ↔
      s ≠ 1 ∧ riemannZeta s = 0 := by
  rw [nymanConductorLFunction_eq_conductorZeta,
    nymanConductorLFunction_eq_conductorZeta,
    conductorZeta_two_three_common_zero_iff]

end RiemannResearch.RH
