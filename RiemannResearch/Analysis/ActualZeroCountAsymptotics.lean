/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.ActualZeroOrdinate
import RiemannResearch.RH.WeilExplicitFormula.Assembly
import RiemannResearch.RH.WeilExplicitFormula.GammaFacts.Complete
import RiemannResearch.RH.WeilExplicitFormula.RvM.Statement
import RiemannResearch.RH.WeilExplicitFormula.RvM.NcountWindow

/-!
# Actual zeta-zero count normalization

The already proved actual Riemann-von Mangoldt theorem
`Zeta23.RvM.riemannVonMangoldt Zeta23.gammaFacts` supplies the dyadic lower
bound. Passing from (T/2,T] to (0,T] gives the explicit eventual
`T * log T / (16*pi)` normalization and positivity.
All zeros retain their actual analytic multiplicities. No Landau, density,
or Riemann-Hypothesis premise is used.
-/

open Filter Zeta23

namespace RiemannResearch.Analysis.ActualZeroOrdinate

theorem eventually_count_ge_log :
    ∀ᶠ T : ℝ in atTop, (1 / (16 * Real.pi)) * T * Real.log T ≤
      (Ncount 0 T : ℝ) := by
  have hd := Assembly.eventually_N_ge zetaZeroConfig
    (RvM.riemannVonMangoldt gammaFacts)
  have hh : ∀ᶠ T : ℝ in atTop,
      (T / 2) * l (T / 2) / (4 * Real.pi) ≤ (Ncount (T / 2) T : ℝ) := by
    have hc := (tendsto_id.atTop_div_const (by norm_num : (0 : ℝ) < 2)).eventually hd
    filter_upwards [hc] with T hT
    simpa only [id_eq, zetaZeroConfig_N, show 2 * (T / 2) = T by ring] using hT
  filter_upwards [hh, eventually_gt_atTop (0 : ℝ),
    Real.tendsto_log_atTop.eventually_ge_atTop
      (2 * (Real.log 2 + Real.log (2 * Real.pi)))] with T hN hT hL
  have he := Assembly.log_eq_l_add (T := T / 2) (by positivity)
  rw [Real.log_div (ne_of_gt hT) (by norm_num : (2 : ℝ) ≠ 0)] at he
  have hhalf : Real.log T / 2 ≤ l (T / 2) := by linarith
  have hm : (Ncount (T / 2) T : ℝ) ≤ (Ncount 0 T : ℝ) := by
    exact_mod_cast Ncount_mono (a := T / 2) (b := T) (c := 0) (d := T)
      (by linarith) le_rfl
  calc
    _ = T * (Real.log T / 2) / (8 * Real.pi) := by field_simp; ring
    _ ≤ T * l (T / 2) / (8 * Real.pi) :=
      div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hhalf hT.le) (by positivity)
    _ = (T / 2) * l (T / 2) / (4 * Real.pi) := by field_simp; ring
    _ ≤ _ := hN
    _ ≤ _ := hm

theorem exists_count_normalization :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ T : ℝ in atTop,
      c * T * Real.log T ≤ (Ncount 0 T : ℝ) := by
  exact ⟨1 / (16 * Real.pi), by positivity, eventually_count_ge_log⟩

 theorem eventually_count_pos : ∀ᶠ T : ℝ in Filter.atTop, 0 < Ncount 0 T := by
  filter_upwards [eventually_count_ge_log, Filter.eventually_gt_atTop (1 : ℝ)] with T hN hT
  have hlog : 0 < Real.log T := Real.log_pos hT
  have hp : (0 : ℝ) < (Ncount 0 T : ℝ) := lt_of_lt_of_le (by positivity) hN
  exact_mod_cast hp

end RiemannResearch.Analysis.ActualZeroOrdinate
