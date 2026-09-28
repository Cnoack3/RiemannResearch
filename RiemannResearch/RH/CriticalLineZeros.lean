import RiemannResearch.RH.WeilExplicitFormula.FinalMult

/-!
# Critical-line zeros from the imported zero-proportion theorem

Source: Alpöge–Furman, arXiv:2608.13637, and the pinned anthropics/formal-math
Zeta23 proof development. The imported theorems support the simple-zero
proportion and Riemann–von Mangoldt growth; this module extracts actual zeros.
No zero-existence premise or Riemann hypothesis is used.
-/

open Filter
open scoped Topology

namespace RiemannResearch.RH

/-- The number of distinct simple critical-line zeros in (T,2T] tends to infinity. -/
theorem simpleCriticalZeroCount_dyadic_tendsto_atTop :
    Tendsto (fun T : ℝ => (Zeta23.N0simple T (2 * T) : ℝ)) atTop atTop := by
  obtain ⟨T₀, hT₀⟩ := Zeta23.thmB₀_mult (1 / 3) (by norm_num)
  have hN : Tendsto (fun T : ℝ => (Zeta23.Ncount T (2 * T) : ℝ)) atTop atTop := by
    simpa [Zeta23.zetaZeroConfig] using
      (Zeta23.Assembly.tendsto_N_atTop Zeta23.zetaZeroConfig Zeta23.riemannVonMangoldt_zeta)
  have hthird := hN.const_mul_atTop (by norm_num : (0 : ℝ) < 1 / 3)
  apply tendsto_atTop_mono' _ ?_ hthird
  filter_upwards [eventually_ge_atTop T₀] with T hT
  have h := hT₀ T hT
  linarith

/-- Every sufficiently high dyadic window contains a simple critical-line zero. -/
theorem eventually_exists_simple_critical_zero_dyadic :
    ∀ᶠ T : ℝ in atTop, ∃ ρ : ℂ, riemannZeta ρ = 0 ∧ ρ.re = 1 / 2 ∧
      T < ρ.im ∧ ρ.im ≤ 2 * T ∧ Zeta23.zeroMult ρ = 1 := by
  filter_upwards [simpleCriticalZeroCount_dyadic_tendsto_atTop.eventually_gt_atTop 0] with T hT
  have hn : 0 < Zeta23.N0simple T (2 * T) := by exact_mod_cast hT
  obtain ⟨ρ, hρ⟩ := (Set.ncard_pos (Set.finite_of_ncard_pos hn)).mp hn
  exact ⟨ρ, hρ.1.1.1.1, hρ.1.2, hρ.1.1.2.1, hρ.1.1.2.2, hρ.2⟩

/-- Simple critical-line zeros occur above every prescribed height. -/
theorem exists_simple_critical_zero_above (H : ℝ) :
    ∃ ρ : ℂ, riemannZeta ρ = 0 ∧ ρ.re = 1 / 2 ∧ H < ρ.im ∧
      Zeta23.zeroMult ρ = 1 := by
  obtain ⟨T, hT, hTH⟩ :=
    (eventually_exists_simple_critical_zero_dyadic.and (eventually_ge_atTop H)).exists
  obtain ⟨ρ, hz, hr, him, _, hm⟩ := hT
  exact ⟨ρ, hz, hr, lt_of_le_of_lt hTH him, hm⟩

/-- An unconditional critical-line zero, for downstream obstruction theorems. -/
theorem exists_critical_zero :
    ∃ ρ : ℂ, riemannZeta ρ = 0 ∧ ρ.re = 1 / 2 := by
  obtain ⟨ρ, hz, hr, _, _⟩ := exists_simple_critical_zero_above 0
  exact ⟨ρ, hz, hr⟩

end RiemannResearch.RH
