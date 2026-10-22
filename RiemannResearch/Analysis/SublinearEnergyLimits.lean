import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Limit lemmas for sublinear-energy arguments

Source: user-provided `Pareto_Direct_Attempt_Sublinear_Energy_2026-09-22.md`,
Sections 3-4. These abstract lemmas formalize the fixed-cutoff limiting step
and the positive-product obstruction; no arithmetic estimate is assumed true.
The actual Pareto consumers live in `CanonicalMobiusFullEnergy` and
`ParetoSublinearResidualTail`.
-/


open Filter Topology

namespace RiemannResearch.Analysis

/-- A fixed positive product lower bound and a vanishing nonnegative factor
force the other factor to diverge to positive infinity. -/
theorem tendsto_atTop_of_pos_le_mul_tendsto_zero
    {b t : ℕ → ℝ} {c : ℝ}
    (hc : 0 < c)
    (hb0 : ∀ᶠ n in atTop, 0 ≤ b n)
    (hb : Tendsto b atTop (𝓝 0))
    (hprod : ∀ᶠ n in atTop, c ≤ t n * b n) :
    Tendsto t atTop atTop := by
  refine tendsto_atTop.2 fun B => ?_
  let D : ℝ := max B 1
  have hD : 0 < D := lt_of_lt_of_le zero_lt_one (le_max_right B 1)
  have heps : 0 < c / D := div_pos hc hD
  have hsmall : ∀ᶠ n in atTop, b n < c / D :=
    hb.eventually (gt_mem_nhds heps)
  filter_upwards [hb0, hsmall, hprod] with n hbn hsmalln hprodn
  by_contra hnot
  have htB : t n < B := lt_of_not_ge hnot
  have htD : t n ≤ D := (le_of_lt htB).trans (le_max_left B 1)
  have hDb : D * b n < c := by
    have hh : b n * D < c := (lt_div_iff₀ hD).mp hsmalln
    simpa only [mul_comm] using hh
  have htb : t n * b n < c :=
    lt_of_le_of_lt (mul_le_mul_of_nonneg_right htD hbn) hDb
  exact (not_lt_of_ge hprodn) htb


end RiemannResearch.Analysis


open Filter Topology

namespace RiemannResearch.Analysis

/-- The final fixed-cutoff, then growing-cutoff step in the full-energy proof.
The sequence b may depend arbitrarily on K; no uniformity in K is needed. -/
theorem tendsto_zero_of_fixed_cutoff_remainder
    {e : ℕ → ℝ} {C : ℝ}
    (he0 : ∀ᶠ n in atTop, 0 ≤ e n)
    (hcutoff : ∀ K : ℕ, 2 ≤ K →
      ∃ b : ℕ → ℝ, Tendsto b atTop (𝓝 0) ∧
        ∀ᶠ n in atTop, e n ≤ b n + C / (K : ℝ)) :
    Tendsto e atTop (𝓝 0) := by
  refine tendsto_order.2 ⟨?_, ?_⟩
  · intro a ha
    filter_upwards [he0] with n hn
    exact lt_of_lt_of_le ha hn
  · intro ε hε
    have hεhalf : 0 < ε / 2 := by linarith
    obtain ⟨K, hK⟩ := exists_nat_gt (max (C / (ε / 2)) (2 : ℝ))
    have hKtwo : (2 : ℝ) < (K : ℝ) :=
      lt_of_le_of_lt (le_max_right _ _) hK
    have hK2 : 2 ≤ K := by exact_mod_cast le_of_lt hKtwo
    have hKpos : 0 < (K : ℝ) := by linarith
    have hKlarge : C / (ε / 2) < (K : ℝ) :=
      lt_of_le_of_lt (le_max_left _ _) hK
    have hCsmall : C / (K : ℝ) < ε / 2 := by
      apply (div_lt_iff₀ hKpos).2
      have hh : C < (K : ℝ) * (ε / 2) :=
        (div_lt_iff₀ hεhalf).1 hKlarge
      simpa only [mul_comm] using hh
    obtain ⟨b, hb, heb⟩ := hcutoff K hK2
    have hbsmall : ∀ᶠ n in atTop, b n < ε / 2 :=
      hb.eventually (gt_mem_nhds hεhalf)
    filter_upwards [heb, hbsmall] with n hen hbn
    linarith

end RiemannResearch.Analysis
