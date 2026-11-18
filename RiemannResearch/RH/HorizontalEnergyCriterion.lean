/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.ActualZeroOrdinate
import RiemannResearch.Analysis.ActualZeroLoglogRate
import RiemannResearch.RH.RealZetaNonvanishing
import RiemannResearch.RH.RiemannHypothesisStrip
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The unnormalized horizontal energy criterion for RH

A zero off the critical line and its reflected partner give a fixed positive
contribution at every cutoff above their common ordinate. Conjugation and
real-axis nonvanishing extend the resulting positive-height criterion to
Mathlib's `RiemannHypothesis`. The quantitative estimate for the normalized
energy in `ActualZeroLoglogRate` survives the addition of any fixed charge.
-/

noncomputable section
open Filter Zeta23
open scoped Topology BigOperators ComplexConjugate
namespace RiemannResearch.RH
open Analysis.ActualZeroOrdinate

/-- An off-line zero and its reflected partner contribute exactly twice the
single charge. All remaining zeros occur in the displayed remainder. -/
theorem horizontalEnergy_eq_reflected_pair_add {T : ℝ} {ρ : ℂ} (hρ : ρ ∈ cutoff T)
    (hd : ρ.re ≠ 1 / 2) :
    horizontalEnergy T = 2 * (zeroMult ρ : ℝ) * (ρ.re - 1 / 2) ^ 2 +
      ∑ z ∈ ((cutoff T).erase ρ).erase (reflect ρ), (zeroMult z : ℝ) * (z.re - 1 / 2) ^ 2 := by
  classical
  let f := fun z : ℂ => (zeroMult z : ℝ) * (z.re - 1 / 2) ^ 2
  have hn : reflect ρ ≠ ρ := by
    intro h
    have hh := congrArg Complex.re h
    rw [reflect_re] at hh
    exact hd (by linarith)
  have hm : reflect ρ ∈ (cutoff T).erase ρ := Finset.mem_erase.mpr ⟨hn, reflect_mem hρ⟩
  have hf : f (reflect ρ) = f ρ := by
    dsimp only [f]
    rw [zetaSeam.mult_reflect ρ (mem_cutoff.mp hρ).1, reflect_re]
    ring
  calc
    horizontalEnergy T = f ρ + ∑ z ∈ (cutoff T).erase ρ, f z :=
      (Finset.add_sum_erase _ _ hρ).symm
    _ = f ρ + (f (reflect ρ) + ∑ z ∈ ((cutoff T).erase ρ).erase (reflect ρ), f z) := by
      rw [Finset.add_sum_erase _ _ hm]
    _ = _ := by rw [hf]; dsimp only [f]; ring

/-- RH is equivalent to arbitrarily small *total* energy at arbitrarily large heights. -/
theorem riemannHypothesis_iff_cofinal_horizontalEnergy_small :
    RiemannHypothesis ↔ ∀ ε : ℝ, 0 < ε → ∀ B : ℝ,
      ∃ T : ℝ, B ≤ T ∧ horizontalEnergy T < ε := by
  constructor
  · intro hRH ε hε B
    refine ⟨B, le_rfl, ?_⟩
    have hE : horizontalEnergy B = 0 := (horizontalEnergy_eq_zero_iff B).mpr (by
      intro ρ hρ
      obtain ⟨hz, _, _⟩ := mem_cutoff.mp hρ
      exact riemannHypothesis_iff_strip_zeros_on_line.mp hRH ρ hz.1 hz.2.1 hz.2.2)
    simpa only [hE] using hε
  · intro h
    have hpos (ρ : ℂ) (hz : riemannZeta ρ = 0) (hi : 0 < ρ.im) : ρ.re = 1 / 2 := by
      by_contra hd
      have hm : 0 < (zeroMult ρ : ℝ) := by
        exact_mod_cast multiplicity_pos (mem_cutoff_iff_zeta.mpr ⟨hz, hi, le_rfl⟩)
      have hε : 0 < 2 * (zeroMult ρ : ℝ) * (ρ.re - 1 / 2) ^ 2 :=
        mul_pos (mul_pos (by norm_num) hm) (sq_pos_of_ne_zero (sub_ne_zero.mpr hd))
      obtain ⟨T, hT, hE⟩ := h _ hε ρ.im
      rw [horizontalEnergy_eq_reflected_pair_add (mem_cutoff_iff_zeta.mpr ⟨hz, hi, hT⟩) hd] at hE
      have hrem : 0 ≤ ∑ z ∈ ((cutoff T).erase ρ).erase (reflect ρ),
          (zeroMult z : ℝ) * (z.re - 1 / 2) ^ 2 :=
        Finset.sum_nonneg fun z _ => mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)
      linarith
    apply riemannHypothesis_iff_strip_zeros_on_line.mpr
    intro z hz h0 h1
    rcases lt_trichotomy 0 z.im with hi | hi | hi
    · exact hpos z hz hi
    · have hre : z = (z.re : ℂ) := by apply Complex.ext <;> simp [hi.symm]
      exact False.elim (riemannZeta_ofReal_ne_zero z.re h0 h1.ne
        ((congrArg riemannZeta hre).symm.trans hz))
    · have hz' : riemannZeta (conj z) = 0 := by rw [_root_.riemannZeta_conj, hz, map_zero]
      exact hpos (conj z) hz' (by simpa only [Complex.conj_im] using neg_pos.mpr hi)

/-- Adding any fixed total charge preserves the unconditional height-normalized rate. -/
theorem horizontalEnergy_add_const_div_height_isBigO (c : ℝ) :
    Asymptotics.IsBigO atTop (fun T : ℝ => (horizontalEnergy T + c) / T) horizontalLogRate := by
  have hsmall : Asymptotics.IsBigO atTop (fun T : ℝ => c / T) horizontalLogRate := by
    apply Asymptotics.IsBigO.of_bound |c|
    filter_upwards [eventually_gt_atTop (1 : ℝ),
      (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).eventually_ge_atTop 1] with T hT hl
    have hp : 0 < T := by linarith
    have hL := Real.log_pos hT
    have hLT : Real.log T ≤ T := by linarith [Real.log_le_sub_one_of_pos hp]
    have hll : (1 : ℝ) ≤ (Real.log (Real.log T)) ^ 2 := by
      change 1 ≤ Real.log (Real.log T) at hl
      nlinarith [sq_nonneg (Real.log (Real.log T) - 1)]
    have hdiv : 1 / T ≤ horizontalLogRate T :=
      (one_div_le_one_div_of_le hL hLT).trans (div_le_div_of_nonneg_right hll hL.le)
    have hn : 0 ≤ horizontalLogRate T := by unfold horizontalLogRate; positivity
    rw [Real.norm_eq_abs, abs_div, abs_of_pos hp, Real.norm_eq_abs, abs_of_nonneg hn]
    simpa only [div_eq_mul_inv, one_mul] using mul_le_mul_of_nonneg_left hdiv (abs_nonneg c)
  simpa only [add_div, Pi.add_apply] using
    horizontalEnergy_div_height_isBigO_loglog_sq_div_log.add hsmall

end RiemannResearch.RH
