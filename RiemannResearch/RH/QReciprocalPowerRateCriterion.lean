/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QReciprocalMellinCriterion

/-! Positive power reciprocal rates with subpower complete energy. The arithmetic energy bound remains explicit. -/

noncomputable section
open Filter
open scoped Topology
namespace RiemannResearch.RH.QReciprocalMellinCriterion
open ZetaTwoHilbert QShiftedReciprocal

/-- Every fixed positive-power reciprocal rate suffices when the complete
energy is subpower. The growth premise remains the arithmetic RH provider. -/
theorem riemannHypothesis_of_reciprocal_power_rate_subpower_norm
    (U : ℕ → QHilbert) (hU : ∀ k, U k ∈ QFullResidueProjection.legalSpan)
    (C r : ℝ) (hr : 0 < r)
    (herr : ∀ k, ‖B (qOne - U k)‖ ≤ C / ((k : ℝ) + 1) ^ r)
    (hgrowth : ∀ a : ℝ, 0 < a → Tendsto
      (fun (k : ℕ) => ((k : ℝ) + 1) ^ (-a) * ‖U k‖ ^ 2) atTop (𝓝 0)) :
    RiemannHypothesis := by
  have hC : 0 ≤ C := by
    have he := herr 0
    norm_num at he
    exact (norm_nonneg _).trans he
  obtain ⟨m, hm⟩ := exists_nat_gt (1 / r)
  have hmR : 0 < (m : ℝ) := lt_trans (one_div_pos.mpr hr) hm
  have hmN : 0 < m := by exact_mod_cast hmR
  have hmr : 1 < (m : ℝ) * r := (div_lt_iff₀ hr).mp hm
  let stage : ℕ → ℕ := fun j => (j + 1) ^ m - 1
  have hstage_nat (j : ℕ) : stage j + 1 = (j + 1) ^ m := by
    dsimp [stage]
    have hp : 0 < (j + 1) ^ m := by positivity
    omega
  have hstage_cast (j : ℕ) : (stage j : ℝ) + 1 = ((j : ℝ) + 1) ^ m := by
    exact_mod_cast hstage_nat j
  have hstage : Tendsto stage atTop atTop := by
    have hle (j : ℕ) : j ≤ stage j := by
      have hp : j + 1 ≤ (j + 1) ^ m := by
        cases m with
        | zero => omega
        | succ m =>
          rw [pow_succ]
          have hpos : 0 < (j + 1) ^ m := by positivity
          nlinarith
      have he := hstage_nat j
      omega
    exact tendsto_atTop_mono hle tendsto_id
  apply riemannHypothesis_of_reciprocal_rate_subpower_norm
    (fun j => U (stage j)) (fun j => hU (stage j)) C
  · intro j
    have hx : 0 < (j : ℝ) + 1 := by positivity
    have hx1 : 1 ≤ (j : ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) j]
    have hpow : (j : ℝ) + 1 ≤ (((j : ℝ) + 1) ^ m) ^ r := by
      calc
        _ = ((j : ℝ) + 1) ^ (1 : ℝ) := (Real.rpow_one _).symm
        _ ≤ ((j : ℝ) + 1) ^ ((m : ℝ) * r) :=
          Real.rpow_le_rpow_of_exponent_le hx1 hmr.le
        _ = _ := by rw [← Real.rpow_natCast, ← Real.rpow_mul hx.le]
    have he := herr (stage j)
    rw [hstage_cast j] at he
    exact he.trans (div_le_div_of_nonneg_left hC hx hpow)
  · intro a ha
    have he (j : ℕ) : ((stage j : ℝ) + 1) ^ (-(a / (m : ℝ))) =
        ((j : ℝ) + 1) ^ (-a) := by
      rw [hstage_cast j, ← Real.rpow_natCast,
        ← Real.rpow_mul (by positivity : 0 ≤ (j : ℝ) + 1)]
      congr 1
      field_simp [ne_of_gt hmR] <;> ring
    simpa only [Function.comp_def, he] using
      (hgrowth (a / (m : ℝ)) (div_pos ha hmR)).comp hstage

end RiemannResearch.RH.QReciprocalMellinCriterion
