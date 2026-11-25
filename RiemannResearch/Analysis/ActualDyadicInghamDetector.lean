/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.ActualSelbergTransitionWindow
import RiemannResearch.Analysis.ActualZeroCountUpper
import RiemannResearch.Analysis.ActualZeroDensityLogExcess
import RiemannResearch.Analysis.ActualZeroDensityWindow
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The dyadic detector in rStation Paper 184

The cutoff balance and the passage from a capped Littlewood excess to the
one-logarithm dyadic count use actual, multiplicity-weighted zeta zeros.
The analytic excess estimate and the zero-free cap condition are hypotheses
of the assembly theorem. Their classical proofs are given in the accompanying
[dyadic proof](../INGHAM_DYADIC_ONE_LOG_20261125.md).
-/

noncomputable section
open Set
namespace RiemannResearch.Analysis.ActualZeroOrdinate

/-- At the dyadic cutoff, the polynomial and critical-line terms are equal. -/
theorem dyadicInghamCutoff_balance {S v : ℝ} (hS : 1 ≤ S)
    (hv : v ∈ Icc (1/2 : ℝ) 1) :
    let Y := S ^ ((3/2 : ℝ) / (2-v))
    let B := S ^ (3*(1-v)/(2-v))
    S ≤ Y ∧ Y ≤ S ^ (3/2 : ℝ) ∧ S ^ (2*(1-v)) ≤ B ∧
      Y ^ (2*(1-v)) = B ∧ S * Y ^ (-(4/3 : ℝ)*(v-1/2)) = B := by
  dsimp only
  have hp : 0 < 2-v := by linarith [hv.2]
  have hs : 0 ≤ S := zero_le_one.trans hS
  have hl : 1 ≤ (3/2 : ℝ)/(2-v) := (le_div_iff₀ hp).2 (by linarith [hv.1])
  have hu : (3/2 : ℝ)/(2-v) ≤ 3/2 := (div_le_iff₀ hp).2 (by linarith [hv.2])
  refine ⟨?_, Real.rpow_le_rpow_of_exponent_le hS hu, ?_, ?_, ?_⟩
  · simpa using Real.rpow_le_rpow_of_exponent_le hS hl
  · apply Real.rpow_le_rpow_of_exponent_le hS
    apply (le_div_iff₀ hp).2
    nlinarith [mul_nonneg (sub_nonneg.mpr hv.1) (sub_nonneg.mpr hv.2)]
  · rw [← Real.rpow_mul hs]
    congr 1
    ring
  · rw [← Real.rpow_mul hs]
    conv_lhs => lhs; rw [← Real.rpow_one S]
    rw [← Real.rpow_add (zero_lt_one.trans_le hS)]
    congr 1
    field_simp [hp.ne'] <;> ring

/-- When the polynomial energy saves a factor B, increasing the cutoff by
the corresponding power of B yields the exact factor B^(q-1). -/
theorem dyadicInghamCutoff_refined {S B v : ℝ} (hS : 0 < S) (hB : 0 < B)
    (hv : v < 2) :
    let q := 3*(1-v)/(2-v)
    let Y := (S*B) ^ ((3/2 : ℝ)/(2-v))
    Y ^ (2*(1-v)) / B = S ^ q * B ^ (q-1) ∧
      S * Y ^ (-(4/3 : ℝ)*(v-1/2)) = S ^ q * B ^ (q-1) := by
  dsimp only
  have hp : 0 < 2-v := sub_pos.mpr hv
  have hmul : 0 ≤ S*B := mul_nonneg hS.le hB.le
  have hlo : (3/2 : ℝ)/(2-v)*(2*(1-v)) = 3*(1-v)/(2-v) := by ring
  have hhi : (3/2 : ℝ)/(2-v)*(-(4/3 : ℝ)*(v-1/2)) = 3*(1-v)/(2-v)-1 := by
    field_simp [hp.ne'] <;> ring
  constructor
  · rw [← Real.rpow_mul hmul, hlo, Real.mul_rpow hS.le hB.le,
      Real.rpow_sub hB, Real.rpow_one]
    ring
  · rw [← Real.rpow_mul hmul, hhi, Real.mul_rpow hS.le hB.le,
      Real.rpow_sub hS, Real.rpow_one]
    field_simp [hS.ne']

/-- Moving the counting threshold left by h costs at most S^(3h). -/
theorem dyadicIngham_threshold_shift {S v σ : ℝ} (hS : 1 ≤ S)
    (hv : v ≤ σ) (hσ : σ ≤ 1) :
    S ^ (3*(1-v)/(2-v)) ≤
      Real.exp (3*(σ-v)*Real.log S) * S ^ (3*(1-σ)/(2-σ)) := by
  have hp : 0 < 2-σ := by linarith
  have hvp : 0 < 2-v := by linarith
  have hid : 3*(1-v)/(2-v) - 3*(1-σ)/(2-σ) =
      3*(σ-v)/((2-v)*(2-σ)) := by field_simp; ring
  have hden : 1 ≤ (2-v)*(2-σ) := by
    have h1 : 1 ≤ 2-v := by linarith
    have h2 : 1 ≤ 2-σ := by linarith
    nlinarith [mul_nonneg (sub_nonneg.mpr h1) (sub_nonneg.mpr h2)]
  have hq : 3*(1-v)/(2-v) - 3*(1-σ)/(2-σ) ≤ 3*(σ-v) := by
    rw [hid]
    exact div_le_self (by linarith) hden
  have hs : 0 < S := zero_lt_one.trans_le hS
  rw [Real.rpow_def_of_pos hs, Real.rpow_def_of_pos hs, ← Real.exp_add, Real.exp_le_exp]
  nlinarith only [mul_le_mul_of_nonneg_right hq (Real.log_nonneg hS)]

/-- The integrated detector estimate before the interior cutoff is chosen.
The first conclusion on a nonempty window is the cap absorption supplied in
the classical proof by the Vinogradov–Korobov zero-free region. -/
def DyadicInghamDetectorExcess : Prop :=
  ∃ D H : ℝ, 0 ≤ D ∧ 1 < H ∧ ∀ S : ℝ, H ≤ S → ∀ σ ∈ Ico (1/2 : ℝ) 1,
    2 < (σ-1/2)*Real.log S → 0 < rightInclusiveWindow S (2*S) σ →
    Real.log S ≤ S ^ (3*(1-σ)/(2-σ)) ∧
      ∃ v : ℝ, 1/2 ≤ v ∧ v ≤ σ ∧ 1/2 ≤ (σ-v)*Real.log S ∧
        (σ-v)*Real.log S ≤ 1 ∧ ∀ Y : ℝ, S ≤ Y → Y ≤ S ^ (3/2 : ℝ) →
        rightLogExcessWindow S (2*S) v ≤
          D * (S ^ (2*(1-v)) + Y ^ (2*(1-v)) +
            S * Y ^ (-(4/3 : ℝ)*(v-1/2)) + Real.log S)

/-- The balanced detector gives the dyadic Ingham exponent with one log.
The shallow range uses only the unconditional total count. -/
theorem dyadicInghamOneLog_of_detectorExcess
    (h : DyadicInghamDetectorExcess) : DyadicInghamOneLog := by
  obtain ⟨D,H,hD,hH,hdet⟩ := h
  obtain ⟨C,hC,htotal⟩ := exists_count_le_height_log
  let c₁ := 4*C*Real.exp 6
  let c₂ := 2*D*(3*Real.exp 3+1)
  refine ⟨max c₁ c₂,max H 9,le_trans (by dsimp [c₁]; positivity) (le_max_left _ _),
    hH.trans_le (le_max_left _ _),?_⟩
  intro S hS σ hσ
  have h9 : 9 ≤ S := (le_max_right _ _).trans hS
  have hs : 1 < S := by linarith
  have hpos : 0 < S := by linarith
  have hL : 0 < Real.log S := Real.log_pos hs
  let B := S ^ (3*(1-σ)/(2-σ))
  have hB : 0 < B := Real.rpow_pos_of_pos hpos _
  change rightInclusiveWindow S (2*S) σ ≤ max c₁ c₂ * B * Real.log S
  have hinc {c : ℝ} (hc : c ≤ max c₁ c₂) :
      c * B * Real.log S ≤ max c₁ c₂ * B * Real.log S :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc hB.le) hL.le
  by_cases hsh : (σ-1/2)*Real.log S ≤ 2
  · apply le_trans _ (hinc (le_max_left _ _))
    have hshift := dyadicIngham_threshold_shift hs.le hσ.1 hσ.2.le
    norm_num at hshift
    have hpow : S ≤ Real.exp 6 * B := by
      apply hshift.trans
      apply mul_le_mul_of_nonneg_right _ hB.le
      exact Real.exp_le_exp.mpr (by linarith only [hsh])
    have hcount := (rightInclusiveCount_le_count (2*S) σ).trans
      (htotal (2*S) (by linarith))
    have hw : rightInclusiveWindow S (2*S) σ ≤ rightInclusiveCount (2*S) σ := by
      rw [rightInclusiveWindow_eq_sub (by linarith)]
      exact sub_le_self _ (rightInclusiveCount_nonneg _ _)
    have hlog : Real.log (2*S) ≤ 2*Real.log S := by
      rw [Real.log_mul (by norm_num) hpos.ne']
      linarith only [Real.log_le_log (by norm_num : 0 < (2 : ℝ)) (show 2 ≤ S by linarith)]
    calc
      _ ≤ C*(2*S)*Real.log (2*S) := hw.trans hcount
      _ ≤ C*(2*S)*(2*Real.log S) := mul_le_mul_of_nonneg_left hlog (by positivity)
      _ ≤ c₁*B*Real.log S := by
        dsimp [c₁]
        nlinarith only [mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hpow hC.le) hL.le]
  · by_cases hw : 0 < rightInclusiveWindow S (2*S) σ
    · apply le_trans _ (hinc (le_max_right _ _))
      obtain ⟨hcap,v,hv,hvσ,hgap,hgap',hraw⟩ :=
        hdet S ((le_max_left _ _).trans hS) σ hσ (lt_of_not_ge hsh) hw
      have hbal := dyadicInghamCutoff_balance hs.le ⟨hv,hvσ.trans hσ.2.le⟩
      obtain ⟨hY,hY',hlo,hpoly,hhigh⟩ := hbal
      have he := hraw _ hY hY'
      rw [hpoly,hhigh] at he
      have hshift : S ^ (3*(1-v)/(2-v)) ≤ Real.exp 3 * B := by
        apply (dyadicIngham_threshold_shift hs.le hvσ hσ.2.le).trans
        exact mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (by linarith only [hgap'])) hB.le
      have hsum : rightLogExcessWindow S (2*S) v ≤ D*((3*Real.exp 3+1)*B) := by
        apply he.trans
        apply mul_le_mul_of_nonneg_left _ hD
        change Real.log S ≤ B at hcap
        linarith only [hlo,hshift,hcap]
      have hcount := rightInclusiveWindow_mul_gap_le S (2*S) v σ hvσ
      have hx := mul_le_mul_of_nonneg_right (hcount.trans hsum) hL.le
      have hg := mul_le_mul_of_nonneg_left hgap hw.le
      dsimp [c₂]
      nlinarith only [hx,hg]
    · exact (le_of_not_gt hw).trans (mul_nonneg
        (mul_nonneg (le_trans (by dsimp [c₁]; positivity) (le_max_left _ _)) hB.le) hL.le)

#print axioms dyadicInghamCutoff_balance
#print axioms dyadicInghamCutoff_refined
#print axioms dyadicIngham_threshold_shift
#print axioms dyadicInghamOneLog_of_detectorExcess

end RiemannResearch.Analysis.ActualZeroOrdinate
