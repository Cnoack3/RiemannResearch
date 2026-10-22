import RiemannResearch.RH.ParetoProgressionTails
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

/-!
# The actual universal phase constant is positive and finite

Source: Christian Noack, `RH_Two_Seed_Threshold.tex`, 8 September 2026,
Sections 6, 8 and 11.2. The actual logarithmic summand is used below.
The elementary upper bound proved here is `1 / (4*k*(k+1))`, weaker than
the paper's sharper `1 / (12*k*(k+1))`, but already proves summability.
Neither the optimal phase floor nor its Hilbert--Schmidt identification is
assumed or claimed in this module.
-/

namespace RiemannResearch.RH.TwoSeedThreshold

open scoped BigOperators
open Pareto

noncomputable section

/-- The summand in the paper, with the positive index supplied explicitly. -/
def phaseDelta (k : ℕ) : ℝ :=
  1 - (k : ℝ) * ((k : ℝ) + 1) * Real.log (1 + 1 / (k : ℝ)) ^ 2

/-- The strict geometric-mean logarithm inequality behind positivity. -/
theorem log_sq_mul_lt_sub_sq {x : ℝ} (hx : 1 < x) :
    x * Real.log x ^ 2 < (x - 1) ^ 2 := by
  have hx0 : 0 < x := lt_trans zero_lt_one hx
  have hs0 : 0 < Real.sqrt x := Real.sqrt_pos.2 hx0
  have hs2 : Real.sqrt x ^ 2 = x := Real.sq_sqrt (le_of_lt hx0)
  have hs1 : 1 < Real.sqrt x := by nlinarith
  have hlog : 0 < Real.log x := Real.log_pos hx
  have h := Real.self_lt_sinh_iff.2 (Real.log_pos hs1)
  rw [Real.sinh_log hs0, Real.log_sqrt (le_of_lt hx0)] at h
  have hfirst : Real.log x < Real.sqrt x - (Real.sqrt x)⁻¹ := by linarith
  have hmul := mul_lt_mul_of_pos_left hfirst hs0
  have he : Real.sqrt x * (Real.sqrt x - (Real.sqrt x)⁻¹) = x - 1 := by
    rw [mul_sub, mul_inv_cancel₀ (ne_of_gt hs0)]
    nlinarith [hs2]
  rw [he] at hmul
  have hprod := mul_pos
    (show 0 < (x - 1) - Real.sqrt x * Real.log x by linarith)
    (show 0 < (x - 1) + Real.sqrt x * Real.log x by positivity)
  have hsq : (Real.sqrt x * Real.log x) ^ 2 = x * Real.log x ^ 2 := by
    rw [mul_pow, hs2]
  nlinarith

theorem phaseDelta_pos {k : ℕ} (hk : 0 < k) : 0 < phaseDelta k := by
  have hk0 : 0 < (k : ℝ) := by exact_mod_cast hk
  have hkne : (k : ℝ) ≠ 0 := ne_of_gt hk0
  have h := log_sq_mul_lt_sub_sq (x := 1 + 1 / (k : ℝ)) (by
    have hi : 0 < 1 / (k : ℝ) := by positivity
    linarith)
  have hm := mul_lt_mul_of_pos_left h (sq_pos_of_pos hk0)
  have hl : (k : ℝ)^2 * ((1 + 1 / (k : ℝ)) *
      Real.log (1 + 1 / (k : ℝ)) ^ 2) =
      (k : ℝ) * ((k : ℝ) + 1) * Real.log (1 + 1 / (k : ℝ)) ^ 2 := by
    field_simp
    <;> ring
  have hr : (k : ℝ)^2 * ((1 + 1 / (k : ℝ) - 1)^2) = 1 := by
    field_simp
    <;> ring
  rw [hl, hr] at hm
  unfold phaseDelta
  linarith

/-- A rational upper majorant, sufficient for the full infinite sum. -/
theorem phaseDelta_le_square_majorant {k : ℕ} (hk : 0 < k) :
    phaseDelta k ≤ 1 / (2 * (k : ℝ) + 1)^2 := by
  have hk0 : 0 < (k : ℝ) := by exact_mod_cast hk
  have hkne : (k : ℝ) ≠ 0 := ne_of_gt hk0
  have hd : 0 < 2 * (k : ℝ) + 1 := by positivity
  have h := Real.le_log_one_add_of_nonneg (x := 1 / (k : ℝ)) (by positivity)
  have he : 2 * (1 / (k : ℝ)) / (1 / (k : ℝ) + 2) =
      2 / (2 * (k : ℝ) + 1) := by
    field_simp
    <;> ring
  rw [he] at h
  have hs := (sq_le_sq₀ (by positivity : 0 ≤ 2 / (2 * (k : ℝ) + 1))
    (le_trans (by positivity) h)).2 h
  have hm := mul_le_mul_of_nonneg_left hs
    (by positivity : 0 ≤ (k : ℝ) * ((k : ℝ) + 1))
  have hid : 1 - (k : ℝ) * ((k : ℝ) + 1) *
      (2 / (2 * (k : ℝ) + 1))^2 = 1 / (2 * (k : ℝ) + 1)^2 := by
    field_simp
    <;> ring
  unfold phaseDelta
  linarith

theorem phaseDelta_le_quarter_weight {k : ℕ} (hk : 0 < k) :
    phaseDelta k ≤ positiveWeight k / 4 := by
  have hk0 : 0 < (k : ℝ) := by exact_mod_cast hk
  refine le_trans (phaseDelta_le_square_majorant hk) ?_
  unfold positiveWeight
  have hden : 0 < 4 * ((k : ℝ) * ((k : ℝ) + 1)) := by positivity
  have he : (1 / ((k : ℝ) * ((k : ℝ) + 1))) / 4 =
      1 / (4 * ((k : ℝ) * ((k : ℝ) + 1))) := by
    field_simp
    <;> ring
  rw [he]
  exact one_div_le_one_div_of_le hden (by nlinarith)

/-- No analytic convergence hypothesis remains in this summability theorem. -/
theorem phaseDelta_summable : Summable (fun k : ℕ => phaseDelta (k + 1)) := by
  have hw : Summable (fun k : ℕ => positiveWeight (k + 1)) :=
    positiveWeight_summable.comp_injective (by
      intro a b h
      exact Nat.add_right_cancel h)
  exact Summable.of_nonneg_of_le
    (fun k => le_of_lt (phaseDelta_pos (Nat.zero_lt_succ k)))
    (fun k => phaseDelta_le_quarter_weight (Nat.zero_lt_succ k))
    (hw.div_const 4)

/-- The actual base-independent infinite phase constant. -/
def universalPhaseConstant : ℝ := ∑' k : ℕ, phaseDelta (k + 1)

theorem universalPhaseConstant_pos : 0 < universalPhaseConstant := by
  exact phaseDelta_summable.tsum_pos
    (fun k => le_of_lt (phaseDelta_pos (Nat.zero_lt_succ k))) 0
    (phaseDelta_pos (by norm_num))

/-- The entire unresolved tail after the first `N` positive-index terms. -/
def phaseTail (N : ℕ) : ℝ := ∑' k : ℕ, phaseDelta (k + N + 1)

theorem phaseDelta_shift_summable (N : ℕ) :
    Summable (fun k : ℕ => phaseDelta (k + N + 1)) := by
  exact phaseDelta_summable.comp_injective (by
    intro a b h
    exact Nat.add_right_cancel h)

theorem phaseTail_pos (N : ℕ) : 0 < phaseTail N := by
  exact (phaseDelta_shift_summable N).tsum_pos
    (fun k => le_of_lt (phaseDelta_pos (by omega))) 0
    (phaseDelta_pos (by omega))

/-- An unconditional full-tail estimate; it is deliberately recorded with
its proved constant `1/4`, not the paper's sharper `1/12`. -/
theorem phaseTail_le (N : ℕ) : phaseTail N ≤ 1 / (4 * ((N : ℝ) + 1)) := by
  have hw : Summable (fun k : ℕ => positiveWeight (k + N + 1)) :=
    positiveWeight_summable.comp_injective (by
      intro a b h
      exact Nat.add_right_cancel (Nat.add_right_cancel h))
  have hcomp := Summable.tsum_le_tsum
    (fun k => phaseDelta_le_quarter_weight (k := k + N + 1) (by omega))
    (phaseDelta_shift_summable N) (hw.div_const 4)
  have he : (∑' k : ℕ, positiveWeight (k + N + 1)) = progressionWeight 1 (N + 1) := by
    unfold progressionWeight
    apply tsum_congr
    intro k
    congr 1
    omega
  rw [tsum_div_const, he] at hcomp
  have ht := progressionWeight_tail_upper 1 N (by norm_num)
  norm_num only [Nat.cast_one, one_mul] at ht
  have hd := div_le_div_of_nonneg_right ht (by norm_num : (0 : ℝ) ≤ 4)
  unfold phaseTail
  exact le_trans hcomp (by convert hd using 1 <;> field_simp <;> ring)

theorem phaseTail_split (N : ℕ) :
    phaseTail N = phaseDelta (N + 1) + phaseTail (N + 1) := by
  unfold phaseTail
  rw [(phaseDelta_shift_summable N).tsum_eq_zero_add]
  simp only [Nat.zero_add]
  congr 1
  apply tsum_congr
  intro k
  congr 1
  omega

/-- The finite certificate retains the entire positive tail exactly. -/
theorem universalPhaseConstant_head_tail (N : ℕ) :
    universalPhaseConstant = (∑ k ∈ Finset.range N, phaseDelta (k + 1)) +
      phaseTail N := by
  induction N with
  | zero => simp [universalPhaseConstant, phaseTail]
  | succ N ih =>
    rw [Finset.sum_range_succ, ih, phaseTail_split N]
    ring

theorem universalPhaseConstant_le_quarter : universalPhaseConstant ≤ 1 / 4 := by
  simpa [phaseTail, universalPhaseConstant] using phaseTail_le 0

/-- The paper's explicit scalar phase floor.  Its interpretation as a
distance bound requires the actual phase witness construction separately. -/
def phaseFloor (a : ℕ) : ℝ :=
  1 - (a : ℝ) * Real.log (a : ℝ)^2 /
    (((a : ℝ) - 1)^2 * (1 + universalPhaseConstant))

/-- Positivity of the exact scalar formula is unconditional. -/
theorem phaseFloor_pos {a : ℕ} (ha : 2 ≤ a) : 0 < phaseFloor a := by
  have ha1 : 1 < (a : ℝ) := by exact_mod_cast (show 1 < a by omega)
  have hs : 0 < universalPhaseConstant := universalPhaseConstant_pos
  have hsq : 0 < ((a : ℝ) - 1)^2 := sq_pos_of_pos (by linarith)
  have hden : 0 < ((a : ℝ) - 1)^2 * (1 + universalPhaseConstant) := by positivity
  have hnum := log_sq_mul_lt_sub_sq ha1
  have hg : ((a : ℝ) - 1)^2 <
      ((a : ℝ) - 1)^2 * (1 + universalPhaseConstant) := by nlinarith
  have hratio := (div_lt_one hden).2 (lt_trans hnum hg)
  unfold phaseFloor
  linarith

theorem phaseFloor_lt_one {a : ℕ} (ha : 2 ≤ a) : phaseFloor a < 1 := by
  have ha1 : 1 < (a : ℝ) := by exact_mod_cast (show 1 < a by omega)
  have ha0 : 0 < (a : ℝ) := by linarith
  have hl : 0 < Real.log (a : ℝ) := Real.log_pos ha1
  have hs := universalPhaseConstant_pos
  have hsq : 0 < ((a : ℝ) - 1)^2 := sq_pos_of_pos (by linarith)
  have hratio : 0 < (a : ℝ) * Real.log (a : ℝ)^2 /
      (((a : ℝ) - 1)^2 * (1 + universalPhaseConstant)) := by positivity
  unfold phaseFloor
  linarith

end
end RiemannResearch.RH.TwoSeedThreshold
