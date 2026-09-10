import RiemannResearch.Analysis.RotationNearestSpacing
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.FieldSimp

/-!
# Elementary exponential separation for the triadic rotation

Source: user-provided continuation and
`RH/Dyadic_Gram_Prefix_Ordinary_Proof_20260910.md`, Section 4.
The exponential estimate uses Mathlib's `Real.abs_exp_sub_one_le`.
The intended RH consumer is the logarithmic Gram prefix estimate.
-/

namespace RiemannResearch.Analysis

noncomputable def triadicRotation : ℝ := Real.log 3 / Real.log 2

theorem triadicRotation_gt_one : 1 < triadicRotation := by
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h23 : Real.log 2 < Real.log 3 := Real.log_lt_log (by norm_num) (by norm_num)
  apply (lt_div_iff₀ h2).2
  simpa using h23

theorem three_pow_ne_two_pow {q : ℕ} (hq : 0 < q) (p : ℕ) :
    (3 : ℕ) ^ q ≠ 2 ^ p := by
  intro heq
  by_cases hp : p = 0
  · subst p
    cases q with
    | zero => omega
    | succ q =>
      simp only [pow_succ, pow_zero] at heq
      omega
  · have hthree : (3 : ℕ) ^ q % 2 = 1 := by simp [Nat.pow_mod]
    have htwo : (2 : ℕ) ^ p % 2 = 0 := by simp [Nat.pow_mod, hp]
    rw [heq, htwo] at hthree
    omega

theorem three_two_power_integer_gap {q : ℕ} (hq : 0 < q) (p : ℕ) :
    1 ≤ |(2 : ℝ) ^ p - (3 : ℝ) ^ q| := by
  have hne : (2 : ℤ) ^ p - (3 : ℤ) ^ q ≠ 0 := by
    apply sub_ne_zero.mpr
    intro h
    have hn : (2 : ℕ) ^ p = (3 : ℕ) ^ q := by exact_mod_cast h
    exact three_pow_ne_two_pow hq p hn.symm
  have hpos : (0 : ℤ) < |(2 : ℤ) ^ p - (3 : ℤ) ^ q| := abs_pos.mpr hne
  have hone : (1 : ℤ) ≤ |(2 : ℤ) ^ p - (3 : ℤ) ^ q| := hpos
  exact_mod_cast hone

/-- Division-free separation for every actual nearest integer error.
The proof uses only integer discreteness and a local exponential estimate. -/
theorem triadicRotation_distance_mul_lower {q : ℕ} (hq : 0 < q) :
    1 ≤ 2 * (3 : ℝ) ^ q * rotationNearestDistance triadicRotation q := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2lt : Real.log 2 < 1 := by
    have h := Real.log_lt_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
      (by norm_num : (2 : ℝ) ≠ 1)
    norm_num at h ⊢
    exact h
  have hqR : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have halpha := triadicRotation_gt_one
  have harg : 1 < (q : ℝ) * triadicRotation := by nlinarith
  have hhalf := abs_sub_round ((q : ℝ) * triadicRotation)
  have hhalf' := (abs_le.mp hhalf).2
  have hroundR : (0 : ℝ) < (round ((q : ℝ) * triadicRotation) : ℝ) := by
    linarith
  have hround : (0 : ℤ) ≤ round ((q : ℝ) * triadicRotation) := by
    exact_mod_cast hroundR.le
  let p : ℕ := (round ((q : ℝ) * triadicRotation)).toNat
  have hpcast : (p : ℝ) = (round ((q : ℝ) * triadicRotation) : ℝ) := by
    dsimp [p]
    exact_mod_cast Int.toNat_of_nonneg hround
  have he : (q : ℝ) * triadicRotation - (p : ℝ) =
      rotationCenteredError triadicRotation q := by
    rw [hpcast]
    rfl
  let x : ℝ := (p : ℝ) * Real.log 2 - (q : ℝ) * Real.log 3
  have hxeq : x = -Real.log 2 * rotationCenteredError triadicRotation q := by
    rw [← he]
    dsimp [x, triadicRotation]
    field_simp [ne_of_gt hlog2]
    <;> ring
  have habsx : |x| = Real.log 2 * rotationNearestDistance triadicRotation q := by
    rw [hxeq, abs_mul, abs_neg, abs_of_pos hlog2]
    rfl
  have hδnonneg := rotationNearestDistance_nonneg triadicRotation q
  have hδhalf := rotationNearestDistance_le_half triadicRotation q
  have hx : |x| ≤ 1 := by rw [habsx]; nlinarith
  have hquot : Real.exp x = (2 : ℝ) ^ p / (3 : ℝ) ^ q := by
    dsimp [x]
    rw [Real.exp_sub, Real.exp_nat_mul, Real.exp_nat_mul,
      Real.exp_log (by norm_num : (0 : ℝ) < 2),
      Real.exp_log (by norm_num : (0 : ℝ) < 3)]
  have hthreepos : (0 : ℝ) < (3 : ℝ) ^ q := by positivity
  have hid : (3 : ℝ) ^ q * (Real.exp x - 1) =
      (2 : ℝ) ^ p - (3 : ℝ) ^ q := by
    rw [hquot]
    field_simp
    <;> ring
  have habsid := congrArg (fun y : ℝ => |y|) hid
  rw [abs_mul, abs_of_pos hthreepos] at habsid
  have hgap := three_two_power_integer_gap hq p
  have hexp := mul_le_mul_of_nonneg_left (Real.abs_exp_sub_one_le hx) hthreepos.le
  rw [habsx] at hexp
  have hlogδ : Real.log 2 * rotationNearestDistance triadicRotation q ≤
      rotationNearestDistance triadicRotation q := by nlinarith
  have hlogδthree := mul_le_mul_of_nonneg_left hlogδ
    (by positivity : (0 : ℝ) ≤ 2 * (3 : ℝ) ^ q)
  nlinarith

theorem triadicRotation_distance_lower {q : ℕ} (hq : 0 < q) :
    1 / (2 * (3 : ℝ) ^ q) ≤ rotationNearestDistance triadicRotation q := by
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * (3 : ℝ) ^ q)).2
  have h := triadicRotation_distance_mul_lower hq
  nlinarith

theorem triadicRotation_distance_pos {q : ℕ} (hq : 0 < q) :
    0 < rotationNearestDistance triadicRotation q :=
  lt_of_lt_of_le (by positivity) (triadicRotation_distance_lower hq)

/-- The exponential Diophantine input to the elementary prefix lemma is
proved for the actual logarithmic rotation. -/
theorem triadicRotation_log_inverse_distance_le {q : ℕ} (hq : 0 < q) :
    Real.log (1 / rotationNearestDistance triadicRotation q) ≤
      (q : ℝ) * Real.log 6 := by
  have hδpos := triadicRotation_distance_pos hq
  have hmul := triadicRotation_distance_mul_lower hq
  have hinv : 1 / rotationNearestDistance triadicRotation q ≤ 2 * (3 : ℝ) ^ q := by
    apply (div_le_iff₀ hδpos).2
    nlinarith
  have hl := Real.log_le_log (by positivity :
    0 < 1 / rotationNearestDistance triadicRotation q) hinv
  rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0)
    (by positivity : (3 : ℝ) ^ q ≠ 0), Real.log_pow] at hl
  have hqR : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog6 : Real.log 6 = Real.log 2 + Real.log 3 := by
    rw [show (6 : ℝ) = 2 * 3 by norm_num,
      Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by norm_num : (3 : ℝ) ≠ 0)]
  rw [hlog6]
  nlinarith

theorem triadicRotation_irrational : Irrational triadicRotation :=
  irrational_of_rotationNearestDistance_pos (fun _ hq => triadicRotation_distance_pos hq)

/-- Actual block spacing for log 3 / log 2, with no irrationality assumption
remaining in the theorem's type. -/
theorem exists_triadicRotation_prefix_minimum_spacing {N : ℕ} (hN : 0 < N) :
    ∃ q : ℕ, 0 < q ∧ q ≤ N ∧
      (∀ h : ℕ, 0 < h → h ≤ N →
        rotationNearestDistance triadicRotation q ≤
          rotationNearestDistance triadicRotation h) ∧
      ∀ i j : ℕ, i < j → j - i < q →
        1 / (2 * (q : ℝ)) <
          |rotationCenteredError triadicRotation j -
            rotationCenteredError triadicRotation i| :=
  exists_rotationCenteredError_prefix_minimum_spacing triadicRotation_irrational hN

end RiemannResearch.Analysis
