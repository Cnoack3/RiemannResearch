import RiemannResearch.RH.ReciprocalInfiniteCertificate
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith

/-!
# Target-compatible four-site reciprocal certificate

Source: independently developed exact signed normal-equation calculation,
9 October 2026. The only additional head identity is radical compatibility
at site four. This module retains the complete signed quadratic form, proves
a rational 34-site head certificate, and controls every remaining tail site.
It asserts no asymptotic decay and no compatibility of screened vectors.
-/

noncomputable section
open Filter
open scoped BigOperators Topology
namespace RiemannResearch.RH.ReciprocalRadicalFourCertificate
open ReciprocalInfiniteCertificate

def linearRow (a b c : ℝ) (k : ℕ) : ℝ :=
  a * ((k % 2 : ℕ) : ℝ) + b * ((k % 3 : ℕ) : ℝ) + c * ((k % 5 : ℕ) : ℝ)

def rowOne (k : ℕ) : ℝ := linearRow (-9 / 10) (-4 / 15) (1 / 5) k
def rowTwo (k : ℕ) : ℝ := linearRow (8 / 5) (-8 / 5) (-2 / 15) k
def rowThree (k : ℕ) : ℝ := linearRow (-9 / 10) (12 / 5) (-9 / 5) k

def transformedOne (k : ℕ) : ℝ := linearRow (-200 / 223) (-176 / 669) (128 / 669) k
def transformedTwo (k : ℕ) : ℝ := linearRow (347 / 209) (-368 / 209) (-8 / 627) k
def transformedThree (k : ℕ) : ℝ := rowThree k

def headNorm (x y z : ℝ) : ℝ :=
  x ^ 2 + y ^ 2 / 4 + z ^ 2 / 9 + (-x + y + z) ^ 2 / 16

def headReciprocal (x y z : ℝ) : ℝ :=
  x ^ 2 + y ^ 2 / 8 + z ^ 2 / 27 + (-x + y + z) ^ 2 / 64

def headForm (x y z : ℝ) : ℝ :=
  (223 / 320 : ℝ) * (x + y / 223 + z / 223) ^ 2 +
    (209 / 4460 : ℝ) * (y - 14 * z / 209) ^ 2 + (2 / 5643 : ℝ) * z ^ 2

theorem headForm_exact (x y z : ℝ) :
    headForm x y z = headReciprocal x y z - (3 / 10 : ℝ) * headNorm x y z := by
  unfold headForm headReciprocal headNorm
  ring

theorem headForm_signed_cross (x y z : ℝ) :
    headForm x y z = (223 / 320 : ℝ) * x ^ 2 + (1 / 160 : ℝ) * x * y +
      (1 / 160 : ℝ) * x * z + (3 / 64 : ℝ) * y ^ 2 -
      (1 / 160 : ℝ) * y * z + (1 / 1728 : ℝ) * z ^ 2 := by
  unfold headForm
  ring

theorem headForm_nonneg (x y z : ℝ) : 0 ≤ headForm x y z := by
  unfold headForm
  positivity

theorem headNorm_nonneg (x y z : ℝ) : 0 ≤ headNorm x y z := by
  unfold headNorm
  positivity

theorem transformedOne_exact (k : ℕ) :
    transformedOne k = rowOne k + rowTwo k / 223 + rowThree k / 223 := by
  unfold transformedOne rowOne rowTwo rowThree linearRow
  ring

theorem transformedTwo_exact (k : ℕ) :
    transformedTwo k = rowTwo k - 14 * rowThree k / 209 := by
  unfold transformedTwo rowTwo rowThree linearRow
  ring

def traceNumerator (k : ℕ) : ℝ := headForm (rowOne k) (rowTwo k) (rowThree k)

theorem traceNumerator_transformed (k : ℕ) :
    traceNumerator k =
      (223 / 320 : ℝ) * (transformedOne k) ^ 2 +
      (209 / 4460 : ℝ) * (transformedTwo k) ^ 2 +
      (2 / 5643 : ℝ) * (transformedThree k) ^ 2 := by
  unfold traceNumerator headForm transformedThree
  rw [transformedOne_exact, transformedTwo_exact]

theorem traceNumerator_nonneg (k : ℕ) : 0 ≤ traceNumerator k :=
  headForm_nonneg _ _ _

theorem traceNumerator_signed (k : ℕ) :
    traceNumerator k =
      (621 * (((k % 2 : ℕ) : ℝ) ^ 2) +
       48 * ((k % 2 : ℕ) : ℝ) * ((k % 3 : ℕ) : ℝ) -
       216 * ((k % 2 : ℕ) : ℝ) * ((k % 5 : ℕ) : ℝ) +
       176 * (((k % 3 : ℕ) : ℝ) ^ 2) -
       64 * ((k % 3 : ℕ) : ℝ) * ((k % 5 : ℕ) : ℝ) +
       24 * (((k % 5 : ℕ) : ℝ) ^ 2)) / 900 := by
  unfold traceNumerator headForm rowOne rowTwo rowThree linearRow
  ring

theorem residue_numerator_le (a b c : ℕ) (ha : a ≤ 1) (hb : b ≤ 2) (hc : c ≤ 4) :
    (621 * ((a : ℝ) ^ 2) + 48 * (a : ℝ) * (b : ℝ) -
      216 * (a : ℝ) * (c : ℝ) + 176 * ((b : ℝ) ^ 2) -
      64 * (b : ℝ) * (c : ℝ) + 24 * ((c : ℝ) ^ 2)) / 900 ≤ 1421 / 900 := by
  interval_cases a <;> interval_cases b <;> interval_cases c <;> norm_num

theorem traceNumerator_le (k : ℕ) : traceNumerator k ≤ (1421 / 900 : ℝ) := by
  rw [traceNumerator_signed]
  exact residue_numerator_le _ _ _ (by omega) (by omega) (by omega)

def traceTerm (k : ℕ) : ℝ :=
  traceNumerator k / ((k : ℝ) ^ 2 * gap (31 / 100) k)

theorem gap_five_pos (k : ℕ) (hk : 5 ≤ k) : 0 < gap (31 / 100) k := by
  have h := gap_lower (31 / 100) 5 k (by norm_num) hk
  norm_num [gap] at h ⊢
  linarith

theorem traceTerm_nonneg (k : ℕ) (hk : 5 ≤ k) : 0 ≤ traceTerm k :=
  div_nonneg (traceNumerator_nonneg k)
    (mul_nonneg (sq_nonneg _) (gap_five_pos k hk).le)

theorem traceTerm_le (K k : ℕ) (hK : 5 ≤ K) (hk : K ≤ k) :
    traceTerm k ≤ ((1421 / 900 : ℝ) / gap (31 / 100) K) / (k : ℝ) ^ 2 := by
  have hkr : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hg := gap_five_pos k (hK.trans hk)
  have hgK := gap_five_pos K hK
  have hmon := gap_lower (31 / 100) K k (by omega) hk
  unfold traceTerm
  calc
    _ ≤ (1421 / 900 : ℝ) / ((k : ℝ) ^ 2 * gap (31 / 100) k) :=
      div_le_div_of_nonneg_right (traceNumerator_le k) (by positivity)
    _ ≤ (1421 / 900 : ℝ) / ((k : ℝ) ^ 2 * gap (31 / 100) K) := by
      apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
      exact mul_le_mul_of_nonneg_left hmon (sq_nonneg _)
    _ = _ := by ring

theorem trace_summable : Summable (fun i : ℕ => traceTerm (i + 5)) := by
  have hs := ((summable_nat_add_iff 5).mpr
    (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < (2 : ℕ)))).mul_left
      ((1421 / 900 : ℝ) / gap (31 / 100) 5)
  apply Summable.of_nonneg_of_le (fun i => traceTerm_nonneg _ (by omega)) _ hs
  intro i
  simpa only [mul_one_div] using traceTerm_le 5 (i + 5) le_rfl (by omega)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
-- Expanding all 34 rational summands requires more arithmetic reduction steps.
theorem finite_trace_le : (∑ i : Fin 34, traceTerm (i.val + 5)) ≤ (17 / 20 : ℝ) := by
  norm_num [traceTerm, traceNumerator_signed, gap, Fin.sum_univ_succ]

/-- The terminal remainder is retained in the finite telescoping comparison. -/
theorem inverseSquare_tail_partial (M : ℕ) :
    (∑ i ∈ Finset.range M, 1 / ((i + 39 : ℕ) : ℝ) ^ 2) ≤
      1 / 38 - 1 / ((M : ℝ) + 38) := by
  induction M with
  | zero => norm_num
  | succ M ih =>
    rw [Finset.sum_range_succ]
    have hM : (0 : ℝ) < (M : ℝ) + 38 := by positivity
    have hM' : (0 : ℝ) < (M : ℝ) + 39 := by positivity
    have hstep : 1 / ((M : ℝ) + 39) ^ 2 ≤
        1 / ((M : ℝ) + 38) - 1 / ((M : ℝ) + 39) := by
      have he : 1 / ((M : ℝ) + 38) - 1 / ((M : ℝ) + 39) =
          1 / (((M : ℝ) + 38) * ((M : ℝ) + 39)) := by
        field_simp [ne_of_gt hM, ne_of_gt hM']
        ring
      rw [he]
      apply div_le_div_of_nonneg_left (by norm_num) (mul_pos hM hM')
      nlinarith [Nat.cast_nonneg (α := ℝ) M]
    push_cast at ih ⊢
    rw [show (M : ℝ) + 1 + 38 = (M : ℝ) + 39 by ring]
    linarith

theorem inverseSquare_tail_le :
    (∑' i : ℕ, 1 / ((i + 39 : ℕ) : ℝ) ^ 2) ≤ 1 / 38 := by
  have hs := (summable_nat_add_iff 39).mpr
    (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < (2 : ℕ)))
  apply le_of_tendsto' hs.hasSum.tendsto_sum_nat
  intro M
  exact (inverseSquare_tail_partial M).trans (sub_le_self _ (by positivity))

theorem complete_tail_le :
    (∑' i : ℕ, traceTerm (i + 39)) ≤ (18473 / 126426 : ℝ) := by
  have hs := (summable_nat_add_iff 34).mpr trace_summable
  simp only [Nat.add_assoc] at hs
  have hbase := (summable_nat_add_iff 39).mpr
    (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < (2 : ℕ)))
  have hC : 0 ≤ (1421 / 900 : ℝ) / gap (31 / 100) 39 := by norm_num [gap]
  calc
    _ ≤ ∑' i : ℕ, ((1421 / 900 : ℝ) / gap (31 / 100) 39) *
        (1 / ((i + 39 : ℕ) : ℝ) ^ 2) := by
      apply Summable.tsum_le_tsum _ hs (hbase.mul_left _)
      intro i
      simpa only [mul_one_div] using traceTerm_le 39 (i + 39) (by norm_num) (by omega)
    _ = _ * (∑' i : ℕ, 1 / ((i + 39 : ℕ) : ℝ) ^ 2) := by rw [tsum_mul_left]
    _ ≤ _ * (1 / 38) := mul_le_mul_of_nonneg_left inverseSquare_tail_le hC
    _ = _ := by norm_num [gap]

theorem complete_trace_le :
    (∑' i : ℕ, traceTerm (i + 5)) ≤ (1259351 / 1264260 : ℝ) := by
  have he := trace_summable.sum_add_tsum_nat_add 34
  rw [← Fin.sum_univ_eq_sum_range] at he
  simp only [Nat.add_assoc] at he
  linarith [finite_trace_le, complete_tail_le]

theorem complete_trace_cap_lt_one : (1259351 / 1264260 : ℝ) < 1 := by norm_num

end RiemannResearch.RH.ReciprocalRadicalFourCertificate
