import RiemannResearch.RH.ReciprocalHeadCertificate
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Complete infinite reciprocal head-tail certificates

Source: `RH/ReciprocalHeadCertificate20261008.md`, for the 34-site head,
complete positive arithmetic tail, and weighted Cauchy argument. The threshold
107/250 is an exact rational refinement of the same certificate. Computation
was used to choose it; all certificate inequalities below are proved in Lean.
These are complete series estimates, not an assumed operator bound.
-/

noncomputable section
open Filter
open scoped BigOperators Topology
namespace RiemannResearch.RH.ReciprocalInfiniteCertificate
open ReciprocalHeadCertificate

def gap (τ : ℝ) (k : ℕ) : ℝ := τ - 1 / (k : ℝ)

def finiteGram (τ : ℝ) (a b : ℕ → ℝ) : ℝ :=
  ∑ i : Fin 34, a (i.val + 3) * b (i.val + 3) /
    (((i.val + 3 : ℕ) : ℝ) ^ 2 * gap τ (i.val + 3))

def charge (τ : ℝ) (x y : ℝ) (k : ℕ) : ℝ :=
  Real.sqrt (1 - τ) * weightOne k * x +
    Real.sqrt ((1 / 2 - τ) / 4) * weightTwo k * y

def gramTerm (τ x y : ℝ) (k : ℕ) : ℝ :=
  (charge τ x y k) ^ 2 / ((k : ℝ) ^ 2 * gap τ k)

def tailTraceCap (τ : ℝ) : ℝ :=
  (3 / 2 - 2 * τ) / (36 * gap τ 37)

theorem gap_lower (τ : ℝ) (K k : ℕ) (hK : 0 < K) (hk : K ≤ k) :
    gap τ K ≤ gap τ k := by
  have hKR : (0 : ℝ) < K := by exact_mod_cast hK
  have hkk : (K : ℝ) ≤ k := by exact_mod_cast hk
  have h := div_le_div_of_nonneg_left (show (0 : ℝ) ≤ 1 by norm_num) hKR hkk
  unfold gap
  linarith

theorem gap_pos (τ : ℝ) (hτ : 1 / 3 < τ) (k : ℕ) (hk : 3 ≤ k) :
    0 < gap τ k := by
  have h := gap_lower τ 3 k (by norm_num) hk
  norm_num [gap] at h
  simp only [gap, one_div]
  linarith

/-- The finite telescoping comparison retains its terminal term. -/
theorem inverseSquare_tail_partial (M : ℕ) :
    (∑ i ∈ Finset.range M, 1 / ((i + 37 : ℕ) : ℝ) ^ 2) ≤
      1 / 36 - 1 / ((M : ℝ) + 36) := by
  induction M with
  | zero => norm_num
  | succ M ih =>
    rw [Finset.sum_range_succ]
    have hM : (0 : ℝ) < (M : ℝ) + 36 := by positivity
    have hM' : (0 : ℝ) < (M : ℝ) + 37 := by positivity
    have hstep : 1 / ((M : ℝ) + 37) ^ 2 ≤
        1 / ((M : ℝ) + 36) - 1 / ((M : ℝ) + 37) := by
      have he : 1 / ((M : ℝ) + 36) - 1 / ((M : ℝ) + 37) =
          1 / (((M : ℝ) + 36) * ((M : ℝ) + 37)) := by
        field_simp [ne_of_gt hM, ne_of_gt hM']
        ring
      rw [he]
      apply div_le_div_of_nonneg_left (by norm_num) (mul_pos hM hM')
      nlinarith [Nat.cast_nonneg (α := ℝ) M]
    push_cast at ih ⊢
    rw [show (M : ℝ) + 1 + 36 = (M : ℝ) + 37 by ring]
    linarith

theorem inverseSquare_tail_le :
    (∑' i : ℕ, 1 / ((i + 37 : ℕ) : ℝ) ^ 2) ≤ 1 / 36 := by
  have hs := (summable_nat_add_iff 37).mpr
    (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < (2 : ℕ)))
  apply le_of_tendsto' hs.hasSum.tendsto_sum_nat
  intro M
  exact (inverseSquare_tail_partial M).trans (sub_le_self _ (by positivity))

theorem residue_trace_le (τ : ℝ) (hτ : 1 / 3 < τ) (hτ' : τ < 1 / 2) (k : ℕ) :
    (1 - τ) * (weightOne k) ^ 2 +
      ((1 / 2 - τ) / 4) * (weightTwo k) ^ 2 ≤ 3 / 2 - 2 * τ := by
  have ha : k % 2 ≤ 1 := Nat.le_of_lt_succ (Nat.mod_lt _ (by norm_num))
  have hb : k % 3 ≤ 2 := Nat.le_of_lt_succ (Nat.mod_lt _ (by norm_num))
  unfold weightOne weightTwo
  generalize k % 2 = a at *
  generalize k % 3 = b at *
  interval_cases a <;> interval_cases b <;> norm_num at * <;> nlinarith

theorem charge_sq_le (τ x y : ℝ) (hτ : 1 / 3 < τ) (hτ' : τ < 1 / 2) (k : ℕ) :
    (charge τ x y k) ^ 2 ≤ (3 / 2 - 2 * τ) * (x ^ 2 + y ^ 2) := by
  have hp : 0 ≤ 1 - τ := by linarith
  have hq : 0 ≤ (1 / 2 - τ) / 4 := by linarith
  have hs1 := Real.sq_sqrt hp
  have hs2 := Real.sq_sqrt hq
  have htrace := mul_le_mul_of_nonneg_right (residue_trace_le τ hτ hτ' k)
    (add_nonneg (sq_nonneg x) (sq_nonneg y))
  have hsq := sq_nonneg
    (Real.sqrt (1 - τ) * weightOne k * y -
      Real.sqrt ((1 / 2 - τ) / 4) * weightTwo k * x)
  have he : (charge τ x y k) ^ 2 +
      (Real.sqrt (1 - τ) * weightOne k * y -
        Real.sqrt ((1 / 2 - τ) / 4) * weightTwo k * x) ^ 2 =
      ((1 - τ) * (weightOne k) ^ 2 + ((1 / 2 - τ) / 4) * (weightTwo k) ^ 2) *
        (x ^ 2 + y ^ 2) := by
    unfold charge
    simp only [add_sq, sub_sq, mul_pow, hs1, hs2]
    ring
  linarith

theorem gramTerm_le (τ x y : ℝ) (hτ : 1 / 3 < τ) (hτ' : τ < 1 / 2)
    (K k : ℕ) (hK : 3 ≤ K) (hk : K ≤ k) :
    gramTerm τ x y k ≤
      ((3 / 2 - 2 * τ) * (x ^ 2 + y ^ 2) / gap τ K) /
        (k : ℝ) ^ 2 := by
  have hk3 : 3 ≤ k := hK.trans hk
  have hkR : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hR : 0 ≤ 3 / 2 - 2 * τ := by linarith
  have hg := gap_pos τ hτ k hk3
  have hgK := gap_pos τ hτ K hK
  have hmon := gap_lower τ K k (by omega) hk
  unfold gramTerm
  calc
    _ ≤ ((3 / 2 - 2 * τ) * (x ^ 2 + y ^ 2)) /
        ((k : ℝ) ^ 2 * gap τ k) :=
      div_le_div_of_nonneg_right (charge_sq_le τ x y hτ hτ' k) (by positivity)
    _ ≤ ((3 / 2 - 2 * τ) * (x ^ 2 + y ^ 2)) /
        ((k : ℝ) ^ 2 * gap τ K) := by
      apply div_le_div_of_nonneg_left (by positivity) (by positivity)
      exact mul_le_mul_of_nonneg_left hmon (sq_nonneg _)
    _ = _ := by ring

theorem gram_summable (τ x y : ℝ) (hτ : 1 / 3 < τ) (hτ' : τ < 1 / 2) :
    Summable (fun i : ℕ => gramTerm τ x y (i + 3)) := by
  have hs := ((summable_nat_add_iff 3).mpr
    (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < (2 : ℕ)))).mul_left
      ((3 / 2 - 2 * τ) * (x ^ 2 + y ^ 2) / gap τ 3)
  apply Summable.of_nonneg_of_le
    (fun i => div_nonneg (sq_nonneg _) (by
      exact mul_nonneg (sq_nonneg _) (gap_pos τ hτ (i + 3) (by omega)).le))
    _ hs
  intro i
  simpa only [gramTerm, mul_one_div] using gramTerm_le τ x y hτ hτ' 3 (i + 3) le_rfl (by omega)

/-- Every residue channel in the infinite tail from site 37 is retained. -/
theorem complete_tail_le (τ x y : ℝ) (hτ : 1 / 3 < τ) (hτ' : τ < 1 / 2) :
    (∑' i : ℕ, gramTerm τ x y (i + 37)) ≤ tailTraceCap τ * (x ^ 2 + y ^ 2) := by
  have hs := (summable_nat_add_iff 34).mpr (gram_summable τ x y hτ hτ')
  simp only [Nat.add_assoc] at hs
  have hbase := (summable_nat_add_iff 37).mpr
    (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < (2 : ℕ)))
  have hg37 := gap_pos τ hτ 37 (by norm_num)
  have hR : 0 ≤ 3 / 2 - 2 * τ := by linarith
  have hC : 0 ≤ (3 / 2 - 2 * τ) * (x ^ 2 + y ^ 2) / gap τ 37 := by positivity
  calc
    _ ≤ ∑' i : ℕ, ((3 / 2 - 2 * τ) * (x ^ 2 + y ^ 2) / gap τ 37) *
        (1 / ((i + 37 : ℕ) : ℝ) ^ 2) := by
      apply Summable.tsum_le_tsum _ hs (hbase.mul_left _)
      intro i
      simpa only [mul_one_div] using gramTerm_le τ x y hτ hτ' 37 (i + 37)
        (by norm_num) (by omega)
    _ = _ * (∑' i : ℕ, 1 / ((i + 37 : ℕ) : ℝ) ^ 2) := by rw [tsum_mul_left]
    _ ≤ _ * (1 / 36) := mul_le_mul_of_nonneg_left inverseSquare_tail_le hC
    _ = _ := by unfold tailTraceCap; ring

theorem finite_head_exact (τ x y : ℝ) (hτ' : τ < 1 / 2) :
    (∑ i : Fin 34, gramTerm τ x y (i.val + 3)) =
      ((1 - τ) * finiteGram τ weightOne weightOne) * x ^ 2 +
      2 * (Real.sqrt (1 - τ) * Real.sqrt ((1 / 2 - τ) / 4) *
        finiteGram τ weightOne weightTwo) * x * y +
      (((1 / 2 - τ) / 4) * finiteGram τ weightTwo weightTwo) * y ^ 2 := by
  have hs1 := Real.sq_sqrt (show 0 ≤ 1 - τ by linarith)
  have hs2 := Real.sq_sqrt (show 0 ≤ (1 / 2 - τ) / 4 by linarith)
  have hterm (k : ℕ) : gramTerm τ x y k =
      (1 - τ) * x ^ 2 * (weightOne k * weightOne k / ((k : ℝ) ^ 2 * gap τ k)) +
      (2 * (Real.sqrt (1 - τ) * Real.sqrt ((1 / 2 - τ) / 4)) * x * y) *
        (weightOne k * weightTwo k / ((k : ℝ) ^ 2 * gap τ k)) +
      ((1 / 2 - τ) / 4) * y ^ 2 *
        (weightTwo k * weightTwo k / ((k : ℝ) ^ 2 * gap τ k)) := by
    unfold gramTerm charge
    simp only [add_sq, mul_pow, hs1, hs2]
    ring
  simp_rw [hterm]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
  unfold finiteGram
  ring

/-- The signed head cross term is estimated only after the complete equality. -/
theorem complete_gram_le (τ A B α β Λ x y : ℝ)
    (hτ : 1 / 3 < τ) (hτ' : τ < 1 / 2) (hα : 0 < α)
    (h11 : (1 - τ) * finiteGram τ weightOne weightOne ≤ A)
    (h22 : ((1 / 2 - τ) / 4) * finiteGram τ weightTwo weightTwo ≤ B)
    (h12 : (1 - τ) * ((1 / 2 - τ) / 4) *
      (finiteGram τ weightOne weightTwo) ^ 2 ≤ α * β)
    (hA : A + α + tailTraceCap τ ≤ Λ) (hB : B + β + tailTraceCap τ ≤ Λ) :
    (∑' i : ℕ, gramTerm τ x y (i + 3)) ≤ Λ * (x ^ 2 + y ^ 2) := by
  let c := Real.sqrt (1 - τ) * Real.sqrt ((1 / 2 - τ) / 4) *
    finiteGram τ weightOne weightTwo
  have hc : c ^ 2 ≤ α * β := by
    dsimp [c]
    simpa only [mul_pow, Real.sq_sqrt (show 0 ≤ 1 - τ by linarith),
      Real.sq_sqrt (show 0 ≤ (1 / 2 - τ) / 4 by linarith)] using h12
  have hcy := mul_le_mul_of_nonneg_right hc (sq_nonneg y)
  have hcross : 2 * c * x * y ≤ α * x ^ 2 + β * y ^ 2 := by
    have hsq := sq_nonneg (α * x - c * y)
    have hpos : 0 ≤ α * (α * x ^ 2 + β * y ^ 2 - 2 * c * x * y) := by nlinarith
    have h := (mul_nonneg_iff_of_pos_left hα).mp hpos
    linarith
  have hsplit := (gram_summable τ x y hτ hτ').sum_add_tsum_nat_add 34
  rw [← Fin.sum_univ_eq_sum_range] at hsplit
  simp only [Nat.add_assoc] at hsplit
  rw [finite_head_exact τ x y hτ'] at hsplit
  have ht := complete_tail_le τ x y hτ hτ'
  have hAx := mul_le_mul_of_nonneg_right h11 (sq_nonneg x)
  have hBy := mul_le_mul_of_nonneg_right h22 (sq_nonneg y)
  have hAx' := mul_le_mul_of_nonneg_right hA (sq_nonneg x)
  have hBy' := mul_le_mul_of_nonneg_right hB (sq_nonneg y)
  dsimp [c] at hcross
  nlinarith

theorem original_complete_gram_le (x y : ℝ) :
    (∑' i : ℕ, gramTerm (3 / 7) x y (i + 3)) ≤
      (4137 / 4160 : ℝ) * (x ^ 2 + y ^ 2) := by
  apply complete_gram_le (3 / 7) (89 / 100) (4 / 25) (3 / 50) (7 / 10)
    (4137 / 4160) x y (by norm_num) (by norm_num) (by norm_num)
  · have he : finiteGram (3 / 7) weightOne weightOne = headGram11 := by
      simp only [finiteGram, gap, headGram11, pow_two]
    rw [he]
    nlinarith [normalized_head11_le]
  · have he : finiteGram (3 / 7) weightTwo weightTwo = headGram22 := by
      simp only [finiteGram, gap, headGram22, pow_two]
    rw [he]
    nlinarith [normalized_head22_le]
  · have he : finiteGram (3 / 7) weightOne weightTwo = headGram12 := rfl
    rw [he]
    nlinarith [normalized_head12_sq_le]
  · norm_num [tailTraceCap, gap]
  · norm_num [tailTraceCap, gap]

set_option maxRecDepth 4096 in
theorem sharper_head11_le :
    (1 - (107 / 250 : ℝ)) * finiteGram (107 / 250) weightOne weightOne ≤ 223 / 250 := by
  norm_num [finiteGram, gap, weightOne, Fin.sum_univ_succ]

set_option maxRecDepth 4096 in
theorem sharper_head22_le :
    ((1 / 2 - (107 / 250 : ℝ)) / 4) *
      finiteGram (107 / 250) weightTwo weightTwo ≤ 157 / 1000 := by
  norm_num [finiteGram, gap, weightTwo, Fin.sum_univ_succ]

set_option maxRecDepth 4096 in
theorem sharper_head12_sq_le :
    (1 - (107 / 250 : ℝ)) * ((1 / 2 - (107 / 250 : ℝ)) / 4) *
      (finiteGram (107 / 250) weightOne weightTwo) ^ 2 ≤ 43 / 1000 := by
  norm_num [finiteGram, gap, weightOne, weightTwo, Fin.sum_univ_succ]

theorem sharper_complete_gram_le (x y : ℝ) :
    (∑' i : ℕ, gramTerm (107 / 250) x y (i + 3)) ≤
      (33101057 / 33381000 : ℝ) * (x ^ 2 + y ^ 2) := by
  apply complete_gram_le (107 / 250) (223 / 250) (157 / 1000) (11 / 200) (43 / 55)
    (33101057 / 33381000) x y (by norm_num) (by norm_num) (by norm_num)
  · exact sharper_head11_le
  · exact sharper_head22_le
  · convert sharper_head12_sq_le using 1
    norm_num
  · norm_num [tailTraceCap, gap]
  · norm_num [tailTraceCap, gap]


end RiemannResearch.RH.ReciprocalInfiniteCertificate
