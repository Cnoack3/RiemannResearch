import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp

/-!
# A continuous primitive from a discretely dilation-invariant sequence

Source: user-provided argument in
`RH_Iff_Two_Seed_Approximation_20260914.md`, the multiplicative rigidity lemma.
The formal proof uses finite prefix averages in place of the note's local
`L²` interpolation. It constructs the actual limiting primitive, proves a
quantitative Hölder estimate, and derives its exact two- and three-scaling
identities from the discrete hypotheses.
-/

namespace RiemannResearch.Analysis
open scoped BigOperators
open Filter
noncomputable section

def sequencePrefix (a : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ k ∈ Finset.range n, a k

def sequenceIncrement (a : ℕ → ℝ) (n : ℕ) : ℝ := a (n+1) - a n

theorem sequencePrefix_double (a : ℕ → ℝ)
    (h2 : ∀ n, a (2*n) = a n) (n : ℕ) :
    sequencePrefix a (2*n) = 2 * sequencePrefix a n +
      ∑ k ∈ Finset.range n, sequenceIncrement a (2*k) := by
  induction n with
  | zero => simp [sequencePrefix]
  | succ n ih =>
    have hidx : 2*(n+1) = 2*n+1+1 := by omega
    simp only [sequencePrefix, hidx, Finset.sum_range_succ] at *
    rw [ih]
    simp only [sequenceIncrement, h2]
    ring

theorem sequencePrefix_triple (a : ℕ → ℝ)
    (h3 : ∀ n, a (3*n) = a n) (n : ℕ) :
    sequencePrefix a (3*n) = 3 * sequencePrefix a n +
      ∑ k ∈ Finset.range n,
        (2 * sequenceIncrement a (3*k) + sequenceIncrement a (3*k+1)) := by
  induction n with
  | zero => simp [sequencePrefix]
  | succ n ih =>
    have hidx : 3*(n+1) = 3*n+1+1+1 := by omega
    simp only [sequencePrefix, hidx, Finset.sum_range_succ] at *
    rw [ih]
    simp only [sequenceIncrement, h3]
    ring

theorem sequencePrefix_sub_sq_le (a : ℕ → ℝ) (m n : ℕ) (hmn : m ≤ n) :
    (sequencePrefix a n - sequencePrefix a m)^2 ≤
      (n-m : ℕ) * ∑ k ∈ Finset.Ico m n, a k^2 := by
  unfold sequencePrefix
  rw [← Finset.sum_Ico_eq_sub a hmn]
  simpa using (sq_sum_le_card_mul_sum_sq (s := Finset.Ico m n) (f := a))

theorem sequencePrefix_sq_le (a : ℕ → ℝ) (n : ℕ) :
    (sequencePrefix a n)^2 ≤ (n : ℝ) * ∑ k ∈ Finset.range n, a k^2 := by
  simpa [sequencePrefix] using
    (sq_sum_le_card_mul_sum_sq (s := Finset.range n) (f := a))

theorem finite_sq_comp_le_tsum (b : ℕ → ℝ)
    (hb : Summable (fun n => b n^2)) (i : ℕ → ℕ)
    (hi : Function.Injective i) (s : Finset ℕ) :
    (∑ k ∈ s, b (i k)^2) ≤ ∑' n, b n^2 := by
  have hc := hb.comp_injective hi
  calc
    (∑ k ∈ s, b (i k)^2) ≤ ∑' k, b (i k)^2 := by
      exact Summable.sum_le_tsum s (fun k hk => sq_nonneg _) hc
    _ ≤ ∑' n, b n^2 := by
      exact tsum_comp_le_tsum_of_inj hb (fun n => sq_nonneg _) hi

theorem sequencePrefix_double_error_sq (a : ℕ → ℝ)
    (h2 : ∀ n, a (2*n) = a n)
    (hb : Summable (fun n => sequenceIncrement a n^2)) (n : ℕ) :
    (sequencePrefix a (2*n) - 2 * sequencePrefix a n)^2 ≤
      (n : ℝ) * ∑' k, sequenceIncrement a k^2 := by
  rw [sequencePrefix_double a h2 n]
  simp only [add_sub_cancel_left]
  apply (sq_sum_le_card_mul_sum_sq
    (s := Finset.range n) (f := fun k => sequenceIncrement a (2*k))).trans
  simp only [Finset.card_range]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  exact finite_sq_comp_le_tsum (sequenceIncrement a) hb (fun k => 2*k)
    (by intro k l h; dsimp at h; omega) (Finset.range n)

theorem sequencePrefix_triple_error_sq (a : ℕ → ℝ)
    (h3 : ∀ n, a (3*n) = a n)
    (hb : Summable (fun n => sequenceIncrement a n^2)) (n : ℕ) :
    (sequencePrefix a (3*n) - 3 * sequencePrefix a n)^2 ≤
      10 * (n : ℝ) * ∑' k, sequenceIncrement a k^2 := by
  rw [sequencePrefix_triple a h3 n]
  simp only [add_sub_cancel_left]
  have h0 := finite_sq_comp_le_tsum (sequenceIncrement a) hb (fun k => 3*k)
    (by intro k l h; dsimp at h; omega) (Finset.range n)
  have h1 := finite_sq_comp_le_tsum (sequenceIncrement a) hb (fun k => 3*k+1)
    (by intro k l h; dsimp at h; omega) (Finset.range n)
  have hsum : (∑ k ∈ Finset.range n,
      (2*sequenceIncrement a (3*k)+sequenceIncrement a (3*k+1))^2) ≤
        10 * ∑' k, sequenceIncrement a k^2 := by
    calc
      _ ≤ ∑ k ∈ Finset.range n,
          (8*sequenceIncrement a (3*k)^2+2*sequenceIncrement a (3*k+1)^2) := by
        apply Finset.sum_le_sum
        intro k hk
        have hh := add_sq_le (a := 2*sequenceIncrement a (3*k))
          (b := sequenceIncrement a (3*k+1))
        nlinarith
      _ = 8*(∑ k ∈ Finset.range n, sequenceIncrement a (3*k)^2) +
          2*(∑ k ∈ Finset.range n, sequenceIncrement a (3*k+1)^2) := by
        simp only [Finset.sum_add_distrib, Finset.mul_sum]
      _ ≤ 10 * ∑' k, sequenceIncrement a k^2 := by linarith
  apply (sq_sum_le_card_mul_sum_sq (s := Finset.range n)
    (f := fun k => 2*sequenceIncrement a (3*k)+sequenceIncrement a (3*k+1))).trans
  simp only [Finset.card_range]
  have hh := mul_le_mul_of_nonneg_left hsum (by positivity : 0 ≤ (n : ℝ))
  nlinarith

theorem sequence_sq_le_cesaro (a : ℕ → ℝ) {C : ℝ}
    (hC : ∀ N, ∑ k ∈ Finset.range N, a k^2 ≤ C * N) (n : ℕ) :
    a n^2 ≤ C * (n+1 : ℕ) := by
  have hsingle : a n^2 ≤ ∑ k ∈ Finset.range (n+1), a k^2 :=
    Finset.single_le_sum (fun k hk => sq_nonneg (a k)) (by simp)
  exact hsingle.trans (hC (n+1))

theorem sequencePrefix_sub_sq_le_cesaro (a : ℕ → ℝ) {C : ℝ}
    (hC : ∀ N, ∑ k ∈ Finset.range N, a k^2 ≤ C * N)
    (m n : ℕ) (hmn : m ≤ n) :
    (sequencePrefix a n - sequencePrefix a m)^2 ≤
      C * (n : ℝ) * (n-m : ℕ) := by
  apply (sequencePrefix_sub_sq_le a m n hmn).trans
  have hsum : ∑ k ∈ Finset.Ico m n, a k^2 ≤ C * n := by
    apply le_trans _ (hC n)
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro k hk
      exact Finset.mem_range.mpr (Finset.mem_Ico.mp hk).2
    · intro k hk hnot
      exact sq_nonneg _
  calc
    (n-m : ℕ) * ∑ k ∈ Finset.Ico m n, a k^2 ≤
      (n-m : ℕ) * (C*n) := mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = C * (n : ℝ) * (n-m : ℕ) := by ring

def dyadicPrefixPrimitive (a : ℕ → ℝ) (j : ℕ) (x : ℝ) : ℝ :=
  sequencePrefix a ⌊(2 : ℝ)^j * x⌋₊ / (2 : ℝ)^j

theorem dyadicPrefixPrimitive_increment_sq (a : ℕ → ℝ)
    (h2 : ∀ n, a (2*n) = a n)
    (hb : Summable (fun n => sequenceIncrement a n^2))
    {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ N, ∑ k ∈ Finset.range N, a k^2 ≤ C * N)
    (j : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    (dyadicPrefixPrimitive a (j+1) x - dyadicPrefixPrimitive a j x)^2 ≤
      ((∑' k, sequenceIncrement a k^2) + C) * (x+1) / (2 : ℝ)^j := by
  let q : ℝ := (2 : ℝ)^j
  let n := ⌊q*x⌋₊
  let N := ⌊(2 : ℝ)^(j+1)*x⌋₊
  let E : ℝ := ∑' k, sequenceIncrement a k^2
  have hq : 0 < q := by dsimp [q]; positivity
  have hq1 : 1 ≤ q := by
    simpa [q] using (one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2) : (1 : ℝ) ≤ 2^j)
  have hE : 0 ≤ E := tsum_nonneg (fun k => sq_nonneg _)
  have hn : (n : ℝ) ≤ q*x := Nat.floor_le (mul_nonneg hq.le hx)
  have hNdiv : N/2 = n := by
    dsimp [N, n, q]
    simpa [pow_succ, mul_assoc, mul_left_comm, mul_comm] using
      (Nat.cast_mul_floor_div_cancel (R := ℝ) (n := 2) (by norm_num)
        ((2 : ℝ)^j*x))
  have hNcases : N = 2*n ∨ N = 2*n+1 := by omega
  have herr := sequencePrefix_double_error_sq a h2 hb n
  have hpoint := sequence_sq_le_cesaro a hC n
  have hnum : (sequencePrefix a N - 2*sequencePrefix a n)^2 ≤
      2 * (E*(n : ℝ) + C*((n : ℝ)+1)) := by
    rcases hNcases with hN | hN
    · rw [hN]
      dsimp [E] at *
      have hnn : 0 ≤ (n : ℝ) := by positivity
      nlinarith [mul_nonneg hE hnn, mul_nonneg hC0 (by positivity : 0 ≤ (n : ℝ)+1)]
    · have heq : sequencePrefix a N - 2*sequencePrefix a n =
          (sequencePrefix a (2*n) - 2*sequencePrefix a n) + a n := by
        simp [hN, sequencePrefix, Finset.sum_range_succ, h2]
        ring
      rw [heq]
      have hadd := add_sq_le (a := sequencePrefix a (2*n) - 2*sequencePrefix a n)
        (b := a n)
      simp only [Nat.cast_add, Nat.cast_one] at hpoint
      dsimp [E] at *
      nlinarith
  have hmajor : E*(n : ℝ) + C*((n : ℝ)+1) ≤ q*((E+C)*(x+1)) := by
    have h1 := mul_le_mul_of_nonneg_left hn hE
    have h2' := mul_le_mul_of_nonneg_left hn hC0
    have h3' := mul_le_mul_of_nonneg_left hq1 hC0
    have h4' : 0 ≤ q*E := mul_nonneg hq.le hE
    nlinarith
  have heq : dyadicPrefixPrimitive a (j+1) x - dyadicPrefixPrimitive a j x =
      (sequencePrefix a N - 2*sequencePrefix a n) / (2*q) := by
    simp only [dyadicPrefixPrimitive]
    change sequencePrefix a N / (2 : ℝ)^(j+1) - sequencePrefix a n / q = _
    rw [pow_succ]
    change sequencePrefix a N / (q*2) - sequencePrefix a n / q = _
    field_simp [ne_of_gt hq]
    <;> ring
  rw [heq, div_pow]
  change _ ≤ (E+C)*(x+1)/q
  apply (div_le_iff₀ (sq_pos_of_pos (by positivity : 0 < 2*q))).2
  have hK : 0 ≤ (E+C)*(x+1) := by positivity
  have hcalc : ((E+C)*(x+1)/q) * (2*q)^2 = 4*q*((E+C)*(x+1)) := by
    field_simp [ne_of_gt hq]
    <;> ring
  rw [hcalc]
  nlinarith [mul_nonneg hq.le hK]

theorem dyadicPrefixPrimitive_holder (a : ℕ → ℝ) {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ N, ∑ k ∈ Finset.range N, a k^2 ≤ C * N)
    (j : ℕ) {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) :
    (dyadicPrefixPrimitive a j y - dyadicPrefixPrimitive a j x)^2 ≤
      C * y * (y-x + 1/(2 : ℝ)^j) := by
  have hy0 : 0 ≤ y := hx.trans hxy
  let q : ℝ := (2 : ℝ)^j
  let m := ⌊q*x⌋₊
  let n := ⌊q*y⌋₊
  have hq : 0 < q := by dsimp [q]; positivity
  have hm : (m : ℝ) ≤ q*x := Nat.floor_le (mul_nonneg hq.le hx)
  have hn : (n : ℝ) ≤ q*y := Nat.floor_le (mul_nonneg hq.le (hx.trans hxy))
  have hmlt : q*x < (m : ℝ)+1 := Nat.lt_floor_add_one (q*x)
  have hmn : m ≤ n := Nat.floor_mono (mul_le_mul_of_nonneg_left hxy hq.le)
  have hbase := sequencePrefix_sub_sq_le_cesaro a hC m n hmn
  have hnm : ((n-m : ℕ) : ℝ) = (n : ℝ)-(m : ℝ) := by
    rw [Nat.cast_sub hmn]
  have heq : dyadicPrefixPrimitive a j y - dyadicPrefixPrimitive a j x =
      (sequencePrefix a n - sequencePrefix a m) / q := by
    simp [dyadicPrefixPrimitive, m, n, q, sub_div]
  rw [heq, div_pow]
  apply (div_le_div_of_nonneg_right hbase (sq_nonneg q)).trans
  rw [hnm]
  have hdiff : (n : ℝ)-(m : ℝ) ≤ q*(y-x)+1 := by linarith
  have hnm0 : 0 ≤ (n : ℝ)-(m : ℝ) := sub_nonneg.mpr (by exact_mod_cast hmn)
  have hfactor : C*(n : ℝ)*((n : ℝ)-(m : ℝ)) ≤
      C*(q*y)*(q*(y-x)+1) := by
    apply mul_le_mul
    · exact mul_le_mul_of_nonneg_left hn hC0
    · exact hdiff
    · exact hnm0
    · positivity
  apply (div_le_div_of_nonneg_right hfactor (sq_nonneg q)).trans_eq
  field_simp [ne_of_gt hq]
  <;> ring

theorem cauchySeq_of_increment_sq_le_half_pow (u : ℕ → ℝ) {K : ℝ}
    (hK : 0 ≤ K)
    (hu : ∀ j, (u (j+1) - u j)^2 ≤ K/(2 : ℝ)^j) :
    CauchySeq u := by
  apply cauchySeq_of_dist_le_of_summable (fun j => (K+1)*(3/4 : ℝ)^j)
  · intro j
    rw [Real.dist_eq]
    have hp : 1/(2 : ℝ)^j ≤ ((3/4 : ℝ)^j)^2 := by
      calc
        1/(2 : ℝ)^j = (1/2 : ℝ)^j := by simp [div_pow]
        _ ≤ (9/16 : ℝ)^j := pow_le_pow_left₀ (by norm_num) (by norm_num) j
        _ = ((3/4 : ℝ)^2)^j := by norm_num
        _ = ((3/4 : ℝ)^j)^2 := by
          rw [← pow_mul, ← pow_mul]
          congr 1
          omega
    have hKK : K ≤ (K+1)^2 := by nlinarith
    have hs : |u j-u (j+1)|^2 ≤ ((K+1)*(3/4 : ℝ)^j)^2 := by
      have hs' : (u j-u (j+1))^2 = (u (j+1)-u j)^2 := by ring
      rw [sq_abs, hs', mul_pow]
      apply (hu j).trans
      calc
        K/(2 : ℝ)^j = K*(1/(2 : ℝ)^j) := by ring
        _ ≤ K*((3/4 : ℝ)^j)^2 := mul_le_mul_of_nonneg_left hp hK
        _ ≤ (K+1)^2*((3/4 : ℝ)^j)^2 :=
          mul_le_mul_of_nonneg_right hKK (sq_nonneg _)
    exact (sq_le_sq₀ (abs_nonneg _) (by positivity)).mp hs
  · exact (summable_geometric_of_abs_lt_one (by norm_num : |(3/4 : ℝ)| < 1)).mul_left _

def prefixPrimitiveLimit (a : ℕ → ℝ) (x : ℝ) : ℝ :=
  limUnder atTop (fun j => dyadicPrefixPrimitive a j x)

theorem dyadicPrefixPrimitive_tendsto (a : ℕ → ℝ)
    (h2 : ∀ n, a (2*n) = a n)
    (hb : Summable (fun n => sequenceIncrement a n^2))
    {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ N, ∑ k ∈ Finset.range N, a k^2 ≤ C * N)
    {x : ℝ} (hx : 0 ≤ x) :
    Tendsto (fun j => dyadicPrefixPrimitive a j x) atTop (nhds (prefixPrimitiveLimit a x)) := by
  apply tendsto_nhds_limUnder
  apply cauchySeq_tendsto_of_complete
  apply cauchySeq_of_increment_sq_le_half_pow
      (K := ((∑' k, sequenceIncrement a k^2)+C)*(x+1))
  · have he : 0 ≤ ∑' k, sequenceIncrement a k^2 := tsum_nonneg (fun k => sq_nonneg _)
    positivity
  · exact fun j => dyadicPrefixPrimitive_increment_sq a h2 hb hC0 hC j hx

theorem prefixPrimitiveLimit_holder (a : ℕ → ℝ)
    (h2 : ∀ n, a (2*n) = a n)
    (hb : Summable (fun n => sequenceIncrement a n^2))
    {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ N, ∑ k ∈ Finset.range N, a k^2 ≤ C * N)
    {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) :
    (prefixPrimitiveLimit a y - prefixPrimitiveLimit a x)^2 ≤ C*y*(y-x) := by
  have htx := dyadicPrefixPrimitive_tendsto a h2 hb hC0 hC hx
  have hty := dyadicPrefixPrimitive_tendsto a h2 hb hC0 hC (hx.trans hxy)
  have hz : Tendsto (fun j => 1/(2 : ℝ)^j) atTop (nhds 0) := by
    simpa only [div_pow, one_pow] using
      (tendsto_pow_atTop_nhds_zero_of_abs_lt_one (by norm_num : |(1/2 : ℝ)| < 1))
  have hr : Tendsto (fun j => C*y*(y-x + 1/(2 : ℝ)^j)) atTop
      (nhds (C*y*(y-x))) := by
    simpa using tendsto_const_nhds.mul (tendsto_const_nhds.add hz)
  exact le_of_tendsto_of_tendsto (hty.sub htx |>.pow 2) hr
    (Filter.Eventually.of_forall (fun j => dyadicPrefixPrimitive_holder a hC0 hC j hx hxy))

theorem dyadicPrefixPrimitive_double (a : ℕ → ℝ) (j : ℕ) (x : ℝ) :
    dyadicPrefixPrimitive a j (2*x) = 2*dyadicPrefixPrimitive a (j+1) x := by
  unfold dyadicPrefixPrimitive
  have harg : (2 : ℝ)^j*(2*x) = (2 : ℝ)^(j+1)*x := by rw [pow_succ]; ring
  rw [harg]
  have hp : (2 : ℝ)^j ≠ 0 := by positivity
  rw [pow_succ]
  field_simp
  <;> ring

theorem prefixPrimitiveLimit_double (a : ℕ → ℝ)
    (h2 : ∀ n, a (2*n) = a n)
    (hb : Summable (fun n => sequenceIncrement a n^2))
    {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ N, ∑ k ∈ Finset.range N, a k^2 ≤ C * N)
    {x : ℝ} (hx : 0 ≤ x) :
    prefixPrimitiveLimit a (2*x) = 2*prefixPrimitiveLimit a x := by
  have hleft := dyadicPrefixPrimitive_tendsto a h2 hb hC0 hC
    (by positivity : 0 ≤ 2*x)
  have hright : Tendsto (fun j => dyadicPrefixPrimitive a j (2*x)) atTop
      (nhds (2*prefixPrimitiveLimit a x)) := by
    simp_rw [dyadicPrefixPrimitive_double]
    exact tendsto_const_nhds.mul
      ((dyadicPrefixPrimitive_tendsto a h2 hb hC0 hC hx).comp (tendsto_add_atTop_nat 1))
  exact tendsto_nhds_unique hleft hright

theorem dyadicPrefixPrimitive_triple_error_sq (a : ℕ → ℝ)
    (h3 : ∀ n, a (3*n) = a n)
    (hb : Summable (fun n => sequenceIncrement a n^2))
    {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ N, ∑ k ∈ Finset.range N, a k^2 ≤ C * N)
    (j : ℕ) {x : ℝ} (hx : 0 ≤ x) :
    (dyadicPrefixPrimitive a j (3*x) - 3*dyadicPrefixPrimitive a j x)^2 ≤
      (12*C+20*(∑' k, sequenceIncrement a k^2))*x/(2 : ℝ)^j := by
  let q : ℝ := (2 : ℝ)^j
  let n := ⌊q*x⌋₊
  let N := ⌊q*(3*x)⌋₊
  let E : ℝ := ∑' k, sequenceIncrement a k^2
  have hq : 0 < q := by dsimp [q]; positivity
  have hE : 0 ≤ E := tsum_nonneg (fun k => sq_nonneg _)
  have hn : (n : ℝ) ≤ q*x := Nat.floor_le (mul_nonneg hq.le hx)
  have hN : (N : ℝ) ≤ q*(3*x) := Nat.floor_le (by positivity)
  have hNdiv : N/3 = n := by
    dsimp [N, n]
    simpa [mul_assoc, mul_left_comm, mul_comm] using
      (Nat.cast_mul_floor_div_cancel (R := ℝ) (n := 3) (by norm_num) (q*x))
  have hNlo : 3*n ≤ N := by omega
  have hNhi : N-3*n ≤ 2 := by omega
  have hboundary := sequencePrefix_sub_sq_le_cesaro a hC (3*n) N hNlo
  have hbn : (sequencePrefix a N-sequencePrefix a (3*n))^2 ≤ 2*C*(N : ℝ) := by
    have hnh : ((N-3*n : ℕ) : ℝ) ≤ 2 := by exact_mod_cast hNhi
    have hh := mul_le_mul_of_nonneg_left hnh (by positivity : 0 ≤ C*(N : ℝ))
    nlinarith
  have htriple := sequencePrefix_triple_error_sq a h3 hb n
  have heq : sequencePrefix a N - 3*sequencePrefix a n =
      (sequencePrefix a N-sequencePrefix a (3*n)) +
      (sequencePrefix a (3*n)-3*sequencePrefix a n) := by ring
  have hnum : (sequencePrefix a N - 3*sequencePrefix a n)^2 ≤
      q*((12*C+20*E)*x) := by
    rw [heq]
    have hadd := add_sq_le (a := sequencePrefix a N-sequencePrefix a (3*n))
      (b := sequencePrefix a (3*n)-3*sequencePrefix a n)
    have h1 := mul_le_mul_of_nonneg_left hN (by positivity : 0 ≤ 4*C)
    have h2' := mul_le_mul_of_nonneg_left hn (by positivity : 0 ≤ 20*E)
    dsimp [E] at *
    nlinarith
  have hprim : dyadicPrefixPrimitive a j (3*x) - 3*dyadicPrefixPrimitive a j x =
      (sequencePrefix a N - 3*sequencePrefix a n)/q := by
    dsimp [dyadicPrefixPrimitive, N, n, q]
    ring
  rw [hprim, div_pow]
  apply (div_le_div_of_nonneg_right hnum (sq_nonneg q)).trans_eq
  change q*((12*C+20*E)*x)/q^2 = (12*C+20*E)*x/q
  field_simp [ne_of_gt hq]
  <;> ring

theorem prefixPrimitiveLimit_triple (a : ℕ → ℝ)
    (h2 : ∀ n, a (2*n) = a n) (h3 : ∀ n, a (3*n) = a n)
    (hb : Summable (fun n => sequenceIncrement a n^2))
    {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ N, ∑ k ∈ Finset.range N, a k^2 ≤ C * N)
    {x : ℝ} (hx : 0 ≤ x) :
    prefixPrimitiveLimit a (3*x) = 3*prefixPrimitiveLimit a x := by
  have htx := dyadicPrefixPrimitive_tendsto a h2 hb hC0 hC hx
  have ht3x := dyadicPrefixPrimitive_tendsto a h2 hb hC0 hC
    (by positivity : 0 ≤ 3*x)
  have hz : Tendsto (fun j => 1/(2 : ℝ)^j) atTop (nhds 0) := by
    simpa only [div_pow, one_pow] using
      (tendsto_pow_atTop_nhds_zero_of_abs_lt_one (by norm_num : |(1/2 : ℝ)| < 1))
  have hr : Tendsto (fun j => (12*C+20*(∑' k, sequenceIncrement a k^2))*x/(2 : ℝ)^j)
      atTop (nhds 0) := by
    simpa [div_eq_mul_inv] using
      tendsto_const_nhds.mul hz
  have hs : (prefixPrimitiveLimit a (3*x)-3*prefixPrimitiveLimit a x)^2 ≤ 0 :=
    le_of_tendsto_of_tendsto ((ht3x.sub (tendsto_const_nhds.mul htx)).pow 2) hr
      (Filter.Eventually.of_forall (fun j =>
        dyadicPrefixPrimitive_triple_error_sq a h3 hb hC0 hC j hx))
  nlinarith [sq_nonneg (prefixPrimitiveLimit a (3*x)-3*prefixPrimitiveLimit a x)]

end
end RiemannResearch.Analysis
