import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# A discrete Hardy estimate with the terminal boundary retained

Source: user-provided argument, Section 25.5 of
`RH_First_Coordinate_and_Tail_Capacity_Continuation_2026-09-19.md`.
The finite proof uses square completion. The infinite theorem requires the
weighted terminal square to vanish; its Pareto application supplies this from
the actual weighted Hilbert norm in `ParetoSignedTailRegularity`.
-/

noncomputable section
open scoped BigOperators
open Filter

namespace RiemannResearch.Analysis.DiscreteTailHardy

/-- Finite Hardy estimate; no summability or asymptotic hypothesis is hidden. -/
theorem prefix_le_with_boundary (a q : ℕ → ℝ)
    (hq : ∀ n, 0 ≤ q n)
    (hd : ∀ n : ℕ, 0 < n →
      (n : ℝ) ^ 2 * (a n - a (n + 1)) ^ 2 ≤ q n) (N : ℕ) :
    (∑ k ∈ Finset.range N, a (k + 1) ^ 2) ≤
      4 * (∑ k ∈ Finset.range (N + 1), q k) +
        (2 * (N : ℝ) + 1 / 2) * a (N + 1) ^ 2 := by
  induction N with
  | zero =>
      have hq0 := hq 0
      simp only [Finset.sum_range_zero, zero_add, Finset.sum_range_one,
        Nat.cast_zero, mul_zero]
      positivity
  | succ N ih =>
      have hdN := hd (N + 1) (Nat.succ_pos N)
      have hsquare := sq_nonneg
        (2 * ((N : ℝ) + 1) * (a (N + 1) - a (N + 1 + 1)) -
          (a (N + 1) + a (N + 1 + 1)) / 2)
      have hsquare' := sq_nonneg (a (N + 1) - a (N + 1 + 1))
      have hstep :
          (2 * (N : ℝ) + 3 / 2) * a (N + 1) ^ 2 ≤
            4 * q (N + 1) +
              (2 * (N : ℝ) + 5 / 2) * a (N + 1 + 1) ^ 2 := by
        push_cast at hdN
        nlinarith
      change (∑ k ∈ Finset.range (N + 1), a (k + 1) ^ 2) ≤
        4 * (∑ k ∈ Finset.range (N + 1 + 1), q k) +
          (2 * ((N + 1 : ℕ) : ℝ) + 1 / 2) * a (N + 1 + 1) ^ 2
      rw [Finset.sum_range_succ, Finset.sum_range_succ (f := q)]
      push_cast
      nlinarith

/-- Passing to a vanishing terminal boundary gives a uniform prefix bound. -/
theorem prefix_le (a q : ℕ → ℝ) (hqs : Summable q)
    (hq : ∀ n, 0 ≤ q n)
    (hd : ∀ n : ℕ, 0 < n →
      (n : ℝ) ^ 2 * (a n - a (n + 1)) ^ 2 ≤ q n)
    (hb : Tendsto (fun n : ℕ => (n : ℝ) * a n ^ 2) atTop (nhds 0))
    (N : ℕ) :
    (∑ k ∈ Finset.range N, a (k + 1) ^ 2) ≤ 4 * ∑' k, q k := by
  have hlim : Tendsto
      (fun M : ℕ => 4 * (∑' k, q k) +
        2 * (((M + 1 : ℕ) : ℝ) * a (M + 1) ^ 2))
      atTop (nhds (4 * ∑' k, q k)) := by
    simpa only [Function.comp_def, mul_zero, add_zero] using
      (tendsto_const_nhds.add ((hb.comp (tendsto_add_atTop_nat 1)).const_mul 2))
  apply le_of_tendsto_of_tendsto tendsto_const_nhds hlim
  filter_upwards [eventually_ge_atTop N] with M hNM
  have hmono : (∑ k ∈ Finset.range N, a (k + 1) ^ 2) ≤
      ∑ k ∈ Finset.range M, a (k + 1) ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hNM)
      (fun k _ _ => sq_nonneg _)
  have hfinite := prefix_le_with_boundary a q hq hd M
  have hsum := hqs.sum_le_tsum (Finset.range (M + 1)) (fun k _ => hq k)
  have hsq := sq_nonneg (a (M + 1))
  push_cast
  nlinarith

/-- Weighted discrete derivative control and a vanishing boundary imply l². -/
theorem positive_square_summable (a q : ℕ → ℝ) (hqs : Summable q)
    (hq : ∀ n, 0 ≤ q n)
    (hd : ∀ n : ℕ, 0 < n →
      (n : ℝ) ^ 2 * (a n - a (n + 1)) ^ 2 ≤ q n)
    (hb : Tendsto (fun n : ℕ => (n : ℝ) * a n ^ 2) atTop (nhds 0)) :
    Summable (fun k => a (k + 1) ^ 2) :=
  summable_of_sum_range_le (fun k => sq_nonneg _)
    (prefix_le a q hqs hq hd hb)

/-- The full Hardy bound on all positive coordinates, with constant four. -/
theorem positive_square_tsum_le (a q : ℕ → ℝ) (hqs : Summable q)
    (hq : ∀ n, 0 ≤ q n)
    (hd : ∀ n : ℕ, 0 < n →
      (n : ℝ) ^ 2 * (a n - a (n + 1)) ^ 2 ≤ q n)
    (hb : Tendsto (fun n : ℕ => (n : ℝ) * a n ^ 2) atTop (nhds 0)) :
    (∑' k, a (k + 1) ^ 2) ≤ 4 * ∑' k, q k := by
  apply le_of_tendsto (positive_square_summable a q hqs hq hd hb).hasSum.tendsto_sum_nat
  exact Filter.Eventually.of_forall (prefix_le a q hqs hq hd hb)

/-- Weighted telescoping, before dropping the endpoint. -/
theorem weighted_square_difference_sum (t : ℕ → ℝ) (M : ℕ) :
    (∑ n ∈ Finset.range M,
      ((n : ℝ) + 1) * (t n ^ 2 - t (n + 1) ^ 2)) =
      (∑ n ∈ Finset.range M, t n ^ 2) - (M : ℝ) * t M ^ 2 := by
  induction M with
  | zero => simp
  | succ M ih =>
    simp only [Finset.sum_range_succ, Nat.cast_add, Nat.cast_one]
    rw [ih]
    ring

/-- Finite dual Hardy estimate in recurrence form. For the standard tails,
`t n - t (n+1) = a n / (n+2)`, the weighted decrement condition follows
from `(n+1)/(n+2) ≤ 1`. All endpoint terms are explicit. -/
theorem tail_recurrence_energy_le_four (a t : ℕ → ℝ) (M : ℕ)
    (ha : ∀ n < M, 0 ≤ a n)
    (ht : ∀ n ≤ M, 0 ≤ t n)
    (hmono : ∀ n < M, t (n + 1) ≤ t n)
    (hdec : ∀ n < M, ((n : ℝ) + 1) * (t n - t (n + 1)) ≤ a n)
    (hend : t M = 0) :
    (∑ n ∈ Finset.range M, t n ^ 2) ≤
      4 * ∑ n ∈ Finset.range M, a n ^ 2 := by
  let S : ℝ := ∑ n ∈ Finset.range M, t n ^ 2
  let A : ℝ := ∑ n ∈ Finset.range M, a n ^ 2
  let C : ℝ := ∑ n ∈ Finset.range M, a n * t n
  have hS : 0 ≤ S := Finset.sum_nonneg (fun n hn => sq_nonneg _)
  have hA : 0 ≤ A := Finset.sum_nonneg (fun n hn => sq_nonneg _)
  have hC : 0 ≤ C := by
    apply Finset.sum_nonneg
    intro n hn
    have hnM := Finset.mem_range.mp hn
    exact mul_nonneg (ha n hnM) (ht n hnM.le)
  have hid : S = ∑ n ∈ Finset.range M,
      ((n : ℝ) + 1) * (t n ^ 2 - t (n + 1) ^ 2) := by
    rw [weighted_square_difference_sum, hend]
    simp [S]
  have hbound : S ≤ 2 * C := by
    rw [hid]
    calc
      _ ≤ ∑ n ∈ Finset.range M, 2 * (a n * t n) := by
        apply Finset.sum_le_sum
        intro n hn
        have hnM := Finset.mem_range.mp hn
        have ht0 := ht n hnM.le
        have hstep := hmono n hnM
        have hweight : 0 ≤ ((n : ℝ) + 1) * (t n - t (n + 1)) :=
          mul_nonneg (by positivity) (sub_nonneg.mpr hstep)
        have hprod := mul_le_mul_of_nonneg_left hstep hweight
        have hlast := mul_le_mul_of_nonneg_right (hdec n hnM) ht0
        nlinarith
      _ = 2 * C := by rw [Finset.mul_sum]
  have hcs : C ^ 2 ≤ A * S := by
    simpa only [C, A, S] using
      Finset.sum_mul_sq_le_sq_mul_sq (Finset.range M) a t
  have hsq := mul_self_le_mul_self hS hbound
  change S ≤ 4 * A
  by_cases hzero : S = 0
  · rw [hzero]
    positivity
  · have hpos : 0 < S := lt_of_le_of_ne hS (Ne.symm hzero)
    nlinarith


def truncatedTail (a : ℕ → ℝ) (M d : ℕ) : ℝ :=
  ∑ n ∈ Finset.range M, if d ≤ n then a n / ((n : ℝ) + 2) else 0

theorem truncatedTail_nonneg (a : ℕ → ℝ) (M d : ℕ)
    (ha : ∀ n < M, 0 ≤ a n) : 0 ≤ truncatedTail a M d := by
  apply Finset.sum_nonneg
  intro n hn
  split_ifs
  · exact div_nonneg (ha n (Finset.mem_range.mp hn)) (by positivity)
  · exact le_rfl

theorem truncatedTail_end (a : ℕ → ℝ) (M : ℕ) : truncatedTail a M M = 0 := by
  apply Finset.sum_eq_zero
  intro n hn
  exact if_neg (by have := Finset.mem_range.mp hn; omega)

theorem truncatedTail_step (a : ℕ → ℝ) (M d : ℕ) (hd : d < M) :
    truncatedTail a M d = truncatedTail a M (d + 1) + a d / ((d : ℝ) + 2) := by
  have hp (n : ℕ) :
      (if d ≤ n then a n / ((n : ℝ) + 2) else 0) =
      (if d + 1 ≤ n then a n / ((n : ℝ) + 2) else 0) +
        (if n = d then a n / ((n : ℝ) + 2) else 0) := by
    by_cases he : n = d
    · subst n; simp
    · by_cases hn : d ≤ n
      · have hs : d + 1 ≤ n := by omega
        simp [hn, hs, he]
      · have hs : ¬d + 1 ≤ n := by omega
        simp [hn, hs, he]
  unfold truncatedTail
  simp_rw [hp]
  rw [Finset.sum_add_distrib]
  simp [Finset.mem_range.mpr hd]

theorem truncatedTail_energy_le_four (a : ℕ → ℝ) (M : ℕ)
    (ha : ∀ n < M, 0 ≤ a n) :
    (∑ d ∈ Finset.range M, truncatedTail a M d ^ 2) ≤
      4 * ∑ n ∈ Finset.range M, a n ^ 2 := by
  apply tail_recurrence_energy_le_four a (truncatedTail a M) M ha
  · intro d hd
    exact truncatedTail_nonneg a M d ha
  · intro d hd
    rw [truncatedTail_step a M d hd]
    exact le_add_of_nonneg_right (div_nonneg (ha d hd) (by positivity))
  · intro d hd
    rw [truncatedTail_step a M d hd]
    have had := ha d hd
    have hden : 0 < (d : ℝ) + 2 := by positivity
    have hid : ((d : ℝ) + 1) *
        (truncatedTail a M (d + 1) + a d / ((d : ℝ) + 2) -
          truncatedTail a M (d + 1)) =
        a d * (((d : ℝ) + 1) / ((d : ℝ) + 2)) := by ring
    rw [hid]
    have hratio : ((d : ℝ) + 1) / ((d : ℝ) + 2) ≤ 1 := by
      apply (div_le_iff₀ hden).mpr
      linarith
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hratio had
  · exact truncatedTail_end a M

/-- Finite triangular matrices dominated by the dual Hardy kernel have a
dimension-independent Euclidean norm bound. -/
theorem triangular_matrix_bessel (a : ℕ → ℝ) (K : ℕ → ℕ → ℝ)
    (M D : ℕ) (hDM : D ≤ M)
    (hzero : ∀ d n : ℕ, n < d → K d n = 0)
    (hbound : ∀ d n : ℕ, |K d n| ≤ 1 / ((n : ℝ) + 2)) :
    (∑ d ∈ Finset.range D,
      (∑ n ∈ Finset.range M, a n * K d n) ^ 2) ≤
      4 * ∑ n ∈ Finset.range M, a n ^ 2 := by
  have ha : ∀ n < M, 0 ≤ |a n| := fun n hn => abs_nonneg _
  have hpoint (d : ℕ) :
      |∑ n ∈ Finset.range M, a n * K d n| ≤ truncatedTail (fun n => |a n|) M d := by
    calc
      _ ≤ ∑ n ∈ Finset.range M, |a n * K d n| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro n hn
        by_cases hdn : d ≤ n
        · rw [if_pos hdn, abs_mul]
          simpa only [mul_one_div] using
            mul_le_mul_of_nonneg_left (hbound d n) (abs_nonneg (a n))
        · rw [if_neg hdn, hzero d n (Nat.lt_of_not_ge hdn), mul_zero, abs_zero]
  have hsquare (d : ℕ) :
      (∑ n ∈ Finset.range M, a n * K d n) ^ 2 ≤
        truncatedTail (fun n => |a n|) M d ^ 2 := by
    have hs := mul_self_le_mul_self
      (abs_nonneg (∑ n ∈ Finset.range M, a n * K d n)) (hpoint d)
    nlinarith [sq_abs (∑ n ∈ Finset.range M, a n * K d n)]
  calc
    _ ≤ ∑ d ∈ Finset.range D, truncatedTail (fun n => |a n|) M d ^ 2 :=
      Finset.sum_le_sum (fun d hd => hsquare d)
    _ ≤ ∑ d ∈ Finset.range M, truncatedTail (fun n => |a n|) M d ^ 2 := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hDM)
      intro d hd hdnot
      exact sq_nonneg _
    _ ≤ 4 * ∑ n ∈ Finset.range M, |a n| ^ 2 :=
      truncatedTail_energy_le_four _ M ha
    _ = _ := by simp only [sq_abs]


end RiemannResearch.Analysis.DiscreteTailHardy
