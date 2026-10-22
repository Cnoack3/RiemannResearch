import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Topology.Algebra.InfiniteSum.Constructions
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
/-!
# Summable tails from a first absolute moment
Source: user-provided analytic repair note, September 11, 2026.
Tonelli supplies absolute summability of the tails. The weighted-tail limit
comes from domination by the vanishing tail of the first absolute moment.
-/
namespace RiemannResearch.Analysis
open Filter
noncomputable section
theorem rawTail_summable_of_firstMoment (a : ℕ → ℝ)
    (ha : Summable a)
    (hm : Summable (fun n : ℕ => (n : ℝ) * |a n|)) :
    Summable (fun k : ℕ => ∑' j : ℕ, a (j+k)) := by
  let g : ℕ × ℕ → ℝ := fun p => if p.2 < p.1 then |a p.1| else 0
  have hg0 : 0 ≤ g := by intro p; dsimp [g]; split_ifs <;> positivity
  have hrow (n : ℕ) : Summable (fun k : ℕ => g (n,k)) := by
    apply summable_of_ne_finset_zero (s := Finset.range n)
    intro k hk
    simp only [Finset.mem_range] at hk
    simp [g, hk]
  have hrowsum (n : ℕ) : (∑' k : ℕ, g (n,k)) = (n : ℝ)*|a n| := by
    rw [tsum_eq_sum (s := Finset.range n) (fun k hk => by
      simp only [Finset.mem_range] at hk
      simp [g, hk])]
    calc
      _ = ∑ _k ∈ Finset.range n, |a n| := by
        apply Finset.sum_congr rfl
        intro k hk
        exact if_pos (Finset.mem_range.mp hk)
      _ = _ := by simp
  have hg : Summable g := (summable_prod_of_nonneg hg0).2
    ⟨hrow, by simpa only [hrowsum] using hm⟩
  have hgs := (summable_prod_of_nonneg
    (f := fun p : ℕ × ℕ => g p.swap) (by intro p; exact hg0 p.swap)).mp hg.prod_symm
  have hcut : Summable (fun k : ℕ => ∑' n : ℕ, if k < n then a n else 0) := by
    apply hgs.2.of_norm_bounded
    intro k
    have hs : Summable (fun n : ℕ => ‖if k < n then a n else 0‖) := by
      simpa only [apply_ite, norm_zero, Real.norm_eq_abs, g, Prod.swap_prod_mk]
        using hgs.1 k
    simpa only [apply_ite, norm_zero, Real.norm_eq_abs, g, Prod.swap_prod_mk]
      using norm_tsum_le_tsum_norm hs
  have hident (k : ℕ) : (∑' n : ℕ, if k < n then a n else 0) =
      ∑' j : ℕ, a (j+(k+1)) := by
    have he (j : ℕ) : (if k < j+(k+1) then a (j+(k+1)) else 0) =
        a (j+(k+1)) := if_pos (by omega)
    have hs : Summable (fun j : ℕ => if k < j+(k+1) then a (j+(k+1)) else 0) := by
      simpa only [he] using (summable_nat_add_iff (k+1)).mpr ha
    have hi := Summable.sum_add_tsum_nat_add'
      (f := fun n : ℕ => if k < n then a n else 0) (k := k+1) hs
    have hz : (∑ i ∈ Finset.range (k+1), if k < i then a i else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      have hip := Finset.mem_range.mp hi
      rw [if_neg (by omega)]
    rw [hz, zero_add] at hi
    simpa only [he] using hi.symm
  have hpositive : Summable (fun k : ℕ => ∑' j : ℕ, a (j+(k+1))) := by
    simpa only [hident] using hcut
  exact (summable_nat_add_iff 1).mp hpositive

theorem rawTail_tendsto_zero {a : ℕ → ℝ} (ha : Summable a) :
    Tendsto (fun k : ℕ => ∑' j, a (j+k)) atTop (nhds 0) := by
  have he (k : ℕ) : (∑' j, a (j+k)) = (∑' j, a j) - (∑ j ∈ Finset.range k, a j) := by
    have ht := Summable.sum_add_tsum_nat_add k ha
    linarith
  simp_rw [he]
  simpa only [sub_self] using
    ((tendsto_const_nhds : Tendsto (fun _ : ℕ => ∑' j, a j) atTop (nhds (∑' j, a j))).sub ha.hasSum.tendsto_sum_nat)

theorem weighted_rawTail_tendsto_zero_of_firstMoment (a : ℕ → ℝ)
    (ha : Summable a)
    (hm : Summable (fun n : ℕ => (n : ℝ) * |a n|)) :
    Tendsto (fun n : ℕ => (n : ℝ)*(∑' j, a (j+n))) atTop (nhds 0) := by
  have hbound (n : ℕ) :
      ‖(n : ℝ)*(∑' j, a (j+n))‖ ≤
        ∑' j, ((j+n : ℕ) : ℝ)*|a (j+n)| := by
    have hs : Summable (fun j => |a (j+n)|) := (summable_nat_add_iff n).mpr ha.abs
    have ht : Summable (fun j => ((j+n : ℕ) : ℝ)*|a (j+n)|) :=
      (summable_nat_add_iff n).mpr hm
    have hnorm : ‖∑' j, a (j+n)‖ ≤ ∑' j, |a (j+n)| := by
      simpa only [Real.norm_eq_abs] using
        norm_tsum_le_tsum_norm (f := fun j : ℕ => a (j+n)) (by simpa only [Real.norm_eq_abs] using hs)
    calc
      _ = (n : ℝ)*‖∑' j, a (j+n)‖ := by
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (Nat.cast_nonneg n), Real.norm_eq_abs]
      _ ≤ (n : ℝ)*(∑' j, |a (j+n)|) :=
        mul_le_mul_of_nonneg_left hnorm (Nat.cast_nonneg n)
      _ = ∑' j, (n : ℝ)*|a (j+n)| := tsum_mul_left.symm
      _ ≤ _ := (hs.mul_left (n : ℝ)).tsum_le_tsum (fun j => by
        apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
        exact_mod_cast (Nat.le_add_left n j)) ht
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  exact squeeze_zero (fun n => norm_nonneg _) hbound (rawTail_tendsto_zero hm)
end
end RiemannResearch.Analysis
