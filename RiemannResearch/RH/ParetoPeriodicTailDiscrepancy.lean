import RiemannResearch.RH.ParetoResidueUniformCovariance
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! # Periodic prefix discrepancy and monotone Pareto weights

Section 5 of the supplied *Pareto Parity Projection* gives the periodic discrepancy
argument. A complete period cancels at every starting site. The sharp
elementary bound for a partial period is retained before summation by parts.
-/

open scoped BigOperators
namespace RiemannResearch.RH.Pareto.PeriodicDiscrepancy

private theorem shift_period_sum (f : ℕ → ℝ) (p : ℕ) (hp : ∀ n, f (n+p) = f n)
    (a : ℕ) : (∑ j ∈ Finset.range p, f (a+j)) = ∑ j ∈ Finset.range p, f j := by
  induction a with
  | zero => simp
  | succ a ih =>
    have h := (Finset.sum_range_succ' (fun j => f (a+j)) p).symm.trans
      (Finset.sum_range_succ (fun j => f (a+j)) p)
    simp only [Nat.add_zero, hp] at h
    convert (add_right_cancel h).trans ih using 2 <;> congr 1 <;> omega

private theorem prefix_mod (f : ℕ → ℝ) (p : ℕ) (hp : 0 < p)
    (hzero : ∀ a, (∑ j ∈ Finset.range p, f (a+j)) = 0) (a k : ℕ) :
    (∑ j ∈ Finset.range k, f (a+j)) = ∑ j ∈ Finset.range (k%p), f (a+j) := by
  induction k using Nat.strong_induction_on with
  | h k ih =>
    by_cases h : k < p
    · rw [Nat.mod_eq_of_lt h]
    · have hkp : k-p+p = k := by omega
      have hex : (∑ j ∈ Finset.range k, f (a+j)) =
          ∑ j ∈ Finset.range (k-p), f (a+j) := by
        conv_lhs => rw [← hkp, Finset.sum_range_add]
        simpa only [← Nat.add_assoc, hzero, add_zero]
      rw [hex, ih (k-p) (by omega)]
      have hm : (k-p)%p = k%p := by
        conv_rhs => rw [← hkp, Nat.add_mod_right]
      rw [hm]

private theorem sum_abs_bound (f : ℕ → ℝ) {K : ℝ} (hf : ∀ n, |f n| ≤ K)
    (a k : ℕ) : |∑ j ∈ Finset.range k, f (a+j)| ≤ (k : ℝ) * K := by
  calc
    _ ≤ ∑ j ∈ Finset.range k, |f (a+j)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j ∈ Finset.range k, K := Finset.sum_le_sum fun j _ => hf _
    _ = _ := by simp

/-- The discrepancy estimate holds for every starting site and every prefix length. -/
theorem prefix_error_le (f : ℕ → ℝ) (p a k : ℕ) (hp : 0 < p)
    (hper : ∀ n, f (n+p) = f n) {K μ : ℝ} (hf : ∀ n, |f n| ≤ K)
    (hm : (∑ j ∈ Finset.range p, f j) = (p:ℝ)*μ) :
    |(∑ j ∈ Finset.range k, f (a+j)) - (k:ℝ)*μ| ≤ (p:ℝ)*K/2 := by
  let g := fun n => f n - μ
  have hsum (b l : ℕ) : (∑ j ∈ Finset.range l, g (b+j)) =
      (∑ j ∈ Finset.range l, f (b+j)) - (l:ℝ)*μ := by
    simp [g, Finset.sum_sub_distrib]
  have hz (b : ℕ) : (∑ j ∈ Finset.range p, g (b+j)) = 0 := by
    rw [hsum, shift_period_sum f p hper, hm, sub_self]
  rw [← hsum, prefix_mod g p hp hz, hsum]
  let r := k%p
  let s := p-r
  let x := ∑ j ∈ Finset.range r, f (a+j)
  let y := ∑ j ∈ Finset.range s, f (a+r+j)
  have hr : r ≤ p := (Nat.mod_lt k hp).le
  have hrs : r+s = p := by dsimp [s]; omega
  have hrs' : (r:ℝ)+(s:ℝ) = (p:ℝ) := by exact_mod_cast hrs
  have hxy : x+y = (p:ℝ)*μ := by
    calc
      _ = ∑ j ∈ Finset.range (r+s), f (a+j) := by
        rw [Finset.sum_range_add]; simp only [x,y,Nat.add_assoc]
      _ = _ := by rw [hrs,shift_period_sum f p hper,hm]
  have hx := sum_abs_bound f hf a r
  have hy := sum_abs_bound f hf (a+r) s
  change |x| ≤ _ at hx
  change |y| ≤ _ at hy
  have he : (p:ℝ)*(x-(r:ℝ)*μ) = (s:ℝ)*x-(r:ℝ)*y := by
    linear_combination x * hrs'.symm + (r:ℝ) * hxy
  have hK : 0 ≤ K := (abs_nonneg _).trans (hf 0)
  have hr0 : (0:ℝ) ≤ r := Nat.cast_nonneg _
  have hs0 : (0:ℝ) ≤ s := Nat.cast_nonneg _
  have hp0 : (0:ℝ) < p := by exact_mod_cast hp
  change |x-(r:ℝ)*μ| ≤ _
  apply (mul_le_mul_iff_right₀ hp0).mp
  calc
    (p:ℝ)*|x-(r:ℝ)*μ| = |(s:ℝ)*x-(r:ℝ)*y| := by rw [← he, abs_mul, abs_of_pos hp0]
    _ ≤ |(s:ℝ)*x| + |(r:ℝ)*y| := abs_sub _ _
    _ ≤ (s:ℝ)*((r:ℝ)*K) + (r:ℝ)*((s:ℝ)*K) := by
      rw [abs_mul,abs_mul,abs_of_nonneg hs0,abs_of_nonneg hr0]
      exact add_le_add (mul_le_mul_of_nonneg_left hx hs0) (mul_le_mul_of_nonneg_left hy hr0)
    _ ≤ (p:ℝ)*((p:ℝ)*K/2) := by
      rw [← hrs']
      nlinarith [mul_nonneg (sq_nonneg ((r:ℝ)-(s:ℝ))) hK]

/-- A one-sided bound for every ordinary prefix transfers to every decreasing
nonnegative weighted prefix. -/
theorem abel_upper (f w : ℕ → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hmon : ∀ i, w (i+1) ≤ w i) (K : ℝ)
    (hb : ∀ j, (∑ i ∈ Finset.range j, f i) ≤ K) (n : ℕ) :
    (∑ i ∈ Finset.range n, w i * f i) ≤ w 0 * K := by
  let S (j : ℕ) := ∑ i ∈ Finset.range j, f i
  have hstep (j : ℕ) : S (j+1) = S j + f j := Finset.sum_range_succ _ _
  have hform (j : ℕ) : (∑ i ∈ Finset.range j, w i * f i) =
      w j * S j + ∑ i ∈ Finset.range j, (w i-w (i+1)) * S (i+1) := by
    induction j with
    | zero => simp [S]
    | succ j ih =>
      rw [Finset.sum_range_succ, ih, Finset.sum_range_succ, hstep]
      ring
  have htel : (∑ i ∈ Finset.range n, (w i - w (i+1))) = w 0 - w n := by
    induction n with
    | zero => simp
    | succ n ih => rw [Finset.sum_range_succ,ih]; ring
  rw [hform]
  calc
    _ ≤ w n*K + ∑ i ∈ Finset.range n, (w i - w (i+1))*K :=
      add_le_add (mul_le_mul_of_nonneg_left (hb n) (hw n)) (Finset.sum_le_sum
        fun i _ => mul_le_mul_of_nonneg_left (hb _) (sub_nonneg.mpr (hmon i)))
    _ = _ := by rw [← Finset.sum_mul,htel];ring

end RiemannResearch.RH.Pareto.PeriodicDiscrepancy
