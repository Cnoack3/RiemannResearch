import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Finite interscale constraints on signed residual correlations

Source: user-provided `RH_Coupled_Residual_Corrections_2026-09-16.md`,
Section 4. These scalar consequences apply to the actual dyadic distances
once their already proved interscale Cauchy--Schwarz estimate is supplied.
Every mixed sign is retained in the source estimate. No lower estimate
for the correlations or RH assertion is made here.
-/
noncomputable section
open scoped BigOperators

namespace RiemannResearch.Analysis.InterscaleResidualConstraints

/-- Division by a vanishing source energy contributes zero. The source
itself also vanishes in this case. -/
theorem source_eq_zero_of_zero_energy {a b h : ℝ}
    (ha : a = 0) (hh : h^2 ≤ 2*a*b) : h = 0 := by
  rw [ha] at hh
  nlinarith [sq_nonneg h]

theorem source_quotient_le {a b h : ℝ}
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hh : h^2 ≤ 2*a*b) :
    h^2 / (2*a) ≤ b := by
  by_cases hz : a = 0
  · simpa [hz] using hb
  · apply (div_le_iff₀ (mul_pos (by norm_num) (lt_of_le_of_ne ha (Ne.symm hz)))).mpr
    nlinarith

/-- Finite weighted square summability; valid even when some consecutive
projection gains vanish. The first source uses the drops d(0)-d(1) and
d(1)-d(2), so the right side starts at d(1). -/
theorem sum_source_quotients_le (d h : ℕ → ℝ)
    (hmono : Antitone d)
    (hsource : ∀ j, (h j)^2 ≤
      2*(d j-d (j+1))*(d (j+1)-d (j+2))) (N : ℕ) :
    (∑ j ∈ Finset.range N, (h j)^2 / (2*(d j-d (j+1)))) ≤
      d 1-d (N+1) := by
  calc
    _ ≤ ∑ j ∈ Finset.range N, (d (j+1)-d (j+2)) := by
      apply Finset.sum_le_sum
      intro j hj
      exact source_quotient_le
        (sub_nonneg.mpr (hmono (Nat.le_succ j)))
        (sub_nonneg.mpr (hmono (Nat.le_succ (j+1))))
        (hsource j)
    _ = d 1-d (N+1) := by
      simpa only [Nat.zero_add, Nat.add_assoc] using
        (Finset.sum_range_sub' (fun j => d (j+1)) N)

/-- A elementary finite Cauchy--Schwarz consequence of the pointwise
interscale estimate. Proved without extracting individual signs. -/
theorem sum_abs_sq_le (a b h : ℕ → ℝ)
    (ha : ∀ j, 0 ≤ a j) (hb : ∀ j, 0 ≤ b j)
    (hsource : ∀ j, (h j)^2 ≤ 2*a j*b j) (N : ℕ) :
    (∑ j ∈ Finset.range N, |h j|)^2 ≤
      2*(∑ j ∈ Finset.range N, a j)*(∑ j ∈ Finset.range N, b j) := by
  have hpoint (j : ℕ) : |h j| ≤ Real.sqrt (2*a j) * Real.sqrt (b j) := by
    have ha' : 0 ≤ 2*a j := mul_nonneg (by norm_num) (ha j)
    have hs1 := Real.sq_sqrt ha'
    have hs2 := Real.sq_sqrt (hb j)
    have hprod : (Real.sqrt (2*a j)*Real.sqrt (b j))^2 = 2*a j*b j := by
      rw [mul_pow, hs1, hs2]
    nlinarith [sq_abs (h j), abs_nonneg (h j),
      mul_nonneg (Real.sqrt_nonneg (2*a j)) (Real.sqrt_nonneg (b j)), hsource j]
  have hsum := Finset.sum_le_sum (fun j (_hj : j ∈ Finset.range N) => hpoint j)
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.range N)
    (fun j => Real.sqrt (2*a j)) (fun j => Real.sqrt (b j))
  have hsqa : (∑ j ∈ Finset.range N, (Real.sqrt (2*a j))^2) =
      2*(∑ j ∈ Finset.range N, a j) := by
    calc
      _ = ∑ j ∈ Finset.range N, 2*a j := by
        apply Finset.sum_congr rfl
        intro j hj
        exact Real.sq_sqrt (mul_nonneg (by norm_num) (ha j))
      _ = _ := (Finset.mul_sum ..).symm
  have hsqb : (∑ j ∈ Finset.range N, (Real.sqrt (b j))^2) =
      ∑ j ∈ Finset.range N, b j := by
    apply Finset.sum_congr rfl
    intro j hj
    exact Real.sq_sqrt (hb j)
  rw [hsqa, hsqb] at hcs
  have hn1 : 0 ≤ ∑ j ∈ Finset.range N, |h j| :=
    Finset.sum_nonneg (fun j _ => abs_nonneg (h j))
  have hn2 : 0 ≤ ∑ j ∈ Finset.range N,
      Real.sqrt (2*a j)*Real.sqrt (b j) :=
    Finset.sum_nonneg (fun j _ => mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
  nlinarith

/-- Exact finite counterpart of the manuscript's absolute-sum tail
bound, with both endpoint projection distances retained. -/
theorem sum_abs_sources_sq_le (d h : ℕ → ℝ)
    (hmono : Antitone d)
    (hsource : ∀ j, (h j)^2 ≤
      2*(d j-d (j+1))*(d (j+1)-d (j+2))) (N : ℕ) :
    (∑ j ∈ Finset.range N, |h j|)^2 ≤
      2*(d 0-d N)*(d 1-d (N+1)) := by
  have h := sum_abs_sq_le
    (fun j => d j-d (j+1)) (fun j => d (j+1)-d (j+2)) h
    (fun j => sub_nonneg.mpr (hmono (Nat.le_succ j)))
    (fun j => sub_nonneg.mpr (hmono (Nat.le_succ (j+1)))) hsource N
  rw [Finset.sum_range_sub'] at h
  have ht : (∑ j ∈ Finset.range N, (d (j+1)-d (j+2))) = d 1-d (N+1) := by
    simpa only [Nat.zero_add, Nat.add_assoc] using
      (Finset.sum_range_sub' (fun j => d (j+1)) N)
  rwa [ht] at h

/-- A uniform partial-sum bound when distances are nonnegative. -/
theorem sum_abs_sources_le (d h : ℕ → ℝ)
    (hmono : Antitone d) (hd : ∀ j, 0 ≤ d j)
    (hsource : ∀ j, (h j)^2 ≤
      2*(d j-d (j+1))*(d (j+1)-d (j+2))) (N : ℕ) :
    (∑ j ∈ Finset.range N, |h j|) ≤ d 0+d 1 := by
  have hs := sum_abs_sources_sq_le d h hmono hsource N
  have hprod : (d 0-d N)*(d 1-d (N+1)) ≤ d 0*d 1 :=
    mul_le_mul (sub_le_self _ (hd N)) (sub_le_self _ (hd (N+1)))
      (sub_nonneg.mpr (hmono (Nat.succ_le_succ (Nat.zero_le N)))) (hd 0)
  have hn : 0 ≤ ∑ j ∈ Finset.range N, |h j| :=
    Finset.sum_nonneg (fun j _ => abs_nonneg (h j))
  have hbound : 0 ≤ d 0+d 1 := add_nonneg (hd 0) (hd 1)
  nlinarith [sq_nonneg (d 0), sq_nonneg (d 1)]

/-- Actual absolute summability follows from the interscale source
bound and nonnegative decreasing distances. -/
theorem summable_abs_sources (d h : ℕ → ℝ)
    (hmono : Antitone d) (hd : ∀ j, 0 ≤ d j)
    (hsource : ∀ j, (h j)^2 ≤
      2*(d j-d (j+1))*(d (j+1)-d (j+2))) :
    Summable (fun j => |h j|) := by
  exact summable_of_sum_range_le (fun j => abs_nonneg (h j))
    (sum_abs_sources_le d h hmono hd hsource)

theorem summable_sources (d h : ℕ → ℝ)
    (hmono : Antitone d) (hd : ∀ j, 0 ≤ d j)
    (hsource : ∀ j, (h j)^2 ≤
      2*(d j-d (j+1))*(d (j+1)-d (j+2))) :
    Summable h := by
  apply summable_norm_iff.mp
  simpa only [Real.norm_eq_abs] using summable_abs_sources d h hmono hd hsource

/-- The weighted squared correlations are summable as well. Lean's
real division by zero is zero, matching the convention justified by
`source_eq_zero_of_zero_energy`. -/
theorem summable_source_quotients (d h : ℕ → ℝ)
    (hmono : Antitone d) (hd : ∀ j, 0 ≤ d j)
    (hsource : ∀ j, (h j)^2 ≤
      2*(d j-d (j+1))*(d (j+1)-d (j+2))) :
    Summable (fun j => (h j)^2/(2*(d j-d (j+1)))) := by
  apply summable_of_sum_range_le
    (fun j => div_nonneg (sq_nonneg _) (mul_nonneg (by norm_num)
      (sub_nonneg.mpr (hmono (Nat.le_succ j)))))
  intro N
  exact (sum_source_quotients_le d h hmono hsource N).trans (sub_le_self _ (hd (N+1)))

end RiemannResearch.Analysis.InterscaleResidualConstraints
