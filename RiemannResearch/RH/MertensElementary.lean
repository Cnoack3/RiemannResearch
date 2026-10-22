import RiemannResearch.RH.ArithmeticReturnConvolution
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Elementary weighted von Mangoldt discrepancy

Source: user-provided argument, §6.6 of
`RH_Nyman_Weil_Null_Channels_and_Exact_Prime_Compensation_2026-09-07.md`.
The proof uses the exact factorial identity and Chebyshev's elementary bound.
No prime asymptotic or Riemann-hypothesis input occurs.
-/

open scoped BigOperators
namespace RiemannResearch.RH

private theorem log_factorial_eq_sum_range (N : ℕ) :
    Real.log (N.factorial : ℝ) = ∑ m ∈ Finset.range (N + 1), Real.log m := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Nat.factorial_succ, Nat.cast_mul,
        Real.log_mul (by positivity) (by exact_mod_cast Nat.factorial_ne_zero N),
        Finset.sum_range_succ, ih]
      ring

/-- Exact count of positive multiples, reusable in finite divisor regrouping. -/
theorem sum_floor_weight (N k : ℕ) (hk : k ≠ 0) (a : ℝ) :
    (∑ l ∈ Finset.range (N + 1),
      if k * l ≤ N then (if l = 0 then 0 else a) else 0) = (N / k : ℕ) * a := by
  have hk0 : 0 < k := Nat.pos_of_ne_zero hk
  have hs :
      (∑ l ∈ Finset.range (N + 1),
        if k * l ≤ N then (if l = 0 then 0 else a) else 0) =
      ∑ l ∈ Finset.range (N / k + 1),
        if k * l ≤ N then (if l = 0 then 0 else a) else 0 := by
    symm
    apply Finset.sum_subset (Finset.range_mono (Nat.succ_le_succ (Nat.div_le_self N k)))
    intro l hl hn
    have hlt : N / k < l := by
      simp only [Finset.mem_range] at hn
      omega
    have hlarge : ¬ k * l ≤ N := by
      intro h
      have h' : l ≤ N / k := (Nat.le_div_iff_mul_le hk0).mpr (by simpa [Nat.mul_comm] using h)
      omega
    simp [hlarge]
  rw [hs]
  have hs2 :
      (∑ l ∈ Finset.range (N / k + 1),
        if k * l ≤ N then (if l = 0 then 0 else a) else 0) =
      ∑ l ∈ Finset.range (N / k + 1), if l = 0 then 0 else a := by
    apply Finset.sum_congr rfl
    intro l hl
    have hle : l ≤ N / k := Nat.le_of_lt_succ (Finset.mem_range.mp hl)
    have hprod : k * l ≤ N := by
      simpa only [Nat.mul_comm] using (Nat.le_div_iff_mul_le hk0).mp hle
    simp [hprod]
  rw [hs2, Finset.sum_range_succ']
  simp

/-- Exact factorial identity, retaining every prime power through `vonMangoldt`. -/
theorem log_factorial_eq_sum_vonMangoldt_div (N : ℕ) :
    Real.log (N.factorial : ℝ) =
      ∑ k ∈ Finset.range (N + 1), ArithmeticFunction.vonMangoldt k * (N / k : ℕ) := by
  let F : ℕ → ℕ → ℝ := fun k l => if l = 0 then 0 else ArithmeticFunction.vonMangoldt k
  have hF0 : ∀ l, F 0 l = 0 := by intro l; simp [F]
  have hF1 : ∀ k, F k 0 = 0 := by intro k; simp [F]
  have hlocal (m : ℕ) :
      (∑ p ∈ m.divisorsAntidiagonal, F p.1 p.2) = Real.log m := by
    calc
      _ = ∑ p ∈ m.divisorsAntidiagonal, ArithmeticFunction.vonMangoldt p.1 := by
        apply Finset.sum_congr rfl
        intro p hp
        have hp2 : p.2 ≠ 0 := Nat.right_ne_zero_of_mem_divisorsAntidiagonal hp
        simp [F, hp2]
      _ = ∑ k ∈ m.divisors, ArithmeticFunction.vonMangoldt k :=
        Nat.sum_divisorsAntidiagonal (fun k _ => ArithmeticFunction.vonMangoldt k)
      _ = _ := ArithmeticFunction.vonMangoldt_sum
  rw [log_factorial_eq_sum_range]
  simp_rw [← hlocal]
  rw [Nat.sum_divisorsAntidiagonal_range N F hF0 hF1]
  apply Finset.sum_congr rfl
  intro k hk
  by_cases hk0 : k = 0
  · simp [hk0, F]
  · simpa only [F, mul_comm] using sum_floor_weight N k hk0 (ArithmeticFunction.vonMangoldt k)

/-- The exact reciprocal weighted Mangoldt prefix. -/
noncomputable def mangoldtReciprocalPrefix (N : ℕ) : ℝ :=
  ∑ k ∈ Finset.range (N + 1), ArithmeticFunction.vonMangoldt k / k

private theorem nat_div_fractional_bounds (N k : ℕ) (hk : k ≠ 0) :
    0 ≤ (N : ℝ) / k - (N / k : ℕ) ∧
      (N : ℝ) / k - (N / k : ℕ) ≤ 1 := by
  have hk0 : 0 < (k : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hk
  have he : (N : ℝ) = (N / k : ℕ) * (k : ℝ) + (N % k : ℕ) := by
    exact_mod_cast (show N = N / k * k + N % k by
      simpa only [Nat.mul_comm] using (Nat.div_add_mod N k).symm)
  have hrem1 : (N % k : ℕ) < (k : ℝ) := by exact_mod_cast Nat.mod_lt N (Nat.pos_of_ne_zero hk)
  constructor
  · exact sub_nonneg.mpr Nat.cast_div_le
  · apply (sub_le_iff_le_add).mpr
    apply (div_le_iff₀ hk0).mpr
    nlinarith

/-- The factorial approximation error is nonnegative and at most the exact
Chebyshev sum; this is not a discarded signed term. -/
theorem mangoldtReciprocalPrefix_factorial_bounds (N : ℕ) :
    0 ≤ (N : ℝ) * mangoldtReciprocalPrefix N - Real.log (N.factorial : ℝ) ∧
      (N : ℝ) * mangoldtReciprocalPrefix N - Real.log (N.factorial : ℝ) ≤
        Chebyshev.psi N := by
  have he : (N : ℝ) * mangoldtReciprocalPrefix N - Real.log (N.factorial : ℝ) =
      ∑ k ∈ Finset.range (N + 1), ArithmeticFunction.vonMangoldt k *
        ((N : ℝ) / k - (N / k : ℕ)) := by
    rw [mangoldtReciprocalPrefix, log_factorial_eq_sum_vonMangoldt_div,
      Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro k hk
    ring
  have hk (k : ℕ) : 0 ≤ ArithmeticFunction.vonMangoldt k *
      ((N : ℝ) / k - (N / k : ℕ)) ∧
      ArithmeticFunction.vonMangoldt k * ((N : ℝ) / k - (N / k : ℕ)) ≤
        ArithmeticFunction.vonMangoldt k := by
    by_cases hk0 : k = 0
    · simp [hk0]
    · have hb := nat_div_fractional_bounds N k hk0
      constructor
      · exact mul_nonneg ArithmeticFunction.vonMangoldt_nonneg hb.1
      · exact (mul_le_mul_of_nonneg_left hb.2 ArithmeticFunction.vonMangoldt_nonneg).trans_eq
          (mul_one _)
  rw [he]
  constructor
  · exact Finset.sum_nonneg (fun k hk' => (hk k).1)
  · calc
      _ ≤ ∑ k ∈ Finset.range (N + 1), ArithmeticFunction.vonMangoldt k :=
        Finset.sum_le_sum (fun k hk' => (hk k).2)
      _ = _ := by
        rw [Chebyshev.psi_eq_sum_Icc]
        simp only [Nat.floor_natCast]
        apply Finset.sum_congr
        · ext k
          simp only [Finset.mem_range, Finset.mem_Icc, Nat.zero_le, true_and]
          omega
        · intro k hk
          rfl

private theorem log_factorial_upper {N : ℕ} (_hN : N ≠ 0) :
    Real.log (N.factorial : ℝ) ≤ (N : ℝ) * Real.log N := by
  rw [log_factorial_eq_sum_range, Finset.sum_range_succ']
  simp only [Nat.cast_zero, Real.log_zero, add_zero]
  calc
    _ ≤ ∑ k ∈ Finset.range N, Real.log N := by
      apply Finset.sum_le_sum
      intro k hk
      exact Real.log_le_log (by positivity) (by
        exact_mod_cast Nat.succ_le_iff.mpr (Finset.mem_range.mp hk))
    _ = _ := by simp

private theorem log_factorial_lower {N : ℕ} (hN : N ≠ 0) :
    (N : ℝ) * Real.log N - N ≤ Real.log (N.factorial : ℝ) := by
  have hlog : 0 ≤ Real.log N := Real.log_nonneg (by
    exact_mod_cast Nat.one_le_iff_ne_zero.mpr hN)
  have hpi : 0 ≤ Real.log (2 * Real.pi) := Real.log_nonneg (by
    nlinarith [Real.pi_gt_three])
  have h := Stirling.le_log_factorial_stirling hN
  linarith

/-- An unconditional explicit Mertens bound for the actual Mangoldt prefix. -/
theorem mangoldtReciprocalPrefix_discrepancy_bound {N : ℕ} (hN : N ≠ 0) :
    |mangoldtReciprocalPrefix N - Real.log N| ≤ Real.log 4 + 5 := by
  have hN0 : 0 < (N : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hN
  obtain ⟨he0, he1⟩ := mangoldtReciprocalPrefix_factorial_bounds N
  have hu := log_factorial_upper hN
  have hl := log_factorial_lower hN
  have hpsi := Chebyshev.psi_le_const_mul_self (Nat.cast_nonneg (α := ℝ) N)
  have hlo : -1 ≤ mangoldtReciprocalPrefix N - Real.log N := by
    nlinarith
  have hhi : mangoldtReciprocalPrefix N - Real.log N ≤ Real.log 4 + 4 := by
    nlinarith
  apply abs_le.mpr
  have h4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  constructor <;> linarith

end RiemannResearch.RH
