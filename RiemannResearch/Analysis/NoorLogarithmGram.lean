import RiemannResearch.Analysis.NoorLogarithmDensity
import Mathlib.Tactic.FieldSimp

/-!
# Exact Gram kernel of divisibility logarithms

Source: elementary reindexing of the logVector family already defined in
NoorLogarithmDensity, for the user-requested shifted-lift continuation.
The inner product is supported on multiples of the least common multiple.
This calculation supplies RH/NoorRegularizedGram; no rate is asserted.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.Analysis.Noor
open CoefficientShift

theorem logVector_inner (k l : ℕ) (hk : 0 < k) (hl : 0 < l) :
    inner ℝ (logVector k) (logVector l) =
      ((k : ℝ) * l / (Nat.lcm k l : ℝ)^2) * ∑' j : ℕ, 1 / (j : ℝ)^2 := by
  let L := Nat.lcm k l
  have hL : 0 < L := Nat.lcm_pos hk hl
  have hLR : (L : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hL
  have hinj : Function.Injective (fun j : ℕ => L * j) := by
    intro i j hij
    exact Nat.eq_of_mul_eq_mul_left hL hij
  have hs : Function.support (fun n => logSequence k n * logSequence l n) ⊆
      Set.range (fun j : ℕ => L * j) := by
    intro n hn
    by_cases hd : L ∣ n
    · obtain ⟨j, rfl⟩ := hd
      exact ⟨j, rfl⟩
    · have hd' : ¬ (k ∣ n ∧ l ∣ n) := by simpa only [← Nat.lcm_dvd_iff] using hd
      simp only [Function.mem_support, ne_eq, logSequence] at hn
      by_cases hkn : k ∣ n <;> by_cases hln : l ∣ n <;> simp_all
  have hts : inner ℝ (logVector k) (logVector l) =
      ∑' n, logSequence k n * logSequence l n := by
    rw [lp.inner_eq_tsum]
    apply tsum_congr
    intro n
    simp [mul_comm]
  rw [hts, ← hinj.tsum_eq hs]
  have hterm (j : ℕ) :
      logSequence k (L*j) * logSequence l (L*j) =
        ((k : ℝ) * l / (L : ℝ)^2) * (1 / (j : ℝ)^2) := by
    have hkL : k ∣ L*j := (Nat.dvd_lcm_left k l).trans (Nat.dvd_mul_right L j)
    have hlL : l ∣ L*j := (Nat.dvd_lcm_right k l).trans (Nat.dvd_mul_right L j)
    simp only [logSequence, if_pos hkL, if_pos hlL, Nat.cast_mul]
    by_cases hj : j = 0
    · simp [hj]
    · have hjR : (j : ℝ) ≠ 0 := by exact_mod_cast hj
      field_simp
  simp_rw [hterm]
  exact tsum_mul_left

/-- Exact pairing with a logarithmic divisibility vector, retaining all multiples. -/
theorem inner_logVector_eq_tsum_multiples (a : Space) (k : ℕ) (hk : 0 < k) :
    inner ℝ a (logVector k) = ∑' m : ℕ, a (k*m) / (m : ℝ) := by
  have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hk
  have hinj : Function.Injective (fun m : ℕ => k*m) := by
    intro m n h
    exact Nat.eq_of_mul_eq_mul_left hk h
  have hs : Function.support (fun n => a n * logSequence k n) ⊆
      Set.range (fun m : ℕ => k*m) := by
    intro n hn
    by_cases hd : k ∣ n
    · obtain ⟨m, rfl⟩ := hd
      exact ⟨m, rfl⟩
    · simp only [Function.mem_support, ne_eq, logSequence, if_neg hd, mul_zero,
        not_true_eq_false] at hn
  have hts : inner ℝ a (logVector k) = ∑' n : ℕ, a n * logSequence k n := by
    rw [lp.inner_eq_tsum]
    apply tsum_congr
    intro n
    simp [mul_comm]
  rw [hts, ← hinj.tsum_eq hs]
  apply tsum_congr
  intro m
  have hd : k ∣ k*m := Nat.dvd_mul_right k m
  simp only [logSequence, if_pos hd, Nat.cast_mul]
  by_cases hm : m = 0
  · simp [hm]
  · have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm
    field_simp
end RiemannResearch.Analysis.Noor
