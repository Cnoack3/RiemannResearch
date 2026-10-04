import RiemannResearch.Analysis.PrimePowerCovarianceRowBudget
import RiemannResearch.Analysis.FiniteWeightedSchurPairing
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The full prime-power covariance matrix: conjugation and Schur bound

Source: user-provided manuscript `Prime_Phases_Agenda_Proof_Attempts.tex`,
Theorem `growing-phase-gram`. All finite positive integer frequencies are
retained. The coefficient matrix is an arithmetic object; its quadratic
bound does not require an asymptotic statement about zeta-zero phases.
-/

open scoped BigOperators

namespace RiemannResearch.Fourier

/-- The positive Schur weight for the full integer-frequency dictionary. -/
noncomputable def integerFrequencySchurWeight (n : ℕ) : ℝ :=
  (Real.sqrt (n : ℝ))⁻¹

/-- The raw symmetric covariance kernel, written via exact diagonal
    conjugation of the directed arithmetic row. The signed normalized
    covariance in the manuscript is -1/(2 pi) times this kernel. -/
noncomputable def primePowerCovarianceSymmetricEntry (n m : ℕ) : ℝ :=
  Real.sqrt (m : ℝ) / Real.sqrt (n : ℝ) * primePowerCovarianceDirectedEntry n m

private theorem multiple_balance (n m : ℕ) (hn : 0 < n) (hm : 0 < m) :
    (if n ∣ m then ArithmeticFunction.vonMangoldt (m / n) / (m / n : ℕ) else 0) *
      (m : ℝ) =
    (if n ∣ m then ArithmeticFunction.vonMangoldt (m / n) else 0) * (n : ℝ) := by
  by_cases hd : n ∣ m
  · have hq : 0 < m / n := Nat.div_pos (Nat.le_of_dvd hm hd) hn
    have hq0 : ((m / n : ℕ) : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
    have heq : (m : ℝ) = (n : ℝ) * ((m / n : ℕ) : ℝ) := by
      exact_mod_cast (Nat.mul_div_cancel' hd).symm
    rw [if_pos hd, if_pos hd, heq]
    field_simp [hq0] <;> ring
  · simp only [if_neg hd, zero_mul]

/-- Detailed balance of the exact directed multiples/divisors row. -/
theorem primePowerCovarianceDirectedEntry_balance (n m : ℕ)
    (hn : 0 < n) (hm : 0 < m) :
    primePowerCovarianceDirectedEntry n m * (m : ℝ) =
      primePowerCovarianceDirectedEntry m n * (n : ℝ) := by
  have hnm := multiple_balance n m hn hm
  have hmn := multiple_balance m n hm hn
  unfold primePowerCovarianceDirectedEntry
  rw [add_mul, add_mul, hnm, hmn]
  ring

theorem integerFrequencySchurWeight_pos (n : ℕ) (hn : 0 < n) :
    0 < integerFrequencySchurWeight n := by
  unfold integerFrequencySchurWeight
  exact inv_pos.mpr (Real.sqrt_pos.mpr (by exact_mod_cast hn))

theorem primePowerCovarianceSymmetricEntry_nonneg (n m : ℕ) :
    0 ≤ primePowerCovarianceSymmetricEntry n m := by
  unfold primePowerCovarianceSymmetricEntry
  exact mul_nonneg (div_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
    (primePowerCovarianceDirectedEntry_nonneg n m)

/-- Exact diagonal conjugation; no square-root error is discarded. -/
theorem primePowerCovarianceSymmetricEntry_mul_weight (n m : ℕ)
    (hn : 0 < n) (hm : 0 < m) :
    primePowerCovarianceSymmetricEntry n m * integerFrequencySchurWeight m =
      integerFrequencySchurWeight n * primePowerCovarianceDirectedEntry n m := by
  have hsn : Real.sqrt (n : ℝ) ≠ 0 :=
    (Real.sqrt_pos.mpr (by exact_mod_cast hn)).ne'
  have hsm : Real.sqrt (m : ℝ) ≠ 0 :=
    (Real.sqrt_pos.mpr (by exact_mod_cast hm)).ne'
  unfold primePowerCovarianceSymmetricEntry integerFrequencySchurWeight
  field_simp [hsn, hsm] <;> ring

/-- The conjugated full integer-frequency kernel is symmetric. -/
theorem primePowerCovarianceSymmetricEntry_symm (n m : ℕ)
    (hn : 0 < n) (hm : 0 < m) :
    primePowerCovarianceSymmetricEntry n m = primePowerCovarianceSymmetricEntry m n := by
  have hsn : Real.sqrt (n : ℝ) ≠ 0 :=
    (Real.sqrt_pos.mpr (by exact_mod_cast hn)).ne'
  have hsm : Real.sqrt (m : ℝ) ≠ 0 :=
    (Real.sqrt_pos.mpr (by exact_mod_cast hm)).ne'
  have hp : Real.sqrt (n : ℝ) * Real.sqrt (m : ℝ) ≠ 0 := mul_ne_zero hsn hsm
  have hbal := primePowerCovarianceDirectedEntry_balance n m hn hm
  have heq : primePowerCovarianceSymmetricEntry n m *
      (Real.sqrt (n : ℝ) * Real.sqrt (m : ℝ)) =
      primePowerCovarianceSymmetricEntry m n *
        (Real.sqrt (n : ℝ) * Real.sqrt (m : ℝ)) := by
    calc
      _ = primePowerCovarianceDirectedEntry n m * (Real.sqrt (m : ℝ)) ^ 2 := by
        unfold primePowerCovarianceSymmetricEntry
        field_simp [hsn] <;> ring
      _ = primePowerCovarianceDirectedEntry n m * (m : ℝ) := by
        rw [Real.sq_sqrt (Nat.cast_nonneg m)]
      _ = primePowerCovarianceDirectedEntry m n * (n : ℝ) := hbal
      _ = primePowerCovarianceDirectedEntry m n * (Real.sqrt (n : ℝ)) ^ 2 := by
        rw [Real.sq_sqrt (Nat.cast_nonneg n)]
      _ = _ := by
        unfold primePowerCovarianceSymmetricEntry
        field_simp [hsm] <;> ring
  exact mul_right_cancel₀ hp heq

/-- On an actual integer ratio the conjugated kernel is exactly Lambda(q)/sqrt(q). -/
theorem primePowerCovarianceSymmetricEntry_eq_of_lt_of_dvd (n m : ℕ)
    (hn : 0 < n) (hnm : n < m) (hd : n ∣ m) :
    primePowerCovarianceSymmetricEntry n m =
      ArithmeticFunction.vonMangoldt (m / n) / Real.sqrt (m / n : ℕ) := by
  have hm : 0 < m := lt_trans hn hnm
  have hmd : ¬ m ∣ n := by
    intro h
    have heq := Nat.dvd_antisymm hd h
    omega
  have hq : 0 < m / n := Nat.div_pos (Nat.le_of_dvd hm hd) hn
  have hq0 : ((m / n : ℕ) : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  have hsqn : Real.sqrt (n : ℝ) ≠ 0 :=
    (Real.sqrt_pos.mpr (by exact_mod_cast hn)).ne'
  have hsqq : Real.sqrt (m / n : ℕ) ≠ 0 :=
    (Real.sqrt_pos.mpr (by exact_mod_cast hq)).ne'
  have hcast : (m : ℝ) = (n : ℝ) * ((m / n : ℕ) : ℝ) := by
    exact_mod_cast (Nat.mul_div_cancel' hd).symm
  have hsqrt : Real.sqrt (m : ℝ) =
      Real.sqrt (n : ℝ) * Real.sqrt (m / n : ℕ) := by
    rw [hcast, Real.sqrt_mul (Nat.cast_nonneg n)]
  have hcancel : (Real.sqrt (n : ℝ) * Real.sqrt (m / n : ℕ)) /
      Real.sqrt (n : ℝ) = Real.sqrt (m / n : ℕ) := by
    field_simp [hsqn]
  unfold primePowerCovarianceSymmetricEntry primePowerCovarianceDirectedEntry
  rw [if_pos hd, if_neg hmd, add_zero, hsqrt, hcancel]
  rw [← mul_div_assoc]
  apply (div_eq_div_iff hq0 hsqq).mpr
  calc
    _ = ArithmeticFunction.vonMangoldt (m / n) * (Real.sqrt (m / n : ℕ)) ^ 2 := by ring
    _ = _ := by rw [Real.sq_sqrt (Nat.cast_nonneg (m / n))]

/-- The diagonal is zero exactly, as required by the covariance matrix. -/
theorem primePowerCovarianceSymmetricEntry_diag (n : ℕ) (hn : 0 < n) :
    primePowerCovarianceSymmetricEntry n n = 0 := by
  simp [primePowerCovarianceSymmetricEntry, primePowerCovarianceDirectedEntry,
    Nat.div_self hn]

/-- No nonintegral rational pair creates a prime-power covariance term. -/
theorem primePowerCovarianceSymmetricEntry_eq_zero_of_nondvd (n m : ℕ)
    (hnm : ¬ n ∣ m) (hmn : ¬ m ∣ n) :
    primePowerCovarianceSymmetricEntry n m = 0 := by
  simp [primePowerCovarianceSymmetricEntry, primePowerCovarianceDirectedEntry, hnm, hmn]

/-- Its entire weighted absolute row is exactly the arithmetic row budget. -/
theorem primePowerCovarianceSymmetricEntry_weighted_row (N n : ℕ)
    (hn : 1 ≤ n) (hnN : n ≤ N) :
    (∑ m ∈ Finset.Ioc 0 N, ‖(primePowerCovarianceSymmetricEntry n m : ℂ)‖ *
      integerFrequencySchurWeight m) =
      integerFrequencySchurWeight n * primePowerCovarianceRowBudget N n := by
  have hnpos : 0 < n := lt_of_lt_of_le Nat.zero_lt_one hn
  calc
    _ = ∑ m ∈ Finset.Ioc 0 N, integerFrequencySchurWeight n *
        primePowerCovarianceDirectedEntry n m := by
      apply Finset.sum_congr rfl
      intro m hm
      have hmpos := (Finset.mem_Ioc.mp hm).1
      rw [Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (primePowerCovarianceSymmetricEntry_nonneg n m)]
      exact primePowerCovarianceSymmetricEntry_mul_weight n m hnpos hmpos
    _ = integerFrequencySchurWeight n *
        (∑ m ∈ Finset.Ioc 0 N, primePowerCovarianceDirectedEntry n m) := by
      rw [Finset.mul_sum]
    _ = _ := by rw [sum_primePowerCovarianceDirectedEntry_eq N n hn hnN]

/-- The actual arithmetic symmetric covariance kernel obeys the explicit
    full-dictionary quadratic Schur bound. No phase cancellation hypothesis. -/
theorem primePowerCovarianceSymmetricEntry_pairing_bound (N : ℕ) (a : ℕ → ℂ) :
    ‖finiteGramErrorPairing (Finset.Ioc 0 N) a
      (fun n m => (primePowerCovarianceSymmetricEntry n m : ℂ))‖ ≤
      (Real.log N + Real.log 4 + 4) * (∑ n ∈ Finset.Ioc 0 N, ‖a n‖ ^ 2) := by
  apply finiteGramErrorPairing_norm_le_weighted_schur
    (Finset.Ioc 0 N) a (fun n m => (primePowerCovarianceSymmetricEntry n m : ℂ))
    integerFrequencySchurWeight (Real.log N + Real.log 4 + 4)
  · intro n hn
    exact integerFrequencySchurWeight_pos n (Finset.mem_Ioc.mp hn).1
  · intro n hn m hm
    rw [primePowerCovarianceSymmetricEntry_symm n m
      (Finset.mem_Ioc.mp hn).1 (Finset.mem_Ioc.mp hm).1]
  · intro n hn
    obtain ⟨hnpos, hnN⟩ := Finset.mem_Ioc.mp hn
    have hn1 : 1 ≤ n := hnpos
    rw [primePowerCovarianceSymmetricEntry_weighted_row N n hn1 hnN]
    calc
      _ ≤ integerFrequencySchurWeight n * (Real.log N + Real.log 4 + 4) :=
        mul_le_mul_of_nonneg_left (primePowerCovarianceRowBudget_le N n hn1 hnN)
          (integerFrequencySchurWeight_pos n hnpos).le
      _ = _ := mul_comm _ _

private theorem finiteGramErrorPairing_mul_kernel {ι : Type*}
    (s : Finset ι) (a : ι → ℂ) (R : ι → ι → ℂ) (c : ℂ) :
    finiteGramErrorPairing s a (fun n m => c * R n m) =
      c * finiteGramErrorPairing s a R := by
  unfold finiteGramErrorPairing
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m hm
  ring

/-- The signed normalized covariance has the exact 1/(2 pi) Schur constant
    asserted by the manuscript, with an explicit elementary O(1) remainder. -/
theorem primePowerCovariance_normalized_pairing_bound (N : ℕ) (a : ℕ → ℂ) :
    ‖finiteGramErrorPairing (Finset.Ioc 0 N) a (fun n m =>
      ((-1 / (2 * Real.pi) : ℝ) : ℂ) *
        (primePowerCovarianceSymmetricEntry n m : ℂ))‖ ≤
      ((Real.log N + Real.log 4 + 4) / (2 * Real.pi)) *
        (∑ n ∈ Finset.Ioc 0 N, ‖a n‖ ^ 2) := by
  have hpi : (0 : ℝ) ≤ 2 * Real.pi :=
    (mul_pos (by norm_num : (0 : ℝ) < 2) Real.pi_pos).le
  have hc : ‖((-1 / (2 * Real.pi) : ℝ) : ℂ)‖ = (2 * Real.pi)⁻¹ := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_div, abs_neg, abs_one,
      abs_of_nonneg hpi, one_div]
  rw [finiteGramErrorPairing_mul_kernel, norm_mul, hc]
  calc
    _ ≤ (2 * Real.pi)⁻¹ * ((Real.log N + Real.log 4 + 4) *
        (∑ n ∈ Finset.Ioc 0 N, ‖a n‖ ^ 2)) :=
      mul_le_mul_of_nonneg_left (primePowerCovarianceSymmetricEntry_pairing_bound N a)
        (by positivity)
    _ = _ := by ring

end RiemannResearch.Fourier
