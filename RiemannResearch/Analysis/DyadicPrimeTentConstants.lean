import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic

/-! # Odd-harmonic constants for dyadic prime phases

The coefficients come from the periodic tent and the prime-character bias of
Ford–Zaharescu, *On the distribution of imaginary parts of zeros of the Riemann
zeta function*, Theorem 1. Here we separate the first harmonic and show that
the positive contribution of all higher harmonics is summable across primes.
-/

noncomputable section

namespace RiemannResearch.Analysis.DyadicZeroWasserstein

/-- The odd Fourier harmonics in the integral of the periodic tent against
the first-order signed prime marginal. -/
def primeTentConstant (p : ℕ) : ℝ :=
  2 * Real.log p / Real.pi ^ 2 *
    ∑' j : ℕ, (Real.sqrt (p : ℝ))⁻¹ ^ (2 * j + 1) / ((2 * j + 1 : ℕ) : ℝ) ^ 2

private def oddTerm (r : ℝ) (j : ℕ) : ℝ :=
  r ^ (2 * j + 1) / ((2 * j + 1 : ℕ) : ℝ) ^ 2

private theorem oddTerm_nonneg {r : ℝ} (hr : 0 ≤ r) (j : ℕ) :
    0 ≤ oddTerm r j := by
  unfold oddTerm
  positivity

private theorem oddTerm_le {r : ℝ} (hr : 0 ≤ r) (j : ℕ) :
    oddTerm r j ≤ r ^ (2 * j + 1) := by
  have h : (1 : ℝ) ≤ ((2 * j + 1 : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ 2 * j + 1)
  apply div_le_self (pow_nonneg hr _)
  nlinarith [sq_nonneg (((2 * j + 1 : ℕ) : ℝ) - 1)]

private theorem prime_decay_sq {p : ℕ} (hp : Nat.Prime p) :
    ((Real.sqrt (p : ℝ))⁻¹) ^ 2 ≤ 1 / 2 := by
  have h : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  rw [inv_pow, Real.sq_sqrt (by positivity : 0 ≤ (p : ℝ)), ← one_div]
  exact one_div_le_one_div_of_le (by norm_num) h

private theorem oddTerm_tail_le {r : ℝ} (hr : 0 ≤ r) (hr2 : r ^ 2 ≤ 1 / 2) (j : ℕ) :
    oddTerm r (j + 1) ≤ r ^ 3 * (1 / 2 : ℝ) ^ j := by
  calc
    oddTerm r (j + 1) ≤ r ^ (2 * (j + 1) + 1) := oddTerm_le hr _
    _ = r ^ 3 * (r ^ 2) ^ j := by rw [← pow_mul, ← pow_add]; congr 1; omega
    _ ≤ _ := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (sq_nonneg r) hr2 _) (pow_nonneg hr _)

private theorem oddTerm_tail_summable {r : ℝ} (hr : 0 ≤ r) (hr2 : r ^ 2 ≤ 1 / 2) :
    Summable fun j : ℕ => oddTerm r (j + 1) :=
  Summable.of_nonneg_of_le (fun j => oddTerm_nonneg hr _) (oddTerm_tail_le hr hr2)
    ((summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (1 / 2 : ℝ) < 1)).mul_left (r ^ 3))

theorem summable_primeTentTerms {p : ℕ} (hp : Nat.Prime p) :
    Summable fun j : ℕ => (Real.sqrt (p : ℝ))⁻¹ ^ (2 * j + 1) / ((2 * j + 1 : ℕ) : ℝ) ^ 2 :=
  (summable_nat_add_iff 1).mp (oddTerm_tail_summable (by positivity) (prime_decay_sq hp))

/-- Exact first harmonic plus the complete signed remainder. -/
theorem primeTentConstant_eq_first_add_tail {p : ℕ} (hp : Nat.Prime p) :
    primeTentConstant p =
      (2 / Real.pi ^ 2) * (Real.log p / Real.sqrt p) +
      (2 * Real.log p / Real.pi ^ 2) *
        ∑' j : ℕ, (Real.sqrt (p : ℝ))⁻¹ ^ (2 * (j + 1) + 1) /
          ((2 * (j + 1) + 1 : ℕ) : ℝ) ^ 2 := by
  unfold primeTentConstant
  rw [(summable_primeTentTerms hp).tsum_eq_zero_add]
  simp only [Nat.mul_zero, Nat.zero_add, pow_one, Nat.cast_one, one_pow, div_one]
  ring

/-- For each prime the tent improves even the cosine constant multiplied by
`4/π`. This is strict because the third harmonic is positive. -/
theorem primeTentConstant_gt_rescaled_cosine {p : ℕ} (hp : Nat.Prime p) :
    (4 / Real.pi) * (Real.log p / (2 * Real.pi * Real.sqrt p)) < primeTentConstant p := by
  let r := (Real.sqrt (p : ℝ))⁻¹
  have h1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
  have hr : 0 < r := inv_pos.mpr (Real.sqrt_pos.2 (by linarith))
  have hs := oddTerm_tail_summable hr.le (prime_decay_sq hp)
  have hterm : 0 < oddTerm r (0 + 1) := by unfold oddTerm; positivity
  have hmass : 0 < ∑' j : ℕ, oddTerm r (j + 1) :=
    hterm.trans_le (hs.le_tsum 0 (fun _ _ => oddTerm_nonneg hr.le _))
  rw [primeTentConstant_eq_first_add_tail hp]
  have hmain : (4 / Real.pi) * (Real.log p / (2 * Real.pi * Real.sqrt p)) =
      (2 / Real.pi ^ 2) * (Real.log p / Real.sqrt p) := by
    field_simp [Real.pi_ne_zero, (Real.sqrt_pos.2 (by linarith : 0 < (p : ℝ))).ne']
    ring
  rw [hmain]
  apply lt_add_of_pos_right
  exact mul_pos (div_pos (mul_pos (by norm_num) (Real.log_pos h1))
    (sq_pos_of_pos Real.pi_pos)) hmass

theorem primeTentConstant_pos {p : ℕ} (hp : p.Prime) : 0 < primeTentConstant p := by
  have hlog : 0 < Real.log p := Real.log_pos (by exact_mod_cast hp.one_lt)
  have hsqrt : 0 < Real.sqrt p := Real.sqrt_pos.2 (by exact_mod_cast hp.pos)
  have hpi := Real.pi_pos
  exact (show 0 < (4 / Real.pi) * (Real.log p / (2 * Real.pi * Real.sqrt p)) by positivity).trans
    (primeTentConstant_gt_rescaled_cosine hp)

/-- The excess over the correctly rescaled first harmonic, supported on primes. -/
def primeTentExcess (n : ℕ) : ℝ :=
  if n.Prime then primeTentConstant n - (2 / Real.pi ^ 2) * (Real.log n / Real.sqrt n) else 0

theorem primeTentExcess_nonneg (n : ℕ) : 0 ≤ primeTentExcess n := by
  by_cases hp : n.Prime
  · rw [primeTentExcess, if_pos hp, primeTentConstant_eq_first_add_tail hp]
    have hlog := Real.log_nonneg (show (1 : ℝ) ≤ n by exact_mod_cast hp.one_le)
    rw [add_sub_cancel_left]
    exact mul_nonneg (div_nonneg (by linarith) (sq_nonneg _))
      (tsum_nonneg (fun _ => by positivity))
  · simp [primeTentExcess, hp]

private theorem primeTentExcess_le_majorant (n : ℕ) :
    primeTentExcess n ≤ (16 / Real.pi ^ 2) * (n : ℝ) ^ (-5 / 4 : ℝ) := by
  by_cases hp : n.Prime
  · let r := (Real.sqrt (n : ℝ))⁻¹
    have hn : 0 < (n : ℝ) := by exact_mod_cast hp.pos
    have hr : 0 ≤ r := by dsimp [r]; positivity
    have hlog : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hp.one_le)
    have hgeom := hasSum_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
      (by norm_num : (1 / 2 : ℝ) < 1)
    have hsum : (∑' j : ℕ, oddTerm r (j + 1)) ≤ r ^ 3 * 2 := by
      calc
        _ ≤ ∑' j : ℕ, r ^ 3 * (1 / 2 : ℝ) ^ j :=
          (oddTerm_tail_summable hr (prime_decay_sq hp)).tsum_le_tsum
            (oddTerm_tail_le hr (prime_decay_sq hp)) (hgeom.mul_left (r ^ 3)).summable
        _ = r ^ 3 * 2 := by rw [(hgeom.mul_left (r ^ 3)).tsum_eq]; norm_num
    have hlog_le : Real.log n ≤ 4 * (n : ℝ) ^ (1 / 4 : ℝ) := by
      have h := Real.log_le_self (Real.rpow_nonneg hn.le (1 / 4 : ℝ))
      rw [Real.log_rpow hn] at h
      linarith
    have hrpow : r ^ 3 = (n : ℝ) ^ (-3 / 2 : ℝ) := by
      have hh : r = (n : ℝ) ^ (-(1 / 2 : ℝ)) := by
        rw [Real.rpow_neg hn.le, ← Real.sqrt_eq_rpow]
      rw [hh, ← Real.rpow_natCast _ 3, ← Real.rpow_mul hn.le]
      norm_num
    rw [primeTentExcess, if_pos hp, primeTentConstant_eq_first_add_tail hp, add_sub_cancel_left]
    calc
      _ ≤ (2 * Real.log n / Real.pi ^ 2) * (r ^ 3 * 2) :=
        mul_le_mul_of_nonneg_left hsum (div_nonneg (by linarith) (sq_nonneg _))
      _ = (4 / Real.pi ^ 2) * (Real.log n * r ^ 3) := by ring
      _ ≤ (4 / Real.pi ^ 2) * ((4 * (n : ℝ) ^ (1 / 4 : ℝ)) * r ^ 3) := by
        gcongr
      _ = _ := by
        rw [hrpow, mul_assoc (4 : ℝ), ← Real.rpow_add hn]
        norm_num
        ring
  · rw [primeTentExcess, if_neg hp]
    positivity

theorem summable_primeTentExcess : Summable primeTentExcess :=
  Summable.of_nonneg_of_le primeTentExcess_nonneg primeTentExcess_le_majorant
    ((Real.summable_nat_rpow.mpr (by norm_num : (-5 / 4 : ℝ) < -1)).mul_left (16 / Real.pi ^ 2))

/-- The finite correction across all prime cutoffs is strictly positive. -/
theorem primeTentExcess_tsum_pos : 0 < ∑' n, primeTentExcess n := by
  have htwo : 0 < primeTentExcess 2 := by
    rw [primeTentExcess, if_pos Nat.prime_two, sub_pos]
    convert primeTentConstant_gt_rescaled_cosine Nat.prime_two using 1
    field_simp [Real.pi_ne_zero]
    ring
  exact htwo.trans_le (summable_primeTentExcess.le_tsum 2 (fun n _ => primeTentExcess_nonneg n))

theorem tendsto_primeTentExcess_prefix :
    Filter.Tendsto (fun X : ℕ => ∑ n ∈ Finset.range X, primeTentExcess n)
      Filter.atTop (nhds (∑' n, primeTentExcess n)) :=
  summable_primeTentExcess.hasSum.tendsto_sum_nat

/-- Uniform in every finite prime set, even when the set is not an initial
segment. The universal bound is the exact sum of the higher-harmonic excess. -/
theorem exists_primeTentConstant_correction_sum_bound :
    ∃ C : ℝ, ∀ P : Finset ℕ, (∀ p ∈ P, Nat.Prime p) →
      |(∑ p ∈ P, primeTentConstant p) -
        (2 / Real.pi ^ 2) * ∑ p ∈ P, Real.log p / Real.sqrt p| ≤ C := by
  refine ⟨∑' n, primeTentExcess n, fun P hP => ?_⟩
  have heq : (∑ p ∈ P, primeTentConstant p) -
      (2 / Real.pi ^ 2) * ∑ p ∈ P, Real.log p / Real.sqrt p =
      ∑ p ∈ P, primeTentExcess p := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun p hp => by simp [primeTentExcess, hP p hp])
  rw [heq, abs_of_nonneg (Finset.sum_nonneg fun p _ => primeTentExcess_nonneg p)]
  exact summable_primeTentExcess.sum_le_tsum P (fun p _ => primeTentExcess_nonneg p)

end RiemannResearch.Analysis.DyadicZeroWasserstein
