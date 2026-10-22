import Mathlib.NumberTheory.Chebyshev
import Mathlib.Analysis.PSeries
import Mathlib.Data.Nat.Log
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

/-!
# Unconditional prime logarithmic summability

The final summation step of §5 of
`RH_Noise_Signal_Arithmetic_Repair_2026-09-07.pdf` is elementary once the
individual repair estimate is known. This module proves the required prime
weight convergence from Mathlib's unconditional Chebyshev estimate. It does
not assume a smooth-number gap theorem and does not assert one.
-/

open scoped BigOperators
namespace RiemannResearch.RH.Pareto
noncomputable section

/-- Exact dyadic cardinality estimate, retaining the natural dyadic index. -/
theorem prime_dyadic_card_mul_le (s : Finset ℕ) (j : ℕ)
    (hs : ∀ p ∈ s, p.Prime ∧ 2^j ≤ p ∧ p ≤ 2^(j+1)) :
    (s.card : ℝ) * j ≤ 4 * (2 : ℝ)^j := by
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlo : (s.card : ℝ) * ((j : ℝ) * Real.log 2) ≤
      ∑ p ∈ s, Real.log (p : ℝ) := by
    calc
      _ = ∑ _p ∈ s, (j : ℝ) * Real.log 2 := by simp
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro p hp
        have h := Real.log_le_log (by positivity : 0 < (2 : ℝ)^j)
          (show (2 : ℝ)^j ≤ (p : ℝ) by exact_mod_cast (hs p hp).2.1)
        simpa only [Real.log_pow] using h
  have hsum : (∑ p ∈ s, Real.log (p : ℝ)) ≤
      Chebyshev.theta ((2^(j+1) : ℕ) : ℝ) := by
    rw [Chebyshev.theta_eq_sum_Icc]
    simp only [Nat.floor_natCast]
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro p hp
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_Icc.mpr ⟨Nat.zero_le _, (hs p hp).2.2⟩, (hs p hp).1⟩
    · intro p hp _
      exact Real.log_nonneg (by exact_mod_cast
        (Finset.mem_filter.mp hp).2.one_lt.le)
  have htheta := Chebyshev.theta_le_log4_mul_x
    (by positivity : 0 ≤ ((2^(j+1) : ℕ) : ℝ))
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2^2 by norm_num, Real.log_pow]
    norm_num
  have hall := le_trans hlo (le_trans hsum htheta)
  rw [hlog4] at hall
  push_cast at hall
  rw [pow_succ] at hall
  apply (mul_le_mul_iff_of_pos_right hlog2).mp
  nlinarith

/-- The complete contribution of any finite collection of primes in a dyadic
block; no asymptotic prime-counting hypothesis is introduced. -/
theorem prime_dyadic_weight_sum_le (s : Finset ℕ) (j : ℕ)
    (hj : 0 < j) (ε : ℝ) (hε : 0 < ε)
    (hs : ∀ p ∈ s, p.Prime ∧ 2^j ≤ p ∧ p ≤ 2^(j+1)) :
    (∑ p ∈ s, 1 / ((p : ℝ) * (j : ℝ)^ε)) ≤
      4 / (j : ℝ)^(1+ε) := by
  have hjR : 0 < (j : ℝ) := by exact_mod_cast hj
  have hjpow : 0 < (j : ℝ)^ε := Real.rpow_pos_of_pos hjR ε
  have h2pow : 0 < (2 : ℝ)^j := by positivity
  calc
    _ ≤ ∑ _p ∈ s, 1 / ((2 : ℝ)^j * (j : ℝ)^ε) := by
      apply Finset.sum_le_sum
      intro p hp
      apply one_div_le_one_div_of_le (mul_pos h2pow hjpow)
      exact mul_le_mul_of_nonneg_right
        (by exact_mod_cast (hs p hp).2.1) hjpow.le
    _ = (s.card : ℝ) / ((2 : ℝ)^j * (j : ℝ)^ε) := by simp [div_eq_mul_inv]
    _ ≤ 4 / (j : ℝ)^(1+ε) := by
      rw [Real.rpow_one_add' hjR.le (by linarith)]
      apply (div_le_div_iff₀ (mul_pos h2pow hjpow) (mul_pos hjR hjpow)).2
      have hc := prime_dyadic_card_mul_le s j hs
      nlinarith [mul_le_mul_of_nonneg_right hc hjpow.le]

/-- A finite bound valid simultaneously for every choice of prime set. -/
theorem prime_log_weight_finset_le (s : Finset ℕ)
    (hs : ∀ p ∈ s, p.Prime) (ε : ℝ) (hε : 0 < ε) :
    (∑ p ∈ s, 1 / ((p : ℝ) * (Nat.log 2 p : ℝ)^ε)) ≤
      4 * ∑' j : ℕ, 1 / (j : ℝ)^(1+ε) := by
  classical
  let levels := s.image (Nat.log 2)
  have hmaps : ∀ p ∈ s, Nat.log 2 p ∈ levels := fun p hp =>
    Finset.mem_image_of_mem _ hp
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  calc
    _ ≤ ∑ j ∈ levels, 4 / (j : ℝ)^(1+ε) := by
      apply Finset.sum_le_sum
      intro j hj
      rcases Finset.mem_image.mp hj with ⟨p, hp, hpj⟩
      have hjpos : 0 < j := by
        have h := (Nat.le_log_iff_pow_le (by norm_num : 1 < 2)
          (hs p hp).ne_zero).2 (by simpa using (hs p hp).two_le : 2^1 ≤ p)
        omega
      have hb : ∀ p ∈ s.filter (fun p => Nat.log 2 p = j),
          p.Prime ∧ 2^j ≤ p ∧ p ≤ 2^(j+1) := by
        intro p hp
        rcases Finset.mem_filter.mp hp with ⟨hp, hpj⟩
        refine ⟨hs p hp, ?_, ?_⟩
        · simpa [hpj] using Nat.pow_log_le_self 2 (hs p hp).ne_zero
        · simpa [hpj, Nat.succ_eq_add_one] using
            (Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) p).le
      have heq : (∑ p ∈ s.filter (fun p => Nat.log 2 p = j),
          1 / ((p : ℝ) * (Nat.log 2 p : ℝ)^ε)) =
          ∑ p ∈ s.filter (fun p => Nat.log 2 p = j),
            1 / ((p : ℝ) * (j : ℝ)^ε) := by
        apply Finset.sum_congr rfl
        intro p hp
        rw [(Finset.mem_filter.mp hp).2]
      rw [heq]
      exact prime_dyadic_weight_sum_le _ j hjpos ε hε hb
    _ = 4 * ∑ j ∈ levels, 1 / (j : ℝ)^(1+ε) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact Summable.sum_le_tsum levels (fun j _ => by positivity)
        ((Real.summable_one_div_nat_rpow).2 (by linarith : 1 < 1+ε))

/-- Any positive power of the prime's logarithm makes its reciprocal summable.
This is the unconditional arithmetic summation input of the repair theorem. -/
theorem summable_prime_inv_mul_natLog_rpow (ε : ℝ) (hε : 0 < ε) :
    Summable (fun p : Nat.Primes =>
      1 / ((p.val : ℝ) * (Nat.log 2 p.val : ℝ)^ε)) := by
  classical
  apply summable_of_sum_le (c := 4 * ∑' j : ℕ, 1 / (j : ℝ)^(1+ε))
    (fun _ => by positivity)
  intro s
  have hsum : (∑ p ∈ s, 1 / ((p.val : ℝ) * (Nat.log 2 p.val : ℝ)^ε)) =
      ∑ p ∈ s.image Subtype.val, 1 / ((p : ℝ) * (Nat.log 2 p : ℝ)^ε) := by
    exact (Finset.sum_image (s := s) (g := fun p : Nat.Primes => p.val)
      (f := fun p : ℕ => 1 / ((p : ℝ) * (Nat.log 2 p : ℝ)^ε))
      (fun _ _ _ _ hab => Subtype.ext hab)).symm
  rw [hsum]
  apply prime_log_weight_finset_le _ _ ε hε
  intro p hp
  rcases Finset.mem_image.mp hp with ⟨q, _, rfl⟩
  exact q.property

/-- The same unconditional prime series with the ordinary real logarithm. -/
theorem summable_prime_inv_mul_log_rpow (ε : ℝ) (hε : 0 < ε) :
    Summable (fun p : Nat.Primes =>
      1 / ((p.val : ℝ) * (Real.log (p.val : ℝ))^ε)) := by
  have hs := (summable_prime_inv_mul_natLog_rpow ε hε).mul_left
    ((Real.log 2)^ε)⁻¹
  apply Summable.of_nonneg_of_le (fun _ => by positivity) _ hs
  intro p
  have hpR : 0 < (p.val : ℝ) := by exact_mod_cast p.property.pos
  have hj : 0 < Nat.log 2 p.val := by
    have h := (Nat.le_log_iff_pow_le (by norm_num : 1 < 2)
      p.property.ne_zero).2 (by simpa using p.property.two_le : 2^1 ≤ p.val)
    omega
  have hjR : 0 < (Nat.log 2 p.val : ℝ) := by exact_mod_cast hj
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog : (Nat.log 2 p.val : ℝ) * Real.log 2 ≤ Real.log (p.val : ℝ) := by
    have h := Real.log_le_log (by positivity : 0 < (2 : ℝ)^(Nat.log 2 p.val))
      (show (2 : ℝ)^(Nat.log 2 p.val) ≤ (p.val : ℝ) by
        exact_mod_cast Nat.pow_log_le_self 2 p.property.ne_zero)
    simpa only [Real.log_pow] using h
  have hpow := Real.rpow_le_rpow (mul_pos hjR hlog2).le hlog hε.le
  calc
    _ ≤ 1 / ((p.val : ℝ) *
        ((Nat.log 2 p.val : ℝ) * Real.log 2)^ε) := by
      apply one_div_le_one_div_of_le
        (mul_pos hpR (Real.rpow_pos_of_pos (mul_pos hjR hlog2) ε))
      exact mul_le_mul_of_nonneg_left hpow hpR.le
    _ = _ := by
      rw [Real.mul_rpow hjR.le hlog2.le]
      simp only [div_eq_mul_inv, mul_inv_rev]
      ring

/-- The logarithmic numerator in the report's exact summability estimate is
harmless. Absolute summability also handles the finitely many small primes. -/
theorem summable_prime_loglog_div_mul_log_rpow (ε : ℝ) (hε : 0 < ε) :
    Summable (fun p : Nat.Primes =>
      |Real.log (Real.log (p.val : ℝ))| /
        ((p.val : ℝ) * (Real.log (p.val : ℝ))^ε)) := by
  have hh : 0 < ε/2 := by linarith
  have hs := ((summable_prime_inv_mul_log_rpow (ε/2) hh).mul_left (ε/2)⁻¹).add
    (summable_prime_inv_mul_log_rpow (ε+1) (by linarith))
  apply Summable.of_nonneg_of_le (fun _ => by positivity) _ hs
  intro p
  have hpR : 0 < (p.val : ℝ) := by exact_mod_cast p.property.pos
  have hl : 0 < Real.log (p.val : ℝ) :=
    Real.log_pos (by exact_mod_cast p.property.one_lt)
  have he : 0 < (Real.log (p.val : ℝ))^ε := Real.rpow_pos_of_pos hl ε
  have hhalf : 0 < (Real.log (p.val : ℝ))^(ε/2) := Real.rpow_pos_of_pos hl (ε/2)
  have hupper := Real.log_le_rpow_div hl.le hh
  have hlower := Real.neg_inv_le_log hl.le
  have habs : |Real.log (Real.log (p.val : ℝ))| ≤
      (Real.log (p.val : ℝ))^(ε/2) / (ε/2) + (Real.log (p.val : ℝ))⁻¹ := by
    apply abs_le.mpr
    constructor <;> nlinarith [inv_pos.mpr hl, div_pos hhalf hh]
  have hsplit : (Real.log (p.val : ℝ))^ε =
      (Real.log (p.val : ℝ))^(ε/2) * (Real.log (p.val : ℝ))^(ε/2) := by
    rw [← Real.rpow_add hl]
    congr 1
    ring
  have hsucc : (Real.log (p.val : ℝ))^(ε+1) =
      (Real.log (p.val : ℝ))^ε * Real.log (p.val : ℝ) := by
    rw [Real.rpow_add hl, Real.rpow_one]
  calc
    _ ≤ ((Real.log (p.val : ℝ))^(ε/2) / (ε/2) +
        (Real.log (p.val : ℝ))⁻¹) /
        ((p.val : ℝ) * (Real.log (p.val : ℝ))^ε) :=
      div_le_div_of_nonneg_right habs (mul_pos hpR he).le
    _ = _ := by
      rw [hsucc, hsplit]
      field_simp [ne_of_gt hpR, ne_of_gt hl, ne_of_gt hhalf, ne_of_gt hh]

end
end RiemannResearch.RH.Pareto
