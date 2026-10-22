import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.EulerProduct.Basic
import Mathlib.NumberTheory.ZetaValues
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# The squarefree reciprocal-square series and its Euler product

Source: the classical Euler-product calculation used in equation (40) of
RH_CRT_Packet_Research_2026-09-09.md. Mathlib supplies the general absolutely
convergent Euler-product theorem and the evaluations of ζ(2), ζ(4).
-/

namespace RiemannResearch.NumberTheory

open scoped BigOperators

noncomputable section

private def squarefreeWeight : ArithmeticFunction ℝ :=
  ⟨fun n => (ArithmeticFunction.moebius n : ℝ) ^ 2 / (n : ℝ) ^ 2, by simp⟩

private def zetaPowerWeight (k : ℕ) : ArithmeticFunction ℝ :=
  ⟨fun n => 1 / (n : ℝ) ^ (k + 1), by simp⟩

@[simp] private theorem squarefreeWeight_apply (n : ℕ) :
    squarefreeWeight n = (ArithmeticFunction.moebius n : ℝ) ^ 2 / (n : ℝ) ^ 2 := rfl

@[simp] private theorem zetaPowerWeight_apply (k n : ℕ) :
    zetaPowerWeight k n = 1 / (n : ℝ) ^ (k + 1) := rfl

private theorem squarefreeWeight_multiplicative : squarefreeWeight.IsMultiplicative := by
  apply ArithmeticFunction.IsMultiplicative.iff_ne_zero.mpr
  constructor
  · simp only [squarefreeWeight_apply]
    norm_num
  · intro m n hm hn hc
    have hmu : (ArithmeticFunction.moebius (m * n) : ℝ) =
        (ArithmeticFunction.moebius m : ℝ) * (ArithmeticFunction.moebius n : ℝ) := by
      exact_mod_cast ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hc
    simp only [squarefreeWeight_apply, Nat.cast_mul, hmu, mul_pow, div_mul_div_comm]

private theorem zetaPowerWeight_multiplicative (k : ℕ) : (zetaPowerWeight k).IsMultiplicative := by
  apply ArithmeticFunction.IsMultiplicative.iff_ne_zero.mpr
  constructor
  · simp only [zetaPowerWeight_apply]
    norm_num
  · intro m n hm hn hc
    simp [zetaPowerWeight_apply, Nat.cast_mul, mul_pow, div_mul_div_comm] <;> ring

private theorem squarefreeWeight_norm_summable : Summable (fun n => ‖squarefreeWeight n‖) := by
  apply hasSum_zeta_two.summable.of_norm_bounded
  intro n
  have hmu : |(ArithmeticFunction.moebius n : ℝ)| ≤ 1 := by
    exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := n))
  have hsq : (ArithmeticFunction.moebius n : ℝ) ^ 2 ≤ 1 := by
    have h := mul_self_le_mul_self (abs_nonneg (ArithmeticFunction.moebius n : ℝ)) hmu
    simpa only [← pow_two, sq_abs, one_pow] using h
  simp only [Real.norm_eq_abs, abs_abs]
  change |(ArithmeticFunction.moebius n : ℝ) ^ 2 / (n : ℝ) ^ 2| ≤ 1 / (n : ℝ) ^ 2
  rw [abs_of_nonneg (by positivity)]
  exact div_le_div_of_nonneg_right hsq (sq_nonneg _)

private theorem zetaPowerWeight_norm_summable_two : Summable (fun n => ‖zetaPowerWeight 1 n‖) := by
  have h : (fun n : ℕ => ‖zetaPowerWeight 1 n‖) = (fun n : ℕ => 1 / (n : ℝ) ^ 2) := by
    funext n
    simp [zetaPowerWeight_apply, Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ 1 / (n : ℝ) ^ 2)]
  rw [h]
  exact hasSum_zeta_two.summable

private theorem zetaPowerWeight_norm_summable_four : Summable (fun n => ‖zetaPowerWeight 3 n‖) := by
  have h : (fun n : ℕ => ‖zetaPowerWeight 3 n‖) = (fun n : ℕ => 1 / (n : ℝ) ^ 4) := by
    funext n
    simp [zetaPowerWeight_apply, Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ 1 / (n : ℝ) ^ 4)]
  rw [h]
  exact hasSum_zeta_four.summable

private theorem squarefreeWeight_prime_factor (p : ℕ) (hp : Nat.Prime p) :
    (∑' e : ℕ, squarefreeWeight (p ^ e)) = 1 + 1 / (p : ℝ) ^ 2 := by
  have hs : (∑' e : ℕ, squarefreeWeight (p ^ e)) =
      ∑ e ∈ ({0, 1} : Finset ℕ), squarefreeWeight (p ^ e) := by
    apply tsum_eq_sum
    intro e he
    have he0 : e ≠ 0 := by intro h; apply he; simp [h]
    have he1 : e ≠ 1 := by intro h; apply he; simp [h]
    simp [squarefreeWeight_apply, ArithmeticFunction.moebius_apply_prime_pow hp he0, he1]
  rw [hs]
  simp [squarefreeWeight_apply, ArithmeticFunction.moebius_apply_prime hp]

private theorem zetaPowerWeight_prime_factor (k p : ℕ) (hp : Nat.Prime p)
    (hpow : 1 < (p : ℝ) ^ (k + 1)) :
    (∑' e : ℕ, zetaPowerWeight k (p ^ e)) = (1 - 1 / (p : ℝ) ^ (k + 1))⁻¹ := by
  have he (e : ℕ) : zetaPowerWeight k (p ^ e) = (1 / (p : ℝ) ^ (k + 1)) ^ e := by
    simp only [zetaPowerWeight_apply, Nat.cast_pow,
      one_div, inv_pow, ← pow_mul]
    rw [Nat.mul_comm e (k + 1)]
  simp_rw [he]
  exact tsum_geometric_of_lt_one (by positivity) ((div_lt_one (by positivity)).mpr hpow)

private theorem prime_square_gt_one (p : Nat.Primes) : 1 < (p : ℝ) ^ 2 := by
  have hp : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast p.property.two_le
  nlinarith

private theorem prime_fourth_gt_one (p : Nat.Primes) : 1 < (p : ℝ) ^ 4 := by
  have hp := prime_square_gt_one p
  nlinarith [sq_nonneg ((p : ℝ) ^ 2 - 1)]

private theorem squarefreeWeight_hasProd :
    HasProd (fun p : Nat.Primes => 1 + 1 / (p : ℝ) ^ 2)
      (∑' n : ℕ, (ArithmeticFunction.moebius n : ℝ) ^ 2 / (n : ℝ) ^ 2) := by
  have h := squarefreeWeight_multiplicative.eulerProduct_hasProd squarefreeWeight_norm_summable
  have hlocal (p : Nat.Primes) : (∑' e : ℕ, squarefreeWeight (p.val ^ e)) =
      1 + 1 / (p : ℝ) ^ 2 := squarefreeWeight_prime_factor p p.property
  simp_rw [hlocal] at h
  simpa only [squarefreeWeight_apply] using h

private theorem reciprocal_square_hasProd :
    HasProd (fun p : Nat.Primes => (1 - 1 / (p : ℝ) ^ 2)⁻¹) (Real.pi ^ 2 / 6) := by
  have h := (zetaPowerWeight_multiplicative 1).eulerProduct_hasProd zetaPowerWeight_norm_summable_two
  have hlocal (p : Nat.Primes) : (∑' e : ℕ, zetaPowerWeight 1 (p.val ^ e)) =
      (1 - 1 / (p : ℝ) ^ 2)⁻¹ := zetaPowerWeight_prime_factor 1 p p.property (prime_square_gt_one p)
  simp_rw [hlocal] at h
  simpa only [zetaPowerWeight_apply, hasSum_zeta_two.tsum_eq] using h

private theorem reciprocal_fourth_hasProd :
    HasProd (fun p : Nat.Primes => (1 - 1 / (p : ℝ) ^ 4)⁻¹) (Real.pi ^ 4 / 90) := by
  have h := (zetaPowerWeight_multiplicative 3).eulerProduct_hasProd zetaPowerWeight_norm_summable_four
  have hlocal (p : Nat.Primes) : (∑' e : ℕ, zetaPowerWeight 3 (p.val ^ e)) =
      (1 - 1 / (p : ℝ) ^ 4)⁻¹ := zetaPowerWeight_prime_factor 3 p p.property (prime_fourth_gt_one p)
  simp_rw [hlocal] at h
  simpa only [zetaPowerWeight_apply, hasSum_zeta_four.tsum_eq] using h

/-- The full squarefree reciprocal-square series is evaluated without a hypothesis. -/
theorem squarefree_reciprocal_square_sum :
    (∑' n : ℕ, (ArithmeticFunction.moebius n : ℝ) ^ 2 / (n : ℝ) ^ 2) =
      15 / Real.pi ^ 2 := by
  have hm := squarefreeWeight_hasProd.mul reciprocal_fourth_hasProd
  have hlocal (p : Nat.Primes) :
      (1 + 1 / (p : ℝ) ^ 2) * (1 - 1 / (p : ℝ) ^ 4)⁻¹ =
        (1 - 1 / (p : ℝ) ^ 2)⁻¹ := by
    have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast p.property.ne_zero
    have hp2 : (p : ℝ) ^ 2 - 1 ≠ 0 := ne_of_gt (sub_pos.mpr (prime_square_gt_one p))
    have hp4 : (p : ℝ) ^ 4 - 1 ≠ 0 := ne_of_gt (sub_pos.mpr (prime_fourth_gt_one p))
    field_simp <;> ring
  simp_rw [hlocal] at hm
  have he := hm.unique reciprocal_square_hasProd
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  apply (eq_div_iff (pow_ne_zero 2 hpi)).mpr
  field_simp at he
  have he' :
      ((∑' n : ℕ, (ArithmeticFunction.moebius n : ℝ) ^ 2 / (n : ℝ) ^ 2) *
        Real.pi ^ 2 - 15) * Real.pi ^ 2 = 0 := by nlinarith
  have hv := (mul_eq_zero.mp he').resolve_right (pow_ne_zero 2 hpi)
  linarith

private def roughSquarefreeWeight : ArithmeticFunction ℝ :=
  ⟨fun n => if Nat.Coprime n 6 then squarefreeWeight n else 0, by norm_num⟩

@[simp] private theorem roughSquarefreeWeight_apply (n : ℕ) :
    roughSquarefreeWeight n = if Nat.Coprime n 6 then squarefreeWeight n else 0 := rfl

private theorem roughSquarefreeWeight_multiplicative : roughSquarefreeWeight.IsMultiplicative := by
  apply ArithmeticFunction.IsMultiplicative.iff_ne_zero.mpr
  constructor
  · simp only [roughSquarefreeWeight_apply]
    norm_num
  · intro m n hm hn hc
    have he := squarefreeWeight_multiplicative.map_mul_of_coprime hc
    simp only [roughSquarefreeWeight_apply, Nat.coprime_mul_iff_left]
    by_cases hm6 : Nat.Coprime m 6
    · by_cases hn6 : Nat.Coprime n 6
      · rw [if_pos ⟨hm6, hn6⟩, if_pos hm6, if_pos hn6, he]
      · rw [if_neg (fun h => hn6 h.2), if_pos hm6,
          if_neg hn6, mul_zero]
    · by_cases hn6 : Nat.Coprime n 6
      · rw [if_neg (fun h => hm6 h.1), if_neg hm6,
          if_pos hn6, zero_mul]
      · rw [if_neg (fun h => hm6 h.1), if_neg hm6, if_neg hn6, zero_mul]


private theorem roughSquarefreeWeight_norm_summable : Summable (fun n => ‖roughSquarefreeWeight n‖) := by
  apply squarefreeWeight_norm_summable.of_norm_bounded
  intro n
  simp only [roughSquarefreeWeight_apply]
  split_ifs <;> simp [norm_nonneg] <;> positivity

private theorem roughSquarefreeWeight_prime_factor (p : ℕ) (hp : Nat.Prime p) :
    (∑' e : ℕ, roughSquarefreeWeight (p ^ e)) =
      if Nat.Coprime p 6 then 1 + 1 / (p : ℝ) ^ 2 else 1 := by
  have hs : (∑' e : ℕ, roughSquarefreeWeight (p ^ e)) =
      ∑ e ∈ ({0, 1} : Finset ℕ), roughSquarefreeWeight (p ^ e) := by
    apply tsum_eq_sum
    intro e he
    have he0 : e ≠ 0 := by intro h; apply he; simp [h]
    have he1 : e ≠ 1 := by intro h; apply he; simp [h]
    simp [roughSquarefreeWeight_apply, squarefreeWeight_apply,
      ArithmeticFunction.moebius_apply_prime_pow hp he0, he1]
  rw [hs, Finset.sum_insert (by decide : (0 : ℕ) ∉ ({1} : Finset ℕ)),
    Finset.sum_singleton]
  have hzero : roughSquarefreeWeight (p ^ 0) = 1 := by
    simp [roughSquarefreeWeight_apply, squarefreeWeight_apply]
  rw [hzero, pow_one, roughSquarefreeWeight_apply, squarefreeWeight_apply,
    ArithmeticFunction.moebius_apply_prime hp]
  by_cases hc : Nat.Coprime p 6
  · rw [if_pos hc, if_pos hc]
    norm_num
  · rw [if_neg hc, if_neg hc]
    norm_num


private theorem roughSquarefreeWeight_hasProd :
    HasProd (fun p : Nat.Primes => if Nat.Coprime p.val 6 then 1 + 1 / (p : ℝ) ^ 2 else 1)
      (∑' n : ℕ, roughSquarefreeWeight n) := by
  have h := roughSquarefreeWeight_multiplicative.eulerProduct_hasProd roughSquarefreeWeight_norm_summable
  have hlocal (p : Nat.Primes) : (∑' e : ℕ, roughSquarefreeWeight (p.val ^ e)) =
      if Nat.Coprime p.val 6 then 1 + 1 / (p : ℝ) ^ 2 else 1 :=
    roughSquarefreeWeight_prime_factor p p.property
  simpa only [hlocal] using h

private def seedEulerCorrection (p : Nat.Primes) : ℝ :=
  if p.val = 2 then 5 / 4 else if p.val = 3 then 10 / 9 else 1

private theorem seedEulerCorrection_hasProd : HasProd seedEulerCorrection ((25 : ℝ) / 18) := by
  classical
  let p2 : Nat.Primes := ⟨2, by decide⟩
  let p3 : Nat.Primes := ⟨3, by decide⟩
  have h : HasProd seedEulerCorrection
      (∏ p ∈ ({p2, p3} : Finset Nat.Primes), seedEulerCorrection p) := by
    apply hasProd_prod_of_ne_finset_one
    intro p hp
    have h2 : p.val ≠ 2 := by
      intro he
      have he' : p = p2 := Subtype.ext he
      apply hp
      simp [he']
    have h3 : p.val ≠ 3 := by
      intro he
      have he' : p = p3 := Subtype.ext he
      apply hp
      simp [he']
    simp [seedEulerCorrection, h2, h3]
  have hne : p2 ≠ p3 := by
    intro he
    have hv := congrArg Subtype.val he
    norm_num [p2, p3] at hv
  have hmem : p2 ∉ ({p3} : Finset Nat.Primes) := by simpa only [Finset.mem_singleton] using hne
  rw [Finset.prod_insert hmem, Finset.prod_singleton] at h
  norm_num [p2, p3, seedEulerCorrection] at h
  exact h

private theorem prime_coprime_six {p : ℕ} (hp : Nat.Prime p) (h2 : p ≠ 2) (h3 : p ≠ 3) :
    Nat.Coprime p 6 := by
  apply hp.coprime_iff_not_dvd.mpr
  intro hd
  have hb : p ≤ 6 := Nat.le_of_dvd (by omega) hd
  have hp2 := hp.two_le
  interval_cases p <;> norm_num at *
  exact (by decide : ¬ Nat.Prime 6) hp

private theorem seedEulerCorrection_mul_factor (p : Nat.Primes) :
    seedEulerCorrection p *
      (if Nat.Coprime p.val 6 then 1 + 1 / (p : ℝ) ^ 2 else 1) =
        1 + 1 / (p : ℝ) ^ 2 := by
  by_cases h2 : p.val = 2
  · have hcop : ¬ Nat.Coprime p.val 6 := by rw [h2]; decide
    simp only [seedEulerCorrection, if_pos h2, if_neg hcop, mul_one]
    have hpR : (p : ℝ) = 2 := by exact_mod_cast h2
    rw [hpR]
    norm_num
  by_cases h3 : p.val = 3
  · have hcop : ¬ Nat.Coprime p.val 6 := by rw [h3]; decide
    simp only [seedEulerCorrection, if_neg h2, if_pos h3, if_neg hcop, mul_one]
    have hpR : (p : ℝ) = 3 := by exact_mod_cast h3
    rw [hpR]
    norm_num
  have hc := prime_coprime_six p.property h2 h3
  simp [seedEulerCorrection, h2, h3, hc]

private theorem roughSquarefreeWeight_sum :
    (∑' n : ℕ, roughSquarefreeWeight n) = 54 / (5 * Real.pi ^ 2) := by
  have hm := seedEulerCorrection_hasProd.mul roughSquarefreeWeight_hasProd
  simp_rw [seedEulerCorrection_mul_factor] at hm
  have he := hm.unique squarefreeWeight_hasProd
  rw [squarefree_reciprocal_square_sum] at he
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  apply (eq_div_iff (by positivity : (5 : ℝ) * Real.pi ^ 2 ≠ 0)).mpr
  field_simp at he
  nlinarith

/-- Removing the exact prime factors at 2 and 3 yields the rough-core series. -/
theorem hasSum_squarefree_coprime_six :
    HasSum (fun n : ℕ => if Nat.Coprime n 6 then
      (ArithmeticFunction.moebius n : ℝ) ^ 2 / (n : ℝ) ^ 2 else 0)
        (54 / (5 * Real.pi ^ 2)) := by
  have hs := (summable_norm_iff.mp roughSquarefreeWeight_norm_summable).hasSum
  rw [roughSquarefreeWeight_sum] at hs
  have hf : (fun n : ℕ => roughSquarefreeWeight n) =
      (fun n : ℕ => if Nat.Coprime n 6 then
        (ArithmeticFunction.moebius n : ℝ) ^ 2 / (n : ℝ) ^ 2 else 0) := by
    funext n
    simp only [roughSquarefreeWeight_apply, squarefreeWeight_apply]
  change HasSum (fun n : ℕ => roughSquarefreeWeight n) _ at hs
  rw [hf] at hs
  exact hs

end
end RiemannResearch.NumberTheory
