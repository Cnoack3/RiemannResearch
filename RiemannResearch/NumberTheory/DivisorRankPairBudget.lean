import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp

/-! # Total pair budget of a divisor-ranked point configuration

Factoring the divisor count proves a subpower bound at every integer power.
Consequently even the entire set of ordered pairs has negligible mass at the
Riemann--von Mangoldt normalization when the period is polynomial in the
physical height. The assertion holds for every realization and every gap mask.
-/
noncomputable section
open Filter
open scoped BigOperators Topology

namespace RiemannResearch.NumberTheory.DivisorRankPairBudget

/-- The polynomial in a prime exponent is absorbed uniformly by its geometric growth. -/
private theorem exponent_budget (k : ℕ) :
    ∃ b : ℕ, 1 ≤ b ∧ ∀ a : ℕ, (a + 1)^k ≤ b * 2^a := by
  obtain ⟨n, hn⟩ := eventually_atTop.1 ((tendsto_pow_const_div_const_pow_of_one_lt k
    (by norm_num : (1 : ℝ) < 2)).eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1)))
  let b := (n + 1)^k + 2
  refine ⟨b, by dsimp [b]; omega, ?_⟩
  intro a
  by_cases h : n ≤ a+1
  · have hu := (div_lt_iff₀ (show 0 < (2 : ℝ) ^ (a+1) by positivity)).mp (hn _ h)
    have hur : (((a+1 : ℕ) : ℝ))^k ≤ ((2 : ℝ) ^ (a+1)) := by simpa using hu.le
    have hv : (a+1)^k ≤ 2^(a+1) := by exact_mod_cast hur
    exact hv.trans (by rw [pow_succ, mul_comm]; apply Nat.mul_le_mul_right; dsimp [b]; omega)
  · have hv : (a+1)^k ≤ (n+1)^k := Nat.pow_le_pow_left (by omega) _
    have hb : (n+1)^k ≤ b := by dsimp [b]; omega
    exact (hv.trans hb).trans (Nat.le_mul_of_pos_right _ (pow_pos (by decide) _))

/-- For every positive period and every integer power, the powered divisor
count is at most a constant times the period. -/
theorem divisor_card_pow_le_const_mul (k : ℕ) :
    ∃ C : ℕ, 0 < C ∧ ∀ L : ℕ, L ≠ 0 → L.divisors.card ^ k ≤ C * L := by
  obtain ⟨b, hb, hbnd⟩ := exponent_budget k
  refine ⟨b ^ (2^k), pow_pos (by omega) _, ?_⟩
  intro L hL
  let w (p : ℕ) := if p < 2^k then b else 1
  have hfac (p : ℕ) (hp : p ∈ L.primeFactors) :
      (L.factorization p + 1)^k ≤ w p * p^(L.factorization p) := by
    let a := L.factorization p
    change (a+1)^k ≤ w p * p^a
    by_cases h : p < 2^k
    · simpa [w,h] using (hbnd a).trans (Nat.mul_le_mul_left b
        (Nat.pow_le_pow_left (Nat.prime_of_mem_primeFactors hp).two_le _))
    · have ha : a+1 ≤ 2^a := Nat.lt_two_pow_self
      have hz := (Nat.pow_le_pow_left ha k).trans_eq (by rw [←pow_mul, Nat.mul_comm a k, pow_mul])
      simpa [w,h] using hz.trans (Nat.pow_le_pow_left (le_of_not_gt h) a)
  have hc : (∏ p ∈ L.primeFactors, w p) ≤ b^(2^k) := by
    have hsub : (L.primeFactors.filter (· < 2^k)) ⊆ Finset.range (2^k) :=
      fun p hp => Finset.mem_range.mpr (Finset.mem_filter.mp hp).2
    have hcard := Finset.card_le_card hsub
    change (∏ p ∈ L.primeFactors, if p < 2^k then b else 1) ≤ _
    rw [← Finset.prod_filter, Finset.prod_const]
    exact Nat.pow_le_pow_right (by omega) (by simpa using hcard)
  have hprod : (∏ p ∈ L.primeFactors, p ^ L.factorization p) = L := by
    simpa [Finsupp.prod, Nat.support_factorization] using Nat.prod_factorization_pow_eq_self hL
  calc
    L.divisors.card ^ k = ∏ p ∈ L.primeFactors, (L.factorization p + 1)^k := by
      rw [Nat.card_divisors hL, Finset.prod_pow]
    _ ≤ ∏ p ∈ L.primeFactors, w p * p ^ L.factorization p := Finset.prod_le_prod' hfac
    _ ≤ b^(2^k) * L := by rw [Finset.prod_mul_distrib, hprod]; exact Nat.mul_le_mul_right _ hc

/-- Any count or expected mass bounded by the square of the divisor rank
vanishes after the physical PCC normalization at polynomially related heights. -/
theorem normalized_pair_mass_tendsto_zero {L : ℕ → ℕ} {T A : ℕ → ℝ}
    (hT : Tendsto T atTop atTop) (k : ℕ) (hk : k ≠ 0)
    (hL : ∀ᶠ j in atTop, L j ≠ 0 ∧ (L j : ℝ) ≤ (T j)^k)
    (hA : ∀ᶠ j in atTop, 0 ≤ A j ∧ A j ≤ ((L j).divisors.card : ℝ)^2) :
    Tendsto (fun j => A j / (T j * Real.log (T j) / (2 * Real.pi))) atTop (𝓝 0) := by
  obtain ⟨C, hC, hbound⟩ := divisor_card_pow_le_const_mul (2*k)
  have hc : (1 : ℝ) ≤ C := by exact_mod_cast hC
  have ht := hT.eventually_gt_atTop 1
  apply squeeze_zero' ?_ ?_ ((Real.tendsto_log_atTop.comp hT).const_div_atTop
    ((C : ℝ) * (2 * Real.pi)))
  · filter_upwards [ht, hA] with j hj ha
    exact div_nonneg ha.1 (by have := Real.log_pos hj; positivity)
  · filter_upwards [ht,hL,hA] with j hj hl ha
    have ht0 : 0 < T j := by linarith
    have hl0 := Real.log_pos hj
    have hB : ((L j).divisors.card : ℝ)^(2*k) ≤ (C : ℝ) * (L j : ℝ) := by
      exact_mod_cast hbound (L j) hl.1
    have hB' : ((L j).divisors.card : ℝ)^2 ≤ C * T j := by
      apply (pow_le_pow_iff_left₀ (sq_nonneg _) (by positivity) hk).mp
      calc
        _ = ((L j).divisors.card : ℝ)^(2*k) := (pow_mul _ _ _).symm
        _ ≤ C * (L j : ℝ) := hB
        _ ≤ (C : ℝ)^k * (T j)^k := mul_le_mul (le_self_pow₀ hc hk) hl.2 (by positivity) (by positivity)
        _ = _ := (mul_pow _ _ _).symm
    calc
      _ ≤ ((C : ℝ) * T j) / (T j * Real.log (T j) / (2 * Real.pi)) :=
        div_le_div_of_nonneg_right (ha.2.trans hB') (by positivity)
      _ = _ := by simp only [Function.comp_apply]; field_simp

/-- Configuration-level uniformity. The selected pairs may depend arbitrarily
on the stage, the realized point locations, their ordering, and the gap width. -/
theorem selected_pairs_tendsto_zero {L r : ℕ → ℕ} {T : ℕ → ℝ}
    (S : ∀ j, Finset (Fin (r j) × Fin (r j))) (hr : ∀ j, r j ≤ (L j).divisors.card)
    (hT : Tendsto T atTop atTop) (k : ℕ) (hk : k ≠ 0)
    (hL : ∀ᶠ j in atTop, L j ≠ 0 ∧ (L j : ℝ) ≤ (T j)^k) :
    Tendsto (fun j => ((S j).card : ℝ) / (T j * Real.log (T j) / (2 * Real.pi)))
      atTop (𝓝 0) := by
  apply normalized_pair_mass_tendsto_zero hT k hk hL
  apply Filter.Eventually.of_forall
  intro j
  refine ⟨Nat.cast_nonneg _, ?_⟩
  have hs := (S j).card_le_univ
  have hc : (S j).card ≤ (L j).divisors.card ^ 2 := by
    simpa only [Fintype.card_prod, Fintype.card_fin, pow_two] using
      hs.trans (by simpa using Nat.mul_le_mul (hr j) (hr j))
  exact_mod_cast hc

end RiemannResearch.NumberTheory.DivisorRankPairBudget
