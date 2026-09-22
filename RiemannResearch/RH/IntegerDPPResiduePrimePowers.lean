import RiemannResearch.RH.IntegerDPPResidueAccounting
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.Data.Nat.Factorization.Basic

/-!
# Prime-power steps in the residue-class DPP recurrence

Source: user-provided von Mangoldt case-split request, September 2026.
Prime-power divisibility identifies exactly when the canonical lcm changes.
At Lambda(N+2)=0 there is no retention loss; at N+2=p^(k+1) the modulus
is multiplied by p. The gain and loss budgets below start after q_1=1.
Neither the prime-power split nor these upper bounds prove limit q_N=1.
-/

open scoped BigOperators
noncomputable section
namespace RiemannResearch.RH.Pareto.IntegerDPP

theorem residueModulus_succ_eq_of_vonMangoldt_zero (N : ℕ)
    (hΛ : ArithmeticFunction.vonMangoldt (N + 2) = 0) :
    residueModulus (N + 1) = residueModulus N := by
  have hn : ¬ IsPrimePow (N + 2) := ArithmeticFunction.vonMangoldt_eq_zero_iff.mp hΛ
  have hd : N + 2 ∣ residueModulus N := by
    apply (Nat.dvd_iff_prime_pow_dvd_dvd _ _).mpr
    intro p k hp hpk
    by_cases hk : k = 0
    · simp [hk]
    have hpp : IsPrimePow (p ^ k) := hp.isPrimePow.pow hk
    have hle : p ^ k ≤ N + 2 := Nat.le_of_dvd (by omega) hpk
    have hne : p ^ k ≠ N + 2 := by
      intro he
      exact hn (he ▸ hpp)
    have hlt : p ^ k - 2 < N := by have := hpp.two_le; omega
    simpa only [Nat.sub_add_cancel hpp.two_le] using
      conductor_dvd_residueModulus N (p ^ k - 2) hlt
  change Nat.lcm (residueModulus N) (N + 2) = residueModulus N
  exact Nat.lcm_eq_left hd

private theorem primePow_dvd_lcm_iff {p k a b : ℕ} (hp : Nat.Prime p)
    (ha : 0 < a) (hb : 0 < b) :
    p ^ k ∣ Nat.lcm a b ↔ p ^ k ∣ a ∨ p ^ k ∣ b := by
  rw [hp.pow_dvd_iff_le_factorization (ne_of_gt (Nat.lcm_pos ha hb)),
    hp.pow_dvd_iff_le_factorization ha.ne',
    hp.pow_dvd_iff_le_factorization hb.ne',
    Nat.factorization_lcm ha.ne' hb.ne', Finsupp.sup_apply]
  exact le_max_iff

theorem primePow_le_of_dvd_residueModulus (N d : ℕ) (hd : IsPrimePow d)
    (hdiv : d ∣ residueModulus N) : d ≤ N + 1 := by
  obtain ⟨p, k, hp, hk, rfl⟩ := (isPrimePow_nat_iff d).mp hd
  revert hdiv
  induction N with
  | zero =>
    intro hdiv
    change p ^ k ∣ 1 at hdiv
    exact Nat.le_of_dvd (by omega) hdiv
  | succ N ih =>
    intro hdiv
    change p ^ k ∣ Nat.lcm (residueModulus N) (N+2) at hdiv
    rcases (primePow_dvd_lcm_iff hp (residueModulus_pos N) (by omega)).mp hdiv with h | h
    · exact le_trans (ih h) (by omega)
    · exact Nat.le_of_dvd (by omega) h

theorem residueModulus_lt_succ_of_vonMangoldt_ne_zero (N : ℕ)
    (hΛ : ArithmeticFunction.vonMangoldt (N+2) ≠ 0) :
    residueModulus N < residueModulus (N+1) := by
  have hd : IsPrimePow (N+2) := ArithmeticFunction.vonMangoldt_ne_zero_iff.mp hΛ
  have hle : residueModulus N ≤ residueModulus (N+1) :=
    Nat.le_of_dvd (residueModulus_pos _) (Nat.dvd_lcm_left _ _)
  apply lt_of_le_of_ne hle
  intro he
  have hdiv : N+2 ∣ residueModulus (N+1) := Nat.dvd_lcm_right _ _
  rw [←he] at hdiv
  have := primePow_le_of_dvd_residueModulus N (N+2) hd hdiv
  omega

theorem residueModulus_succ_eq_iff_vonMangoldt_zero (N : ℕ) :
    residueModulus (N+1) = residueModulus N ↔
      ArithmeticFunction.vonMangoldt (N+2) = 0 := by
  constructor
  · intro he
    by_contra hΛ
    have hlt := residueModulus_lt_succ_of_vonMangoldt_ne_zero N hΛ
    omega
  · exact residueModulus_succ_eq_of_vonMangoldt_zero N

theorem residueModulus_succ_of_prime_power (N p k : ℕ) (hp : Nat.Prime p)
    (hpow : N + 2 = p ^ (k + 1)) :
    residueModulus (N + 1) = p * residueModulus N := by
  have hpp : IsPrimePow (N + 2) := by
    rw [hpow]
    exact hp.isPrimePow.pow (by omega)
  have hstrict := residueModulus_lt_succ_of_vonMangoldt_ne_zero N
    (ArithmeticFunction.vonMangoldt_ne_zero_iff.mpr hpp)
  have hprev : p ^ k ∣ residueModulus N := by
    by_cases hk : k = 0
    · simp [hk]
    have htwo := (hp.isPrimePow.pow hk).two_le
    have hlt : p ^ k < N + 2 := by
      rw [hpow]
      exact pow_lt_pow_right₀ hp.one_lt (by omega)
    simpa only [Nat.sub_add_cancel htwo] using
      conductor_dvd_residueModulus N (p ^ k - 2) (by omega)
  have hnew : N + 2 ∣ p * residueModulus N := by
    obtain ⟨c, hc⟩ := hprev
    refine ⟨c, ?_⟩
    rw [hc, hpow, pow_succ]
    ring
  have hnext : residueModulus (N + 1) ∣ p * residueModulus N :=
    Nat.lcm_dvd (by exact ⟨p, by ring⟩) hnew
  obtain ⟨c, hc⟩ : residueModulus N ∣ residueModulus (N + 1) :=
    Nat.dvd_lcm_left _ _
  have hcp : c ∣ p := (Nat.mul_dvd_mul_iff_left (residueModulus_pos N)).mp (by
    simpa only [hc, Nat.mul_comm p (residueModulus N)] using hnext)
  rcases hp.eq_one_or_self_of_dvd c hcp with hc1 | hcp
  · rw [hc, hc1, Nat.mul_one] at hstrict
    exact (lt_irrefl _ hstrict).elim
  · rw [hc, hcp, Nat.mul_comm]

theorem classRetention_eq_one_of_vonMangoldt_zero (N : ℕ)
    (hΛ : ArithmeticFunction.vonMangoldt (N+2) = 0) :
    classRetention N = 1 := by
  unfold classRetention firstClassWeight
  rw [residueModulus_succ_eq_of_vonMangoldt_zero N hΛ]
  exact div_self (ne_of_gt (firstClassWeight_pos N))

theorem classLoss_eq_zero_of_vonMangoldt_zero (N : ℕ)
    (hΛ : ArithmeticFunction.vonMangoldt (N+2) = 0) :
    classLoss N = 0 := by
  rw [classLoss, classRetention_eq_one_of_vonMangoldt_zero N hΛ]
  ring

theorem qN_succ_of_vonMangoldt_zero (N : ℕ)
    (hΛ : ArithmeticFunction.vonMangoldt (N+2) = 0) :
    qN (N+1) = qN N + classEntry N := by
  rw [qN_succ_entry_loss, classLoss_eq_zero_of_vonMangoldt_zero N hΛ, sub_zero]

theorem qN_le_succ_of_vonMangoldt_zero (N : ℕ)
    (hΛ : ArithmeticFunction.vonMangoldt (N+2) = 0) :
    qN N ≤ qN (N+1) := by
  rw [qN_succ_of_vonMangoldt_zero N hΛ]
  exact le_add_of_nonneg_right (classEntry_nonneg N)

theorem classRetention_lt_one_of_vonMangoldt_ne_zero (N : ℕ)
    (hΛ : ArithmeticFunction.vonMangoldt (N+2) ≠ 0) :
    classRetention N < 1 := by
  apply (div_lt_one (firstClassWeight_pos N)).mpr
  have hm := residueModulus_lt_succ_of_vonMangoldt_ne_zero N hΛ
  have hs : positiveWeight (1 + residueModulus (N+1) * 1) <
      positiveWeight (1 + residueModulus N * 1) :=
    positiveWeight_strictAntiOn (by simp) (by simp)
      (by simpa using Nat.add_lt_add_left hm 1)
  apply Summable.tsum_lt_tsum _ hs
    (progressionWeight_summable _ _ (residueModulus_pos _))
    (progressionWeight_summable _ _ (residueModulus_pos _))
  intro j
  exact positiveWeight_strictAntiOn.antitoneOn (by simp) (by simp)
    (Nat.add_le_add_left (Nat.mul_le_mul_right j hm.le) 1)

theorem loss_sum_eq_primePower_sum (m : ℕ) :
    (∑ n ∈ Finset.range m, classLoss (n+1)) =
      ∑ n ∈ Finset.range m,
        if ArithmeticFunction.vonMangoldt (n+3) ≠ 0 then classLoss (n+1) else 0 := by
  apply Finset.sum_congr rfl
  intro n hn
  by_cases h : ArithmeticFunction.vonMangoldt (n+3) = 0
  · simp only [h, ne_eq, not_true_eq_false, ite_false]
    exact classLoss_eq_zero_of_vonMangoldt_zero (n+1) h
  · simp only [h, ne_eq, not_false_eq_true, ite_true]

theorem primePower_entry_sum_le_log_budget (m : ℕ) :
    (∑ n ∈ Finset.range m,
      if ArithmeticFunction.vonMangoldt (n+3) ≠ 0 then classEntry (n+1) else 0) ≤
        Real.log (2 * Real.log 2) := by
  have h : (∑ n ∈ Finset.range m,
      if ArithmeticFunction.vonMangoldt (n+3) ≠ 0 then classEntry (n+1) else 0) ≤
      ∑ n ∈ Finset.range m, classEntry (n+1) := by
    apply Finset.sum_le_sum
    intro n hn
    split_ifs
    · exact le_rfl
    · exact classEntry_nonneg _
  exact h.trans (entry_sum_le_log_budget m)

theorem primePower_loss_sum_lt_log_two (m : ℕ) :
    (∑ n ∈ Finset.range m,
      if ArithmeticFunction.vonMangoldt (n+3) ≠ 0 then classLoss (n+1) else 0) <
        Real.log 2 := by
  rw [← loss_sum_eq_primePower_sum]
  exact (loss_sum_le_log_budget m).trans_lt log_budget_lt_log_two


/-- Sums start with transition 1 to 2, after the initialization q_1=1. -/
theorem primePower_entry_tsum_lt_one :
    (∑' n, if ArithmeticFunction.vonMangoldt (n+3) ≠ 0
      then classEntry (n+1) else 0) < 1 := by
  have h0 (n : ℕ) : 0 ≤ if ArithmeticFunction.vonMangoldt (n+3) ≠ 0
      then classEntry (n+1) else 0 := by
    split_ifs
    · exact classEntry_nonneg _
    · exact le_rfl
  have hs := summable_of_sum_range_le h0 primePower_entry_sum_le_log_budget
  exact (hs.tsum_le_of_sum_range_le primePower_entry_sum_le_log_budget).trans_lt
    (log_budget_lt_log_two.trans class_log_two_lt_one)

theorem primePower_loss_tsum_lt_log_two :
    (∑' n, if ArithmeticFunction.vonMangoldt (n+3) ≠ 0
      then classLoss (n+1) else 0) < Real.log 2 := by
  have he : (fun n => if ArithmeticFunction.vonMangoldt (n+3) ≠ 0
      then classLoss (n+1) else 0) = (fun n => classLoss (n+1)) := by
    funext n
    split_ifs with h
    · rfl
    · exact (classLoss_eq_zero_of_vonMangoldt_zero (n+1) (not_ne_iff.mp h)).symm
  rw [he]
  exact loss_tsum_le_log_budget.trans_lt log_budget_lt_log_two

end RiemannResearch.RH.Pareto.IntegerDPP
