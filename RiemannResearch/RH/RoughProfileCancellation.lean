import RiemannResearch.RH.RoughDiagonalEvaluation
import RiemannResearch.RH.ComponentHeadEnergy
import Mathlib.Algebra.BigOperators.Intervals

/-!
# Exact cancellation of the actual rough arithmetic profiles

Source: RH_CRT_Packet_Research_2026-09-09.md, equations (39)--(41).
Möbius inversion proves the pointwise head decomposition. The resulting
mixed energy contains every ordered off-diagonal term with its original
Pareto weight. Its negative linear asymptotic is an unconditional theorem.
-/

namespace RiemannResearch.RH.Pareto

open scoped BigOperators Topology
open Filter OneBoundaryRepair

noncomputable section

/-- The actual signed rough-core profile, including its arithmetic support. -/
def roughArithmeticProfile (q k : ℕ) : ℝ :=
  if 0 < q ∧ Nat.Coprime q 6 then
    (ArithmeticFunction.moebius q : ℝ) * roughHeadProfile q k else 0

private theorem coprime_six_iff_nondivisibility (n : ℕ) :
    Nat.Coprime n 6 ↔ ¬ 2 ∣ n ∧ ¬ 3 ∣ n := by
  constructor
  · intro hc
    change Nat.gcd n 6 = 1 at hc
    constructor
    · intro h
      have hh := Nat.dvd_gcd h (by decide : 2 ∣ 6)
      rw [hc] at hh
      norm_num at hh
    · intro h
      have hh := Nat.dvd_gcd h (by decide : 3 ∣ 6)
      rw [hc] at hh
      norm_num at hh
  · rintro ⟨h2, h3⟩
    change Nat.gcd n 6 = 1
    have hm : Nat.gcd n 6 ∈ (6 : ℕ).divisors :=
      Nat.mem_divisors.mpr ⟨Nat.gcd_dvd_right n 6, by decide⟩
    have hd : (6 : ℕ).divisors = {1, 2, 3, 6} := by decide
    rw [hd] at hm
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm
    rcases hm with h | h | h | h
    · exact h
    · exact False.elim (h2 (by simpa [h] using Nat.gcd_dvd_left n 6))
    · exact False.elim (h3 (by simpa [h] using Nat.gcd_dvd_left n 6))
    · have hh : 6 ∣ n := by simpa [h] using Nat.gcd_dvd_left n 6
      exact False.elim (h2 (dvd_trans (by decide : 2 ∣ 6) hh))

private theorem coprime_mul_dvd_iff (a q n : ℕ) (hc : Nat.Coprime q a) :
    a * q ∣ n ↔ a ∣ n ∧ q ∣ n := by
  constructor
  · intro h
    exact ⟨dvd_trans (show a ∣ a * q from ⟨q, rfl⟩) h,
      dvd_trans (show q ∣ a * q from ⟨a, Nat.mul_comm a q⟩) h⟩
  · rintro ⟨ha, hq⟩
    exact hc.symm.mul_dvd_of_dvd_of_dvd ha hq

/-- A rough-core count jumps precisely on multiples that remain coprime to six. -/
theorem roughHeadProfile_difference (q n : ℕ) (hq : 0 < q)
    (hc : Nat.Coprime q 6) (hn : 0 < n) :
    roughHeadProfile q n - roughHeadProfile q (n - 1) =
      if q ∣ n ∧ Nat.Coprime n 6 then (1 : ℝ) else 0 := by
  have hq2 : Nat.Coprime q 2 := Nat.Coprime.of_dvd_right (by decide : 2 ∣ 6) hc
  have hq3 : Nat.Coprime q 3 := Nat.Coprime.of_dvd_right (by decide : 3 ∣ 6) hc
  have h6 : 6 ∣ n ↔ 2 ∣ n ∧ 3 ∣ n := by
    simpa using coprime_mul_dvd_iff 2 3 n (by decide)
  have he : roughHeadProfile q n - roughHeadProfile q (n - 1) =
      (if q ∣ n then (1 : ℝ) else 0) -
      (if 2 * q ∣ n then 1 else 0) -
      (if 3 * q ∣ n then 1 else 0) +
      (if 6 * q ∣ n then 1 else 0) := by
    unfold roughHeadProfile
    linarith [floorBlock_difference q n hq hn,
      floorBlock_difference (2 * q) n (by omega) hn,
      floorBlock_difference (3 * q) n (by omega) hn,
      floorBlock_difference (6 * q) n (by omega) hn]
  rw [he]
  simp only [coprime_mul_dvd_iff 2 q n hq2,
    coprime_mul_dvd_iff 3 q n hq3, coprime_mul_dvd_iff 6 q n hc,
    h6, coprime_six_iff_nondivisibility]
  by_cases hqn : q ∣ n <;> by_cases h2 : 2 ∣ n <;> by_cases h3 : 3 ∣ n
  all_goals simp [hqn, h2, h3]

private theorem roughArithmeticProfile_difference_of_not_dvd (q n : ℕ)
    (hn : 0 < n) (hqd : ¬ q ∣ n) :
    roughArithmeticProfile q n - roughArithmeticProfile q (n - 1) = 0 := by
  unfold roughArithmeticProfile
  by_cases hq : 0 < q ∧ Nat.Coprime q 6
  · simp only [if_pos hq, ← mul_sub,
      roughHeadProfile_difference q n hq.1 hq.2 hn, hqd, false_and, if_false, mul_zero]
  · simp [hq]

private theorem roughArithmeticProfile_sum_difference (N n : ℕ)
    (hn : 0 < n) (hnN : n ≤ N) :
    (∑ q ∈ Finset.range (N + 1), roughArithmeticProfile q n) -
        (∑ q ∈ Finset.range (N + 1), roughArithmeticProfile q (n - 1)) =
      if n = 1 then (1 : ℝ) else 0 := by
  rw [← Finset.sum_sub_distrib]
  have hsub : n.divisors ⊆ Finset.range (N + 1) := by
    intro q hq
    have hqn : q ≤ n := Nat.le_of_dvd hn (Nat.dvd_of_mem_divisors hq)
    exact Finset.mem_range.mpr (by omega)
  have hs : (∑ q ∈ Finset.range (N + 1),
        (roughArithmeticProfile q n - roughArithmeticProfile q (n - 1))) =
      ∑ q ∈ n.divisors,
        (roughArithmeticProfile q n - roughArithmeticProfile q (n - 1)) := by
    symm
    apply Finset.sum_subset hsub
    intro q hq hnot
    apply roughArithmeticProfile_difference_of_not_dvd q n hn
    intro hqd
    exact hnot (Nat.mem_divisors.mpr ⟨hqd, ne_of_gt hn⟩)
  rw [hs]
  by_cases hc : Nat.Coprime n 6
  · have he : (∑ q ∈ n.divisors,
        (roughArithmeticProfile q n - roughArithmeticProfile q (n - 1))) =
        ∑ q ∈ n.divisors, (ArithmeticFunction.moebius q : ℝ) := by
      apply Finset.sum_congr rfl
      intro q hq
      have hqd := Nat.dvd_of_mem_divisors hq
      have hqpos : 0 < q := Nat.pos_of_dvd_of_pos hqd hn
      have hqc := Nat.Coprime.of_dvd_left hqd hc
      have hqq : 0 < q ∧ Nat.Coprime q 6 := ⟨hqpos, hqc⟩
      simp only [roughArithmeticProfile, if_pos hqq, ← mul_sub]
      rw [roughHeadProfile_difference q n hqpos hqc hn,
        if_pos (show q ∣ n ∧ Nat.Coprime n 6 from ⟨hqd, hc⟩), mul_one]
    rw [he]
    by_cases hn1 : n = 1
    · subst n
      norm_num
    · rw [if_neg hn1, moebius_divisor_sum_zero n (by omega)]
  · have hn1 : n ≠ 1 := by intro h; apply hc; subst n; decide
    rw [if_neg hn1]
    apply Finset.sum_eq_zero
    intro q hq
    unfold roughArithmeticProfile
    by_cases hqc : 0 < q ∧ Nat.Coprime q 6
    · simp only [if_pos hqc, ← mul_sub,
        roughHeadProfile_difference q n hqc.1 hqc.2 hn,
        hc, and_false, if_false, mul_zero]
    · simp [hqc]

/-- Möbius inversion proves the complete arithmetic partition on the finite head. -/
theorem roughArithmeticProfile_exact_head (N k : ℕ) (hk : 0 < k) (hkN : k ≤ N) :
    (∑ q ∈ Finset.range (N + 1), roughArithmeticProfile q k) = 1 := by
  have htotal : ∀ k, k ≤ N →
      (∑ q ∈ Finset.range (N + 1), roughArithmeticProfile q k) =
        if k = 0 then (0 : ℝ) else 1 := by
    intro k
    induction k with
    | zero =>
      intro _
      simp [roughArithmeticProfile, roughHeadProfile, floorBlock]
    | succ k ih =>
      intro hkN
      have hi := ih (by omega)
      have hd := roughArithmeticProfile_sum_difference N (k + 1) (by omega) hkN
      simp only [Nat.add_sub_cancel] at hd
      by_cases hk0 : k = 0
      · subst k
        simp only [if_pos rfl, zero_add, if_true] at hi hd
        simp only [Nat.succ_ne_zero, if_false]
        linarith
      · have hk1 : k + 1 ≠ 1 := by omega
        simp only [if_neg hk0] at hi
        simp only [if_neg hk1] at hd
        simp only [Nat.succ_ne_zero, if_false]
        linarith
  simpa only [if_neg (ne_of_gt hk)] using htotal k hkN

/-- The diagonal uses the genuine arithmetic profiles and the original head weights. -/
theorem roughArithmeticProfile_diagonal (N : ℕ) :
    componentDiagonalHead N (Finset.range (N + 1)) roughArithmeticProfile =
      roughDiagonalHead N := by
  unfold componentDiagonalHead roughDiagonalHead
  apply Finset.sum_congr rfl
  intro q hq
  by_cases hc : 0 < q ∧ Nat.Coprime q 6
  · simp only [roughArithmeticProfile, if_pos hc, headEnergy]
    rw [Finset.sum_Ico_eq_sum_range]
    simp only [Nat.add_sub_cancel, Nat.add_comm 1, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    ring
  · simp [roughArithmeticProfile, hc, headEnergy]

/-- Every ordered mixed term is retained in the exact arithmetic cancellation. -/
theorem roughArithmeticProfile_mixed_exact (N : ℕ) :
    componentMixedHead N (Finset.range (N + 1)) roughArithmeticProfile =
      (N : ℝ) / ((N : ℝ) + 1) - roughDiagonalHead N := by
  rw [exact_head_mixed_energy N (Finset.range (N + 1)) roughArithmeticProfile
    (fun k hk hkN => roughArithmeticProfile_exact_head N k hk hkN),
    roughArithmeticProfile_diagonal]

/-- The signed mixed energy cancels the complete positive linear diagonal asymptotic. -/
theorem roughArithmeticProfile_mixed_div_tendsto :
    Tendsto (fun N : ℕ =>
      componentMixedHead N (Finset.range (N + 1)) roughArithmeticProfile / (N : ℝ))
      atTop (𝓝 (-(6 / (5 * Real.pi ^ 2)))) := by
  have hinv : Tendsto (fun N : ℕ => 1 / ((N : ℝ) + 1)) atTop (𝓝 (0 : ℝ)) := by
    have ht : Tendsto (fun N : ℕ => (N : ℝ) + 1) atTop atTop :=
      Filter.tendsto_atTop_mono
        (fun N : ℕ => show (N : ℝ) ≤ (N : ℝ) + 1 by linarith)
        tendsto_natCast_atTop_atTop
    exact ht.const_div_atTop 1
  have ht := hinv.sub roughDiagonalHead_div_tendsto_explicit
  simp only [zero_sub] at ht
  apply ht.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with N hN
  rw [roughArithmeticProfile_mixed_exact]
  have hN0 : (N : ℝ) ≠ 0 := by positivity
  have hN1 : (N : ℝ) + 1 ≠ 0 := by positivity
  field_simp [hN0, hN1]
  <;> ring

end
end RiemannResearch.RH.Pareto
