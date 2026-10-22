import RiemannResearch.RH.DivisorComponentJumpRow
import RiemannResearch.RH.ComponentJumpGram

/-! # An explicit totient-divisor upper bound for the actual component row norm -/

namespace RiemannResearch.RH.DivisorComponentJumpRow

open scoped BigOperators
open Pareto FiniteSeedComponentCharge PositiveSeedCone DivisorSeedComponentObstruction

noncomputable section

def totientDivisorNorm (D : ℕ) : ℝ :=
  ∑ d ∈ D.divisors, ((Nat.totient d : ℝ) / (d : ℝ)) ^ 2

theorem componentDualNorm_eq_jump_gram (D : ℕ) (hD : 0 < D) :
    componentDualNorm D.divisors D = ComponentJumpGram.gram (jumpWeight D) (jumpWeight D) D := by
  have hg : ComponentJumpGram.gram (jumpWeight D) (jumpWeight D) D =
      ∑ k ∈ Finset.range D, ((k : ℝ) + 1) * ((k : ℝ) + 2) *
        (jumpWeight D (k + 1) - jumpWeight D (k + 2)) ^ 2 := by
    unfold ComponentJumpGram.gram
    rw [Finset.sum_range_succ']
    simp only [Nat.cast_zero, zero_mul, zero_add, add_zero]
    apply Finset.sum_congr rfl
    intro k hk
    simp only [Nat.cast_add, Nat.cast_one]
    ring
  rw [hg]
  unfold componentDualNorm
  apply Finset.sum_congr rfl
  intro k hk
  rw [componentRow_eq_jump_difference D hD]
  unfold positiveWeight
  simp only [Nat.cast_add, Nat.cast_one]
  field_simp
  ring

theorem jumpWeight_diagonal_sum (D : ℕ) (hD : 0 < D) :
    (∑ n ∈ Finset.range (D + 1), (n : ℝ) ^ 2 * (jumpWeight D n) ^ 2) =
      totientDivisorNorm D := by
  have hsub : D.divisors ⊆ Finset.range (D + 1) := by
    intro n hn
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.divisor_le hn))
  have hsum : (∑ n ∈ Finset.range (D + 1), (n : ℝ) ^ 2 * (jumpWeight D n) ^ 2) =
      ∑ d ∈ D.divisors, (d : ℝ) ^ 2 * (jumpWeight D d) ^ 2 := by
    symm
    apply Finset.sum_subset hsub
    intro n hn hnot
    simp [jumpWeight, hnot]
  rw [hsum]
  have he : (∑ d ∈ D.divisors, (d : ℝ) ^ 2 * (jumpWeight D d) ^ 2) =
      ∑ d ∈ D.divisors, ((Nat.totient (D / d) : ℝ) / ((D / d : ℕ) : ℝ)) ^ 2 := by
    apply Finset.sum_congr rfl
    intro d hd
    have hdpos := Nat.pos_of_mem_divisors hd
    have hquot : 0 < D / d := Nat.div_pos
      (Nat.le_of_dvd hD (Nat.dvd_of_mem_divisors hd)) hdpos
    have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hdpos)
    have hqR : ((D / d : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hquot)
    have hDR : (D : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hD)
    have hprod : (d : ℝ) * ((D / d : ℕ) : ℝ) = (D : ℝ) := by
      exact_mod_cast Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors hd)
    simp only [jumpWeight, hd, ↓reduceIte]
    field_simp
    rw [← hprod]
    ring
  rw [he]
  rw [← Nat.sum_divisorsAntidiagonal'
    (fun x _ => ((Nat.totient x : ℝ) / (x : ℝ)) ^ 2)]
  rw [Nat.sum_divisorsAntidiagonal
    (fun x _ => ((Nat.totient x : ℝ) / (x : ℝ)) ^ 2)]
  rfl

/-- This is a bound on the original arithmetic row, not on a surrogate matrix. -/
theorem componentDualNorm_le_totientDivisorNorm (D : ℕ) (hD : 0 < D) :
    componentDualNorm D.divisors D ≤ 2 * totientDivisorNorm D := by
  rw [componentDualNorm_eq_jump_gram D hD]
  calc
    _ ≤ 2 * ∑ n ∈ Finset.range (D + 1), (n : ℝ) ^ 2 * (jumpWeight D n) ^ 2 :=
      ComponentJumpGram.gram_self_le (jumpWeight D) D
        (jumpWeight_eq_zero_of_lt D (D + 1) hD (by omega))
        (fun n _ => jumpWeight_nonneg D n)
    _ = 2 * totientDivisorNorm D := by rw [jumpWeight_diagonal_sum D hD]

theorem divisorComponent_totient_fullError_lower {ι : Type*}
    (D r : ℕ) (hD : 0 < D) (hr : Nat.Coprime 6 r)
    (s : Finset ι) (a m : ι → ℕ) (c : ι → ℝ)
    (ha : ∀ i ∈ s, a i = 2 ∨ a i = 3)
    (hm : ∀ i ∈ s, 0 < m i)
    (hperiod : ∀ i ∈ s, a i * m i ∣ D * r) :
    ((Nat.totient D : ℝ) / (D : ℝ)) ^ 2 / (2 * totientDivisorNorm D) ≤
      ∑' k : ℕ, weightedError (seedCombination s a m c) k := by
  have hknown := divisorComponent_seedCombination_fullError_lower D r hD hr s a m c ha hm hperiod
  have hT : componentSignal D.divisors ≠ 0 := ne_of_gt (divisor_moebius_signal_pos hD)
  have hSD : ∀ n ∈ D.divisors, 0 < n ∧ n ≤ D := by
    intro n hn
    exact ⟨Nat.pos_of_mem_divisors hn, Nat.divisor_le hn⟩
  have hK : 0 < componentDualNorm D.divisors D := componentDualNorm_pos D.divisors D hSD hT
  have hbound := componentDualNorm_le_totientDivisorNorm D hD
  have hden : 0 < 2 * totientDivisorNorm D := lt_of_lt_of_le hK hbound
  have hratio : ((Nat.totient D : ℝ) / (D : ℝ)) ^ 2 / (2 * totientDivisorNorm D) ≤
      ((Nat.totient D : ℝ) / (D : ℝ)) ^ 2 / componentDualNorm D.divisors D := by
    apply (div_le_div_iff₀ hden hK).mpr
    exact mul_le_mul_of_nonneg_left hbound (sq_nonneg _)
  rw [divisorComponent_signal D hD] at hknown
  exact hratio.trans hknown.2

end
end RiemannResearch.RH.DivisorComponentJumpRow
