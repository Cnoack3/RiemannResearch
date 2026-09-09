import RiemannResearch.RH.DivisorSeedComponentObstruction

/-!
# The actual divisor-component row as a totient-weighted jump row

Dirichlet-convolution associativity performs the divisor reindexing.  This
identifies the previously defined arithmetic component functional and its
actual coordinate coefficients, for every positive conductor D.
-/

namespace RiemannResearch.RH.DivisorComponentJumpRow

open scoped BigOperators
open Pareto FiniteSeedComponentCharge

noncomputable section

private def positiveOne : ArithmeticFunction ℝ :=
  ⟨fun n => if n = 0 then 0 else 1, by simp⟩

private def mobiusRatio : ArithmeticFunction ℝ :=
  ⟨fun n => (ArithmeticFunction.moebius n : ℝ) / (n : ℝ), by simp⟩

private def differenceRatio (F : ℕ → ℝ) : ArithmeticFunction ℝ :=
  ⟨fun n => (F n - F (n - 1)) / (n : ℝ), by simp⟩

private theorem positiveOne_mul (f : ArithmeticFunction ℝ) (D : ℕ) (hD : 0 < D) :
    (positiveOne * f) D = ∑ d ∈ D.divisors, f d := by
  rw [mul_comm, ArithmeticFunction.mul_apply,
    Nat.sum_divisorsAntidiagonal (fun x y => f x * positiveOne y)]
  apply Finset.sum_congr rfl
  intro d hd
  have hdpos := Nat.pos_of_mem_divisors hd
  have hquot : 0 < D / d := Nat.div_pos
    (Nat.le_of_dvd hD (Nat.dvd_of_mem_divisors hd)) hdpos
  simp [positiveOne, ne_of_gt hquot]

private theorem normalized_mobius_convolution (F : ℕ → ℝ) (D : ℕ) (hD : 0 < D) :
    (mobiusRatio * differenceRatio F) D = mobiusDifference D F / (D : ℝ) := by
  rw [mul_comm, ArithmeticFunction.mul_apply,
    Nat.sum_divisorsAntidiagonal (fun x y => differenceRatio F x * mobiusRatio y)]
  unfold mobiusDifference
  rw [Finset.sum_div]
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
  change ((F d - F (d - 1)) / (d : ℝ)) *
      ((ArithmeticFunction.moebius (D / d) : ℝ) / ((D / d : ℕ) : ℝ)) = _
  field_simp
  rw [← hprod]
  ring

private theorem positiveOne_mul_mobiusRatio (D : ℕ) (hD : 0 < D) :
    (positiveOne * mobiusRatio) D = (Nat.totient D : ℝ) / (D : ℝ) := by
  rw [positiveOne_mul mobiusRatio D hD]
  exact divisor_moebius_signal_eq_totient_div hD

/-- The actual component functional is an explicitly positive weighted jump row. -/
theorem componentCharge_eq_totient_jumps (D : ℕ) (hD : 0 < D) (F : ℕ → ℝ) :
    componentCharge D.divisors F =
      ∑ d ∈ D.divisors, (Nat.totient (D / d) : ℝ) / (D : ℝ) *
        (F d - F (d - 1)) := by
  have hconv : componentCharge D.divisors F =
      ((positiveOne * mobiusRatio) * differenceRatio F) D := by
    rw [mul_assoc, positiveOne_mul _ D hD]
    unfold componentCharge
    apply Finset.sum_congr rfl
    intro d hd
    exact (normalized_mobius_convolution F d (Nat.pos_of_mem_divisors hd)).symm
  rw [hconv, mul_comm, ArithmeticFunction.mul_apply,
    Nat.sum_divisorsAntidiagonal
      (fun x y => differenceRatio F x * (positiveOne * mobiusRatio) y)]
  apply Finset.sum_congr rfl
  intro d hd
  have hdpos := Nat.pos_of_mem_divisors hd
  have hquot : 0 < D / d := Nat.div_pos
    (Nat.le_of_dvd hD (Nat.dvd_of_mem_divisors hd)) hdpos
  rw [positiveOne_mul_mobiusRatio (D / d) hquot]
  have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hdpos)
  have hqR : ((D / d : ℕ) : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hquot)
  have hDR : (D : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hD)
  have hprod : (d : ℝ) * ((D / d : ℕ) : ℝ) = (D : ℝ) := by
    exact_mod_cast Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors hd)
  change ((F d - F (d - 1)) / (d : ℝ)) *
      ((Nat.totient (D / d) : ℝ) / ((D / d : ℕ) : ℝ)) = _
  field_simp
  rw [← hprod]
  ring

def jumpWeight (D n : ℕ) : ℝ :=
  if n ∈ D.divisors then (Nat.totient (D / n) : ℝ) / (D : ℝ) else 0

theorem jumpWeight_nonneg (D n : ℕ) : 0 ≤ jumpWeight D n := by
  unfold jumpWeight
  split_ifs <;> positivity

/-- Identification with the original coordinate-spike definition. -/
theorem componentRow_eq_jump_difference (D : ℕ) (hD : 0 < D) (k : ℕ) :
    componentRow D.divisors k = jumpWeight D (k + 1) - jumpWeight D (k + 2) := by
  unfold componentRow
  rw [componentCharge_eq_totient_jumps D hD]
  have he : (∑ d ∈ D.divisors, (Nat.totient (D / d) : ℝ) / (D : ℝ) *
      (coordinateSpike k d - coordinateSpike k (d - 1))) =
      (∑ d ∈ D.divisors, if d = k + 1 then (Nat.totient (D / d) : ℝ) / (D : ℝ) else 0) -
      (∑ d ∈ D.divisors, if d = k + 2 then (Nat.totient (D / d) : ℝ) / (D : ℝ) else 0) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro d hd
    have hdpos := Nat.pos_of_mem_divisors hd
    have hsub : d - 1 = k + 1 ↔ d = k + 2 := by omega
    simp [coordinateSpike, hsub, mul_sub, mul_ite]
  rw [he]
  simp [jumpWeight, Finset.sum_ite_eq']

theorem jumpWeight_eq_zero_of_lt (D n : ℕ) (hD : 0 < D) (hn : D < n) :
    jumpWeight D n = 0 := by
  have hnot : n ∉ D.divisors := by
    intro h
    exact not_le_of_gt hn (Nat.le_of_dvd hD (Nat.dvd_of_mem_divisors h))
  simp [jumpWeight, hnot]

end
end RiemannResearch.RH.DivisorComponentJumpRow
