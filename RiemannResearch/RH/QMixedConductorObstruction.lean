import RiemannResearch.RH.ZetaTwoHilbertSpace
import RiemannResearch.RH.ParetoResidueDuality
import RiemannResearch.RH.ArithmeticCumulativeBasic
import RiemannResearch.RH.ZetaTwoProbability
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Data.Nat.PrimeFin
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# A quantitative mixed-conductor obstruction in the actual Q Hilbert space

Source: user-provided Ramanujan/Von-Mangoldt discussion, October 13, 2026.
The conductor-six charge reuses `Pareto.mobiusDifference`; the new result is
its exact four-coordinate square identity and its actual Q norm bound.
In particular, finite combinations of prime-power integrated Ramanujan
packets stay at squared Q distance at least `1 / (74 * zetaTwo)` from one.
This is an obstruction to discarding mixed conductors, not an obstruction to
the full legal residue dictionary.
-/

namespace RiemannResearch.RH.QMixedConductorObstruction
noncomputable section
open scoped BigOperators Topology
open Filter
open RiemannResearch.RH.ZetaTwoProbability
open RiemannResearch.RH.ZetaTwoHilbert
open RiemannResearch.RH.ArithmeticCumulative
open RiemannResearch.RH.Pareto

/-- The existing arithmetic charge at conductor six, on physical Q values. -/
def sixthCharge (f : QHilbert) : ℝ := mobiusDifference 6 (qSequence f)

theorem sixthCharge_eq (f : QHilbert) :
    sixthCharge f = 2 * qSequence f 1 - qSequence f 3 - qSequence f 5 +
      qSequence f 6 := by
  have hd : (6 : ℕ).divisors = {1, 2, 3, 6} := by decide
  have hm3 : ArithmeticFunction.moebius 3 = -1 :=
    ArithmeticFunction.moebius_apply_prime (by norm_num)
  have hm2 : ArithmeticFunction.moebius 2 = -1 :=
    ArithmeticFunction.moebius_apply_prime (by norm_num)
  have hm6 : ArithmeticFunction.moebius 6 = 1 := by
    change ArithmeticFunction.moebius (2 * 3) = 1
    rw [ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime
      (by norm_num : Nat.gcd 2 3 = 1), hm2, hm3]
    norm_num
  norm_num [sixthCharge, mobiusDifference, hd, hm6, hm3, hm2] <;> ring

theorem sixthCharge_sub (f g : QHilbert) :
    sixthCharge (f - g) = sixthCharge f - sixthCharge g := by
  have hs : qSequence (f - g) = qSequence f - qSequence g :=
    qSequenceLinear.map_sub f g
  simp only [sixthCharge_eq, hs, Pi.sub_apply]
  ring

@[simp] theorem sixthCharge_qOne : sixthCharge qOne = 1 := by
  rw [sixthCharge_eq]
  simp only [qSequence_qOne]
  norm_num [qOneSequence]

/-- The exact six-square remainder behind the numerical constant 74. -/
theorem fourPoint_lagrange_identity (x₁ x₃ x₅ x₆ : ℝ) :
    74 * (x₁ ^ 2 + x₃ ^ 2 / 9 + x₅ ^ 2 / 25 + x₆ ^ 2 / 36) -
        (2 * x₁ - x₃ - x₅ + x₆) ^ 2 =
      (3 * x₁ + 2 * x₃ / 3) ^ 2 +
      (5 * x₁ + 2 * x₅ / 5) ^ 2 +
      (6 * x₁ - x₆ / 3) ^ 2 +
      (5 * x₃ / 3 - 3 * x₅ / 5) ^ 2 +
      (2 * x₃ + x₆ / 2) ^ 2 +
      (6 * x₅ / 5 + 5 * x₆ / 6) ^ 2 := by ring

theorem fourPoint_charge_sq_le (x₁ x₃ x₅ x₆ : ℝ) :
    (2 * x₁ - x₃ - x₅ + x₆) ^ 2 ≤
      74 * (x₁ ^ 2 + x₃ ^ 2 / 9 + x₅ ^ 2 / 25 + x₆ ^ 2 / 36) := by
  nlinarith only [fourPoint_lagrange_identity x₁ x₃ x₅ x₆,
    sq_nonneg (3 * x₁ + 2 * x₃ / 3),
    sq_nonneg (5 * x₁ + 2 * x₅ / 5),
    sq_nonneg (6 * x₁ - x₆ / 3),
    sq_nonneg (5 * x₃ / 3 - 3 * x₅ / 5),
    sq_nonneg (2 * x₃ + x₆ / 2),
    sq_nonneg (6 * x₅ / 5 + 5 * x₆ / 6)]

theorem fourPoint_energy_le_qNorm (f : QHilbert) :
    (qSequence f 1) ^ 2 + (qSequence f 3) ^ 2 / 9 +
      (qSequence f 5) ^ 2 / 25 + (qSequence f 6) ^ 2 / 36 ≤
      zetaTwo * ‖f‖ ^ 2 := by
  have hs := Summable.sum_le_tsum ({1, 3, 5, 6} : Finset ℕ)
    (fun n _ => mul_nonneg (positiveQWeight_nonneg n) (sq_nonneg (qSequence f n)))
    (qSequence_square_summable f)
  rw [← qNorm_weighted_sq] at hs
  have hmul := mul_le_mul_of_nonneg_left hs zetaTwo_pos.le
  have he : zetaTwo * (∑ n ∈ ({1, 3, 5, 6} : Finset ℕ),
      positiveQWeight n * (qSequence f n) ^ 2) =
      (qSequence f 1) ^ 2 + (qSequence f 3) ^ 2 / 9 +
        (qSequence f 5) ^ 2 / 25 + (qSequence f 6) ^ 2 / 36 := by
    norm_num [positiveQWeight]
    field_simp [ne_of_gt zetaTwo_pos] <;> ring
  rwa [he] at hmul

theorem sixthCharge_sq_le_qNorm (f : QHilbert) :
    (sixthCharge f) ^ 2 ≤ 74 * zetaTwo * ‖f‖ ^ 2 := by
  rw [sixthCharge_eq]
  have hc := fourPoint_charge_sq_le
    (qSequence f 1) (qSequence f 3) (qSequence f 5) (qSequence f 6)
  have he := fourPoint_energy_le_qNorm f
  nlinarith only [hc, he]

/-- Vanishing conductor-six charge gives a strict actual Q separation. -/
theorem qResidual_sq_lower_bound (f : QHilbert) (hf : sixthCharge f = 0) :
    1 / (74 * zetaTwo) ≤ ‖qOne - f‖ ^ 2 := by
  have hz : 0 < zetaTwo := zetaTwo_pos
  have h := sixthCharge_sq_le_qNorm (qOne - f)
  rw [sixthCharge_sub, sixthCharge_qOne, hf] at h
  norm_num only [sub_zero, one_pow] at h
  apply (div_le_iff₀ (show 0 < 74 * zetaTwo by positivity)).mpr
  nlinarith only [h]

/-- A sequence in the charge kernel cannot converge to the actual Q constant. -/
theorem not_tendsto_qOne_of_sixthCharge_zero (f : ℕ → QHilbert)
    (hf : ∀ j, sixthCharge (f j) = 0) :
    ¬ Tendsto f atTop (𝓝 qOne) := by
  intro ht
  have hz : 0 < zetaTwo := zetaTwo_pos
  have he : Tendsto (fun j => ‖qOne - f j‖ ^ 2) atTop (𝓝 (0 : ℝ)) := by
    simpa using (((tendsto_const_nhds (x := qOne)).sub ht).norm.pow 2)
  have hle : 1 / (74 * zetaTwo) ≤ 0 :=
    ge_of_tendsto' he (fun j => qResidual_sq_lower_bound (f j) (hf j))
  have hpos : 0 < 1 / (74 * zetaTwo) := by positivity
  linarith

/-- Normalizing the existing unnormalized-residue duality. -/
theorem mobiusDifference_residueFraction (m d : ℕ) (hm : 1 < m) (hd : 0 < d) :
    mobiusDifference m (residueFraction d) = if m = d then -1 else 0 := by
  have hlin : mobiusDifference m (residueFraction d) =
      mobiusDifference m (residue d) / (d : ℝ) := by
    simp only [mobiusDifference, residueFraction, residue, ← sub_div,
      mul_div_assoc, Finset.sum_div]
  rw [hlin, mobiusDifference_residue m d hm]
  by_cases he : m = d
  · simp [he, ne_of_gt (show (0 : ℝ) < d by exact_mod_cast hd)]
  · simp [he]

/-- Finite legal residue candidates with conductor six omitted are separated. -/
theorem qResidual_sq_lower_bound_missing_six (f : QHilbert)
    (s : Finset ℕ) (c : ℕ → ℝ)
    (hs : ∀ d ∈ s, 0 < d) (h6 : 6 ∉ s)
    (hseq : qSequence f = fun n => ∑ d ∈ s, c d * residueFraction d n) :
    1 / (74 * zetaTwo) ≤ ‖qOne - f‖ ^ 2 := by
  apply qResidual_sq_lower_bound f
  rw [sixthCharge, hseq, mobiusDifference_sum]
  apply Finset.sum_eq_zero
  intro d hd
  rw [mobiusDifference_residueFraction 6 d (by norm_num) (hs d hd)]
  have hne : (6 : ℕ) ≠ d := by
    intro h
    subst d
    exact h6 hd
  simp [hne]

/-- Mixed conductors cannot be deleted just because their Von-Mangoldt mean
vanishes: all prime-power-only Ramanujan combinations have this fixed gap. -/
theorem qResidual_sq_lower_bound_primePowerPackets (f : QHilbert)
    (s : Finset ℕ) (c : ℕ → ℝ)
    (hs : ∀ q ∈ s, 0 < q ∧ q.primeFactors.card ≤ 1)
    (hseq : qSequence f = fun n => ∑ q ∈ s, c q * ramanujanPacket q n) :
    1 / (74 * zetaTwo) ≤ ‖qOne - f‖ ^ 2 := by
  apply qResidual_sq_lower_bound f
  rw [sixthCharge, hseq]
  have hpf : (6 : ℕ).primeFactors = {2, 3} := by
    change (2 * 3 : ℕ).primeFactors = {2, 3}
    rw [Nat.primeFactors_mul (by norm_num) (by norm_num),
      (show Nat.Prime 2 by norm_num).primeFactors,
      (show Nat.Prime 3 by norm_num).primeFactors]
    simp
  exact boundedPrimeSupport_dual_zero 6 1 s c (by norm_num)
    (by rw [hpf]; norm_num) hs

end
end RiemannResearch.RH.QMixedConductorObstruction
