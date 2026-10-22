import RiemannResearch.RH.QResidueMoments
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Conditional dilation under the actual inverse-square law

Source: user-provided prime-divisibility Q-law, 13 October 2026.
The reindexing proof follows the support bijection used by the existing
`ZetaTwoProbability.measure_dvd`, now with an arbitrary signed observable.
Consequently the exact law is available for residue atoms and finite
inclusion-exclusion wavelets, without an independence assumption on residues.
-/

noncomputable section
open scoped BigOperators

namespace RiemannResearch.RH.ZetaTwoHilbert
open RiemannResearch.RH.ZetaTwoProbability
open RiemannResearch.RH.ArithmeticCumulative

/-- The literal shifted series can be indexed by positive naturals. -/
theorem inversePowerMean_zero_eq_pnat_tsum (f : ℕ → ℝ) :
    inversePowerMean 0 f = ∑' k : ℕ+, positiveQWeight k * f k := by
  rw [tsum_pnat_eq_tsum_succ (f := fun n : ℕ => positiveQWeight n * f n)]
  unfold inversePowerMean positiveQWeight
  apply tsum_congr
  intro k
  ring

/-- Complete multiplicativity of the unnormalized inverse-square weight. -/
theorem positiveQWeight_mul (m n : ℕ) :
    positiveQWeight (m * n) = (1 / (m : ℝ)^2) * positiveQWeight n := by
  simp only [positiveQWeight, Nat.cast_mul, mul_pow, one_div, mul_inv]
  ring

private def qMulPositive (m : ℕ) (hm : 0 < m) (k : ℕ+) : ℕ+ :=
  ⟨m * k, Nat.mul_pos hm k.pos⟩

/-- Exact expectation conditioned by divisibility. No boundedness is needed
for this equality of `tsum`s; bounded observables are integrable under Q. -/
theorem inversePowerMean_dvd (m : ℕ) (hm : 0 < m) (f : ℕ → ℝ) :
    inversePowerMean 0 (fun n => if m ∣ n then f n else 0) =
      (1 / (m : ℝ)^2) * inversePowerMean 0 (fun n => f (m * n)) := by
  classical
  rw [inversePowerMean_zero_eq_pnat_tsum, inversePowerMean_zero_eq_pnat_tsum]
  have hreindex :
      (∑' k : ℕ+, if m ∣ (k : ℕ) then positiveQWeight k * f k else 0) =
      ∑' k : ℕ+, positiveQWeight (qMulPositive m hm k) *
        f (qMulPositive m hm k) := by
    apply tsum_eq_tsum_of_ne_zero_bij
      (fun k : Function.support (fun k : ℕ+ =>
        positiveQWeight (qMulPositive m hm k) * f (qMulPositive m hm k)) =>
        qMulPositive m hm k.val)
    · intro a b hab
      apply Subtype.ext
      apply PNat.coe_injective
      exact Nat.eq_of_mul_eq_mul_left hm (congrArg (fun x : ℕ+ => (x : ℕ)) hab)
    · intro k hk
      change (if m ∣ (k : ℕ) then positiveQWeight k * f k else 0) ≠ 0 at hk
      have hd : m ∣ (k : ℕ) := by
        by_contra h
        exact hk (by simp [h])
      obtain ⟨a, ha⟩ := hd
      have ha0 : 0 < a := by
        by_contra h
        have : a = 0 := Nat.eq_zero_of_not_pos h
        simp [this] at ha
      let a' : ℕ+ := ⟨a, ha0⟩
      have heq : qMulPositive m hm a' = k := PNat.coe_injective ha.symm
      refine ⟨⟨a', ?_⟩, heq⟩
      change positiveQWeight (qMulPositive m hm a') * f (qMulPositive m hm a') ≠ 0
      rw [heq]
      simpa only [if_pos (show m ∣ (k : ℕ) from ⟨a, ha⟩)] using hk
    · intro k
      change (if m ∣ m * (k.val : ℕ) then
        positiveQWeight (m * (k.val : ℕ)) * f (m * (k.val : ℕ)) else 0) = _
      rw [if_pos (dvd_mul_right m (k.val : ℕ))]
      rfl
  calc
    (∑' k : ℕ+, positiveQWeight k * (if m ∣ (k : ℕ) then f k else 0)) =
        ∑' k : ℕ+, if m ∣ (k : ℕ) then positiveQWeight k * f k else 0 := by
      apply tsum_congr
      intro k
      split_ifs <;> simp
    _ = ∑' k : ℕ+, positiveQWeight (qMulPositive m hm k) *
        f (qMulPositive m hm k) := hreindex
    _ = ∑' k : ℕ+, (1 / (m : ℝ)^2) * (positiveQWeight k * f (m * k)) := by
      apply tsum_congr
      intro k
      change positiveQWeight (m * (k : ℕ)) * f (m * (k : ℕ)) = _
      rw [positiveQWeight_mul]
      ring
    _ = (1 / (m : ℝ)^2) * ∑' k : ℕ+, positiveQWeight k * f (m * k) :=
      tsum_mul_left

/-- The exact residue/divisibility mixed moment is a scaled twisted mean. -/
theorem residue_divisibility_mixed_mean (d k : ℕ) (hk : 0 < k) :
    inversePowerMean 0
      (fun n => residueFraction d n * (if k ∣ n then (1 : ℝ) else 0)) =
      (1 / (k : ℝ)^2) * qTwistedResidueMean d k := by
  have hpoint :
      (fun n => residueFraction d n * (if k ∣ n then (1 : ℝ) else 0)) =
      (fun n => if k ∣ n then residueFraction d n else 0) := by
    funext n
    split_ifs <;> simp
  rw [hpoint]
  exact inversePowerMean_dvd k hk (residueFraction d)

/-- Conditioning on a multiple of the conductor kills the atom exactly. -/
theorem residue_divisibility_mixed_mean_eq_zero (d k : ℕ)
    (hk : 0 < k) (hdk : d ∣ k) :
    inversePowerMean 0
      (fun n => residueFraction d n * (if k ∣ n then (1 : ℝ) else 0)) = 0 := by
  rw [residue_divisibility_mixed_mean d k hk,
    qTwistedResidueMean_eq_zero_of_dvd d k hdk, mul_zero]

end RiemannResearch.RH.ZetaTwoHilbert
