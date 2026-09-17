import RiemannResearch.Probability.ConditionalIIDUniformMoments
import Mathlib.Data.Nat.Factorization.Basic

/-!
# Conditional probabilities of divisibility events

Source: user-provided `Conditional_IID_Cesaro_Mathematical_Completion_2026-09-17.md`,
Section 2. These are exact conditional probabilities in the constructed model.
Within a row, simultaneous divisibility uses the least common multiple.
-/

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

namespace RiemannResearch.Probability.ConditionalIID

theorem uniformLaw_divisibility (k d : ℕ) :
    uniformLaw k {n | d ∣ n} = ((k + 1) / d : ℕ) / (k + 1 : ℝ≥0∞) := by
  rw [uniformLaw_apply]
  congr 1
  norm_cast
  calc
    _ = ((Finset.range (k + 1).succ).filter (fun n => n ≠ 0 ∧ d ∣ n)).card := by
      congr 1
      ext n
      simp only [Finset.mem_filter, Finset.mem_Icc, Set.mem_ofPred_eq, Finset.mem_range]
      omega
    _ = (k + 1) / d := Nat.card_multiples' (k + 1) d

theorem uniformLaw_joint_divisibility (k a b : ℕ) :
    uniformLaw k {n | a ∣ n ∧ b ∣ n} =
      ((k + 1) / Nat.lcm a b : ℕ) / (k + 1 : ℝ≥0∞) := by
  simpa only [Nat.lcm_dvd_iff] using uniformLaw_divisibility k (Nat.lcm a b)

/-- The conditional probability is the exact count of multiples, divided by the endpoint. -/
theorem conditional_divisibility_event (i d : ℕ) :
    probability[(coordinate i ⁻¹' {n | d ∣ n}).indicator (fun _ : Omega => (1 : ℝ)) |
      latentSigma] =ᵐ[probability]
      (fun ω => (endpoint ω / d : ℕ) / (endpoint ω : ℝ)) := by
  filter_upwards [conditional_coordinate_event i {n | d ∣ n}] with ω hω
  rw [hω]
  simp [Measure.real, uniformLaw_divisibility, ENNReal.toReal_add, endpoint, latentIndex]

/-- Same-row divisibility correlations are retained through the exact lcm. -/
theorem conditional_joint_divisibility_event (i a b : ℕ) :
    probability[(coordinate i ⁻¹' {n | a ∣ n ∧ b ∣ n}).indicator
      (fun _ : Omega => (1 : ℝ)) | latentSigma] =ᵐ[probability]
      (fun ω => (endpoint ω / Nat.lcm a b : ℕ) / (endpoint ω : ℝ)) := by
  simpa only [Nat.lcm_dvd_iff] using conditional_divisibility_event i (Nat.lcm a b)

end RiemannResearch.Probability.ConditionalIID
