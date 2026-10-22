import RiemannResearch.RH.ExactHeadCharges
import RiemannResearch.RH.SmoothComponentClosedFloor

/-!
# Mandatory boundary charge of smooth divisor regions

Source: user-provided argument, RH_CRT_Packet_Research_2026-09-09.md,
Sections 8 and 9.1. The actual finite legal coefficients satisfy an exact
boundary-flux identity with value 1/3 on every fully interpolated positive
smooth rectangle. All integer dilation indices and both endpoint terms
remain. This is not a norm bound and does not assert prefix divergence.
-/

namespace RiemannResearch.RH.FiniteSeedComponentCharge

open scoped BigOperators
open Pareto PositiveSeedCone TwoSeedThreshold

noncomputable section

/-- The divisor-component charge of an exact head is its actual totient ratio. -/
theorem exact_head_divisor_charge (D : ℕ) (hD : 0 < D) (F : ℕ → ℝ)
    (hzero : F 0 = 0) (hhead : ∀ k, 0 < k → k ≤ D → F k = 1) :
    componentCharge D.divisors F = (Nat.totient D : ℝ) / (D : ℝ) := by
  have he : componentCharge D.divisors F = componentSignal D.divisors := by
    unfold componentCharge componentSignal
    apply Finset.sum_congr rfl
    intro n hn
    rw [exact_head_mobiusDifference hzero hhead (Nat.pos_of_mem_divisors hn)
      (Nat.le_of_dvd hD (Nat.dvd_of_mem_divisors hn))]
  rw [he]
  exact DivisorSeedComponentObstruction.divisorComponent_signal D hD

/-- An exact head forces this signed flux in the actual legal edge coefficients. -/
theorem exact_head_seed_boundary_flux {ι : Type*} (D : ℕ) (hD : 0 < D)
    (s : Finset ι) (a m : ι → ℕ) (c : ι → ℝ)
    (ha : ∀ i ∈ s, 0 < a i) (hm : ∀ i ∈ s, 0 < m i)
    (hhead : ∀ k, 0 < k → k ≤ D → seedCombination s a m c k = 1) :
    (∑ i ∈ s, c i *
      ((if m i ∣ D then 1 else 0) - (if a i * m i ∣ D then 1 else 0))) =
        (Nat.totient D : ℝ) / (D : ℝ) := by
  have hz : seedCombination s a m c 0 = 0 := by
    simp [seedCombination, certificateGenerator]
  have he := exact_head_divisor_charge D hD (seedCombination s a m c) hz hhead
  rw [componentCharge_seedCombination] at he
  have hterms (i : ι) (hi : i ∈ s) :
      componentCharge D.divisors (certificateGenerator (a i) (m i)) =
        (if m i ∣ D then 1 else 0) - (if a i * m i ∣ D then 1 else 0) := by
    rw [componentCharge_generator D.divisors (a i) (m i)
      (fun n hn => Nat.pos_of_mem_divisors hn) (ha i hi) (hm i hi)]
    simp [Nat.mem_divisors, ne_of_gt hD]
  convert he using 1
  apply Finset.sum_congr rfl
  intro i hi
  rw [hterms i hi]

/-- The root smooth rectangle has exact outgoing charge 1/3 at every size. -/
theorem exact_head_smooth_boundary_flux {ι : Type*} (A B : ℕ)
    (hA : 0 < A) (hB : 0 < B)
    (s : Finset ι) (a m : ι → ℕ) (c : ι → ℝ)
    (ha : ∀ i ∈ s, 0 < a i) (hm : ∀ i ∈ s, 0 < m i)
    (hhead : ∀ k, 0 < k → k ≤ 2 ^ A * 3 ^ B → seedCombination s a m c k = 1) :
    (∑ i ∈ s, c i *
      ((if m i ∣ 2 ^ A * 3 ^ B then 1 else 0) -
        (if a i * m i ∣ 2 ^ A * 3 ^ B then 1 else 0))) = (1 : ℝ) / 3 := by
  rw [exact_head_seed_boundary_flux (2 ^ A * 3 ^ B) (by positivity)
    s a m c ha hm hhead]
  exact DivisorComponentJumpRow.totient_ratio_smooth A B hA hB

end
end RiemannResearch.RH.FiniteSeedComponentCharge
