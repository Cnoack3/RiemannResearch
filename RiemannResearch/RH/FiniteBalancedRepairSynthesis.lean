import RiemannResearch.RH.ThresholdDilationAlgebra
import RiemannResearch.RH.OneBoundaryRepairObstruction

/-!
# Actual legal synthesis from finite component charge balance

The endpoints are explicitly `r * 2^A * 3^B`.  Finite telescoping along the two
seed directions proves membership in the project's actual algebraic legal
span.  Per-root charge cancellation then identifies the corresponding signed
floor sum with that legal construction.  This is finite arithmetic synthesis;
no density or vanishing-error hypothesis is used.
-/

namespace RiemannResearch.RH.FiniteBalancedRepair

open scoped BigOperators
open Pareto OneBoundaryRepair

noncomputable section

/-- Finite cancellation after grouping arbitrary coefficients by their root. -/
theorem root_sum_zero {ι : Type*} (s : Finset ι) (r : ι → ℕ)
    (c : ι → ℝ) (φ : ℕ → ℝ)
    (hcharge : ∀ t : ℕ, (∑ i ∈ s, if r i = t then c i else 0) = 0) :
    (∑ i ∈ s, c i * φ (r i)) = 0 := by
  classical
  let roots := s.image r
  have hexpand : (∑ i ∈ s, c i * φ (r i)) =
      ∑ i ∈ s, ∑ t ∈ roots, if r i = t then c i * φ t else 0 := by
    apply Finset.sum_congr rfl
    intro i hi
    have hri : r i ∈ roots := Finset.mem_image.mpr ⟨i, hi, rfl⟩
    rw [Finset.sum_eq_single (r i)]
    · simp
    · intro t ht hne
      simp [Ne.symm hne]
    · intro hn
      exact (hn hri).elim
  rw [hexpand, Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro t ht
  have he : (∑ i ∈ s, if r i = t then c i * φ t else 0) =
      (∑ i ∈ s, if r i = t then c i else 0) * φ t := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i hi
    split_ifs <;> simp
  rw [he, hcharge t, zero_mul]

theorem smooth_residue_mem (A B : ℕ) :
    residue (2 ^ A * 3 ^ B) ∈ legalSeedSpan ({2, 3} : Set ℕ) := by
  have h2 := power_seed_mem_legalSeedSpan ({2, 3} : Set ℕ)
    (show 2 ∈ ({2, 3} : Set ℕ) by simp) (by decide : 0 < 2) A
  have h3 := power_seed_mem_legalSeedSpan ({2, 3} : Set ℕ)
    (show 3 ∈ ({2, 3} : Set ℕ) by simp) (by decide : 0 < 3) B
  have hd := legalSeedSpan_dilation ({2, 3} : Set ℕ) h3 (2 ^ A) (by positivity)
  have he : residue (2 ^ A * 3 ^ B) =
      residue (2 ^ A) + dilation (2 ^ A) (residue (3 ^ B)) := by
    funext k
    rw [Pi.add_apply, residue_mul_floor]
    ring
  rw [he]
  exact (legalSeedSpan ({2, 3} : Set ℕ)).add_mem h2 hd

/-- Explicit seed paths synthesize each endpoint-minus-root residue. -/
theorem endpoint_difference_mem (r A B : ℕ) (hr : 0 < r) :
    (residue (r * 2 ^ A * 3 ^ B) - residue r) ∈
      legalSeedSpan ({2, 3} : Set ℕ) := by
  have h := legalSeedSpan_dilation ({2, 3} : Set ℕ) (smooth_residue_mem A B) r hr
  have he : residue (r * 2 ^ A * 3 ^ B) - residue r =
      dilation r (residue (2 ^ A * 3 ^ B)) := by
    funext k
    rw [Pi.sub_apply, residue_mul_floor]
    simp only [Nat.mul_assoc]
  rw [he]
  exact h

def componentEndpoint {ι : Type*} (r A B : ι → ℕ) (i : ι) : ℕ :=
  r i * 2 ^ A i * 3 ^ B i

/-- Each summand is independently legal; coefficients may have either sign. -/
theorem endpoint_difference_sum_mem {ι : Type*} (s : Finset ι)
    (r A B : ι → ℕ) (c : ι → ℝ) (hr : ∀ i ∈ s, 0 < r i) :
    (∑ i ∈ s, c i • (residue (componentEndpoint r A B i) - residue (r i))) ∈
      legalSeedSpan ({2, 3} : Set ℕ) := by
  apply (legalSeedSpan ({2, 3} : Set ℕ)).sum_mem
  intro i hi
  exact (legalSeedSpan ({2, 3} : Set ℕ)).smul_mem (c i)
    (endpoint_difference_mem (r i) (A i) (B i) (hr i hi))

theorem balanced_residue_sum_mem {ι : Type*} (s : Finset ι)
    (r A B : ι → ℕ) (c : ι → ℝ) (hr : ∀ i ∈ s, 0 < r i)
    (hcharge : ∀ t : ℕ, (∑ i ∈ s, if r i = t then c i else 0) = 0) :
    (∑ i ∈ s, c i • residue (componentEndpoint r A B i)) ∈
      legalSeedSpan ({2, 3} : Set ℕ) := by
  have he : (∑ i ∈ s, c i • residue (componentEndpoint r A B i)) =
      ∑ i ∈ s, c i • (residue (componentEndpoint r A B i) - residue (r i)) := by
    funext k
    simp only [Finset.sum_apply, Pi.smul_apply, Pi.sub_apply, smul_eq_mul,
      mul_sub, Finset.sum_sub_distrib]
    rw [root_sum_zero s r c (fun t => residue t k) hcharge, sub_zero]
  rw [he]
  exact endpoint_difference_sum_mem s r A B c hr

/-- The anchored actual floor sum associated with normalized component charges. -/
def balancedFloor {ι : Type*} (s : Finset ι) (r A B : ι → ℕ)
    (c : ι → ℝ) (k : ℕ) : ℝ :=
  ∑ i ∈ s, (componentEndpoint r A B i : ℝ) * c i *
    floorBlock (componentEndpoint r A B i) k

theorem balancedFloor_eq_neg_residue_sum {ι : Type*} (s : Finset ι)
    (r A B : ι → ℕ) (c : ι → ℝ)
    (hcharge : ∀ t : ℕ, (∑ i ∈ s, if r i = t then c i else 0) = 0) :
    balancedFloor s r A B c = -(∑ i ∈ s, c i • residue (componentEndpoint r A B i)) := by
  have hc : (∑ i ∈ s, c i) = 0 := by
    simpa using root_sum_zero s r c (fun _ => 1) hcharge
  funext k
  simp only [balancedFloor, Pi.neg_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  have he : (∑ i ∈ s, (componentEndpoint r A B i : ℝ) * c i *
      floorBlock (componentEndpoint r A B i) k) =
      ∑ i ∈ s, (c i * (k : ℝ) - c i * residue (componentEndpoint r A B i) k) := by
    apply Finset.sum_congr rfl
    intro i hi
    have h := floorBlock_mul (componentEndpoint r A B i) k
    nlinarith [congrArg (fun x : ℝ => c i * x) h]
  rw [he, Finset.sum_sub_distrib, ← Finset.sum_mul, hc]
  ring

/-- Finite component charge balance constructively implies actual legal synthesis. -/
theorem balancedFloor_mem_legalSeedSpan {ι : Type*} (s : Finset ι)
    (r A B : ι → ℕ) (c : ι → ℝ) (hr : ∀ i ∈ s, 0 < r i)
    (hcharge : ∀ t : ℕ, (∑ i ∈ s, if r i = t then c i else 0) = 0) :
    balancedFloor s r A B c ∈ legalSeedSpan ({2, 3} : Set ℕ) := by
  rw [balancedFloor_eq_neg_residue_sum s r A B c hcharge]
  exact (legalSeedSpan ({2, 3} : Set ℕ)).neg_mem
    (balanced_residue_sum_mem s r A B c hr hcharge)

end
end RiemannResearch.RH.FiniteBalancedRepair
