import RiemannResearch.RH.ExactHeadSignedMomentBounds
import RiemannResearch.RH.ExactHeadGcdAtoms
import RiemannResearch.RH.ExactHeadAtomOptimizer
import RiemannResearch.RH.ExactHeadAtomReturnMoments
import RiemannResearch.Analysis.FiniteWeightedNormal
import RiemannResearch.Analysis.FiniteWeightedSpan
import RiemannResearch.Analysis.FiniteWeightedReturnBounds
import RiemannResearch.RH.ParetoProgressionTails
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Actual complete tail-return energy for the signed moment problem

Source: audited A1--A2 continuation, section 23, for the return geometry;
https://drive.google.com/file/d/1DHIp4gGwApIL1V6nHwV4HDxuOAFdijwG/view.
We construct the actual tail representer by finite weighted normal equations,
allowing singular designs. Its full energy is retained, not bounded by an
unproved inverse-Gram constant. All upper atoms and all tail rows are used.
-/
noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.ExactHeadTailReturnEnergy
open RiemannResearch.Analysis.FiniteProfileEnergy
open RiemannResearch.Analysis.FiniteWeightedNormal
open RiemannResearch.Analysis.FiniteWeightedReturnBounds
open RiemannResearch.RH.ExactHeadGcdAtoms
open RiemannResearch.RH.ExactHeadAtomReturnMoments
open RiemannResearch.RH.ExactHeadSignedMomentBounds
open RiemannResearch.RH.Pareto
open RiemannResearch.RH.Pareto.ExactHeadAtomOptimizer

def tailSet (P Y : ℕ) : Finset ℕ := Finset.Icc (Y + 1) (P - 1)

def returnCoefficients (P x Y : ℕ) : ℕ → ℝ :=
  Classical.choose (exists_normal_finset (tailSet P Y) (upperDivisors P x)
    (progressionWeight P) (fun n _ => progressionWeight_nonneg P n)
    (atom P) (fun n => -atomResidual P x n))

def returnProfile (P x Y : ℕ) : ℕ → ℝ :=
  synthesis P (upperDivisors P x) (returnCoefficients P x Y)

def returnCost (P x Y : ℕ) : ℝ :=
  energy (tailSet P Y) (progressionWeight P) (returnProfile P x Y)

def tailGram (P Y g h : ℕ) : ℝ :=
  pairing (tailSet P Y) (progressionWeight P) (atom P g) (atom P h)

theorem returnProfile_mem (P x Y : ℕ) :
    returnProfile P x Y ∈ upperSpan P x (atom P) := by
  have he : returnProfile P x Y =
      ∑ g ∈ upperDivisors P x, returnCoefficients P x Y g • atom P g := by
    funext n
    simp [returnProfile, synthesis, Finset.sum_apply]
  rw [he]
  apply Submodule.sum_mem
  intro g hg
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨g,hg,rfl⟩)

theorem return_normal (P x Y : ℕ) :
    ∀ f ∈ upperSpan P x (atom P),
      pairing (tailSet P Y) (progressionWeight P)
        (atomResidual P x + returnProfile P x Y) f = 0 := by
  apply pairing_eq_zero_on_span
  intro g hg
  have h := (Classical.choose_spec (exists_normal_finset
    (tailSet P Y) (upperDivisors P x) (progressionWeight P)
    (fun n _ => progressionWeight_nonneg P n)
    (atom P) (fun n => -atomResidual P x n))).2 g hg
  have he : pairing (tailSet P Y) (progressionWeight P)
      (atomResidual P x + returnProfile P x Y) (atom P g) =
      -(∑ n ∈ tailSet P Y, progressionWeight P n * atom P g n *
        (-atomResidual P x n -
          ∑ k ∈ upperDivisors P x, returnCoefficients P x Y k * atom P k n)) := by
    unfold pairing returnProfile synthesis
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro n hn
    simp only [Pi.add_apply]
    ring
  rw [he]
  change -(∑ n ∈ tailSet P Y, progressionWeight P n * atom P g n *
    (-atomResidual P x n -
      ∑ k ∈ upperDivisors P x, returnCoefficients P x Y k * atom P k n)) = 0
  exact neg_eq_zero.mpr h

theorem prefix_tail_partition (P Y : ℕ) (hYP : Y < P) :
    Disjoint (Finset.Icc 1 Y) (tailSet P Y) ∧
      Finset.Icc 1 Y ∪ tailSet P Y = Finset.Icc 1 (P - 1) := by
  constructor
  · apply Finset.disjoint_left.mpr
    intro n hn hm
    simp only [tailSet, Finset.mem_Icc] at hn hm
    omega
  · ext n
    simp only [tailSet, Finset.mem_union, Finset.mem_Icc]
    omega

theorem atomEnergy_split (P x Y : ℕ) (hYP : Y < P) :
    atomEnergy P x =
      energy (Finset.Icc 1 Y) (progressionWeight P) (atomResidual P x) +
      energy (tailSet P Y) (progressionWeight P) (atomResidual P x) := by
  obtain ⟨hd,hu⟩ := prefix_tail_partition P Y hYP
  unfold atomEnergy energy
  rw [← Finset.sum_union hd, hu]

theorem return_pairing (P x Y : ℕ) (hYP : Y < P)
    (f : ℕ → ℝ) (hf : f ∈ upperSpan P x (atom P)) :
    pairing (tailSet P Y) (progressionWeight P) (returnProfile P x Y) f =
      pairing (Finset.Icc 1 Y) (progressionWeight P) (atomResidual P x) f := by
  obtain ⟨hd,hu⟩ := prefix_tail_partition P Y hYP
  have hn := atomResidual_normal P x f hf
  have ht := return_normal P x Y f hf
  have hs : pairing (Finset.Icc 1 Y) (progressionWeight P) (atomResidual P x) f +
      pairing (tailSet P Y) (progressionWeight P) (atomResidual P x) f = 0 := by
    unfold pairing
    rw [← Finset.sum_union hd, hu]
    exact hn
  have he : pairing (tailSet P Y) (progressionWeight P)
      (atomResidual P x + returnProfile P x Y) f =
      pairing (tailSet P Y) (progressionWeight P) (atomResidual P x) f +
      pairing (tailSet P Y) (progressionWeight P) (returnProfile P x Y) f := by
    simp [pairing, Pi.add_apply, add_mul, mul_add, Finset.sum_add_distrib]
  rw [he] at ht
  linarith

/-- Exact full energy budget, including the tail-optimal residual remainder. -/
theorem returnCost_budget (P x Y : ℕ) (hYP : Y < P) :
    atomEnergy P x =
      energy (Finset.Icc 1 Y) (progressionWeight P) (atomResidual P x) +
      energy (tailSet P Y) (progressionWeight P)
        (atomResidual P x + returnProfile P x Y) + returnCost P x Y := by
  rw [atomEnergy_split P x Y hYP]
  have h := normal_completion_on_span (tailSet P Y) (progressionWeight P)
    (atomResidual P x + returnProfile P x Y) (upperSpan P x (atom P))
    (return_normal P x Y) (-returnProfile P x Y)
    (Submodule.neg_mem _ (returnProfile_mem P x Y))
  have he : atomResidual P x + returnProfile P x Y + -returnProfile P x Y =
      atomResidual P x := by abel
  rw [he] at h
  have hn : energy (tailSet P Y) (progressionWeight P) (-returnProfile P x Y) =
      returnCost P x Y := by simp [energy, returnCost]
  rw [hn] at h
  rw [h]
  ring

theorem returnCost_nonneg (P x Y : ℕ) : 0 ≤ returnCost P x Y :=
  energy_nonneg _ _ _ (fun n _ => progressionWeight_nonneg P n)

/-- The signed numerator is a covariance with the actual full tail return. -/
theorem tripleMoment_eq_return (P x Y p q r : ℕ) (hYP : Y < P) :
    tripleMoment P x Y p q r (progressionWeight P) (atomResidual P x) =
      pairing (tailSet P Y) (progressionWeight P) (returnProfile P x Y)
        (tripleProfile P x p q r) := by
  rw [return_pairing P x Y hYP _ (tripleProfile_mem P x p q r),
    tripleMoment_eq_prefix]

theorem tripleMoment_sq_le_returnCost (P x Y p q r : ℕ) (hYP : Y < P) :
    tripleMoment P x Y p q r (progressionWeight P) (atomResidual P x)^2 ≤
      returnCost P x Y *
        energy (tailSet P Y) (progressionWeight P) (tripleProfile P x p q r) := by
  rw [tripleMoment_eq_return P x Y p q r hYP]
  exact pairing_sq_le _ _ _ _ (fun n _ => progressionWeight_nonneg P n)

/-- Unconditional two-sided bound for the actual optimizer. No prime-window
hypotheses are needed for the activated-moment version. -/
theorem tripleMoment_sq_le_harmonic (P x Y p q r : ℕ) (hYP : Y < P) :
    tripleMoment P x Y p q r (progressionWeight P) (atomResidual P x)^2 ≤
      atomEnergy P x *
      (energy (Finset.Icc 1 Y) (progressionWeight P) (tripleProfile P x p q r) *
       energy (tailSet P Y) (progressionWeight P) (tripleProfile P x p q r) /
       (energy (Finset.Icc 1 Y) (progressionWeight P) (tripleProfile P x p q r) +
        energy (tailSet P Y) (progressionWeight P) (tripleProfile P x p q r))) := by
  have hs := atomResidual_tripleMoment_eq_tail P x Y p q r hYP
  rw [tripleMoment_eq_prefix] at hs
  rw [tripleMoment_eq_prefix, atomEnergy_split P x Y hYP]
  exact two_region_pairing_sq_le_harmonic _ _ _ _ _
    (fun n _ => progressionWeight_nonneg P n) (fun n _ => progressionWeight_nonneg P n)
    (by dsimp only [tailSet]; linarith)

/-- Full tail normal system. No diagonal or near-return replacement is made. -/
theorem returnGram_equation (P x Y g : ℕ) (hYP : Y < P)
    (hg : g ∈ upperDivisors P x) :
    (∑ k ∈ upperDivisors P x, tailGram P Y g k * returnCoefficients P x Y k) =
      prefixMoment P Y (progressionWeight P) (atomResidual P x) g := by
  have hh := return_pairing P x Y hYP (atom P g)
    (Submodule.subset_span ⟨g,hg,rfl⟩)
  change _ = pairing (Finset.Icc 1 Y) (progressionWeight P) (atomResidual P x) (atom P g)
  rw [← hh]
  unfold tailGram pairing returnProfile synthesis
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro n hn
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k hk
  ring

/-- Coordinate form of the complete inverse-Gram cost on the feasible range.
When an invertible reduced Gram is chosen, this is m transpose G inverse m. -/
theorem returnCost_eq_signed_score (P x Y : ℕ) (hYP : Y < P) :
    returnCost P x Y =
      ∑ g ∈ upperDivisors P x, returnCoefficients P x Y g *
        prefixMoment P Y (progressionWeight P) (atomResidual P x) g := by
  have he : returnCost P x Y =
      pairing (tailSet P Y) (progressionWeight P)
        (returnProfile P x Y) (returnProfile P x Y) := by
    unfold returnCost energy pairing
    apply Finset.sum_congr rfl
    intro n hn
    ring
  rw [he, return_pairing P x Y hYP _ (returnProfile_mem P x Y)]
  exact prefix_pairing_synthesis P Y (upperDivisors P x) (progressionWeight P)
    (atomResidual P x) (returnCoefficients P x Y)

theorem returnCost_eq_full_gram (P x Y : ℕ) (hYP : Y < P) :
    returnCost P x Y =
      ∑ g ∈ upperDivisors P x, ∑ k ∈ upperDivisors P x,
        returnCoefficients P x Y g * tailGram P Y g k * returnCoefficients P x Y k := by
  rw [returnCost_eq_signed_score P x Y hYP]
  apply Finset.sum_congr rfl
  intro g hg
  rw [← returnGram_equation P x Y g hYP hg, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  ring

theorem returnCost_le_remaining_energy (P x Y : ℕ) (hYP : Y < P) :
    returnCost P x Y ≤ atomEnergy P x -
      energy (Finset.Icc 1 Y) (progressionWeight P) (atomResidual P x) := by
  have h := returnCost_budget P x Y hYP
  have hn := energy_nonneg (tailSet P Y) (progressionWeight P)
    (atomResidual P x + returnProfile P x Y) (fun n _ => progressionWeight_nonneg P n)
  linarith

/-- The period-endpoint atom is a zero column on the complete nonterminal tail.
Thus an inverse of the unreduced full Gram cannot simply be postulated. -/
theorem tailGram_period_column_zero (P Y g : ℕ) : tailGram P Y g P = 0 := by
  unfold tailGram pairing
  apply Finset.sum_eq_zero
  intro n hn
  have hn' := Finset.mem_Icc.mp hn
  rw [atom_zero_of_lt P P n (by omega), mul_zero]

/-- Exact strengthened two-sided budget: subtract the tail-optimal residual
before charging the signed numerator. The two defects are Gram minor sums. -/
theorem tripleMoment_return_budget_identity (P x Y p q r : ℕ) (hYP : Y < P) :
    let L := Finset.Icc 1 Y
    let T := tailSet P Y
    let w := progressionWeight P
    let R := atomResidual P x
    let F := tripleProfile P x p q r
    let N := tripleMoment P x Y p q r w R
    (atomEnergy P x - energy T w (R + returnProfile P x Y)) *
        energy L w F * energy T w F -
      (energy L w F + energy T w F) * N ^ 2 =
    energy T w F * (energy L w R * energy L w F - N ^ 2) +
      energy L w F * (returnCost P x Y * energy T w F - N ^ 2) := by
  dsimp only
  rw [returnCost_budget P x Y hYP]
  ring

theorem tripleMoment_sq_le_return_budget (P x Y p q r : ℕ) (hYP : Y < P) :
    let L := Finset.Icc 1 Y
    let T := tailSet P Y
    let w := progressionWeight P
    let R := atomResidual P x
    let F := tripleProfile P x p q r
    let N := tripleMoment P x Y p q r w R
    (energy L w F + energy T w F) * N ^ 2 ≤
      (atomEnergy P x - energy T w (R + returnProfile P x Y)) *
        energy L w F * energy T w F := by
  dsimp only
  have hi := tripleMoment_return_budget_identity P x Y p q r hYP
  dsimp only at hi
  have hL : tripleMoment P x Y p q r (progressionWeight P) (atomResidual P x)^2 ≤
      energy (Finset.Icc 1 Y) (progressionWeight P) (atomResidual P x) *
        energy (Finset.Icc 1 Y) (progressionWeight P) (tripleProfile P x p q r) := by
    rw [tripleMoment_eq_prefix]
    exact pairing_sq_le _ _ _ _ (fun n _ => progressionWeight_nonneg P n)
  have hT := tripleMoment_sq_le_returnCost P x Y p q r hYP
  have h1 := mul_nonneg (energy_nonneg (tailSet P Y) (progressionWeight P)
    (tripleProfile P x p q r) (fun n _ => progressionWeight_nonneg P n)) (sub_nonneg.mpr hL)
  have h2 := mul_nonneg (energy_nonneg (Finset.Icc 1 Y) (progressionWeight P)
    (tripleProfile P x p q r) (fun n _ => progressionWeight_nonneg P n)) (sub_nonneg.mpr hT)
  linarith

end RiemannResearch.RH.ExactHeadTailReturnEnergy
