import RiemannResearch.Analysis.RegularizedDataGeometry
import RiemannResearch.Analysis.FiniteGramMultipleConstraint
import RiemannResearch.Analysis.FiniteHilbertConstraints
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity

/-!
# Exact primal and multiplier certificates for the hard-penalty limit

Source: user-requested sixth Ramanujan transfer program, 24 October 2026.
The hard multiplier is constructed from the actual observation source Gram.
Two exact sum-of-squares identities retain the full physical displacement,
constraint mismatch and multiplier displacement before quantitative bounds.
-/
noncomputable section
open scoped BigOperators
namespace RiemannResearch.Analysis.HardPenaltyGeometry
open FiniteHilbertGram FiniteHilbertConstraints FiniteRegularizedConstraints
open RegularizedDataGeometry FiniteGramCapacity
variable {ι κ H : Type*} [Fintype ι] [Fintype κ]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Actual Lagrange multiplier for the exactly constrained finite minimizer. -/
def hardMultiplier {v : ι → H} (hv : LinearIndependent ℝ v)
    (B : Matrix κ ι ℝ) (hB : LinearIndependent ℝ (FiniteGramMultipleConstraint.sourceRows hv B))
    (f : H) (t : κ → ℝ) : κ → ℝ :=
  inverseSource hB (FiniteGramMultipleConstraint.mismatch hv B f t)

/-- The signed hard normal equation is derived, rather than assumed. -/
theorem hard_normal_pairing {v : ι → H} (hv : LinearIndependent ℝ v)
    (B : Matrix κ ι ℝ) (hB : LinearIndependent ℝ (FiniteGramMultipleConstraint.sourceRows hv B))
    (f : H) (t : κ → ℝ) (c : ι → ℝ) :
    inner ℝ (f - Fintype.linearCombination ℝ v
      (FiniteGramMultipleConstraint.coefficients hv B hB f t))
      (Fintype.linearCombination ℝ v c) =
      -(∑ j, hardMultiplier hv B hB f t j * observe B c j) := by
  rw [FiniteGramMultipleConstraint.coefficients_synthesis hv B hB f t,
    sub_add_eq_sub_sub, inner_sub_left, residual_orthogonal, zero_sub]
  change -inner ℝ (Fintype.linearCombination ℝ (FiniteGramMultipleConstraint.sourceRows hv B)
    (hardMultiplier hv B hB f t)) (Fintype.linearCombination ℝ v c) = _
  rw [inner_synthesis_left]
  simp only [FiniteGramMultipleConstraint.sourceRows_pairing hv B c, observe]

/-- The complete soft/hard discrepancy is paid by its signed multiplier pairing. -/
theorem hard_soft_balance {v : ι → H} (hv : LinearIndependent ℝ v)
    (B : Matrix κ ι ℝ) (hB : LinearIndependent ℝ (FiniteGramMultipleConstraint.sourceRows hv B))
    (f : H) (t : κ → ℝ) (ρ : ℝ) :
    let d := coefficients hv B f t ρ - FiniteGramMultipleConstraint.coefficients hv B hB f t
    ‖Fintype.linearCombination ℝ v d‖ ^ 2 + ρ ^ 2 * observationEnergy B d =
      -(∑ j, hardMultiplier hv B hB f t j * observe B d j) := by
  dsimp only
  let d := coefficients hv B f t ρ - FiniteGramMultipleConstraint.coefficients hv B hB f t
  have hd (j : κ) : observe B (coefficients hv B f t ρ) j - t j = observe B d j := by
    rw [show d = coefficients hv B f t ρ -
      FiniteGramMultipleConstraint.coefficients hv B hB f t from rfl, observe_sub]
    rw [show observe B (FiniteGramMultipleConstraint.coefficients hv B hB f t) j = t j from
      FiniteGramMultipleConstraint.coefficients_source hv B hB f t j]
  have hs := normal_pairing hv B f t ρ d
  simp_rw [hd] at hs
  have hh := hard_normal_pairing hv B hB f t d
  have he : f - Fintype.linearCombination ℝ v (coefficients hv B f t ρ) =
      (f - Fintype.linearCombination ℝ v
        (FiniteGramMultipleConstraint.coefficients hv B hB f t)) -
      Fintype.linearCombination ℝ v d := by
    dsimp only [d]
    rw [map_sub]
    abel
  rw [he, inner_sub_left, real_inner_self_eq_norm_sq] at hs
  have hob : (∑ j, observe B d j * observe B d j) = observationEnergy B d := by
    simp only [observationEnergy, pow_two]
  rw [hob, hh] at hs
  change ‖Fintype.linearCombination ℝ v d‖ ^ 2 + ρ ^ 2 * observationEnergy B d = _
  linarith

/-- Centered multiplier-square completion, valid even at penalty zero. -/
theorem hard_soft_centered_square {v : ι → H} (hv : LinearIndependent ℝ v)
    (B : Matrix κ ι ℝ) (hB : LinearIndependent ℝ (FiniteGramMultipleConstraint.sourceRows hv B))
    (f : H) (t : κ → ℝ) (ρ : ℝ) :
    let d := coefficients hv B f t ρ - FiniteGramMultipleConstraint.coefficients hv B hB f t
    ρ ^ 2 * ‖Fintype.linearCombination ℝ v d‖ ^ 2 +
      (∑ j, (ρ ^ 2 * observe B d j + hardMultiplier hv B hB f t j / 2) ^ 2) =
      (∑ j, (hardMultiplier hv B hB f t j) ^ 2) / 4 := by
  dsimp only
  let d := coefficients hv B f t ρ - FiniteGramMultipleConstraint.coefficients hv B hB f t
  have h := hard_soft_balance hv B hB f t ρ
  change ‖Fintype.linearCombination ℝ v d‖ ^ 2 + ρ ^ 2 * observationEnergy B d = _ at h
  have hmul := congrArg (fun x : ℝ => ρ ^ 2 * x) h
  have he : (∑ j, (ρ ^ 2 * observe B d j + hardMultiplier hv B hB f t j / 2) ^ 2) =
      ρ ^ 4 * observationEnergy B d +
      ρ ^ 2 * (∑ j, hardMultiplier hv B hB f t j * observe B d j) +
      (∑ j, (hardMultiplier hv B hB f t j) ^ 2) / 4 := by
    unfold observationEnergy
    rw [Finset.mul_sum, Finset.mul_sum, Finset.sum_div, ← Finset.sum_add_distrib,
      ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring
  change ρ ^ 2 * ‖Fintype.linearCombination ℝ v d‖ ^ 2 + _ = _
  rw [he]
  nlinarith

/-- Full primal/mismatch/multiplier tradeoff. In particular the mismatch is O(ρ⁻⁴). -/
theorem hard_soft_multiplier_square {v : ι → H} (hv : LinearIndependent ℝ v)
    (B : Matrix κ ι ℝ) (hB : LinearIndependent ℝ (FiniteGramMultipleConstraint.sourceRows hv B))
    (f : H) (t : κ → ℝ) (ρ : ℝ) :
    let d := coefficients hv B f t ρ - FiniteGramMultipleConstraint.coefficients hv B hB f t
    2 * ρ ^ 2 * ‖Fintype.linearCombination ℝ v d‖ ^ 2 +
      ρ ^ 4 * observationEnergy B d +
      (∑ j, (ρ ^ 2 * observe B d j + hardMultiplier hv B hB f t j) ^ 2) =
      ∑ j, (hardMultiplier hv B hB f t j) ^ 2 := by
  dsimp only
  let d := coefficients hv B f t ρ - FiniteGramMultipleConstraint.coefficients hv B hB f t
  have h := hard_soft_balance hv B hB f t ρ
  change ‖Fintype.linearCombination ℝ v d‖ ^ 2 + ρ ^ 2 * observationEnergy B d = _ at h
  have hmul := congrArg (fun x : ℝ => ρ ^ 2 * x) h
  have he : (∑ j, (ρ ^ 2 * observe B d j + hardMultiplier hv B hB f t j) ^ 2) =
      ρ ^ 4 * observationEnergy B d +
      2 * ρ ^ 2 * (∑ j, hardMultiplier hv B hB f t j * observe B d j) +
      ∑ j, (hardMultiplier hv B hB f t j) ^ 2 := by
    unfold observationEnergy
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
      ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring
  change 2 * ρ ^ 2 * ‖Fintype.linearCombination ℝ v d‖ ^ 2 + _ + _ = _
  rw [he]
  nlinarith

theorem hard_soft_displacement_bound {v : ι → H} (hv : LinearIndependent ℝ v)
    (B : Matrix κ ι ℝ) (hB : LinearIndependent ℝ (FiniteGramMultipleConstraint.sourceRows hv B))
    (f : H) (t : κ → ℝ) (ρ : ℝ) (hρ : ρ ≠ 0) :
    ‖Fintype.linearCombination ℝ v (coefficients hv B f t ρ -
      FiniteGramMultipleConstraint.coefficients hv B hB f t)‖ ^ 2 ≤
      (∑ j, (hardMultiplier hv B hB f t j) ^ 2) / (4 * ρ ^ 2) := by
  have h := hard_soft_centered_square hv B hB f t ρ
  dsimp only at h
  have hs := Finset.sum_nonneg (s := Finset.univ) (fun j _ => sq_nonneg
    (ρ ^ 2 * observe B (coefficients hv B f t ρ -
      FiniteGramMultipleConstraint.coefficients hv B hB f t) j + hardMultiplier hv B hB f t j / 2))
  apply (le_div_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 4) (sq_pos_iff.mpr hρ))).mpr
  nlinarith

theorem hard_soft_mismatch_bound {v : ι → H} (hv : LinearIndependent ℝ v)
    (B : Matrix κ ι ℝ) (hB : LinearIndependent ℝ (FiniteGramMultipleConstraint.sourceRows hv B))
    (f : H) (t : κ → ℝ) (ρ : ℝ) (hρ : ρ ≠ 0) :
    mismatchEnergy B t (coefficients hv B f t ρ) ≤
      (∑ j, (hardMultiplier hv B hB f t j) ^ 2) / ρ ^ 4 := by
  have h := hard_soft_multiplier_square hv B hB f t ρ
  dsimp only at h
  have hm : mismatchEnergy B t (coefficients hv B f t ρ) =
      observationEnergy B (coefficients hv B f t ρ -
        FiniteGramMultipleConstraint.coefficients hv B hB f t) := by
    unfold mismatchEnergy observationEnergy
    apply Finset.sum_congr rfl
    intro j _
    rw [observe_sub]
    rw [show observe B (FiniteGramMultipleConstraint.coefficients hv B hB f t) j = t j from
      FiniteGramMultipleConstraint.coefficients_source hv B hB f t j]
  rw [hm]
  have h4 : 0 < ρ ^ 4 := by nlinarith [sq_pos_of_pos (sq_pos_iff.mpr hρ)]
  apply (le_div_iff₀ h4).mpr
  have hp := mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (sq_nonneg ρ))
    (sq_nonneg ‖Fintype.linearCombination ℝ v (coefficients hv B f t ρ -
      FiniteGramMultipleConstraint.coefficients hv B hB f t)‖)
  have hs := Finset.sum_nonneg (s := Finset.univ) (fun j _ => sq_nonneg
    (ρ ^ 2 * observe B (coefficients hv B f t ρ -
      FiniteGramMultipleConstraint.coefficients hv B hB f t) j + hardMultiplier hv B hB f t j))
  nlinarith

/-- The scalar model has the exact same penalized least-squares completion. -/
theorem scalar_penalty_completion (f t a ρ : ℝ) :
    (f - a) ^ 2 + ρ ^ 2 * (a - t) ^ 2 =
      ρ ^ 2 / (1 + ρ ^ 2) * (f - t) ^ 2 +
        (1 + ρ ^ 2) * (a - (f + ρ ^ 2 * t) / (1 + ρ ^ 2)) ^ 2 := by
  have hd : 1 + ρ ^ 2 ≠ 0 := by positivity
  field_simp
  <;> ring

/-- Exact nonnegative slack in the universal quarter-constant bound. -/
theorem scalar_penalty_displacement_slack (f t ρ : ℝ) (hρ : ρ ≠ 0) :
    (f - t) ^ 2 / (4 * ρ ^ 2) -
      ((f + ρ ^ 2 * t) / (1 + ρ ^ 2) - t) ^ 2 =
      (f - t) ^ 2 * (ρ ^ 2 - 1) ^ 2 / (4 * ρ ^ 2 * (1 + ρ ^ 2) ^ 2) := by
  have hd : 1 + ρ ^ 2 ≠ 0 := by positivity
  field_simp
  <;> ring

/-- Even a single feasible scalar observation forces the universal constant
in the squared hard/soft displacement bound to be at least one quarter. -/
theorem scalar_penalty_constant_ge_quarter (C : ℝ)
    (h : ∀ f t ρ : ℝ, ρ ≠ 0 →
      ((f + ρ ^ 2 * t) / (1 + ρ ^ 2) - t) ^ 2 ≤ C * (f - t) ^ 2 / ρ ^ 2) :
    (1 / 4 : ℝ) ≤ C := by
  have h1 := h 1 0 1 (by norm_num)
  norm_num at h1
  exact h1

end RiemannResearch.Analysis.HardPenaltyGeometry
