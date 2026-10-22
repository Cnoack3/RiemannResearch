import RiemannResearch.RH.TwoThreeChordGram
import RiemannResearch.RH.ThresholdRiemannHypothesis

/-!
# Actual two-seed annihilator moments and constant-target charge

Source: user-provided argument,
RH_Global_Approximation_and_Resonance_Blind_Patterns_Handoff_2026-09-16(1).md,
Section 27. The source supports the statements and proof strategy.

The limiting residual is the actual orthogonal residual of the constant
against the closed legal two-seed space. Failure of RH forces a positive-charge
solution of all moments. No such solution is constructed unconditionally.
Moment unique continuation is an explicit Open hypothesis in the RH reduction.
-/

open scoped BigOperators
noncomputable section
namespace RiemannResearch.RH.Pareto.AdjacentPacket
open RiemannResearch.Analysis.ProjectionChordObservability

def arithmeticCharge (e : ThresholdHilbert) (n : ℕ) : ℝ :=
  positiveWeight n * hilbertSequence e n

theorem arithmeticCharge_summable (e : ThresholdHilbert) :
    Summable (arithmeticCharge e) :=
  weighted_summable_of_square (hilbertSequence_square_summable e)

theorem arithmeticCharge_tsum (e : ThresholdHilbert) :
    (∑' n, arithmeticCharge e n) = inner ℝ e hilbertOne := by
  rw [hilbert_inner_one]
  rfl

theorem correlation_arithmeticMoment (e : ThresholdHilbert)
    (p m : ℕ) (hp : 0 < p) (hm : 0 < m) :
    inner ℝ e (generator p m hp hm) =
      (m:ℝ) * ∑' n, arithmeticCharge e n * digitSequence p m n := by
  rw [generator_eq_scaled_digit, real_inner_smul_right, hilbert_inner_weighted,
    hilbertSequence_digitHilbert]
  congr 1
  unfold paretoInner arithmeticCharge
  apply tsum_congr
  intro n
  ring

theorem arithmeticMoment_summable (e : ThresholdHilbert)
    (p m : ℕ) (hp : 0 < p) (_hm : 0 < m) :
    Summable (fun n => arithmeticCharge e n * digitSequence p m n) := by
  have h := weighted_product_summable_of_square
    (hilbertSequence_square_summable e) (digitSequence_square_summable p m hp)
  apply h.congr
  intro n
  dsimp [arithmeticCharge]
  ring

theorem arithmeticMoment_head_zero (e : ThresholdHilbert)
    (p m n : ℕ) (hn : n < m) :
    arithmeticCharge e n * digitSequence p m n = 0 := by
  simp [digitSequence, Nat.div_eq_of_lt hn]

def TwoSeedMoments (e : ThresholdHilbert) : Prop :=
  ∀ p : ℕ, (p=2 ∨ p=3) → ∀ m : ℕ, 0 < m →
    (∑' n, arithmeticCharge e n * digitSequence p m n) = 0

theorem twoSeedMoments_of_orthogonal (e : ThresholdHilbert)
    (h : ∀ p : ℕ, ∀ hp : 0 < p, (p=2 ∨ p=3) →
      ∀ m : ℕ, ∀ hm : 0 < m, inner ℝ e (generator p m hp hm) = 0) :
    TwoSeedMoments e := by
  intro p hp m hm
  have hpos : 0 < p := by rcases hp with rfl | rfl <;> omega
  have he := h p hpos hp m hm
  rw [correlation_arithmeticMoment] at he
  exact (mul_eq_zero.mp he).resolve_left (by positivity)

theorem residual_arithmeticCharge (P : Submodule ℝ ThresholdHilbert)
    [P.HasOrthogonalProjection] :
    (∑' n, arithmeticCharge (RiemannResearch.Analysis.ProjectionSourceImprovement.residual P hilbertOne) n) =
      ‖RiemannResearch.Analysis.ProjectionSourceImprovement.residual P hilbertOne‖^2 := by
  rw [arithmeticCharge_tsum, residual_charge]

theorem residual_twoSeedMoments (P : Submodule ℝ ThresholdHilbert)
    [P.HasOrthogonalProjection]
    (hP : ∀ p : ℕ, ∀ hp : 0 < p, (p=2 ∨ p=3) →
      ∀ m : ℕ, ∀ hm : 0 < m, generator p m hp hm ∈ P) :
    TwoSeedMoments (RiemannResearch.Analysis.ProjectionSourceImprovement.residual P hilbertOne) := by
  apply twoSeedMoments_of_orthogonal
  intro p hp hseed m hm
  exact Submodule.starProjection_inner_eq_zero hilbertOne _ (hP p hp hseed m hm)

theorem nonzero_residual_positive_charge (P : Submodule ℝ ThresholdHilbert)
    [P.HasOrthogonalProjection]
    (he : RiemannResearch.Analysis.ProjectionSourceImprovement.residual P hilbertOne ≠ 0) :
    0 < ∑' n, arithmeticCharge (RiemannResearch.Analysis.ProjectionSourceImprovement.residual P hilbertOne) n := by
  rw [arithmeticCharge_tsum]
  exact residual_charge_pos P hilbertOne he

theorem residual_zero_of_moment_unique_continuation
    (P : Submodule ℝ ThresholdHilbert) [P.HasOrthogonalProjection]
    (hP : ∀ p : ℕ, ∀ hp : 0 < p, (p=2 ∨ p=3) →
      ∀ m : ℕ, ∀ hm : 0 < m, generator p m hp hm ∈ P)
    (hUC : ∀ e : ThresholdHilbert, TwoSeedMoments e →
      (∑' n, arithmeticCharge e n) = 0) :
    RiemannResearch.Analysis.ProjectionSourceImprovement.residual P hilbertOne = 0 := by
  apply residual_zero_of_charge_zero
  rw [← arithmeticCharge_tsum]
  exact hUC _ (residual_twoSeedMoments P hP)

end RiemannResearch.RH.Pareto.AdjacentPacket

namespace RiemannResearch.RH.Pareto.AdjacentPacket
open RiemannResearch.Analysis.ProjectionChordObservability

theorem generator_mem_twoSeedClosure (p m : ℕ) (hp : 0 < p) (hm : 0 < m)
    (hseed : p=2 ∨ p=3) :
    generator p m hp hm ∈ hilbertLegalClosure {2,3} := by
  apply (hilbertLegalSubspace {2,3}).le_topologicalClosure
  change hilbertSequence (generator p m hp hm) ∈ legalSeedSpan {2,3}
  unfold generator
  rw [hilbertDilation_digit_one_sequence]
  exact Submodule.subset_span ⟨p, by simpa using hseed, m, hm, rfl⟩

instance twoSeedClosure_hasOrthogonalProjection :
    (hilbertLegalClosure {2,3}).HasOrthogonalProjection := by
  unfold hilbertLegalClosure
  infer_instance

def limitingResidual : ThresholdHilbert :=
  RiemannResearch.Analysis.ProjectionSourceImprovement.residual
    (hilbertLegalClosure {2,3}) hilbertOne

theorem limitingResidual_moments : TwoSeedMoments limitingResidual := by
  apply residual_twoSeedMoments
  intro p hp hseed m hm
  exact generator_mem_twoSeedClosure p m hp hm hseed

theorem limitingResidual_charge :
    (∑' n, arithmeticCharge limitingResidual n) = ‖limitingResidual‖^2 :=
  residual_arithmeticCharge (hilbertLegalClosure {2,3})

theorem riemannHypothesis_of_limitingResidual_zero (h : limitingResidual = 0) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_twoSeed_closure
  have he : hilbertOne = (hilbertLegalClosure {2,3}).starProjection hilbertOne :=
    sub_eq_zero.mp h
  rw [he]
  exact Submodule.starProjection_apply_mem _ _

theorem riemannHypothesis_of_moment_unique_continuation
    (hUC : ∀ e : ThresholdHilbert, TwoSeedMoments e →
      (∑' n, arithmeticCharge e n) = 0) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_limitingResidual_zero
  apply residual_zero_of_moment_unique_continuation
  · intro p hp hseed m hm
    exact generator_mem_twoSeedClosure p m hp hm hseed
  · exact hUC

theorem positive_charge_pattern_of_not_rh (h : ¬RiemannHypothesis) :
    TwoSeedMoments limitingResidual ∧
      Summable (arithmeticCharge limitingResidual) ∧
        0 < ∑' n, arithmeticCharge limitingResidual n := by
  refine ⟨limitingResidual_moments, arithmeticCharge_summable _, ?_⟩
  apply nonzero_residual_positive_charge
  intro he
  exact h (riemannHypothesis_of_limitingResidual_zero he)

theorem limitingResidual_mellin_lower_bound (s : ℂ)
    (hs : (1/2:ℝ) < s.re) (hs1 : s ≠ 1) (hz : riemannZeta s = 0) :
    (2*s.re-1)/‖s‖^2 ≤ ‖limitingResidual‖^2 := by
  apply legalClosure_distance_sq_lower_bound_of_zeta {2,3} _ s hs hs1 hz
    (Submodule.starProjection_apply_mem (hilbertLegalClosure {2,3}) hilbertOne)
  intro p hp
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
  rcases hp with rfl | rfl <;> omega

end RiemannResearch.RH.Pareto.AdjacentPacket
