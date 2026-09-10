import RiemannResearch.RH.DyadicTailRecovery
import RiemannResearch.RH.FiniteSeedMellinObstruction

/-!
# An unavoidable complementary-energy gap for triadic-only lifts

Source: the user-provided dyadic-regularization ledger's remaining full-energy
obligation; the existing finite-seed Mellin obstruction supplies separation.

The actual residue-3 vector is a fixed finite legal seed. The established
Mellin obstruction therefore separates the target from its entire closed
integer-dilation span by a positive distance. Exact orthogonal energy
splitting forces this obstruction into the complementary energy whenever
the projected error is small. No zero of the Riemann zeta-function is assumed.

Consequently quotient recovery alone cannot prove full-space approximation
using only the triadic seed. The signed interaction with a second independent
seed channel must be retained in any completion toward RH.
-/

namespace RiemannResearch.RH.Pareto

open scoped BigOperators
open Filter
noncomputable section

/-- The actual residue-3 vector as a single legal arithmetic coefficient. -/
def triadicResidueCoefficients : ArithmeticCoefficients :=
  Finsupp.single (3, 1) 1

theorem triadicResidueCoefficients_legal :
    ArithmeticCoefficientsLegal triadicResidueCoefficients := by
  intro p hp
  have hs : triadicResidueCoefficients.support = {(3, 1)} := by
    simp [triadicResidueCoefficients]
  rw [hs, Finset.mem_singleton] at hp
  subst p
  norm_num

theorem hilbertResidue_three_arithmeticCombination :
    hilbertSequence (hilbertResidue 3 (by norm_num)) =
      arithmeticCombination triadicResidueCoefficients := by
  rw [hilbertResidue_sequence]
  funext k
  simp [arithmeticCombination, triadicResidueCoefficients, dilation]

/-- A fixed positive full-space squared-distance gap holds for the whole
closed residue-3 dilation span, with all positive integer dilations allowed. -/
theorem triadicResidue_positive_distance_gap :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ f ∈ singleSeedDilationClosure (hilbertResidue 3 (by norm_num)),
        δ ≤ ‖hilbertOne - f‖ ^ 2 :=
  finite_legal_seed_positive_distance_gap triadicResidueCoefficients
    triadicResidueCoefficients_legal (hilbertResidue 3 (by norm_num))
    hilbertResidue_three_arithmeticCombination

theorem dyadicTailTriadicSpan_le_singleSeedClosure (X : ℕ) :
    dyadicTailTriadicSpan X ≤
      singleSeedDilationClosure (hilbertResidue 3 (by norm_num)) := by
  apply Submodule.span_le.mpr
  rintro f ⟨m, hm, hXm, rfl⟩
  apply (Submodule.span ℝ
    (singleSeedDilationSet (hilbertResidue 3 (by norm_num)))).le_topologicalClosure
  exact Submodule.subset_span ⟨m, hm, rfl⟩

/-- The same positive gap applies simultaneously to every finite triadic
tail space; the tail boundary cannot remove the single-seed obstruction. -/
theorem dyadicTailTriadicSpan_positive_distance_gap :
    ∃ δ : ℝ, 0 < δ ∧ ∀ X : ℕ, ∀ f ∈ dyadicTailTriadicSpan X,
      δ ≤ ‖hilbertOne - f‖ ^ 2 := by
  obtain ⟨δ, hδ, hgap⟩ := triadicResidue_positive_distance_gap
  exact ⟨δ, hδ, fun X f hf => hgap f
    (dyadicTailTriadicSpan_le_singleSeedClosure X hf)⟩

/-- At the base tail the target lies in the actual dyadic quotient. -/
theorem hilbertOne_mem_dyadicTailQuotientSubspace_one :
    hilbertOne ∈ dyadicTailQuotientSubspace 1 := by
  apply (mem_dyadicTailQuotientSubspace_iff 1 hilbertOne).mpr
  constructor
  · apply (mem_dyadicPhysicalTail_iff 1 hilbertOne).mpr
    intro k hk
    have hk0 : k = 0 := by omega
    subst k
    exact hilbertSequence_zero hilbertOne
  · intro u hu
    rw [inner_sub_left]
    have h := ContinuousLinearMap.adjoint_inner_right
      (hilbertDilationContinuous 2 (by norm_num)) u hilbertOne
    change inner ℝ u (hilbertDilationAdjoint 2 (by norm_num) hilbertOne) =
      inner ℝ (hilbertDilation 2 (by norm_num) u) hilbertOne at h
    rw [hilbertDilationAdjoint_one] at h
    exact sub_eq_zero.mpr h

/-- Exact error splitting locates the positive single-seed obstruction in
the complementary lift energy after subtracting the actual projected error. -/
theorem dyadicTriadic_complementary_energy_gap :
    ∃ δ : ℝ, 0 < δ ∧ ∀ f ∈ dyadicTailTriadicSpan 1,
      δ - ‖hilbertOne - dyadicTailQuotientProjection 1 f‖ ^ 2 ≤
        ‖f - dyadicTailQuotientProjection 1 f‖ ^ 2 := by
  obtain ⟨δ, hδ, hgap⟩ := dyadicTailTriadicSpan_positive_distance_gap
  refine ⟨δ, hδ, ?_⟩
  intro f hf
  have hg := hgap 1 f hf
  have hp := dyadicTail_finite_lift_error_pythagoras 1 hilbertOne f
    hilbertOne_mem_dyadicTailQuotientSubspace_one
  linarith

/-- Along any sequence of actual finite triadic lifts with vanishing
projected squared error, the complementary energy stays positively bounded
away from zero. The sequence need not be an arithmetic regularization. -/
theorem dyadicTriadic_complementary_energy_eventually_positive
    (f : ℕ → ThresholdHilbert) (hf : ∀ n, f n ∈ dyadicTailTriadicSpan 1)
    (hproj : Tendsto (fun n =>
      ‖hilbertOne - dyadicTailQuotientProjection 1 (f n)‖ ^ 2) atTop (nhds 0)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ n in atTop,
      δ ≤ ‖f n - dyadicTailQuotientProjection 1 (f n)‖ ^ 2 := by
  obtain ⟨δ, hδ, hgap⟩ := dyadicTriadic_complementary_energy_gap
  refine ⟨δ / 2, half_pos hδ, ?_⟩
  have hsmall : ∀ᶠ n in atTop,
      ‖hilbertOne - dyadicTailQuotientProjection 1 (f n)‖ ^ 2 < δ / 2 :=
    hproj.eventually (gt_mem_nhds (half_pos hδ))
  filter_upwards [hsmall] with n hn
  have hb := hgap (f n) (hf n)
  linarith

/-- Adding a second channel retains its complete signed complementary
interaction. This equality supplies no cancellation estimate by itself. -/
theorem dyadic_two_channel_lift_error_eq (u v : ThresholdHilbert) :
    ‖hilbertOne - (u + v)‖ ^ 2 =
      ‖hilbertOne - dyadicTailQuotientProjection 1 (u + v)‖ ^ 2 +
      ‖u - dyadicTailQuotientProjection 1 u‖ ^ 2 +
      ‖v - dyadicTailQuotientProjection 1 v‖ ^ 2 +
      2 * inner ℝ (u - dyadicTailQuotientProjection 1 u)
        (v - dyadicTailQuotientProjection 1 v) := by
  rw [dyadicTail_finite_lift_error_pythagoras 1 hilbertOne (u + v)
    hilbertOne_mem_dyadicTailQuotientSubspace_one]
  have hcomp : u + v - dyadicTailQuotientProjection 1 (u + v) =
      (u - dyadicTailQuotientProjection 1 u) +
        (v - dyadicTailQuotientProjection 1 v) := by
    rw [map_add]
    abel
  rw [hcomp, norm_add_sq_real]
  ring

end
end RiemannResearch.RH.Pareto
