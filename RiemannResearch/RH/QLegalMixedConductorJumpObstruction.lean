/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QLegalMixedConductorWeightedEnergy
import RiemannResearch.RH.QCountablePairEnergy
import RiemannResearch.RH.QPrimeResamplingPoincare
import RiemannResearch.RH.QPrimeRawSourceEnergy
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Lean.Elab.Tactic.Omega

/-!
# Complete jump-energy divergence for the actual mixed-conductor family

Source: LegalSubspaceProjectionObstruction.md, Section 4. The analytic
consumer below requires the exact complete pair-energy Poincare bound for
the chosen kernel. The canonical prime kernel supplies this separately.
-/

noncomputable section
open Filter
open scoped Topology BigOperators ENNReal
namespace RiemannResearch.RH.QLegalMixedConductor
open ZetaTwoHilbert ZetaTwoProbability QPolylogTailEnergy
open QCountableJumpEnergy QPairVariance
open RiemannResearch.Analysis.LogTailWeights
open RiemannResearch.Analysis.CountableJumpEnergy

theorem actualCorrection_weighted_anchor_sq_le_one (d : ℕ) :
    qWeightedSequence (actualCorrection d) 1 ^ 2 ≤ 1 := by
  have hterm : positiveQWeight 1 * qSequence (actualCorrection d) 1 ^ 2 ≤
      ‖actualCorrection d‖ ^ 2 := by
    have h := (qSequence_square_summable (actualCorrection d)).sum_le_tsum
      ({1} : Finset ℕ) (fun n hn => mul_nonneg (positiveQWeight_nonneg n) (sq_nonneg _))
    simpa only [Finset.sum_singleton, ← qNorm_weighted_sq] using h
  have hnorm : ‖actualCorrection d‖ ^ 2 ≤ 1 / 64 := by
    nlinarith [actualCorrection_norm_le_eighth d, norm_nonneg (actualCorrection d)]
  have hdiv : qSequence (actualCorrection d) 1 ^ 2 / zetaTwo ≤ 1 / 64 := by
    calc
      _ = positiveQWeight 1 * qSequence (actualCorrection d) 1 ^ 2 := by
        simp only [positiveQWeight, Nat.cast_one, one_pow, mul_one]
        ring
      _ ≤ ‖actualCorrection d‖ ^ 2 := hterm
      _ ≤ _ := hnorm
  have hpoint := (div_le_iff₀ zetaTwo_pos).mp hdiv
  have hprofile : polylogTailProfile 2 1 = (1 / 64 : ℝ) := by
    rw [polylogTailProfile_eq]
    norm_num
  rw [qWeightedSequence_sq, hprofile]
  nlinarith [QFiniteEnergyBounds.zetaTwo_rational_bounds.2]

theorem correctionWeightedEnergy_ofReal_eq (d : ℕ)
    (hs : Summable (polylogWeightedEnergyTerm 2 (actualCorrection d))) :
    ENNReal.ofReal (correctionWeightedEnergy d) =
      ∑' n : ℕ, ENNReal.ofReal
        (positiveQWeight n * qWeightedSequence (actualCorrection d) n ^ 2) := by
  rw [correctionWeightedEnergy,
    ENNReal.ofReal_tsum_of_nonneg (polylogWeightedEnergyTerm_nonneg 2 (actualCorrection d)) hs]
  apply tsum_congr
  intro n
  rw [qWeightedSequence_square_term]

def correctionJumpEnergy (W : ℕ → ℕ → ℝ≥0∞) (d : ℕ) : ℝ≥0∞ :=
  countableJumpEnergy W (qWeightedSequence (actualCorrection d))

/-- Complete pair variance itself diverges in the actual family. -/
theorem pairVariance_actualCorrection_large_eventually (M : ℝ) :
    ∀ᶠ d : ℕ in atTop,
      ENNReal.ofReal M ≤ pairVariance (qWeightedSequence (actualCorrection d)) := by
  by_cases hM : M ≤ 0
  · exact Eventually.of_forall (fun _ => by simp [ENNReal.ofReal_eq_zero.mpr hM])
  have hMpos : 0 < M := lt_of_not_ge hM
  have hz := zetaTwo_pos
  have hA : 0 ≤ 4 * zetaTwo * M + 2 := by positivity
  have hlarge := correctionWeightedEnergy_tendsto_atTop.eventually
    (eventually_ge_atTop (4 * zetaTwo * M + 3))
  filter_upwards [hlarge, actualCorrection_weightedEnergy_summable_eventually] with d hd hs
  by_contra h
  have hD : pairVariance (qWeightedSequence (actualCorrection d)) ≤ ENNReal.ofReal M :=
    le_of_lt (lt_of_not_ge h)
  have ha := qSquareEnergy_le_pairEnergy_anchor (qWeightedSequence (actualCorrection d))
  rw [← correctionWeightedEnergy_ofReal_eq d hs] at ha
  have hanchor : ENNReal.ofReal (qWeightedSequence (actualCorrection d) 1 ^ 2) ≤ 1 := by
    simpa only [ENNReal.ofReal_one] using
      ENNReal.ofReal_le_ofReal (actualCorrection_weighted_anchor_sq_le_one d)
  have hupper : ENNReal.ofReal (correctionWeightedEnergy d) ≤
      ENNReal.ofReal (4 * zetaTwo * M + 2) := by
    calc
      _ ≤ (4 * ENNReal.ofReal zetaTwo) *
          countableJumpEnergy pairFlow (qWeightedSequence (actualCorrection d)) +
            2 * ENNReal.ofReal (qWeightedSequence (actualCorrection d) 1 ^ 2) := ha
      _ ≤ (4 * ENNReal.ofReal zetaTwo) * ENNReal.ofReal M + 2 * 1 :=
        add_le_add (mul_le_mul_of_nonneg_left hD zero_le)
          (mul_le_mul_of_nonneg_left hanchor zero_le)
      _ = _ := by
        rw [mul_one, ← ENNReal.ofReal_ofNat 4,
          ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4),
          ← ENNReal.ofReal_mul (by positivity : 0 ≤ 4 * zetaTwo),
          ← ENNReal.ofReal_ofNat 2,
          ← ENNReal.ofReal_add (by positivity : 0 ≤ 4 * zetaTwo * M) (by norm_num)]
  have hreal : correctionWeightedEnergy d ≤ 4 * zetaTwo * M + 2 :=
    (ENNReal.ofReal_le_ofReal_iff hA).mp hupper
  linarith

/-- Any complete kernel with the pair-energy Poincare property inherits
the actual mixed-conductor divergence. No integrability of the weighted
sequence is assumed in the Poincare premise. -/
theorem correctionJumpEnergy_large_eventually
    (W : ℕ → ℕ → ℝ≥0∞)
    (hpoincare : ∀ g : ℕ → ℝ, pairVariance g ≤ countableJumpEnergy W g)
    (M : ℝ) : ∀ᶠ d : ℕ in atTop, ENNReal.ofReal M ≤ correctionJumpEnergy W d := by
  filter_upwards [pairVariance_actualCorrection_large_eventually M] with d hd
  exact hd.trans (hpoincare _)

theorem exists_prime_actualCorrection_large_jumpEnergy
    (W : ℕ → ℕ → ℝ≥0∞)
    (hpoincare : ∀ g : ℕ → ℝ, pairVariance g ≤ countableJumpEnergy W g)
    (M : ℝ) (N : ℕ) :
    ∃ d : ℕ, d.Prime ∧ N ≤ d ∧ 3 < d ∧
      ENNReal.ofReal M ≤ correctionJumpEnergy W d := by
  obtain ⟨T, hT⟩ := eventually_atTop.mp
    (correctionJumpEnergy_large_eventually W hpoincare M)
  obtain ⟨d, hdge, hp⟩ := Nat.exists_infinite_primes (max (max T N) 4)
  have hdT : T ≤ d := (le_trans (le_max_left T N)
    (le_max_left (max T N) 4)).trans hdge
  have hdN : N ≤ d := (le_trans (le_max_right T N)
    (le_max_left (max T N) 4)).trans hdge
  have hd4 : 4 ≤ d := (le_max_right (max T N) 4).trans hdge
  exact ⟨d, hp, hdN, by omega, hT d hdT⟩

/-- The actual complete prime-resampling energy diverges; the Poincare
provider is discharged by the proved arithmetic prime-kernel theorem. -/
theorem actualPrimeDirichletEnergy_large_eventually (M : ℝ) :
    ∀ᶠ d : ℕ in atTop,
      ENNReal.ofReal M ≤ PrimeResampling.dirichletEnergy
        (qWeightedSequence (actualCorrection d)) := by
  exact correctionJumpEnergy_large_eventually PrimeResampling.primeFlow
    QPrimeResampling.prime_resampling_poincare M

theorem exists_prime_actualCorrection_large_primeDirichletEnergy
    (M : ℝ) (N : ℕ) :
    ∃ d : ℕ, d.Prime ∧ N ≤ d ∧ 3 < d ∧
      ENNReal.ofReal M ≤ PrimeResampling.dirichletEnergy
        (qWeightedSequence (actualCorrection d)) := by
  exact exists_prime_actualCorrection_large_jumpEnergy PrimeResampling.primeFlow
    QPrimeResampling.prime_resampling_poincare M N

/-- The same family's actual raw source has the uniform paper budget. -/
theorem actualPrimeRawSourceDirichletEnergy_le (d : ℕ) :
    PrimeResampling.dirichletEnergy
      (qWeightedSequence (QShiftedReciprocal.B (actualResidual d))) ≤
        ENNReal.ofReal (1 / 128 : ℝ) := by
  calc
    _ ≤ ENNReal.ofReal (‖actualResidual d‖ ^ 2 / 32) :=
      rawSourceDirichletEnergy_le (actualResidual d)
    _ ≤ _ := by
      apply ENNReal.ofReal_le_ofReal
      nlinarith [actualResidual_norm_le_half d, norm_nonneg (actualResidual d)]

/-- No fixed finite transfer constant controls the actual projected prime
Dirichlet energy over these legal squarefree subspaces, despite their actual
residual forcing and their uniformly bounded raw source. -/
theorem no_uniform_prime_dirichlet_transfer :
    ¬ ∃ C : ℝ, 0 ≤ C ∧ ∀ d : ℕ, d.Prime → 3 < d →
      PrimeResampling.dirichletEnergy (qWeightedSequence (actualCorrection d)) ≤
        ENNReal.ofReal C *
          (PrimeResampling.dirichletEnergy
              (qWeightedSequence (QShiftedReciprocal.B (actualResidual d))) +
            ENNReal.ofReal (‖actualResidual d‖ ^ 2)) := by
  rintro ⟨C, hC, hbound⟩
  obtain ⟨d, hp, _, hd, hlarge⟩ :=
    exists_prime_actualCorrection_large_primeDirichletEnergy (C * (33 / 128) + 1) 0
  have hres : ‖actualResidual d‖ ^ 2 ≤ 1 / 4 := by
    nlinarith [actualResidual_norm_le_half d, norm_nonneg (actualResidual d)]
  have hbudget : PrimeResampling.dirichletEnergy
        (qWeightedSequence (QShiftedReciprocal.B (actualResidual d))) +
      ENNReal.ofReal (‖actualResidual d‖ ^ 2) ≤ ENNReal.ofReal (33 / 128 : ℝ) := by
    calc
      _ ≤ ENNReal.ofReal (1 / 128 : ℝ) + ENNReal.ofReal (1 / 4 : ℝ) :=
        add_le_add (actualPrimeRawSourceDirichletEnergy_le d)
          (ENNReal.ofReal_le_ofReal hres)
      _ = _ := by
        rw [← ENNReal.ofReal_add (by norm_num : (0 : ℝ) ≤ 1 / 128)
          (by norm_num : (0 : ℝ) ≤ 1 / 4)]
        congr 1
        norm_num
  have hupper : PrimeResampling.dirichletEnergy (qWeightedSequence (actualCorrection d)) ≤
      ENNReal.ofReal (C * (33 / 128)) := by
    calc
      _ ≤ _ := hbound d hp hd
      _ ≤ ENNReal.ofReal C * ENNReal.ofReal (33 / 128 : ℝ) :=
        mul_le_mul_of_nonneg_left hbudget zero_le
      _ = _ := (ENNReal.ofReal_mul hC).symm
  have hreal := (ENNReal.ofReal_le_ofReal_iff
    (show 0 ≤ C * (33 / 128) by positivity)).mp (hlarge.trans hupper)
  linarith

end RiemannResearch.RH.QLegalMixedConductor
