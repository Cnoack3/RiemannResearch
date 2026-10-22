import RiemannResearch.RH.CanonicalMobiusStretchedEnergy
import RiemannResearch.RH.ResidueGramCorrectionPairing
import RiemannResearch.RH.ExactHeadCoefficientCounterexample
import RiemannResearch.RH.ParetoAnnihilatorTail

/-!
# Stretched energy bounds for the actual inverse-Gram correction
Source: the user's requested transfer audit, 28 September 2026.
The proof combines the checked canonical energy with exact head cancellation
and orthogonal projection. No density or unproved inverse-Gram estimate is used.
-/
noncomputable section
open Filter
open scoped Topology BigOperators
namespace RiemannResearch.RH.Pareto
open RiemannResearch.Analysis

theorem canonicalMobiusResidual_head_zero (N : ℕ) :
    ∀ k < N, (hilbertOne - canonicalMobiusHilbert N) k = 0 := by
  intro k hk
  have hs := canonicalMobiusHilbert_exact N (k + 1) (by omega) (by omega)
  have hone : hilbertSequence hilbertOne (k + 1) = 1 := by
    rw [hilbertOne_sequence]
    simp [zeroAnchor]
  have hsame := hone.trans hs.symm
  have hw : Real.sqrt (paretoWeight k) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.mpr (paretoWeight_pos k))
  have hc : hilbertOne k = canonicalMobiusHilbert N k := (div_left_inj' hw).mp hsame
  change hilbertOne k - canonicalMobiusHilbert N k = 0
  exact sub_eq_zero.mpr hc

namespace CoefficientStabilization
open RiemannResearch.Analysis

/-- Complete physical tail bound, uniformly over the residue modulus. -/
theorem residueAtom_tail_norm_sq_le (i N : ℕ) :
    ‖hilbertTailShift (residueAtom i) N‖ ^ 2 ≤ 1 / ((N : ℝ) + 1) := by
  rw [hilbertTailShift_energy_eq_weighted]
  have hw : Summable (fun k : ℕ => positiveWeight (k + N + 1)) :=
    positiveWeight_summable.comp_injective (fun _ _ h => by omega)
  have hle (k : ℕ) :
      positiveWeight (k + N + 1) *
          hilbertSequence (residueAtom i) (k + N + 1) ^ 2 ≤
        positiveWeight (k + N + 1) := by
    have hs : hilbertSequence (residueAtom i) (k + N + 1) ^ 2 ≤ 1 := by
      rw [residueAtom, normalizedResidueHilbert_sequence]
      have ha := residueFraction_abs_le_one (i + 2) (k + N + 1) (by omega)
      have hh := (sq_le_sq₀ (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)).mpr ha
      simpa only [sq_abs, one_pow] using hh
    calc
      _ ≤ positiveWeight (k + N + 1) * 1 :=
        mul_le_mul_of_nonneg_left hs (positiveWeight_nonneg _)
      _ = _ := mul_one _
  have hs : Summable (fun k : ℕ => positiveWeight (k + N + 1) *
      hilbertSequence (residueAtom i) (k + N + 1) ^ 2) :=
    Summable.of_nonneg_of_le
      (fun k => mul_nonneg (positiveWeight_nonneg _) (sq_nonneg _)) hle hw
  calc
    _ ≤ ∑' k : ℕ, positiveWeight (k + N + 1) := Summable.tsum_le_tsum hle hs hw
    _ = 1 / ((N : ℝ) + 1) := by
      simpa only [Nat.add_assoc, Nat.cast_add, Nat.cast_one] using
        positiveWeight_tail_tsum (N + 1) (by omega)

/-- The auxiliary exact-head residual has a uniformly small pairing with every
residue atom whenever its full energy is sublinear. -/
theorem canonicalMobiusResidual_inner_atom_sq_le (N i : ℕ) :
    (inner ℝ (hilbertOne - canonicalMobiusHilbert N) (residueAtom i)) ^ 2 ≤
      ‖hilbertOne - canonicalMobiusHilbert N‖ ^ 2 / ((N : ℝ) + 1) := by
  have hcs := hilbertTailShift_inner_sq_le (residueAtom i)
    (hilbertOne - canonicalMobiusHilbert N) N (canonicalMobiusResidual_head_zero N)
  calc
    _ = (inner ℝ (residueAtom i) (hilbertOne - canonicalMobiusHilbert N)) ^ 2 := by
      rw [real_inner_comm]
    _ ≤ ‖hilbertTailShift (residueAtom i) N‖ ^ 2 *
        ‖hilbertOne - canonicalMobiusHilbert N‖ ^ 2 := hcs
    _ ≤ (1 / ((N : ℝ) + 1)) * ‖hilbertOne - canonicalMobiusHilbert N‖ ^ 2 :=
      mul_le_mul_of_nonneg_right (residueAtom_tail_norm_sq_le i N) (sq_nonneg _)
    _ = _ := by ring

/-- Uniformity includes all moduli, including those beyond the cutoff. This is
an unconditional source estimate, not an inverse-Gram correction estimate. -/
theorem canonicalMobiusResidual_eventual_uniform_atom_pairing :
    ∃ a : ℝ, 0 < a ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ N : ℕ in Filter.atTop, ∀ i : ℕ,
      (inner ℝ (hilbertOne - canonicalMobiusHilbert N) (residueAtom i)) ^ 2 ≤
        8 / ((N : ℝ) + 1) + C *
          Real.exp (-a * logProductPower (1 / 11) (6 + Real.log (N : ℝ))) := by
  obtain ⟨a, ha, C, hC, hb⟩ := canonicalMobiusResidual_eventual_stretched_energy
  refine ⟨a, ha, C, hC, ?_⟩
  filter_upwards [hb] with N hN
  intro i
  have hden : 0 < (N : ℝ) + 1 := by positivity
  have hratio : (N : ℝ) / ((N : ℝ) + 1) ≤ 1 :=
    (div_le_one hden).mpr (by linarith)
  have hexp : 0 ≤ C *
      Real.exp (-a * logProductPower (1 / 11) (6 + Real.log (N : ℝ))) :=
    mul_nonneg hC (Real.exp_pos _).le
  calc
    _ ≤ ‖hilbertOne - canonicalMobiusHilbert N‖ ^ 2 / ((N : ℝ) + 1) :=
      canonicalMobiusResidual_inner_atom_sq_le N i
    _ ≤ (8 + C * (N : ℝ) *
        Real.exp (-a * logProductPower (1 / 11) (6 + Real.log (N : ℝ)))) /
          ((N : ℝ) + 1) := div_le_div_of_nonneg_right hN hden.le
    _ = 8 / ((N : ℝ) + 1) +
        (C * Real.exp (-a * logProductPower (1 / 11) (6 + Real.log (N : ℝ)))) *
          ((N : ℝ) / ((N : ℝ) + 1)) := by ring
    _ ≤ 8 / ((N : ℝ) + 1) +
        (C * Real.exp (-a * logProductPower (1 / 11) (6 + Real.log (N : ℝ)))) * 1 :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_left hratio hexp)
    _ = _ := by ring

end CoefficientStabilization


namespace CoefficientStabilization

/-- A finite-stage analogue of the limiting residual tail product, allowing
an independently chosen exact-head cutoff N at any later stage M. -/
theorem projection_error_sq_le_canonicalResidual_tail (N M : ℕ) (hNM : N ≤ M) :
    (‖hilbertOne - projection M‖ ^ 2) ^ 2 ≤
      ‖hilbertTailShift (hilbertOne - projection M) N‖ ^ 2 *
        ‖hilbertOne - canonicalMobiusHilbert N‖ ^ 2 := by
  have hmem : canonicalMobiusHilbert N ∈ finiteSpace M :=
    RiemannResearch.Analysis.ExhaustiveWalk.walkSpan_mono residueAtom id hNM
      (canonicalMobiusHilbert_mem_finiteSpace N)
  have horth : inner ℝ (hilbertOne - projection M) (canonicalMobiusHilbert N) = 0 :=
    Submodule.starProjection_inner_eq_zero hilbertOne _ hmem
  have hp : inner ℝ (hilbertOne - projection M) (projection M) = 0 :=
    Submodule.starProjection_inner_eq_zero hilbertOne _
      ((finiteSpace M).starProjection_apply_mem hilbertOne)
  have hone : inner ℝ (hilbertOne - projection M) hilbertOne =
      ‖hilbertOne - projection M‖ ^ 2 := by
    have h := inner_sub_right (𝕜 := ℝ) (hilbertOne - projection M) hilbertOne (projection M)
    rw [real_inner_self_eq_norm_sq, hp, sub_zero] at h
    exact h.symm
  have h := hilbertTailShift_inner_sq_le (hilbertOne - projection M)
    (hilbertOne - canonicalMobiusHilbert N) N (canonicalMobiusResidual_head_zero N)
  simpa only [inner_sub_right, horth, sub_zero, hone] using h

theorem projection_error_eventual_stretched_tail_bound :
    ∃ a : ℝ, 0 < a ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ N : ℕ in atTop,
      ∀ M : ℕ, N ≤ M →
        (‖hilbertOne - projection M‖ ^ 2) ^ 2 ≤
          ‖hilbertTailShift (hilbertOne - projection M) N‖ ^ 2 *
            (8 + C * (N : ℝ) *
              Real.exp (-a * logProductPower (1 / 11) (6 + Real.log (N : ℝ)))) := by
  obtain ⟨a, ha, C, hC, hb⟩ := canonicalMobiusResidual_eventual_stretched_energy
  refine ⟨a, ha, C, hC, ?_⟩
  filter_upwards [hb] with N hN
  intro M hNM
  exact (projection_error_sq_le_canonicalResidual_tail N M hNM).trans
    (mul_le_mul_of_nonneg_left hN (sq_nonneg _))

end CoefficientStabilization

namespace CoefficientStabilization.GramMobiusCorrection

/-- The auxiliary exact head may use a smaller cutoff than the projection. -/
theorem correction_eq_canonicalResidual_pairing (N M i : ℕ)
    (hNM : N ≤ M) (hi : i + 2 ≤ N) :
    correction M (i + 2) =
      inner ℝ (hilbertOne - canonicalMobiusHilbert N)
        ((finiteSpace M).starProjection (coefficientDual i)) := by
  have hmem : canonicalMobiusHilbert N ∈ finiteSpace M :=
    RiemannResearch.Analysis.ExhaustiveWalk.walkSpan_mono residueAtom id hNM
      (canonicalMobiusHilbert_mem_finiteSpace N)
  rw [← Submodule.inner_starProjection_left_eq_right, map_sub,
    Submodule.starProjection_eq_self_iff.mpr hmem, inner_sub_left,
    coefficientDual_inner, coefficientDual_inner,
    coefficientCLM_eq_mobius_of_exact_head _ N (i + 2) (by omega) hi
      (canonicalMobiusHilbert_exact N)]
  change coefficient M (i + 2) + _ = coefficient M (i + 2) - -_
  ring

/-- Only the physical tail of the projected coefficient dual is charged. -/
theorem correction_sq_le_canonicalResidual_tail (N M i : ℕ)
    (hNM : N ≤ M) (hi : i + 2 ≤ N) :
    correction M (i + 2) ^ 2 ≤
      ‖hilbertTailShift ((finiteSpace M).starProjection (coefficientDual i)) N‖ ^ 2 *
        ‖hilbertOne - canonicalMobiusHilbert N‖ ^ 2 := by
  rw [correction_eq_canonicalResidual_pairing N M i hNM hi, real_inner_comm]
  exact hilbertTailShift_inner_sq_le _ _ N (canonicalMobiusResidual_head_zero N)

/-- An unconditional two-cutoff estimate for the actual matrix correction.
The unknown quantity is the physical tail of its projected dual. -/
theorem correction_eventual_stretched_tail_bound :
    ∃ a : ℝ, 0 < a ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ N : ℕ in atTop,
      ∀ M : ℕ, N ≤ M → ∀ i : ℕ, i + 2 ≤ N →
        correction M (i + 2) ^ 2 ≤
          ‖hilbertTailShift ((finiteSpace M).starProjection (coefficientDual i)) N‖ ^ 2 *
            (8 + C * (N : ℝ) *
              Real.exp (-a * logProductPower (1 / 11) (6 + Real.log (N : ℝ)))) := by
  obtain ⟨a, ha, C, hC, hb⟩ := canonicalMobiusResidual_eventual_stretched_energy
  refine ⟨a, ha, C, hC, ?_⟩
  filter_upwards [hb] with N hN
  intro M hNM i hi
  exact (correction_sq_le_canonicalResidual_tail N M i hNM hi).trans
    (mul_le_mul_of_nonneg_left hN (sq_nonneg _))

/-- Fixed diagonal growth is already controlled; this does not control its
physical tail at the stretched scale. -/
theorem residueInverseEntry_diagonal_le_dual (N : ℕ) (i : Fin N) :
    residueInverseEntry N i i ≤ ‖coefficientDual i.val‖ ^ 2 := by
  have h := residueInverseEntry_diagonal N i
  nlinarith [sq_nonneg ‖coefficientDual i.val -
    (finiteSpace N).starProjection (coefficientDual i.val)‖]

end CoefficientStabilization.GramMobiusCorrection
end RiemannResearch.RH.Pareto
