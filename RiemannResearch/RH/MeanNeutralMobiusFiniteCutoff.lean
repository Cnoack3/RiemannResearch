/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.ConditionalMeanFiniteCutoff
import RiemannResearch.RH.ConditionalMeanEnergy
import RiemannResearch.RH.ConditionalMeanLowerGrowth
import RiemannResearch.RH.SquarefreeMobiusCesaroEnergy
import RiemannResearch.RH.SquarefreeMobiusCesaroHeads
import RiemannResearch.Analysis.LowerLogGrowth
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Certified finite windows for the mean-neutral Mobius RH criterion

Source: prior-chat finite-cutoff recovery handoff of 1 November 2026,
for the cubic cutoff and intended RH assembly. The exact signed family and
complete cubic-tail bound come from SquarefreeMobiusCesaroEnergy.
The finite-prefix growth provider remains Open; the RH endpoints are
conditional research reductions. This module does not prove that provider.
-/

noncomputable section
open Filter
open scoped BigOperators Topology
namespace RiemannResearch.RH.Pareto
open Analysis.Cesaro Probability.ConditionalIID
open RiemannResearch.Analysis.SubpolynomialWindow

def meanNeutralCubicBudget (H D E : ℕ) : ℝ :=
  mobiusPrefixDefectBudget H + |mobiusReciprocalSum H| *
    (|mobiusRepairWeightLeft H D E| * (D : ℝ) ^ 2 +
      |mobiusRepairWeightRight H D E| * (E : ℝ) ^ 2) / 8

theorem meanNeutralMobiusHead_mem_fullLegal (H D E : ℕ)
    (hD : H < D) (hDE : D < E) :
    meanNeutralMobiusHead H D E ∈ legalSeedSpan (Set.Ici 1) := by
  change mobiusRepairWeightLeft H D E • squarefreeMobiusHead H D +
      mobiusRepairWeightRight H D E • squarefreeMobiusHead H E ∈
    legalSeedSpan (Set.Ici 1)
  exact (legalSeedSpan (Set.Ici 1)).add_mem
    ((legalSeedSpan (Set.Ici 1)).smul_mem _ (squarefreeMobiusHead_mem_legal H D hD))
    ((legalSeedSpan (Set.Ici 1)).smul_mem _
      (squarefreeMobiusHead_mem_legal H E (hD.trans hDE)))

theorem meanNeutralMobiusHead_tail_le_one (H D E N : ℕ)
    (hH : 0 < H) (hD : H < D) (hDE : D < E)
    (hcut : 2 * meanNeutralCubicBudget H D E ^ 2 ≤
      ((N : ℝ) + 2) * ((N : ℝ) + 1) ^ 2) :
    conditionalMeanTailSquare N (meanNeutralMobiusHead H D E) ≤ 1 := by
  have hb := meanNeutralMobiusHead_cubic_tail H D E N hH hD hDE
  change conditionalMeanTailSquare N (meanNeutralMobiusHead H D E) ≤
    2 * meanNeutralCubicBudget H D E ^ 2 /
      (((N : ℝ) + 2) * ((N : ℝ) + 1) ^ 2) at hb
  apply hb.trans
  apply (div_le_iff₀ (by positivity :
    (0 : ℝ) < ((N : ℝ) + 2) * ((N : ℝ) + 1) ^ 2)).mpr
  simpa only [one_mul] using hcut

theorem exists_meanNeutralCubicCutoff (H D E : ℕ) :
    ∃ N : ℕ, H ≤ N ∧ 2 * meanNeutralCubicBudget H D E ^ 2 ≤
      ((N : ℝ) + 2) * ((N : ℝ) + 1) ^ 2 := by
  obtain ⟨N, hN⟩ := exists_nat_gt
    (max (H : ℝ) (2 * meanNeutralCubicBudget H D E ^ 2))
  have hHN : (H : ℝ) < N := (le_max_left _ _).trans_lt hN
  have hBN : 2 * meanNeutralCubicBudget H D E ^ 2 < (N : ℝ) :=
    (le_max_right _ _).trans_lt hN
  have h0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hs : (1 : ℝ) ≤ ((N : ℝ) + 1) ^ 2 := by nlinarith
  have hm := mul_le_mul_of_nonneg_left hs (by positivity : (0 : ℝ) ≤ (N : ℝ) + 2)
  refine ⟨N, ?_, ?_⟩
  · have : H < N := by exact_mod_cast hHN
    omega
  · nlinarith

theorem meanNeutral_lowerLogGrowth_zero_iff_finitePrefix
    (H D E N : ℕ → ℕ) (hH : ∀ j, 0 < H j)
    (hD : ∀ j, H j < D j) (hDE : ∀ j, D j < E j)
    (hHt : Tendsto H atTop atTop)
    (hcut : ∀ j, 2 * meanNeutralCubicBudget (H j) (D j) (E j) ^ 2 ≤
      ((N j : ℝ) + 2) * ((N j : ℝ) + 1) ^ 2) :
    lowerLogGrowth (fun j => conditionalMeanSquare
      (meanNeutralMobiusHead (H j) (D j) (E j))) (fun j => (H j : ℝ)) = 0 ↔
    lowerLogGrowth (fun j => conditionalMeanPrefix
      (meanNeutralMobiusHead (H j) (D j) (E j)) (N j)) (fun j => (H j : ℝ)) = 0 := by
  have hs (j : ℕ) := legal_conditionalMeanSquare_summable (Set.Ici 1)
    (by intro a ha; exact ha)
    (meanNeutralMobiusHead_mem_fullLegal (H j) (D j) (E j) (hD j) (hDE j))
  have ht : ∀ᶠ j in atTop,
      conditionalMeanTailSquare (N j)
        (meanNeutralMobiusHead (H j) (D j) (E j)) / |(1 : ℝ)| ^ 2 ≤ 1 :=
    Filter.Eventually.of_forall (fun j => by
      simpa using meanNeutralMobiusHead_tail_le_one
        (H j) (D j) (E j) (N j) (hH j) (hD j) (hDE j) (hcut j))
  simpa using normalized_lowerLogGrowth_zero_iff_finitePrefix
    (fun j => meanNeutralMobiusHead (H j) (D j) (E j)) N
    (fun j => (H j : ℝ)) (fun _ => (1 : ℝ)) 1
    (tendsto_natCast_atTop_atTop.comp hHt) hs ht

/-- Conditional research reduction. Only the finite-prefix growth provider
is unresolved; cutoff existence and the complete tail bound are proved. -/
theorem riemannHypothesis_of_meanNeutral_finitePrefix_lower_growth
    (H D E N : ℕ → ℕ) (hH : ∀ j, 0 < H j)
    (hD : ∀ j, H j < D j) (hDE : ∀ j, D j < E j)
    (hHt : Tendsto H atTop atTop)
    (hcut : ∀ j, 2 * meanNeutralCubicBudget (H j) (D j) (E j) ^ 2 ≤
      ((N j : ℝ) + 2) * ((N j : ℝ) + 1) ^ 2)
    (hsmall : lowerLogGrowth (fun j => conditionalMeanPrefix
      (meanNeutralMobiusHead (H j) (D j) (E j)) (N j)) (fun j => (H j : ℝ)) = 0) :
    RiemannHypothesis := by
  have hfull := (meanNeutral_lowerLogGrowth_zero_iff_finitePrefix
    H D E N hH hD hDE hHt hcut).mpr hsmall
  apply riemannHypothesis_of_cofinally_small_conditionalMean_heads (Set.Ici 1)
    (by intro a ha; exact ha)
    (fun j => meanNeutralMobiusHead (H j) (D j) (E j)) H
    (fun j => meanNeutralMobiusHead_mem_fullLegal _ _ _ (hD j) (hDE j))
    (fun j n hn hnH => meanNeutralMobiusHead_exact _ _ _ (hH j) (hD j) (hDE j) n hn hnH)
    hHt
  exact (lowerLogGrowth_eq_zero_iff _ _).mp hfull


/-- A complete energy certificate, including the nonnegative infinite tail. -/
theorem meanNeutralMobiusHead_finite_certificate (H D E N : ℕ)
    (hH : 0 < H) (hD : H < D) (hDE : D < E)
    (hcut : 2 * meanNeutralCubicBudget H D E ^ 2 ≤
      ((N : ℝ) + 2) * ((N : ℝ) + 1) ^ 2) :
    conditionalMeanPrefix (meanNeutralMobiusHead H D E) N ≤
        conditionalMeanSquare (meanNeutralMobiusHead H D E) ∧
      conditionalMeanSquare (meanNeutralMobiusHead H D E) ≤
        conditionalMeanPrefix (meanNeutralMobiusHead H D E) N + 1 := by
  have hs := legal_conditionalMeanSquare_summable (Set.Ici 1)
    (by intro a ha; exact ha) (meanNeutralMobiusHead_mem_fullLegal H D E hD hDE)
  have he := conditionalMeanSquare_eq_prefix_add_tail
    (meanNeutralMobiusHead H D E) N hs
  have ht := meanNeutralMobiusHead_tail_le_one H D E N hH hD hDE hcut
  exact ⟨conditionalMeanPrefix_le _ _ hs, by linarith⟩

/-- Least certified cutoff. Existence is arithmetic, without an asymptotic
energy or cancellation hypothesis. -/
def meanNeutralCubicCutoff (H D E : ℕ) : ℕ := by
  classical
  exact Nat.find (exists_meanNeutralCubicCutoff H D E)

theorem meanNeutralCubicCutoff_spec (H D E : ℕ) :
    H ≤ meanNeutralCubicCutoff H D E ∧
      2 * meanNeutralCubicBudget H D E ^ 2 ≤
        ((meanNeutralCubicCutoff H D E : ℝ) + 2) *
          ((meanNeutralCubicCutoff H D E : ℝ) + 1) ^ 2 := by
  classical
  exact Nat.find_spec (exists_meanNeutralCubicCutoff H D E)

/-- Conditional research reduction with its cutoff premise discharged.
Open: zero lower logarithmic growth of this actual finite-prefix energy. -/
theorem riemannHypothesis_of_meanNeutral_certifiedPrefix_lower_growth
    (H D E : ℕ → ℕ) (hH : ∀ j, 0 < H j)
    (hD : ∀ j, H j < D j) (hDE : ∀ j, D j < E j)
    (hHt : Tendsto H atTop atTop)
    (hsmall : lowerLogGrowth (fun j => conditionalMeanPrefix
      (meanNeutralMobiusHead (H j) (D j) (E j))
      (meanNeutralCubicCutoff (H j) (D j) (E j))) (fun j => (H j : ℝ)) = 0) :
    RiemannHypothesis :=
  riemannHypothesis_of_meanNeutral_finitePrefix_lower_growth H D E
    (fun j => meanNeutralCubicCutoff (H j) (D j) (E j))
    hH hD hDE hHt
    (fun j => (meanNeutralCubicCutoff_spec (H j) (D j) (E j)).2) hsmall

end RiemannResearch.RH.Pareto
