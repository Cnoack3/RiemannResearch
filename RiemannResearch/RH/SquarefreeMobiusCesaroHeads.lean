/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.ConditionalMeanLowerGrowth
import RiemannResearch.RH.CoupledCorrectionRHBridge
import RiemannResearch.RH.CanonicalMobiusConditionalHead
import RiemannResearch.RH.CRTSquarefreeBoundedTail
import RiemannResearch.RH.SquarefreeStageExhaustion
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Squarefree Möbius exact heads with a free repair conductor

Source: user-provided `Conditional_IID_Pareto_Cesaro_Research_Agenda_2026-11-01.md`,
Sections 9 and 11. The prefix identity is supplied by
`CanonicalMobiusConditionalHead`. The new repair conductor can be any
squarefree integer larger than the head. Membership is in the literal
finite divisor-residue span of a squarefree common period, with composite
squarefree conductors retained. No asymptotic energy bound is asserted.
-/

noncomputable section
open Filter
open scoped BigOperators Topology
namespace RiemannResearch.RH.Pareto
open ArithmeticCumulative SquarefreeStageExhaustion

/-- A correction conductor strictly beyond the head may be chosen squarefree.
No energy bound is part of this definition. -/
def squarefreeMobiusHead (H D : ℕ) (n : ℕ) : ℝ :=
  -(∑ d ∈ Finset.Icc 1 H, (ArithmeticFunction.moebius d : ℝ) * residueFraction d n) +
    (D : ℝ) * mobiusReciprocalSum H * residueFraction D n

theorem squarefreeMobiusHead_exact (H D n : ℕ) (hD : H < D)
    (hn : 0 < n) (hnH : n ≤ H) : squarefreeMobiusHead H D n = 1 := by
  have hDR : (D : ℝ) ≠ 0 := by exact_mod_cast (by omega : D ≠ 0)
  unfold squarefreeMobiusHead
  rw [mobius_residue_prefix_identity H n hn hnH]
  unfold residueFraction
  rw [Nat.mod_eq_of_lt (lt_of_le_of_lt hnH hD)]
  field_simp
  ring

/-- Literal finite squarefree membership, including every composite squarefree
conductor in the Mobius prefix. No dilation closure is used. -/
theorem squarefreeMobiusHead_mem_divisorSpan (H D : ℕ) (hH : 0 < H)
    (hD : H < D) (hDs : Squarefree D) :
    squarefreeMobiusHead H D ∈ divisorResidueSpan (primorialPeriod (max H D)) := by
  classical
  let S := divisorResidueSpan (primorialPeriod (max H D))
  have hsum : (∑ d ∈ Finset.Icc 1 H,
      (ArithmeticFunction.moebius d : ℝ) • residueFraction d) ∈ S := by
    apply S.sum_mem
    intro d hd
    by_cases h1 : d = 1
    · subst d
      have hz : (ArithmeticFunction.moebius 1 : ℝ) • residueFraction 1 = 0 := by
        ext n
        simp [residueFraction, Nat.mod_one]
      rw [hz]
      exact S.zero_mem
    by_cases hsf : Squarefree d
    · apply S.smul_mem
      apply Submodule.subset_span
      exact ⟨d, by have := (Finset.mem_Icc.mp hd).1; omega,
        squarefree_dvd_primorialPeriod d (max H D) hsf
          ((Finset.mem_Icc.mp hd).2.trans (le_max_left H D)), rfl⟩
    · rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree hsf]
      simp only [Int.cast_zero, zero_smul]
      exact S.zero_mem
  have hrepair : residueFraction D ∈ S :=
    Submodule.subset_span ⟨D, by omega,
      squarefree_dvd_primorialPeriod D (max H D) hDs (le_max_right H D), rfl⟩
  have h := S.add_mem (S.neg_mem hsum)
    (S.smul_mem ((D : ℝ) * mobiusReciprocalSum H) hrepair)
  convert h using 1
  ext n
  simp only [squarefreeMobiusHead, Pi.add_apply, Pi.neg_apply,
    Finset.sum_apply, Pi.smul_apply, smul_eq_mul]

/-- Unconditional existence of a completely explicit squarefree repair.
A primorial is a convenient witness; energy-efficient choices remain separate. -/
theorem exists_squarefreeMobiusHead (H : ℕ) (hH : 0 < H) :
    ∃ D : ℕ, H < D ∧ Squarefree D ∧
      squarefreeMobiusHead H D ∈ divisorResidueSpan (primorialPeriod (max H D)) ∧
      ∀ n, 0 < n → n ≤ H → squarefreeMobiusHead H D n = 1 := by
  have hD : H < primorialPeriod H := by
    have hb : H + 3 ≤ primorialPeriod H := le_primorial_self
    omega
  exact ⟨primorialPeriod H, hD, primorialPeriod_squarefree H,
    squarefreeMobiusHead_mem_divisorSpan H _ hH hD (primorialPeriod_squarefree H),
    fun n hn hnH => squarefreeMobiusHead_exact H _ n hD hn hnH⟩

/-- Every fixed squarefree conductor has a nonzero Mobius prefix coefficient. -/
theorem squarefree_mobius_prefix_coefficient_ne_zero (d : ℕ) (hd : Squarefree d) :
    -(ArithmeticFunction.moebius d : ℝ) ≠ 0 := by
  apply neg_ne_zero.mpr
  exact_mod_cast ArithmeticFunction.moebius_ne_zero_iff_squarefree.mpr hd

/-- Deterministic finite averaging preserves the entire exact head.
Weights may be signed; their sum, not probabilistic independence, is used. -/
theorem squarefreeMobiusHead_average_exact
    {ι : Type*} (S : Finset ι) (a : ι → ℝ) (D : ι → ℕ) (H : ℕ)
    (ha : ∑ i ∈ S, a i = 1)
    (hD : ∀ i ∈ S, H < D i) (n : ℕ) (hn : 0 < n) (hnH : n ≤ H) :
    (∑ i ∈ S, a i * squarefreeMobiusHead H (D i) n) = 1 := by
  calc
    _ = ∑ i ∈ S, a i := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [squarefreeMobiusHead_exact H (D i) n (hD i hi) hn hnH, mul_one]
    _ = 1 := ha


/-- The same explicit functions lie in the full legal algebraic span used by
the Mellin consumer. Summability follows from this genuine membership. -/
theorem squarefreeMobiusHead_mem_legal (H D : ℕ) (hD : H < D) :
    squarefreeMobiusHead H D ∈ legalSeedSpan allPositiveSeeds := by
  have hp := finite_residue_correction_mem (Finset.Icc 1 H)
    (fun d => (ArithmeticFunction.moebius d : ℝ))
    (fun d hd => (Finset.mem_Icc.mp hd).1)
  change -(fun n => ∑ d ∈ Finset.Icc 1 H,
      (ArithmeticFunction.moebius d : ℝ) * residueFraction d n) +
      ((D : ℝ) * mobiusReciprocalSum H) • residueFraction D ∈
    legalSeedSpan allPositiveSeeds
  exact (legalSeedSpan allPositiveSeeds).add_mem
    ((legalSeedSpan allPositiveSeeds).neg_mem hp)
    ((legalSeedSpan allPositiveSeeds).smul_mem _
      (residueFraction_mem_legal D (by omega)))

/-- Each fixed squarefree conductor eventually occurs in the prefix with
nonzero coefficient, distinct from the moving repair conductor. -/
theorem squarefreeMobiusHead_prefix_exhaustion (D : ℕ → ℕ)
    (hD : ∀ H, H < D H) (d : ℕ) (hd : 2 ≤ d) (hds : Squarefree d) :
    ∀ᶠ H : ℕ in Filter.atTop, d ∈ Finset.Icc 1 H ∧ d ≠ D H ∧
      -(ArithmeticFunction.moebius d : ℝ) ≠ 0 := by
  filter_upwards [Filter.eventually_ge_atTop d] with H hH
  exact ⟨Finset.mem_Icc.mpr ⟨by omega, hH⟩, by have := hD H; omega,
    squarefree_mobius_prefix_coefficient_ne_zero d hds⟩

/-- Conditional research reduction for the explicit family. Choosing the
repair conductors squarefree is justified by the literal membership theorem
above. Establishing the lower-growth premise remains Open. -/
theorem riemannHypothesis_of_mobiusHead_lower_growth
    (Y D : ℕ → ℕ) (hD : ∀ j, Y j < D j)
    (hY : Filter.Tendsto Y Filter.atTop Filter.atTop)
    (hsmall : Analysis.SubpolynomialWindow.lowerLogGrowth
      (fun j => conditionalMeanSquare (squarefreeMobiusHead (Y j) (D j)))
      (fun j => (Y j : ℝ)) = 0) : RiemannHypothesis := by
  apply riemannHypothesis_of_cofinally_small_conditionalMean_heads
    allPositiveSeeds (by intro a ha; exact ha)
    (fun j => squarefreeMobiusHead (Y j) (D j)) Y
    (fun j => squarefreeMobiusHead_mem_legal (Y j) (D j) (hD j))
    (fun j n hn hnY => squarefreeMobiusHead_exact (Y j) (D j) n (hD j) hn hnY) hY
  exact (Analysis.SubpolynomialWindow.lowerLogGrowth_eq_zero_iff _ _).mp hsmall

end RiemannResearch.RH.Pareto
