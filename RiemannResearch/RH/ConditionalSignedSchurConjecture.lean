import RiemannResearch.RH.ConditionalMeanGram
import RiemannResearch.RH.ConditionalResidueGram
import RiemannResearch.RH.ConditionalMeanMinimumCriteria

/-!
# Assertion (11.7) and its conjectured RH equivalence

Source: user-provided
`Conditional_IID_Cesaro_Mathematical_Completion_2026-09-17.md`,
Section 11, equations (11.6)--(11.7), for the statement and signed
square-completion strategy.

`UniformSignedSchurTarget` is the literal bound (11.7), already defined
using actual normalized residue matrices. Its parameter D counts columns,
so its maximum conductor is D+1 and Y <= D means Y+1 <= D+1.

Here the implication from that bound to actual Mathlib RH is proved.
`SignedSchurRHEquivalenceConjecture` records the requested equivalence
as a proposition only: it is neither an axiom nor a theorem.
The reverse implication still needs the classical RH-to-density
formalization and the exact-head/kernel-basis assembly. Neither the
bound nor its reverse implication is asserted by this module.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.ConditionalMeanGram
open RiemannResearch.RH.Pareto
open RiemannResearch.RH.ArithmeticCumulative
open RiemannResearch.Probability.ConditionalIID
open RiemannResearch.Analysis.FiniteSignedQuadratic

/-- The actual arithmetic witness attached to the Fin D matrix columns. -/
def columnSynthesis (D : ℕ) (c : Fin D → ℝ) : ℕ → ℝ :=
  fun n => ∑ d : Fin D, c d * residueFraction (d.val + 2) n

theorem columnSynthesis_mem_legal (D : ℕ) (c : Fin D → ℝ) :
    columnSynthesis D c ∈ legalSeedSpan (Set.Ici 1) := by
  have he : columnSynthesis D c =
      ∑ d : Fin D, (c d / (d.val + 2 : ℕ)) • Pareto.residue (d.val + 2) := by
    funext n
    simp only [columnSynthesis, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro d _
    simp only [residueFraction, Pareto.residue]
    ring
  rw [he]
  apply Submodule.sum_mem
  intro d _
  apply Submodule.smul_mem
  simpa only [dilation_one] using
    (dilation_generator_mem (Set.Ici 1) (a := d.val + 2) (m := 1)
      (show d.val + 2 ∈ Set.Ici 1 from by change 1 ≤ d.val + 2; omega) (by omega))

theorem cesaro_columnSynthesis (D : ℕ) (c : Fin D → ℝ) (t : ℕ) :
    cesaro (columnSynthesis D c) t = ∑ d : Fin D, c d * column d.val t := by
  exact cesaro_finsetCombination Finset.univ c
    (fun d : Fin D => residueFraction (d.val + 2)) t

/-- A feasible matrix vector has the actual exact ordinary head. -/
theorem columnSynthesis_headClass (Y D : ℕ) (c : Fin D → ℝ)
    (hc : ∀ t : Fin Y, (headMatrix Y D).mulVec c t = 1) :
    columnSynthesis D c ∈ conditionalHeadClass Y := by
  refine ⟨columnSynthesis_mem_legal D c, ?_⟩
  have hmean (t : ℕ) (ht : 0 < t) (htY : t ≤ Y) :
      cesaro (columnSynthesis D c) t = 1 := by
    let i : Fin Y := ⟨t - 1, by omega⟩
    have h := hc i
    rw [cesaro_columnSynthesis]
    simpa only [headMatrix, Matrix.mulVec, dotProduct, i,
      show t - 1 + 1 = t by omega, mul_comm] using h
  intro n hn hnY
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (ne_of_gt hn)
  rw [cesaro_recover (columnSynthesis D c) k, hmean (k + 1) (by omega) hnY]
  by_cases hk : k = 0
  · simp [hk]
  · rw [hmean k (Nat.pos_of_ne_zero hk) (by omega)]
    push_cast
    ring

/-- Exact energy identity for the signed finite matrix witness. -/
theorem columnSynthesis_energy (Y D : ℕ) (c : Fin D → ℝ)
    (hc : ∀ t : Fin Y, (headMatrix Y D).mulVec c t = 1) :
    conditionalMeanSquare (columnSynthesis D c) =
      (Y : ℝ) / ((Y : ℝ) + 2) + quadratic (tailMatrix Y D) c := by
  rw [conditionalMeanSquare_exact_head_split Y (columnSynthesis_headClass Y D c hc),
    tail_quadratic_series]
  simp_rw [cesaro_columnSynthesis]

/-- The concrete finite-tail conjecture supplies bounded actual legal minima. -/
theorem bounded_headMinimum_of_finiteTailTarget (h : UniformFiniteTailTarget) :
    ∃ C : ℝ, ∀ Y, conditionalHeadMinimum Y ≤ C := by
  obtain ⟨K, hK⟩ := h
  refine ⟨K + 1, ?_⟩
  intro Y
  obtain ⟨D, hD, c, hc, hbound⟩ := hK (Y + 1) (by omega)
  have hm := conditionalHeadMinimum_le (Y + 1) (columnSynthesis_headClass (Y + 1) D c hc)
  rw [columnSynthesis_energy (Y + 1) D c hc] at hm
  have hmass : ((Y + 1 : ℕ) : ℝ) / (((Y + 1 : ℕ) : ℝ) + 2) ≤ 1 := by
    apply (div_le_one (by positivity)).mpr
    linarith
  have hmono := conditionalHeadMinimum_mono (show Y ≤ Y + 1 by omega)
  linarith

/-- Conditional research reduction: (11.7) implies actual Mathlib RH.
The only substantive hypothesis is the displayed, unproved bound. -/
theorem riemannHypothesis_of_uniformSignedSchurTarget
    (h : UniformSignedSchurTarget) : RiemannHypothesis :=
  riemannHypothesis_of_bounded_conditionalHeadMinimum
    (bounded_headMinimum_of_finiteTailTarget (finiteTailTarget_of_signedSchurTarget h))

/-- Requested RH equivalence of (11.7), recorded as an unproved conjecture.
Defining this proposition supplies no proof of either RH or the bound. -/
def SignedSchurRHEquivalenceConjecture : Prop :=
  UniformSignedSchurTarget ↔ RiemannHypothesis

/-- The forward direction is proved; the precise remaining equivalence
obligation is RH implies the concrete signed-Schur target. -/
theorem signedSchurRHEquivalenceConjecture_iff_reverse :
    SignedSchurRHEquivalenceConjecture ↔
      (RiemannHypothesis → UniformSignedSchurTarget) := by
  constructor
  · intro h
    exact h.mpr
  · intro h
    exact ⟨riemannHypothesis_of_uniformSignedSchurTarget, h⟩

end RiemannResearch.RH.ConditionalMeanGram
