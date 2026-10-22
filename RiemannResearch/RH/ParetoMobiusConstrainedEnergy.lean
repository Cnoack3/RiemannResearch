import RiemannResearch.RH.ParetoMobiusHeadInterpolation
import RiemannResearch.Analysis.FiniteConstrainedProjection

/-!
# Actual constrained head energy with the concrete Möbius repair cost

Source: user-provided Green--Pareto--Schur continuation, Section 3 of
RH/GreenParetoGitHubAdvance20261006.md. The finite repair constant is now
provided by ParetoMobiusHeadInterpolation rather than assumed.
All norms are complete Pareto norms and the exact orthogonal repair square
is retained before obtaining the infimum comparison. No RH premise or
arithmetic decay provider occurs in these finite statements.
-/

noncomputable section
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
namespace RiemannResearch.RH.Pareto.CoefficientStabilization
open RiemannResearch.Analysis
open FiniteHilbertGram FiniteConstrainedProjection

/-- Exact-head errors over every conductor 2 through M+1. -/
def mobiusExactHeadErrorSet (H M : ℕ) (x : ThresholdHilbert) : Set ℝ :=
  {E | ∃ c : Fin M → ℝ,
    compactHead H (Fintype.linearCombination ℝ (fun i : Fin M => residueAtom i.val) c) =
      compactHead H x ∧
    ‖x - Fintype.linearCombination ℝ (fun i : Fin M => residueAtom i.val) c‖^2 = E}

/-- The literal full-norm constrained error infimum. -/
def mobiusExactHeadEnergy (H M : ℕ) (x : ThresholdHilbert) : ℝ :=
  sInf (mobiusExactHeadErrorSet H M x)

private theorem interpolation_coefficients (H M : ℕ) (hHM : H ≤ M)
    (f : ThresholdHilbert) :
    ∃ d : Fin M → ℝ,
      Fintype.linearCombination ℝ (fun i : Fin M => residueAtom i.val) d =
        mobiusHeadInterpolation H f := by
  have hmem := ExhaustiveWalk.walkSpan_mono residueAtom id hHM
    (mobiusHeadInterpolation_mem H f)
  obtain ⟨d, hd⟩ := finiteSpace_expansion M (mobiusHeadInterpolation H f) hmem
  exact ⟨d, by simpa only [Fintype.linearCombination_apply] using hd.symm⟩

/-- A concrete complete legal competitor, with its full Pythagorean square. -/
theorem exists_mobius_repaired_projection (H M : ℕ) (hHM : H ≤ M)
    (x : ThresholdHilbert) :
    ∃ c : Fin M → ℝ,
      compactHead H (Fintype.linearCombination ℝ (fun i : Fin M => residueAtom i.val) c) =
        compactHead H x ∧
      ‖x - Fintype.linearCombination ℝ (fun i : Fin M => residueAtom i.val) c‖^2 =
        ‖projectionResidual (finiteResidue_independent M) x‖^2 +
          ‖mobiusHeadInterpolation H (projectionResidual (finiteResidue_independent M) x)‖^2 ∧
      ‖x - Fintype.linearCombination ℝ (fun i : Fin M => residueAtom i.val) c‖^2 ≤
        ‖projectionResidual (finiteResidue_independent M) x‖^2 +
          (12 * (H : ℝ))^2 *
            ‖compactHead H (projectionResidual (finiteResidue_independent M) x)‖^2 := by
  let hv := finiteResidue_independent M
  let r := projectionResidual hv x
  obtain ⟨d, hd⟩ := interpolation_coefficients H M hHM r
  have hhead : compactHeadLinear H
      (Fintype.linearCombination ℝ (fun i : Fin M => residueAtom i.val) d) =
      compactHeadLinear H r := by
    change compactHead H _ = compactHead H r
    rw [hd, compactHead_mobiusHeadInterpolation]
  have hnorm : ‖Fintype.linearCombination ℝ (fun i : Fin M => residueAtom i.val) d‖ ≤
      (12*(H : ℝ)) * ‖compactHeadLinear H r‖ := by
    rw [hd]
    exact mobiusHeadInterpolation_norm_le H r
  have htrial := repaired_projection_head_and_error hv x (compactHeadLinear H)
    d (12*(H : ℝ)) hhead hnorm
  refine ⟨inverseCoeff hv x + d, htrial.1, ?_, htrial.2⟩
  rw [residual_completion hv x]
  have he : inverseCoeff hv x + d - inverseCoeff hv x = d := by abel
  rw [he, hd]
  rfl

theorem mobiusExactHeadErrorSet_nonempty (H M : ℕ) (hHM : H ≤ M)
    (x : ThresholdHilbert) : (mobiusExactHeadErrorSet H M x).Nonempty := by
  obtain ⟨c, hc, he, hb⟩ := exists_mobius_repaired_projection H M hHM x
  exact ⟨_, c, hc, rfl⟩

theorem mobiusExactHeadErrorSet_bddBelow (H M : ℕ) (x : ThresholdHilbert) :
    BddBelow (mobiusExactHeadErrorSet H M x) := by
  refine ⟨0, ?_⟩
  rintro E ⟨c, hc, he⟩
  rw [← he]
  positivity

/-- Concrete full-tail comparison: no repair-norm assumption remains. -/
theorem mobiusExactHeadEnergy_comparison (H M : ℕ) (hHM : H ≤ M)
    (x : ThresholdHilbert) :
    ‖projectionResidual (finiteResidue_independent M) x‖^2 +
        ‖compactHead H (projectionResidual (finiteResidue_independent M) x)‖^2 ≤
      mobiusExactHeadEnergy H M x ∧
    mobiusExactHeadEnergy H M x ≤
      ‖projectionResidual (finiteResidue_independent M) x‖^2 +
        (12*(H : ℝ))^2 *
          ‖compactHead H (projectionResidual (finiteResidue_independent M) x)‖^2 := by
  constructor
  · apply le_csInf (mobiusExactHeadErrorSet_nonempty H M hHM x)
    rintro E ⟨c, hc, he⟩
    rw [← he]
    exact constrained_error_lower_bound (finiteResidue_independent M) x
      (compactHeadLinear H) (compactHead_norm_le H) c hc
  · obtain ⟨c, hc, he, hb⟩ := exists_mobius_repaired_projection H M hHM x
    have hle := csInf_le (mobiusExactHeadErrorSet_bddBelow H M x)
      (show ‖x - Fintype.linearCombination ℝ
        (fun i : Fin M => residueAtom i.val) c‖^2 ∈ mobiusExactHeadErrorSet H M x
        from ⟨c,hc,rfl⟩)
    exact hle.trans hb

/-- The complete infimum pays no additional triangle-inequality factor. -/
theorem mobiusExactHeadEnergy_le_projection_cost (H M : ℕ) (hHM : H ≤ M)
    (x : ThresholdHilbert) :
    mobiusExactHeadEnergy H M x ≤
      (1 + (12*(H : ℝ))^2) *
        ‖projectionResidual (finiteResidue_independent M) x‖^2 := by
  have hb := (mobiusExactHeadEnergy_comparison H M hHM x).2
  have hq := compactHead_norm_le H (projectionResidual (finiteResidue_independent M) x)
  have hs : ‖compactHead H (projectionResidual (finiteResidue_independent M) x)‖^2 ≤
      ‖projectionResidual (finiteResidue_independent M) x‖^2 := by
    nlinarith [norm_nonneg (compactHead H (projectionResidual (finiteResidue_independent M) x)),
      norm_nonneg (projectionResidual (finiteResidue_independent M) x)]
  have hm := mul_le_mul_of_nonneg_left hs (sq_nonneg (12*(H : ℝ)))
  nlinarith

end RiemannResearch.RH.Pareto.CoefficientStabilization
