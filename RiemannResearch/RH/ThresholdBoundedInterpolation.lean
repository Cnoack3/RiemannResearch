import RiemannResearch.Analysis.BoundedInterpolation
import RiemannResearch.RH.ThresholdHilbertLegal
import RiemannResearch.RH.ThresholdHilbertMean

/-!
# Bounded exact interpolation in the actual Nyman-Pareto legal span

Source: user-provided request, September 9, 2026. This applies the exact
Pythagorean convergence argument to the genuine complete weighted Hilbert
space and the algebraic legal seed span with all positive integer dilations.

Conditional research reduction: uniformly bounded finite legal interpolants
are still an open arithmetic input, including for seeds {2, 3}.
This module does not prove that bound or an RH equivalence.
-/

namespace RiemannResearch.RH.Pareto
noncomputable section

private def hilbertEval (n : ℕ) : ThresholdHilbert →L[ℝ] ℝ :=
  ({ toFun := fun f => f n
     map_add' := by intros; rfl
     map_smul' := by intros; rfl } : ThresholdHilbert →ₗ[ℝ] ℝ).mkContinuous 1
    (fun f => by
      change ‖f n‖ ≤ 1 * ‖f‖
      rw [one_mul]
      exact lp.norm_apply_le_norm (by norm_num : (2 : ENNReal) ≠ 0) f n)

/-- A single uniform bound on full squared norms, with exact positive heads,
suffices for target membership in the actual legal closure. The functions in
the hypothesis are finite legal combinations, not arbitrary periodic vectors. -/
theorem hilbertLegalClosure_of_bounded_exact_heads (A : Set ℕ) (C : ℝ)
    (hbounded : ∀ N, ∃ f : ThresholdHilbert, f ∈ hilbertLegalSubspace A ∧
      (∀ k, 0 < k → k ≤ N → hilbertSequence f k = 1) ∧ ‖f‖^2 ≤ C) :
    hilbertOne ∈ hilbertLegalClosure A := by
  apply Analysis.BoundedInterpolation.mem_of_bounded_exact_interpolation
    (hilbertLegalClosure A) (hilbertLegalSubspace A).isClosed_topologicalClosure
    hilbertEval (by intro x y h; apply Subtype.ext; exact h) hilbertOne C
  intro N
  obtain ⟨f, hf, hhead, hbound⟩ := hbounded (N+1)
  refine ⟨f, (hilbertLegalSubspace A).le_topologicalClosure hf, ?_, hbound⟩
  intro k hk
  change f k = hilbertOne k
  have he : hilbertSequence f (k+1) = hilbertSequence hilbertOne (k+1) := by
    calc
      hilbertSequence f (k+1) = 1 :=
        hhead (k+1) (Nat.succ_pos _) (Nat.succ_le_succ hk)
      _ = hilbertSequence hilbertOne (k+1) := by
        rw [hilbertOne_sequence]
        simp [zeroAnchor]
  change f k / Real.sqrt (paretoWeight k) =
    hilbertOne k / Real.sqrt (paretoWeight k) at he
  exact (div_left_inj' (show Real.sqrt (paretoWeight k) ≠ 0 by
    apply ne_of_gt
    apply Real.sqrt_pos.2
    unfold paretoWeight
    positivity)).mp he

end
end RiemannResearch.RH.Pareto
