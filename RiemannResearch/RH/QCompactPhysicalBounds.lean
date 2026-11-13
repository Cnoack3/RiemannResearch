import RiemannResearch.RH.ZetaTwoHilbertSpace
import Mathlib.Topology.ContinuousMap.Bounded.Basic

/-!
# Physical bounds from compact continuous approximations

Source: the user's request about continuity of the actual displacement,
2026-11-12. This is the standard compactness bound plus the triangle inequality.
It is independent of the arithmetic rigidity of any particular displacement.
-/

noncomputable section
namespace RiemannResearch.RH.QCompactPhysicalBounds
open ZetaTwoHilbert

/-- A finite uniform error from a continuous compact trace implies physical boundedness. -/
theorem physically_bounded_of_compact_error
    {X : Type*} [TopologicalSpace X] [CompactSpace X]
    (ι : ℕ → X) (f : QHilbert) (F : C(X, ℝ)) (C : ℝ)
    (h : ∀ n : ℕ, 1 ≤ n → |qSequence f n - F (ι n)| ≤ C) :
    ∃ K : ℝ, ∀ n : ℕ, |qSequence f n| ≤ K := by
  refine ⟨|C| + ‖F‖, ?_⟩
  intro n
  cases n with
  | zero =>
    simpa only [qSequence_zero, abs_zero] using add_nonneg (abs_nonneg C) (norm_nonneg F)
  | succ k =>
    calc
      |qSequence f (k+1)| =
          |(qSequence f (k+1) - F (ι (k+1))) + F (ι (k+1))| := by
            rw [sub_add_cancel]
      _ ≤ |qSequence f (k+1) - F (ι (k+1))| + |F (ι (k+1))| := abs_add_le _ _
      _ ≤ C + ‖F‖ := add_le_add (h (k+1) (Nat.succ_le_succ (Nat.zero_le k)))
        (by simpa only [Real.norm_eq_abs] using F.norm_coe_le_norm (ι (k+1)))
      _ ≤ |C| + ‖F‖ := add_le_add (le_abs_self C) (le_refl ‖F‖)

end RiemannResearch.RH.QCompactPhysicalBounds
