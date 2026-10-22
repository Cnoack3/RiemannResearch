import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Ring

/-!
# Exact energy of any orthogonal-projection trial

Source: user-provided finite-trial continuation (2026-09-30).
This is the elementary Hilbert-space Pythagorean identity, with the complete
trial-to-projection square retained. No approximation provider is assumed.
-/

namespace RiemannResearch.Analysis
theorem projection_trial_energy {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] (S : Submodule ℝ H) [S.HasOrthogonalProjection]
    (x y : H) (hy : y ∈ S) :
    ‖x - y‖ ^ 2 = ‖x - S.starProjection x‖ ^ 2 +
      ‖S.starProjection x - y‖ ^ 2 := by
  have ho : inner ℝ (x - S.starProjection x) (S.starProjection x - y) = 0 := by
    rw [real_inner_comm]
    exact (S.mem_orthogonal _).mp (Submodule.sub_starProjection_mem_orthogonal x) _
      (S.sub_mem (S.starProjection_apply_mem x) hy)
  have he : x - y = (x - S.starProjection x) + (S.starProjection x - y) := by abel
  rw [he, norm_add_sq_real, ho]
  ring
end RiemannResearch.Analysis
