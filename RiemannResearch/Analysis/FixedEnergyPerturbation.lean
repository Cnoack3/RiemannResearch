import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Norm and squared-energy perturbation bounds.
Source: user-provided Prime_Phases_Agenda_Proof_Attempts.tex, prime-power correction. -/
namespace RiemannResearch.Analysis.FixedEnergyPerturbation

variable {E : Type*} [NormedAddCommGroup E]

/-- A fixed norm error gives the reverse-norm estimate on every finite head. -/
theorem root_energy_comparison (u v : E) (K : ℝ) (h : ‖u - v‖ ≤ K) :
    |‖u‖ - ‖v‖| ≤ K := by
  have hu : ‖u‖ ≤ ‖u - v‖ + ‖v‖ := by
    calc
      ‖u‖ = ‖(u - v) + v‖ := by rw [sub_add_cancel]
      _ ≤ ‖u - v‖ + ‖v‖ := norm_add_le _ _
  have hv : ‖v‖ ≤ ‖u - v‖ + ‖u‖ := by
    calc
      ‖v‖ = ‖(v - u) + u‖ := by rw [sub_add_cancel]
      _ ≤ ‖v - u‖ + ‖u‖ := norm_add_le _ _
      _ = ‖u - v‖ + ‖u‖ := by rw [norm_sub_rev]
  apply abs_le.mpr
  constructor <;> linarith

/-- Squared energies differ by the fixed error times their root energies. -/
theorem energy_difference (u v : E) (K : ℝ) (h : ‖u - v‖ ≤ K) :
    |‖u‖ ^ 2 - ‖v‖ ^ 2| ≤ K * (‖u‖ + ‖v‖) := by
  calc
    |‖u‖ ^ 2 - ‖v‖ ^ 2| = |‖u‖ - ‖v‖| * (‖u‖ + ‖v‖) := by
      rw [← abs_of_nonneg (add_nonneg (norm_nonneg u) (norm_nonneg v)),
        ← abs_mul]
      congr 1
      ring
    _ ≤ K * (‖u‖ + ‖v‖) :=
      mul_le_mul_of_nonneg_right (root_energy_comparison u v K h)
        (add_nonneg (norm_nonneg u) (norm_nonneg v))

end RiemannResearch.Analysis.FixedEnergyPerturbation
