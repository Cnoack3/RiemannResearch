import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Topology.Sequences
import Mathlib.Tactic.Abel

/-!
# Closure with a finite-dimensional continuous correction

Source: user-provided argument,
`Conditional_IID_Cesaro_Mathematical_Completion_2026-09-17.md`,
Section 10.3. This is the exact-head repair used to identify the
algebraic constrained infimum with the closed constrained problem.

The hypotheses give an actual continuous linear right inverse into the
algebraic space. A finite-dimensional domain makes an algebraic right
inverse continuous, but that construction is a separate application.
No bound uniform in the number of constraints is asserted.
-/

open Filter
open scoped Topology
namespace RiemannResearch.Analysis.FiniteConstraintClosure
noncomputable section

variable {H E : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

def repair (L : H →L[ℝ] E) (R : E →L[ℝ] H) (b : E) (y : H) : H :=
  y + R (b - L y)

theorem repair_constraint (L : H →L[ℝ] E) (R : E →L[ℝ] H)
    (hR : Function.RightInverse R L) (b : E) (y : H) :
    L (repair L R b y) = b := by
  rw [repair, map_add, hR (b - L y)]
  abel

theorem repair_mem (S : Submodule ℝ H) (L : H →L[ℝ] E) (R : E →L[ℝ] H)
    (hRS : ∀ a, R a ∈ S) (b : E) (y : H) (hy : y ∈ S) :
    repair L R b y ∈ S :=
  S.add_mem hy (hRS _)

theorem repair_fixed (L : H →L[ℝ] E) (R : E →L[ℝ] H)
    (b : E) (x : H) (hx : L x = b) : repair L R b x = x := by
  simp [repair, hx]

theorem repair_tendsto (L : H →L[ℝ] E) (R : E →L[ℝ] H)
    (b : E) (x : H) (hx : L x = b) (u : ℕ → H)
    (hu : Tendsto u atTop (𝓝 x)) :
    Tendsto (fun n => repair L R b (u n)) atTop (𝓝 x) := by
  have ht := (R.continuous.tendsto (b - L x)).comp
    (tendsto_const_nhds.sub ((L.continuous.tendsto x).comp hu))
  have hr : Tendsto (fun n => R (b - L (u n))) atTop (𝓝 (0 : H)) := by
    simpa only [Function.comp_def, hx, sub_self, map_zero] using ht
  simpa only [repair, add_zero] using hu.add hr

/-- Every constrained vector in the closure has a sequence of exactly
constrained algebraic approximants. -/
theorem exists_exact_approximants (S : Submodule ℝ H)
    (L : H →L[ℝ] E) (R : E →L[ℝ] H)
    (hR : Function.RightInverse R L) (hRS : ∀ a, R a ∈ S)
    (b : E) (x : H) (hxS : x ∈ closure (S : Set H)) (hx : L x = b) :
    ∃ u : ℕ → H, (∀ n, u n ∈ S ∧ L (u n) = b) ∧ Tendsto u atTop (𝓝 x) := by
  obtain ⟨u, huS, hu⟩ := mem_closure_iff_seq_limit.mp hxS
  refine ⟨fun n => repair L R b (u n), ?_, repair_tendsto L R b x hx u hu⟩
  intro n
  exact ⟨repair_mem S L R hRS b (u n) (huS n), repair_constraint L R hR b (u n)⟩

/-- The closure commutes with the affine constraint when a continuous
right inverse takes its values in the algebraic subspace. -/
theorem closure_exact_constraints (S : Submodule ℝ H)
    (L : H →L[ℝ] E) (R : E →L[ℝ] H)
    (hR : Function.RightInverse R L) (hRS : ∀ a, R a ∈ S) (b : E) :
    closure {x : H | x ∈ S ∧ L x = b} =
      {x : H | x ∈ closure (S : Set H) ∧ L x = b} := by
  ext x
  constructor
  · intro hx
    constructor
    · exact closure_mono (fun y hy => hy.1) hx
    · have hc : IsClosed {y : H | L y = b} := isClosed_eq L.continuous continuous_const
      exact closure_minimal (fun y hy => hy.2) hc hx
  · rintro ⟨hxS, hx⟩
    obtain ⟨u, hu, hut⟩ := exists_exact_approximants S L R hR hRS b x hxS hx
    exact mem_closure_iff_seq_limit.mpr ⟨u, hu, hut⟩

/-- Quantitative exact repair. A bound on the right inverse yields a complete
norm error bound with no head or tail term discarded. -/
theorem repair_norm_error_le
    {H E : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (L : H →L[ℝ] E) (R : E →L[ℝ] H)
    (b : E) (z y : H) (hz : L z = b) :
    ‖y + R (b - L y) - z‖ ≤ (1 + ‖R‖ * ‖L‖) * ‖y - z‖ := by
  have hs : b - L y = L (z - y) := by rw [map_sub, hz]
  have hv : y + R (b - L y) - z = (y - z) + R (b - L y) := by abel
  rw [hv]
  calc
    _ ≤ ‖y - z‖ + ‖R (b - L y)‖ := norm_add_le _ _
    _ ≤ ‖y - z‖ + ‖R‖ * (‖L‖ * ‖z - y‖) := by
      apply add_le_add_right
      rw [hs]
      exact (R.le_opNorm _).trans (mul_le_mul_of_nonneg_left (L.le_opNorm _)
        (norm_nonneg R))
    _ = _ := by rw [norm_sub_rev z y]; ring


end
end RiemannResearch.Analysis.FiniteConstraintClosure
