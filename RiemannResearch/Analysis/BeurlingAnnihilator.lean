import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Tactic.Linarith

/-!
# Continuous-functional obstruction for a Beurling approximation space

These are general functional-analysis consumers. They do not instantiate a
Mellin functional, prove its boundedness, or import a zeta-zero hypothesis.
Such an actual analytic adapter must separately supply the continuous linear
functional and its values on the corrected Pareto atoms and the target.
-/

noncomputable section

open Filter
open scoped Topology

namespace RiemannResearch.Analysis.BeurlingAnnihilator

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]

/-- An annihilated approximant retains the target's full functional value. -/
theorem functional_error_identity (L : H →L[ℂ] ℂ) (f g : H)
    (hg : L g = 0) : L (f - g) = L f := by
  rw [map_sub, hg, sub_zero]

/-- Quantitative obstruction from an actual bounded functional. -/
theorem functional_value_le_error (L : H →L[ℂ] ℂ) (f g : H)
    (hg : L g = 0) : ‖L f‖ ≤ ‖L‖ * ‖f - g‖ := by
  calc
    ‖L f‖ = ‖L (f - g)‖ := by rw [functional_error_identity L f g hg]
    _ ≤ ‖L‖ * ‖f - g‖ := L.le_opNorm (f - g)

/-- A nonzero target value forces strictly positive operator norm. -/
theorem functional_norm_pos (L : H →L[ℂ] ℂ) (f : H) (hf : L f ≠ 0) :
    0 < ‖L‖ := by
  have hvalue := L.le_opNorm f
  have htarget : 0 < ‖L f‖ := norm_pos_iff.mpr hf
  by_contra hn
  have hL : ‖L‖ ≤ 0 := le_of_not_gt hn
  have hmul : ‖L‖ * ‖f‖ ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg hL (norm_nonneg f)
  linarith

/-- Positive uniform distance from every annihilated approximant. -/
theorem functional_positive_error_bound (L : H →L[ℂ] ℂ) (f g : H)
    (hf : L f ≠ 0) (hg : L g = 0) :
    0 < ‖L f‖ / ‖L‖ ∧ ‖L f‖ / ‖L‖ ≤ ‖f - g‖ := by
  have hL := functional_norm_pos L f hf
  constructor
  · exact div_pos (norm_pos_iff.mpr hf) hL
  · apply (div_le_iff₀ hL).mpr
    simpa [mul_comm] using functional_value_le_error L f g hg

/-- Continuity carries annihilation through a convergent legal sequence. -/
theorem functional_zero_of_annihilated_tendsto
    (L : H →L[ℂ] ℂ) (u : ℕ → H) (f : H)
    (hu : ∀ n, L (u n) = 0) (hlim : Tendsto u atTop (𝓝 f)) : L f = 0 := by
  have hvalue : Tendsto (fun n => L (u n)) atTop (𝓝 (L f)) :=
    (L.continuous.tendsto f).comp hlim
  have hzero : Tendsto (fun n => L (u n)) atTop (𝓝 (0 : ℂ)) := by
    have heq : (fun n => L (u n)) = (fun _ : ℕ => (0 : ℂ)) := funext hu
    rw [heq]
    exact tendsto_const_nhds
  exact tendsto_nhds_unique hvalue hzero

/-- A functional that separates the target forbids legal norm convergence. -/
theorem not_tendsto_of_annihilated
    (L : H →L[ℂ] ℂ) (u : ℕ → H) (f : H)
    (hu : ∀ n, L (u n) = 0) (hf : L f ≠ 0) :
    ¬ Tendsto u atTop (𝓝 f) := by
  intro hlim
  exact hf (functional_zero_of_annihilated_tendsto L u f hu hlim)

/-- The kernel of a continuous functional contains the closure of every
annihilated set. -/
theorem functional_zero_on_closure (L : H →L[ℂ] ℂ) (s : Set H)
    (hs : ∀ x ∈ s, L x = 0) (f : H) (hf : f ∈ closure s) : L f = 0 := by
  have hclosed : IsClosed {x : H | L x = 0} :=
    isClosed_eq L.continuous continuous_const
  have hsub : s ⊆ {x : H | L x = 0} := by
    intro x hx
    exact hs x hx
  exact (closure_minimal hsub hclosed) hf

/-- Linear combinations preserve the complete signed annihilation identity. -/
theorem functional_zero_on_span (L : H →L[ℂ] ℂ) (s : Set H)
    (hs : ∀ x ∈ s, L x = 0) (f : H) (hf : f ∈ Submodule.span ℂ s) : L f = 0 := by
  have hsub : Submodule.span ℂ s ≤ LinearMap.ker L.toLinearMap := by
    apply Submodule.span_le.mpr
    intro x hx
    change L x = 0
    exact hs x hx
  have hker := hsub hf
  change L f = 0 at hker
  exact hker

/-- Closed-span obstruction for an actual separating Beurling functional. -/
theorem target_not_mem_closure_span (L : H →L[ℂ] ℂ) (s : Set H) (f : H)
    (hs : ∀ x ∈ s, L x = 0) (hf : L f ≠ 0) :
    f ∉ closure (Submodule.span ℂ s : Set H) := by
  intro hmem
  apply hf
  apply functional_zero_on_closure L (Submodule.span ℂ s : Set H)
    (fun x hx => functional_zero_on_span L s hs x hx) f hmem

end RiemannResearch.Analysis.BeurlingAnnihilator
