import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Tactic.Abel

/-!
# Absolute summability and finite truncation of a complex zero series

Source: user-provided manuscript `Prime_Phases_Agenda_Proof_Attempts.tex`,
section "A linear terminal-shell criterion, with horizontal information retained".

These generic norm-majorant lemmas justify a complex series and its truncation
AFTER a summable majorant is supplied. They do not assert an actual Riemann-zeta
zero strip, zero counting bound, enumeration, multiplicity bound, or Perron
explicit formula. In particular, a verified utility theorem here does not
verify the manuscript's integrated zero formula.
-/

noncomputable section
open scoped BigOperators

namespace RiemannResearch.Analysis.IntegratedZeroSeriesBounds

/-- A norm majorant gives absolute convergence, not only formal summability. -/
theorem absolutely_summable_of_majorant {ι : Type*}
    (term : ι → ℂ) (majorant : ι → ℝ) (hmajorant : Summable majorant)
    (hbound : ∀ i, ‖term i‖ ≤ majorant i) :
    Summable (fun i => ‖term i‖) ∧ Summable term := by
  have habs : Summable (fun i => ‖term i‖) :=
    Summable.of_nonneg_of_le (fun i => norm_nonneg (term i)) hbound hmajorant
  exact ⟨habs, habs.of_norm⟩

/-- Exact subtraction of a finite enumeration head leaves the infinite tail. -/
theorem finite_head_remainder_eq_tail (term : ℕ → ℂ) (hterm : Summable term)
    (K : ℕ) :
    (∑' i, term i) - (∑ i ∈ Finset.range K, term i) =
      ∑' i, term (i + K) := by
  have hsplit := hterm.sum_add_tsum_nat_add K
  rw [← hsplit]
  abel

/-- The norm of the omitted enumeration tail is bounded by its majorant tail. -/
theorem tail_norm_le_majorant_tail (term : ℕ → ℂ) (majorant : ℕ → ℝ)
    (hmajorant : Summable majorant) (hbound : ∀ i, ‖term i‖ ≤ majorant i)
    (K : ℕ) :
    ‖∑' i, term (i + K)‖ ≤ ∑' i, majorant (i + K) := by
  have hm : Summable (fun i => majorant (i + K)) :=
    (summable_nat_add_iff K).2 hmajorant
  exact tsum_of_norm_bounded hm.hasSum (fun i => hbound (i + K))

/-- A finite-cutoff error bound with every analytic input visible in its type. -/
theorem finite_truncation_error_le (term : ℕ → ℂ) (majorant : ℕ → ℝ)
    (hmajorant : Summable majorant) (hbound : ∀ i, ‖term i‖ ≤ majorant i)
    (K : ℕ) (R : ℝ) (htail : (∑' i, majorant (i + K)) ≤ R) :
    ‖(∑' i, term i) - (∑ i ∈ Finset.range K, term i)‖ ≤ R := by
  have hterm := (absolutely_summable_of_majorant term majorant hmajorant hbound).2
  rw [finite_head_remainder_eq_tail term hterm K]
  exact (tail_norm_le_majorant_tail term majorant hmajorant hbound K).trans htail

end RiemannResearch.Analysis.IntegratedZeroSeriesBounds
