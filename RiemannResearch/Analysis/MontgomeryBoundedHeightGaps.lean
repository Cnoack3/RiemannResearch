import RiemannResearch.Analysis.MontgomeryPositiveGapDeletion
import RiemannResearch.Analysis.ActualZeroOrdinate
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Order.Filter.Finite
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Bounded-height occurrences in microscopic positive-gap counts

Source: the finite-exception observation in the supplied Mellin / prime-orbit
handoff, §7. At fixed bounded unfolded widths the contribution from a fixed
bounded height range is eventually exactly zero. Ties are excluded before
deleting occurrences. The denominator is the original height normalization.
-/

noncomputable section
open Filter
open scoped BigOperators Topology

namespace RiemannResearch.Analysis.MontgomeryPositiveGap

open ActualZeroOrdinate

/-- All strict right gaps originating at height at most `H` eventually exceed
any fixed unfolded width `Q`. The assertion is uniform over both labels. -/
theorem eventually_unfolded_gap_gt_of_bounded_anchor (H Q : ℝ) :
    ∀ᶠ T : ℝ in atTop, ∀ i j : Copies T,
      copyOrdinate T i ≤ H → copyOrdinate T i < copyOrdinate T j →
      Q < Real.log T / (2 * Real.pi) * (copyOrdinate T j - copyOrdinate T i) := by
  classical
  have grow (d : ℝ) (hd : 0 < d) :
      ∀ᶠ T : ℝ in atTop, Q < Real.log T / (2 * Real.pi) * d := by
    filter_upwards [Real.tendsto_log_atTop.eventually
      (eventually_gt_atTop (Q / d * (2 * Real.pi)))] with T hT
    exact (div_lt_iff₀ hd).mp ((lt_div_iff₀ (by positivity : 0 < 2 * Real.pi)).mpr hT)
  let Z := {ρ : ℂ // ρ ∈ cutoff (H + 1)}
  let : Fintype Z := inferInstanceAs (Fintype ↥(cutoff (H + 1)))
  have pair (a b : Z) : ∀ᶠ T : ℝ in atTop, a.val.im < b.val.im →
      Q < Real.log T / (2 * Real.pi) * (b.val.im - a.val.im) := by
    by_cases h : a.val.im < b.val.im
    · exact (grow _ (sub_pos.mpr h)).mono (fun _ ht _ => ht)
    · exact Eventually.of_forall (fun _ ht => (h ht).elim)
  have near : ∀ᶠ T : ℝ in atTop, ∀ a b : Z, a.val.im < b.val.im →
      Q < Real.log T / (2 * Real.pi) * (b.val.im - a.val.im) :=
    eventually_all.mpr (fun a => eventually_all.mpr (pair a))
  filter_upwards [near, grow 1 zero_lt_one, eventually_gt_atTop (1 : ℝ)] with T hn hf hT
  intro i j hi hij
  have ha := mem_cutoff_iff_zeta.mp i.1.2
  have hb := mem_cutoff_iff_zeta.mp j.1.2
  change i.1.1.im ≤ H at hi
  change i.1.1.im < j.1.1.im at hij
  change Q < Real.log T / (2 * Real.pi) * (j.1.1.im - i.1.1.im)
  by_cases hj : j.1.1.im ≤ H + 1
  · exact hn ⟨i.1.1, mem_cutoff_iff_zeta.mpr ⟨ha.1, ha.2.1, by linarith⟩⟩
      ⟨j.1.1, mem_cutoff_iff_zeta.mpr ⟨hb.1, hb.2.1, hj⟩⟩ hij
  · exact hf.trans_le (mul_le_mul_of_nonneg_left (by linarith)
      (div_nonneg (Real.log_pos hT).le (by positivity)))

/-- Deleting any collection of low-height occurrences leaves the exact
repository statistic unchanged, simultaneously at all widths at most `Q`. -/
theorem eventually_positiveGapMass_eq_retained_of_bounded_height (H Q : ℝ) :
    ∀ᶠ T : ℝ in atTop, ∀ q ≤ Q, ∀ E : Finset (Copies T),
      (∀ i ∈ E, copyOrdinate T i ≤ H) →
      positiveGapMass T q = retainedPositiveGapMass T q E := by
  classical
  filter_upwards [eventually_unfolded_gap_gt_of_bounded_anchor H Q,
    eventually_gt_atTop (1 : ℝ)] with T hg hT
  intro q hq E hE
  let S := Finset.univ \ E
  have hS (i : Copies T) (hi : H < copyOrdinate T i) : i ∈ S :=
    Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, fun h => (not_le.mpr hi) (hE i h)⟩
  let a := Real.log T / (2 * Real.pi)
  have ha : 0 < a := div_pos (Real.log_pos hT) (by positivity)
  let f (i j : Copies T) : ℝ :=
    if 0 < a * (copyOrdinate T j - copyOrdinate T i) ∧
        a * (copyOrdinate T j - copyOrdinate T i) ≤ q then 1 else 0
  have supported (i j : Copies T) (h : i ∉ S ∨ j ∉ S) : f i j = 0 := by
    apply if_neg
    intro ht
    have hij : copyOrdinate T i < copyOrdinate T j := sub_pos.mp
      (pos_of_mul_pos_right ht.1 ha.le)
    have hi : copyOrdinate T i ≤ H := by
      by_contra! hi
      exact h.elim (fun hn => hn (hS i hi)) (fun hn => hn (hS j (hi.trans hij)))
    exact (not_lt_of_ge (ht.2.trans hq)) (hg i j hi hij)
  rw [retainedPositiveGapMass, Finset.sum_product]
  change (∑ i, ∑ j, f i j) / _ = (∑ i ∈ S, ∑ j ∈ S, f i j) / _
  congr 1
  calc
    (∑ i, ∑ j, f i j) = ∑ i ∈ S, ∑ j, f i j := by
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro i _ hi
      exact Finset.sum_eq_zero (fun j _ => supported i j (Or.inl hi))
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      symm
      exact Finset.sum_subset (Finset.subset_univ _)
        (fun j _ hj => supported i j (Or.inr hj))

end RiemannResearch.Analysis.MontgomeryPositiveGap
