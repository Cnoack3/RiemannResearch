import RiemannResearch.RH.MobiusResidualSignOscillation
import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# One-sided norm mass of Mobius charges

Source: Priority 4 of the user-provided RH_Research_Agenda_2026-09-24,
and the present reconstruction argument. No novelty claim is made.

Norm summability of either sign part of the ACTUAL residual charges
would imply RH. The proof constructs the summable sign part and invokes
the established order bound for each remaining one-sign vector. The
summability premise is an OPEN arithmetic condition, not proved here.
-/

noncomputable section
open Filter
open scoped Topology BigOperators
namespace RiemannResearch.RH.Pareto.CoefficientStabilization

/-- Continuous coefficient observations commute with a convergent legal series. -/
theorem coefficientCLM_residue_tsum (a : ℕ → ℝ)
    (ha : Summable (fun i => a i • residueAtom i)) (j : ℕ) :
    coefficientCLM (j + 2) (∑' i, a i • residueAtom i) = a j := by
  rw [(coefficientCLM (j + 2)).map_tsum ha]
  simp [map_smul, coefficientCLM_biorthogonal, smul_eq_mul, mul_ite]

/-- A summable negative charge part gives a uniform reconstruction norm bound
for an arbitrary physical Hilbert vector. -/
theorem coordinatePartialSum_bounded_of_summable_negative_charge_mass
    (f : ThresholdHilbert)
    (hs : Summable (fun i : ℕ =>
      max (-mobiusDifferenceCLM (i + 2) f) 0 * ‖residueAtom i‖)) :
    ∃ C : ℝ, ∀ N : ℕ, ‖coordinatePartialSum f N‖ ≤ C := by
  let a : ℕ → ℝ := fun i => max (-mobiusDifferenceCLM (i + 2) f) 0
  have ha : ∀ i, 0 ≤ a i := fun i => le_max_right _ _
  have hsn : Summable (fun i => ‖a i • residueAtom i‖) := by
    simpa only [norm_smul, Real.norm_of_nonneg (ha _)] using hs
  have hsa : Summable (fun i => a i • residueAtom i) := hsn.of_norm
  let h : ThresholdHilbert := ∑' i, a i • residueAtom i
  have hcharge (m : ℕ) (hm : 1 < m) :
      mobiusDifferenceCLM m h = -max (-mobiusDifferenceCLM m f) 0 := by
    obtain ⟨j, rfl⟩ : ∃ j : ℕ, m = j + 2 := ⟨m - 2, by omega⟩
    have hc := coefficientCLM_residue_tsum a hsa j
    change -(mobiusDifferenceCLM (j + 2) h) = a j at hc
    dsimp [a] at hc
    linarith
  have hhn : ∀ m : ℕ, 1 < m → mobiusDifferenceCLM m h ≤ 0 := by
    intro m hm
    rw [hcharge m hm]
    exact neg_nonpos.mpr (le_max_right _ _)
  have hfp : ∀ m : ℕ, 1 < m → 0 ≤ mobiusDifferenceCLM m (f - h) := by
    intro m hm
    rw [map_sub, hcharge m hm]
    have hb := le_max_left (-mobiusDifferenceCLM m f) (0 : ℝ)
    linarith
  refine ⟨‖f - h‖ + ‖h‖, fun N => ?_⟩
  have he : coordinatePartialSum f N =
      coordinatePartialSum (f - h) N + coordinatePartialSum h N := by
    rw [coordinatePartialSum_sub]
    abel
  rw [he]
  exact (norm_add_le _ _).trans (add_le_add
    (coordinatePartialSum_norm_le_of_mobius_nonneg (f - h) hfp N)
    (coordinatePartialSum_norm_le_of_mobius_one_sign h (Or.inr hhn) N))

/-- The opposite sign follows by applying the previous theorem to `-f`. -/
theorem coordinatePartialSum_bounded_of_summable_positive_charge_mass
    (f : ThresholdHilbert)
    (hs : Summable (fun i : ℕ =>
      max (mobiusDifferenceCLM (i + 2) f) 0 * ‖residueAtom i‖)) :
    ∃ C : ℝ, ∀ N : ℕ, ‖coordinatePartialSum f N‖ ≤ C := by
  have hneg : Summable (fun i : ℕ =>
      max (-mobiusDifferenceCLM (i + 2) (-f)) 0 * ‖residueAtom i‖) := by
    simpa only [map_neg, neg_neg] using hs
  obtain ⟨C, hC⟩ :=
    coordinatePartialSum_bounded_of_summable_negative_charge_mass (-f) hneg
  exact ⟨C, fun N => by simpa only [coordinatePartialSum_neg, norm_neg] using hC N⟩

/-- Conditional RH reduction: either norm-summable residual charge part suffices. -/
theorem riemannHypothesis_of_summable_one_sided_charge_mass
    (hs : (Summable (fun i : ℕ =>
      max (-mobiusDifferenceCLM (i + 2) limitResidual) 0 * ‖residueAtom i‖)) ∨
      (Summable (fun i : ℕ =>
      max (mobiusDifferenceCLM (i + 2) limitResidual) 0 * ‖residueAtom i‖))) :
    RiemannHypothesis := by
  have hb : ∃ C : ℝ, ∀ N : ℕ, ‖coordinatePartialSum limitResidual N‖ ≤ C := by
    rcases hs with hn | hp
    · exact coordinatePartialSum_bounded_of_summable_negative_charge_mass limitResidual hn
    · exact coordinatePartialSum_bounded_of_summable_positive_charge_mass limitResidual hp
  obtain ⟨C, hC⟩ := hb
  apply riemannHypothesis_of_cofinally_bounded_defect_reconstruction
  exact ⟨C, fun N => ⟨N, le_rfl, hC N⟩⟩

/-- Failure of RH forces infinite norm mass in BOTH sign parts. -/
theorem not_RH_both_charge_parts_not_summable (hRH : ¬ RiemannHypothesis) :
    (¬ Summable (fun i : ℕ =>
      max (-mobiusDifferenceCLM (i + 2) limitResidual) 0 * ‖residueAtom i‖)) ∧
    (¬ Summable (fun i : ℕ =>
      max (mobiusDifferenceCLM (i + 2) limitResidual) 0 * ‖residueAtom i‖)) := by
  exact ⟨fun hn => hRH (riemannHypothesis_of_summable_one_sided_charge_mass (Or.inl hn)),
    fun hp => hRH (riemannHypothesis_of_summable_one_sided_charge_mass (Or.inr hp))⟩

/-- Failure of RH forces BOTH partial sign masses to tend to positive infinity. -/
theorem not_RH_both_charge_partial_masses_tendsto_atTop (hRH : ¬ RiemannHypothesis) :
    Tendsto (fun N : ℕ => ∑ i ∈ Finset.range N,
      max (-mobiusDifferenceCLM (i + 2) limitResidual) 0 * ‖residueAtom i‖) atTop atTop ∧
    Tendsto (fun N : ℕ => ∑ i ∈ Finset.range N,
      max (mobiusDifferenceCLM (i + 2) limitResidual) 0 * ‖residueAtom i‖) atTop atTop := by
  have h := not_RH_both_charge_parts_not_summable hRH
  exact ⟨(not_summable_iff_tendsto_nat_atTop_of_nonneg
      (fun i => mul_nonneg (le_max_right _ _) (norm_nonneg _))).mp h.1,
    (not_summable_iff_tendsto_nat_atTop_of_nonneg
      (fun i => mul_nonneg (le_max_right _ _) (norm_nonneg _))).mp h.2⟩


end RiemannResearch.RH.Pareto.CoefficientStabilization
