import RiemannResearch.Analysis.DistinctGapNumeric
import RiemannResearch.Analysis.MicroscopicFirstGapVacancy

/-! Positive *adjacent* chronological gaps and the optimized packing floor on
unweighted distinct ordinates. Both assertions use the repository's unconditional
Montgomery–Taylor proportion; the positive-gap count excludes tied labels. -/
noncomputable section
open Filter Zeta23
open scoped Topology BigOperators
namespace RiemannResearch.Analysis.MontgomeryPositiveGap
open ActualZeroOrdinate ActualZeroCollisionCertificate
open MicroscopicPositiveGapProjection ZeroDPPCollisionLoss

private theorem actualSupport_eq_distinct (T : ℝ) :
    actualOrdinateSupport T = distinctOrdinates T := by
  ext y
  constructor
  · intro h
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp h
    exact copyOrdinate_mem_distinct T j
  · intro h
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp h
    let j : Copies T := ⟨⟨z,hz⟩,⟨0,multiplicity_pos hz⟩⟩
    exact Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩

/-- The distinct-height density also gives a floor for the first *positive*
chronological rank, even if an unknown fraction of the labels are tied. -/
theorem eventually_firstPositiveIndexGap_gt_montgomeryTaylor {q z : ℝ}
    (hq : 0 < q) (hz : z < ThmD.HD 1 - 1 / q) :
    ∀ᶠ T : ℝ in atTop, z < positiveIndexGapMass T q 1 := by
  obtain ⟨b, hb, hb'⟩ := exists_between (show z + 1 / q < ThmD.HD 1 by linarith)
  have hbase := eventually_microscopicNeighborBases_lower hq true 0 (z := b)
    (by simpa using hb')
  have hinv := unfoldedCutoff_inv_tendsto_zero.eventually_lt_const
    (show 0 < b - (z + 1 / q) by linarith)
  filter_upwards [hbase, hinv, eventually_gt_atTop (1 : ℝ)] with T hB hI hT
  have hpack := firstGap_distinct_packing hT hq
  rw [actualSupport_eq_distinct, sub_div] at hpack
  simp [microscopicNeighborBases] at hB
  change b < ((distinctOrdinates T).card : ℝ) / unfoldedCutoff T at hB
  change (unfoldedCutoff T)⁻¹ < b - (z + 1 / q) at hI
  change ((distinctOrdinates T).card : ℝ) / unfoldedCutoff T -
    1 / unfoldedCutoff T - 1 / q ≤ positiveIndexGapMass T q 1 at hpack
  rw [← one_div] at hI
  linarith only [hB, hI, hpack]

theorem eventually_firstPositiveIndexGap_three_halves_gt :
    ∀ᶠ T : ℝ in atTop, 7 / 1200 < positiveIndexGapMass T (3 / 2) 1 := by
  apply eventually_firstPositiveIndexGap_gt_montgomeryTaylor (by norm_num)
  norm_num
  linarith only [montgomeryTaylor_fraction_gt_269_div_400]

private theorem rankFloor_sum (q κ : ℝ) (hq : 0 < q) (n : ℕ) :
    (∑ k ∈ Finset.range n, (κ - ((k+1 : ℕ):ℝ)/q)) =
      (n:ℝ)*κ - (n:ℝ)*(n+1)/(2*q) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    push_cast
    field_simp [hq.ne']
    <;> ring

/-- Optimize the rank-sum bound at J = floor (κq). Retaining the fractional
part gives the full integer improvement over the affine envelope. -/
theorem eventually_distinctPositiveMass_gt_optimized {q z : ℝ} (hq : 0 < q)
    (hz : let κ := ThmD.HD 1
          let δ := κ*q - (⌊κ*q⌋₊ : ℝ)
          z < κ^2*q/2 - κ/2 + δ*(1-δ)/(2*q)) :
    ∀ᶠ T : ℝ in atTop, z < distinctPositiveMass T q := by
  let κ := ThmD.HD 1
  let J := ⌊κ*q⌋₊
  let δ := κ*q - (J:ℝ)
  have he : (J:ℝ)*κ - (J:ℝ)*(J+1)/(2*q) =
      κ^2*q/2 - κ/2 + δ*(1-δ)/(2*q) := by
    dsimp only [δ]
    field_simp [hq.ne']
    <;> ring
  apply eventually_distinctPositiveMass_gt_rank_sum hq J
  rw [rankFloor_sum q (ThmD.HD 1) hq J]
  exact lt_of_lt_of_eq hz he.symm

end RiemannResearch.Analysis.MontgomeryPositiveGap
