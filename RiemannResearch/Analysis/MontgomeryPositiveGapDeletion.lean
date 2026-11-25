import RiemannResearch.Analysis.ActualMontgomeryExceptionalPairs
import RiemannResearch.Analysis.MontgomeryMesoscopicGapCount

/-! # Removing zero occurrences from the ordinary positive-gap statistic

The microscopic Cauchy row in Lamzouri, arXiv:2611.14486, Lemma 2.3
majorizes the physical gap indicator on each bounded interval of widths.
A single row moment above one gives uniform stability under deletion.
-/

noncomputable section
open Filter Set Zeta23
open scoped BigOperators Topology Classical

namespace RiemannResearch.Analysis.MontgomeryPositiveGap
open ActualZeroOrdinate ActualMontgomeryExceptionalPairs MontgomeryExceptionalPairs

/-- The unfolded positive-gap indicator on an ordered pair of occurrences. -/
def positiveGapIndicator (T q : ℝ) (e : Copies T × Copies T) : ℝ :=
  let d := unfoldingScale T * (copyOrdinate T e.2 - copyOrdinate T e.1)
  if 0 < d ∧ d ≤ q then 1 else 0

/-- Ordinary positive gaps having both endpoints outside the deleted set.
The normalization remains the full unfolded cutoff. -/
def retainedPositiveGapMass (T q : ℝ) (E : Finset (Copies T)) : ℝ :=
  (∑ e ∈ (Finset.univ \ E) ×ˢ (Finset.univ \ E), positiveGapIndicator T q e) /
    (T * Real.log T / (2 * Real.pi))

theorem positiveGapMass_sub_retained_eq (T q : ℝ) (E : Finset (Copies T)) :
    positiveGapMass T q - retainedPositiveGapMass T q E =
    (∑ e ∈ incident Finset.univ E, positiveGapIndicator T q e) /
      (T * Real.log T / (2 * Real.pi)) := by
  have hfull : positiveGapMass T q =
      (∑ e ∈ (Finset.univ : Finset (Copies T)) ×ˢ Finset.univ, positiveGapIndicator T q e) /
      (T * Real.log T / (2 * Real.pi)) := by
    rw [Finset.sum_product] <;> rfl
  rw [hfull, retainedPositiveGapMass, ← sub_div,
    signed_deletion_identity _ _ (Finset.subset_univ E)]

private theorem positiveGapIndicator_nonneg (T q : ℝ) (e : Copies T × Copies T) :
    0 ≤ positiveGapIndicator T q e := by
  dsimp only [positiveGapIndicator]
  exact ite_nonneg zero_le_one le_rfl

/-- Each positive-gap neighbour is counted once from the exceptional
endpoint. A pair with both endpoints exceptional contributes twice. -/
def exceptionalGapDegreeMass (T q : ℝ) (E : Finset (Copies T)) : ℝ :=
  (∑ i ∈ E, ∑ j : Copies T,
    (positiveGapIndicator T q (i,j) + positiveGapIndicator T q (j,i))) /
      (T * Real.log T / (2 * Real.pi))

theorem exceptionalGapDegreeMass_eq (T q : ℝ) (E : Finset (Copies T)) :
    exceptionalGapDegreeMass T q E =
      (positiveGapMass T q - retainedPositiveGapMass T q E) +
      (∑ e ∈ E ×ˢ E, positiveGapIndicator T q e)/(T * Real.log T / (2 * Real.pi)) := by
  let U := (Finset.univ : Finset (Copies T))
  let F := positiveGapIndicator T q
  have hinter : (E ×ˢ U) ∩ (U ×ˢ E) = E ×ˢ E := by
    ext e
    simp [U, Finset.mem_product, and_comm]
  have h := Finset.sum_union_inter (s₁ := E ×ˢ U) (s₂ := U ×ˢ E) (f := F)
  have hleft : (∑ e ∈ E ×ˢ U, F e) = ∑ i ∈ E, ∑ j ∈ U, F (i,j) := by rw [Finset.sum_product]
  have hright : (∑ e ∈ U ×ˢ E, F e) = ∑ i ∈ U, ∑ j ∈ E, F (i,j) := by rw [Finset.sum_product]
  rw [hinter, hleft, hright] at h
  have hflip : (∑ i ∈ U, ∑ j ∈ E, F (i,j)) = ∑ j ∈ E, ∑ i ∈ U, F (i,j) :=
    Finset.sum_comm
  rw [hflip, ← Finset.sum_add_distrib] at h
  simp_rw [← Finset.sum_add_distrib] at h
  rw [positiveGapMass_sub_retained_eq, ← add_div]
  exact congrArg (fun x ↦ x/(T * Real.log T / (2 * Real.pi))) h.symm

/-- A two-sided bound gives the sharp zero criterion for deleting any
specified occurrence family, even one of unknown density. -/
theorem positiveGapMass_delete_degree_bounds {T : ℝ} (hT : 1 < T)
    (q : ℝ) (E : Finset (Copies T)) :
    0 ≤ positiveGapMass T q - retainedPositiveGapMass T q E ∧
    positiveGapMass T q - retainedPositiveGapMass T q E ≤ exceptionalGapDegreeMass T q E ∧
    exceptionalGapDegreeMass T q E ≤ 2 * (positiveGapMass T q - retainedPositiveGapMass T q E) := by
  let D := T * Real.log T / (2 * Real.pi)
  have hd : 0 < D := div_pos (mul_pos (zero_lt_one.trans hT) (Real.log_pos hT)) (by positivity)
  have hsub : E ×ˢ E ⊆ incident Finset.univ E := by
    intro e he
    exact Finset.mem_union.mpr (.inl (Finset.mem_product.mpr
      ⟨(Finset.mem_product.mp he).1, Finset.mem_univ _⟩))
  have hinner : 0 ≤ (∑ e ∈ E ×ˢ E, positiveGapIndicator T q e)/D :=
    div_nonneg (Finset.sum_nonneg (fun e _ => positiveGapIndicator_nonneg T q e)) hd.le
  have hle := div_le_div_of_nonneg_right (Finset.sum_le_sum_of_subset_of_nonneg hsub
    (fun e _ _ => positiveGapIndicator_nonneg T q e)) hd.le
  rw [exceptionalGapDegreeMass_eq, positiveGapMass_sub_retained_eq]
  change 0 ≤ _ / D ∧ _ ≤ _ ∧ _ ≤ _
  exact ⟨hinner.trans hle, le_add_of_nonneg_right hinner, by dsimp only [D] at hle; linarith only [hle]⟩

theorem positiveGapMass_delete_tendsto_iff_exceptionalDegree
    (E : (T : ℝ) → Finset (Copies T)) (q : ℝ → ℝ) :
    Tendsto (fun T : ℝ => positiveGapMass T (q T) - retainedPositiveGapMass T (q T) (E T))
      atTop (𝓝 0) ↔ Tendsto (fun T : ℝ => exceptionalGapDegreeMass T (q T) (E T))
        atTop (𝓝 0) := by
  have h := (eventually_gt_atTop (1:ℝ)).mono fun T hT =>
    positiveGapMass_delete_degree_bounds hT (q T) (E T)
  constructor
  · intro hlim
    exact squeeze_zero' (h.mono fun T ht => ht.1.trans ht.2.1)
      (h.mono fun T ht => ht.2.2) (by simpa only [mul_zero] using hlim.const_mul 2)
  · intro hlim
    exact squeeze_zero' (h.mono fun T ht => ht.1) (h.mono fun T ht => ht.2.1) hlim

private theorem positiveGapIndicator_le_weight {T q Q : ℝ} (hq : q ≤ Q)
    (e : Copies T × Copies T) :
    positiveGapIndicator T q e ≤ (1 + (2 * Real.pi * Q)^2) * gapWeight T e.1 e.2 := by
  let d := unfoldingScale T * (copyOrdinate T e.2 - copyOrdinate T e.1)
  change (if 0 < d ∧ d ≤ q then (1 : ℝ) else 0) ≤ _
  split_ifs with hd
  · have he : (e.1.1.1.im - e.2.1.1.im) * Real.log T = -(2 * Real.pi * d) := by
      dsimp [d, unfoldingScale, copyOrdinate]
      field_simp [Real.pi_ne_zero] <;> ring
    have hm := mul_le_mul_of_nonneg_left (hd.2.trans hq) (by positivity : 0 ≤ 2 * Real.pi)
    have hsq := pow_le_pow_left₀ (mul_nonneg (by positivity) hd.1.le) hm 2
    rw [gapWeight, he, neg_sq, ← mul_div_assoc, mul_one]
    exact (le_div_iff₀ (by positivity)).mpr (by simpa using add_le_add_left hsq 1)
  · exact mul_nonneg (by positivity) (gapWeight_nonneg T _ _)

/-- At each height the missing positive-gap mass is controlled by the
exceptional density raised to the Hölder exponent of a single ordinate
row moment. The same right side works for all widths below Q. -/
theorem positiveGapMass_delete_bound {T q Q p C : ℝ} (hT : 1 < T)
    (hN : 0 < (Ncount 0 T : ℝ)) (hq : q ≤ Q) (hp : 1 ≤ p)
    (hrow : (∑ i : Copies T, (Ncount 0 T : ℝ)⁻¹ *
      rowMass Finset.univ (gapWeight T) i ^ p) ≤ C) (E : Finset (Copies T)) :
    |positiveGapMass T q - retainedPositiveGapMass T q E| ≤
      ((Ncount 0 T : ℝ) / (T * Real.log T / (2 * Real.pi))) *
      ((1 + (2 * Real.pi * Q)^2) *
      (2 * ((E.card : ℝ) / (Ncount 0 T : ℝ)) ^ (1 - p⁻¹) * C ^ p⁻¹)) := by
  let n : ℝ := Ncount 0 T
  let D := T * Real.log T / (2 * Real.pi)
  let K := 1 + (2 * Real.pi * Q)^2
  let s := incident (Finset.univ : Finset (Copies T)) E
  have hn : 0 < n := hN
  have hD : 0 < D := div_pos (mul_pos (zero_lt_one.trans hT) (Real.log_pos hT)) (by positivity)
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hδ : (∑ _i ∈ E, n⁻¹) ≤ (E.card : ℝ)/n := by simp [div_eq_mul_inv]
  have hm := incident_mass_le Finset.univ E (Finset.subset_univ E) (gapWeight T)
    (gapWeight_nonneg T) (gapWeight_symm T) (inv_nonneg.mpr hn.le) hp hδ hrow
  have h1 : (∑ e ∈ s, n⁻¹ * positiveGapIndicator T q e) ≤ K *
      (∑ e ∈ s, n⁻¹ * gapWeight T e.1 e.2) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro e _
    exact (mul_le_mul_of_nonneg_left (positiveGapIndicator_le_weight hq e)
      (inv_nonneg.mpr hn.le)).trans_eq (by dsimp [K]; ring)
  rw [positiveGapMass_sub_retained_eq, abs_of_nonneg (div_nonneg
    (Finset.sum_nonneg fun e _ => positiveGapIndicator_nonneg T q e) hD.le)]
  change (∑ e ∈ s, positiveGapIndicator T q e) / D ≤ _
  calc
    _ = (n/D) * (∑ e ∈ s, n⁻¹ * positiveGapIndicator T q e) := by
      rw [← Finset.mul_sum]
      field_simp [hn.ne', hD.ne'] <;> ring
    _ ≤ _ := mul_le_mul_of_nonneg_left (h1.trans (mul_le_mul_of_nonneg_left hm hK))
      (div_nonneg hn.le hD.le)

/-- A single finite-order row moment above one suffices to remove any
density-zero family. The tolerance is simultaneous over all q ≤ Q. -/
theorem eventually_compact_positiveGapMass_delete_small
    (E : (T : ℝ) → Finset (Copies T)) {p C : ℝ} (hp : 1 < p)
    (hrow : ∀ᶠ T : ℝ in atTop, (∑ i : Copies T, (Ncount 0 T : ℝ)⁻¹ *
      rowMass Finset.univ (gapWeight T) i ^ p) ≤ C)
    (hδ : Tendsto (fun T : ℝ => ((E T).card : ℝ)/(Ncount 0 T : ℝ)) atTop (𝓝 0))
    (Q : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ T : ℝ in atTop, ∀ q : ℝ, q ≤ Q →
      |positiveGapMass T q - retainedPositiveGapMass T q (E T)| < ε := by
  have hr : 0 < 1-p⁻¹ := sub_pos.mpr (inv_lt_one_of_one_lt₀ hp)
  have hh := hδ.rpow_const (Or.inr hr.le)
  rw [Real.zero_rpow hr.ne'] at hh
  have htop := tendsto_count_div_mainTerm.mul
    (((hh.const_mul 2).mul_const (C ^ p⁻¹)).const_mul (1 + (2 * Real.pi * Q)^2))
  simp only [mul_zero, zero_mul] at htop
  filter_upwards [eventually_gt_atTop (1 : ℝ), hrow,
    tendsto_count_div_mainTerm.eventually (lt_mem_nhds (by norm_num : (0:ℝ) < 1)),
    htop.eventually (gt_mem_nhds hε)] with T hT hm hn hupper
  have hD : 0 < T * Real.log T / (2 * Real.pi) :=
    div_pos (mul_pos (zero_lt_one.trans hT) (Real.log_pos hT)) (by positivity)
  have hn' : 0 < (Ncount 0 T : ℝ) := by
    have hh' : 0 < (Ncount 0 T : ℝ) / (T * Real.log T / (2 * Real.pi)) := hn
    simpa using (lt_div_iff₀ hD).mp hh'
  intro q hq
  exact (positiveGapMass_delete_bound hT hn' hq hp.le hm (E T)).trans_lt hupper

/-- The published Fujii row-moment hypothesis supplies the needed second
row moment and gives uniform density-zero deletion for physical gap tests. -/
theorem compact_positiveGapMass_delete_of_fujii (hRows : FujiiMicroscopicRowMoments)
    (E : (T : ℝ) → Finset (Copies T))
    (hδ : Tendsto (fun T : ℝ => ((E T).card : ℝ)/(Ncount 0 T : ℝ)) atTop (𝓝 0))
    (Q : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ T : ℝ in atTop, ∀ q : ℝ, q ≤ Q →
      |positiveGapMass T q - retainedPositiveGapMass T q (E T)| < ε := by
  obtain ⟨C, _, hC⟩ := eventually_real_row_moment hRows 2 (by norm_num)
  exact eventually_compact_positiveGapMass_delete_small E (p := 2) (by norm_num) hC hδ Q hε

/-- Ordinary positive-gap PCC is equivalent to its restriction to the
surviving occurrences, keeping the original normalization. -/
theorem positiveGapPCC_iff_retained_of_density_zero
    (E : (T : ℝ) → Finset (Copies T)) {p C : ℝ} (hp : 1 < p)
    (hrow : ∀ᶠ T : ℝ in atTop, (∑ i : Copies T, (Ncount 0 T : ℝ)⁻¹ *
      rowMass Finset.univ (gapWeight T) i ^ p) ≤ C)
    (hδ : Tendsto (fun T : ℝ => ((E T).card : ℝ)/(Ncount 0 T : ℝ)) atTop (𝓝 0)) :
    PositiveGapPCC ↔ ∀ a b : ℝ, 0 < a → a ≤ b → ∀ ε : ℝ, 0 < ε →
      ∀ᶠ T : ℝ in atTop, ∀ q ∈ Icc a b,
        |retainedPositiveGapMass T q (E T) - sineGapMass q| ≤ ε := by
  constructor <;> intro h a b ha hab ε hε
  · filter_upwards [h a b ha hab (ε/2) (by positivity),
      eventually_compact_positiveGapMass_delete_small E hp hrow hδ b (half_pos hε)]
      with T hT hE
    intro q hq
    have h₁ := abs_le.mp (hT q hq)
    have h₂ := abs_le.mp (hE q hq.2).le
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  · filter_upwards [h a b ha hab (ε/2) (by positivity),
      eventually_compact_positiveGapMass_delete_small E hp hrow hδ b (half_pos hε)]
      with T hT hE
    intro q hq
    have h₁ := abs_le.mp (hT q hq)
    have h₂ := abs_le.mp (hE q hq.2).le
    exact abs_le.mpr ⟨by linarith, by linarith⟩

/--
info: 'RiemannResearch.Analysis.MontgomeryPositiveGap.positiveGapPCC_iff_retained_of_density_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms positiveGapPCC_iff_retained_of_density_zero

end RiemannResearch.Analysis.MontgomeryPositiveGap
