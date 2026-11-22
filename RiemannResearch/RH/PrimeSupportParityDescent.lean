import RiemannResearch.RH.PrimeSupportParityQuotient
import RiemannResearch.RH.MixedParityCaptureFifteen
import RiemannResearch.RH.MixedConductorCaptureGains

/-!
# The parity class at the tip of the prime-support quotient diagram

Compatible maps to a Hausdorff target descend uniquely to the quotient by the mixed closure.
For the centered conductor-two packet the norm at that vertex is the norm of the centered
snake boundary. Conductors 6, 10, 12, 14 and 15 witness a fractional decrease from stage one
to stage two. Extending that decrease to blocks with arbitrarily late starts would imply RH.
The quotient argument uses the cocone universal property (E. Riehl,
*Category Theory in Context*, §3.1) and closedness of kernels in Hausdorff targets.
-/

noncomputable section

open Filter
open scoped Topology BigOperators

namespace RiemannResearch.RH.Pareto.PrimePowerSchur.MixedConductorBasis

open CoefficientStabilization

/-- The universal property of the support cocone against Hausdorff targets,
written on quotient representatives. Compatibility with stage zero suffices. -/
theorem supportQuotient_hausdorff_desc {Y : Type*} [AddCommGroup Y] [Module ℝ Y]
    [TopologicalSpace Y] [T2Space Y]
    (t : ∀ n : ℕ, (ThresholdHilbert ⧸ ambientSupport n) →L[ℝ] Y)
    (ht : ∀ n (x : ThresholdHilbert), t n ((ambientSupport n).mkQ x) =
      t 0 ((ambientSupport 0).mkQ x)) :
    ∃! f : (ThresholdHilbert ⧸ mixedClosure) →L[ℝ] Y,
      ∀ n (x : ThresholdHilbert), f (mixedClosure.mkQ x) = t n ((ambientSupport n).mkQ x) := by
  let T := (t 0).comp (ambientSupport 0).mkQL
  let R := T.comp mixedClosure.subtypeL
  have hi : (⨆ n, supportSpace n) ≤ R.ker := by
    refine iSup_le fun n m hm => ?_
    change t 0 ((ambientSupport 0).mkQ (m : ThresholdHilbert)) = 0
    have hz : (ambientSupport n).mkQ (m : ThresholdHilbert) = 0 :=
      (Submodule.Quotient.mk_eq_zero _).mpr ⟨m, hm, rfl⟩
    rw [← ht n, hz, map_zero]
  have hc := Submodule.topologicalClosure_minimal _ hi R.isClosed_ker
  rw [supportSpace_dense] at hc
  have hM : mixedClosure ≤ T.ker := by
    intro x hx
    exact hc (show (⟨x, hx⟩ : mixedClosure) ∈ ⊤ from trivial)
  refine ⟨mixedClosure.liftQL T hM, ?_, ?_⟩
  · intro n x
    exact (ht n x).symm
  · intro f hf
    apply ContinuousLinearMap.ext
    intro q
    obtain ⟨x, rfl⟩ := mixedClosure.mkQ_surjective q
    exact hf 0 x

/-- Every leg carries the parity class to the class of the screened defect. -/
theorem supportCocone_parity_eq_defect (n : ℕ) :
    (supportQuotientCocone.ι.app n) (parityQuotientClass n) =
      mixedClosure.mkQ (normalizedScreenedTwo - hilbertOne) := by
  let g := (Real.log 2)⁻¹ • ramanujanPacketHilbert 2
  change mixedClosure.mkQ (g - hilbertOne) = _
  have hu := CenteredMeanSnake.normalizedScreenedTwo_eq_projected_packet
  rw [Submodule.starProjection_orthogonal_val, smul_sub] at hu
  have hg : g - hilbertOne = (normalizedScreenedTwo - hilbertOne) +
      mixedClosure.starProjection g := by
    dsimp only [g]
    rw [map_smul, hu]
    abel
  rw [hg, map_add, show mixedClosure.mkQ (mixedClosure.starProjection g) = 0 from
    (Submodule.Quotient.mk_eq_zero _).mpr (mixedClosure.starProjection_apply_mem g), add_zero]

/-- The parity class at the cocone vertex has exactly the centered boundary norm at every stage. -/
theorem norm_supportCocone_parity (n : ℕ) :
    (fun q : ThresholdHilbert ⧸ mixedClosure => ‖q‖)
      ((supportQuotientCocone.ι.app n) (parityQuotientClass n)) = ‖CenteredMeanSnake.boundary‖ := by
  rw [supportCocone_parity_eq_defect, CenteredMeanSnake.boundary_norm]
  let d := normalizedScreenedTwo - hilbertOne
  calc
    _ = Metric.infDist d (mixedClosure : Set ThresholdHilbert) :=
      QuotientAddGroup.norm_mk (S := mixedClosure.toAddSubgroup) d
    _ = ‖d - mixedClosure.starProjection d‖ := mixedClosure.infDist_eq_norm_sub_starProjection d
    _ = _ := by
      rw [(mixedClosure.starProjection_apply_eq_zero_iff).mpr
        CenteredMeanSnake.screenedTwo_sub_one_mem_orthogonals.2, sub_zero]

/-- Cutoff error plus the captured layer energy is the full centered parity variance. -/
theorem parityQuotient_sq_add_captured (n : ℕ) :
    ‖parityQuotientClass n‖ ^ 2 +
      (∑ k ∈ Finset.range n, ‖(supportLayer k).starProjection parityMixedProjection‖ ^ 2) =
      (Real.log 2)⁻¹ - 1 := by
  have h := parity_support_deficit n
  rw [parityQuotientClass_norm_sq, CenteredMeanSnake.boundary_norm]
  linarith only [h]

/-- Vanishing is equivalent to a fixed fractional improvement at arbitrarily late cutoffs.
The end of each block may be chosen separately. -/
theorem boundary_eq_zero_iff_frequent_support_contraction {c : ℝ} (hc₀ : 0 < c) (hc : c < 1) :
    CenteredMeanSnake.boundary = 0 ↔ ∃ᶠ n in atTop, ∃ m : ℕ, n ≤ m ∧
      ‖parityQuotientClass m‖ ^ 2 ≤ c * ‖parityQuotientClass n‖ ^ 2 := by
  constructor
  · intro hb
    have ht := tendsto_parityQuotientClass_norm_sq
    rw [hb, norm_zero, zero_pow (by decide : 2 ≠ 0)] at ht
    apply Filter.Eventually.frequently
    apply Filter.Eventually.of_forall
    intro n
    by_cases hz : ‖parityQuotientClass n‖ ^ 2 = 0
    · exact ⟨n, le_rfl, by rw [hz, mul_zero]⟩
    · have hp := lt_of_le_of_ne (sq_nonneg ‖parityQuotientClass n‖) (Ne.symm hz)
      obtain ⟨m, hnm, hm⟩ := ((eventually_ge_atTop n).and
        ((tendsto_order.mp ht).2 _ (mul_pos hc₀ hp))).exists
      exact ⟨m, hnm, hm.le⟩
  · intro h
    have hfloor (m : ℕ) : ‖CenteredMeanSnake.boundary‖ ^ 2 ≤ ‖parityQuotientClass m‖ ^ 2 := by
      rw [parityQuotientClass_norm_sq]
      exact le_add_of_nonneg_right (sq_nonneg _)
    have hfreq : ∃ᶠ n in atTop, ‖CenteredMeanSnake.boundary‖ ^ 2 ≤
        c * ‖parityQuotientClass n‖ ^ 2 := h.mono fun n ⟨m, _, hm⟩ => (hfloor m).trans hm
    by_contra hb
    have hp := sq_pos_of_pos (norm_pos_iff.mpr hb)
    have hlt : c * ‖CenteredMeanSnake.boundary‖ ^ 2 < ‖CenteredMeanSnake.boundary‖ ^ 2 := by
      simpa only [one_mul] using mul_lt_mul_of_pos_right hc hp
    have he := (tendsto_order.mp ((tendsto_const_nhds (x := c)).mul
      tendsto_parityQuotientClass_norm_sq)).2 _ hlt
    obtain ⟨n, hn, hn'⟩ := (hfreq.and_eventually he).exists
    exact (not_lt_of_ge hn) hn'

/-- A single fixed factor below one suffices if its successful blocks start arbitrarily late. -/
theorem riemannHypothesis_of_frequently_contracting_support_blocks {c : ℝ} (hc₀ : 0 < c)
    (hc : c < 1) (h : ∃ᶠ n in atTop, ∃ m : ℕ, n ≤ m ∧ ‖parityQuotientClass m‖ ^ 2 ≤
      c * ‖parityQuotientClass n‖ ^ 2) : RiemannHypothesis :=
  CenteredMeanSnake.riemannHypothesis_of_boundary_eq_zero
    ((boundary_eq_zero_iff_frequent_support_contraction hc₀ hc).mpr h)

/-- Every finite conductor window fits in the stage determined by its prime-factor counts. -/
theorem mixedWindow_le_ambientSupport {B n : ℕ}
    (hω : ∀ q ∈ mixedConductors (Finset.Icc 2 B), q.primeFactors.card ≤ n) :
    mixedSpace (Finset.Icc 2 B) ≤ ambientSupport n := by
  apply Submodule.span_le.mpr
  rintro _ ⟨q, rfl⟩
  have hq : q.val ∈ Finset.Icc 2 B ∧ ¬ IsPrimePow q.val := Finset.mem_filter.mp q.property
  let i : Index := ⟨q.val, (Finset.mem_Icc.mp hq.1).1, hq.2⟩
  have hi : packet i ∈ supportSpace n :=
    Submodule.le_topologicalClosure _ (Submodule.subset_span ⟨i, hω q.val q.property, rfl⟩)
  exact ⟨packet i, hi, rfl⟩

/-- A conductor-window fit gives an upper bound for the corresponding ambient quotient error. -/
theorem parityQuotient_le_window_deficit {B n : ℕ}
    (hω : ∀ q ∈ mixedConductors (Finset.Icc 2 B), q.primeFactors.card ≤ n) :
    (Real.log 2) ^ 2 * ‖parityQuotientClass n‖ ^ 2 ≤ CaptureGains.deficit B := by
  let K := mixedSpace (Finset.Icc 2 B)
  let x := (Real.log 2)⁻¹ • ramanujanPacketHilbert 2 - hilbertOne
  have hL : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hz : CaptureGains.centeredParity = Real.log 2 • x := by
    dsimp only [CaptureGains.centeredParity, x]
    rw [smul_sub, smul_smul, mul_inv_cancel₀ hL.ne', one_smul]
  have hq : ‖(ambientSupport n).mkQ CaptureGains.centeredParity‖ =
      Real.log 2 * ‖parityQuotientClass n‖ := by
    change ‖(ambientSupport n).mkQ CaptureGains.centeredParity‖ =
      Real.log 2 * ‖(ambientSupport n).mkQ x‖
    rw [hz, map_smul, norm_smul, Real.norm_eq_abs, abs_of_pos hL]
  have hp := mixedWindow_le_ambientSupport hω
    (K.starProjection_apply_mem CaptureGains.centeredParity)
  have hd : ‖(ambientSupport n).mkQ CaptureGains.centeredParity‖ ≤
      ‖CaptureGains.centeredParity - K.starProjection CaptureGains.centeredParity‖ := calc
    _ = Metric.infDist CaptureGains.centeredParity (ambientSupport n : Set ThresholdHilbert) :=
      QuotientAddGroup.norm_mk (S := (ambientSupport n).toAddSubgroup) CaptureGains.centeredParity
    _ ≤ _ := by simpa only [dist_eq_norm] using
        Metric.infDist_le_dist_of_mem (x := CaptureGains.centeredParity) hp
  have hs := pow_le_pow_left₀ (norm_nonneg _) hd 2
  rw [hq, mul_pow] at hs
  simpa only [CaptureGains.deficit, finiteScreening_apply, K] using hs

/-- The certified five-packet trial already captures more than 1/15 in the unnormalized
variance at the two-prime support stage. -/
theorem twoPrime_parityQuotient_upper :
    (Real.log 2) ^ 2 * ‖parityQuotientClass 2‖ ^ 2 <
      Real.log 2 - (Real.log 2) ^ 2 - 1 / 15 := by
  have hc : ∀ q : Fin 16, (q : ℕ).primeFactors.card ≤ 2 := by decide +kernel
  have hw : ∀ q ∈ mixedConductors (Finset.Icc 2 15), q.primeFactors.card ≤ 2 := by
    intro q hq
    have hq' : q ∈ Finset.Icc 2 15 := (Finset.mem_filter.mp hq).1
    exact hc ⟨q, Nat.lt_succ_of_le (Finset.mem_Icc.mp hq').2⟩
  linarith only [parityQuotient_le_window_deficit hw, CaptureGains.deficit_add_capture 15,
    fixedTwo_mixed_capture_gt_one_fifteenth 15 (by decide)]

/-- The published finite fit gives a uniform fractional decrease on the first nontrivial block. -/
theorem twoPrime_parityQuotient_contracts :
    ‖parityQuotientClass 2‖ ^ 2 < (11 / 15 : ℝ) * ‖parityQuotientClass 1‖ ^ 2 := by
  have hp : (supportSpace 1).starProjection parityMixedProjection = 0 :=
    (Submodule.mem_bot ℝ).mp (supportSpace_one.le ((supportSpace 1).starProjection_apply_mem _))
  have h1 := parityQuotient_sq_add_captured 1
  rw [sum_supportLayer_energy, hp, norm_zero, zero_pow (by decide : 2 ≠ 0), add_zero] at h1
  have hL : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hstart : (Real.log 2) ^ 2 * ‖parityQuotientClass 1‖ ^ 2 =
      Real.log 2 - (Real.log 2) ^ 2 := by
    rw [h1]
    field_simp [hL.ne'] <;> ring
  have he : (Real.log 2) ^ 2 * ‖parityQuotientClass 2‖ ^ 2 <
      (11 / 15 : ℝ) * ((Real.log 2) ^ 2 * ‖parityQuotientClass 1‖ ^ 2) := by
    rw [hstart]
    nlinarith only [twoPrime_parityQuotient_upper, sq_nonneg (Real.log 2 - 1 / 2)]
  by_contra! hbad
  have hh := mul_le_mul_of_nonneg_left hbad (sq_nonneg (Real.log 2))
  nlinarith only [he, hh]

end RiemannResearch.RH.Pareto.PrimePowerSchur.MixedConductorBasis
