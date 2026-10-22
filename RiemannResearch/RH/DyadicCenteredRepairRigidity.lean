import RiemannResearch.RH.DyadicCenteredSeedRepair
import RiemannResearch.RH.ThresholdHilbertCocycle
import RiemannResearch.RH.ThresholdRiemannHypothesis

/-!
# Centered repair has the full residue approximation obstruction

Source: user-provided `DyadicRegularizedVerificationContinuation20260910.md`,
September 10, 2026; auditing its remaining centered repair obligation.

The actual dyadic difference is bounded below. Consequently even approximating
its value at the constant by centered legal repairs forces full residue density
and RH. No centered repair exhaustion or RH converse is assumed or proved.
-/

namespace RiemannResearch.RH.Pareto
noncomputable section

def dyadicRepairDifference : ThresholdHilbert →L[ℝ] ThresholdHilbert :=
  hilbertDilationContinuous 2 (by norm_num) - ContinuousLinearMap.id ℝ ThresholdHilbert

@[simp] theorem dyadicRepairDifference_apply (f : ThresholdHilbert) :
    dyadicRepairDifference f = hilbertDilation 2 (by norm_num) f - f := rfl

@[simp] theorem dyadicRepairDifference_residue (m : ℕ) (hm : 0 < m) :
    dyadicRepairDifference (hilbertResidue m hm) = dyadicCenteredSeed m hm :=
  (dyadicCenteredSeed_cocycle m hm).symm

/-- The exact reverse-triangle lower estimate, with the actual dilation. -/
theorem dyadicRepairDifference_norm_lower (f : ThresholdHilbert) :
    (Real.sqrt 2 - 1) * ‖f‖ ≤ ‖dyadicRepairDifference f‖ := by
  have ht : ‖hilbertDilation 2 (by norm_num) f‖ ≤
      ‖dyadicRepairDifference f‖ + ‖f‖ := by
    calc
      _ = ‖dyadicRepairDifference f + f‖ := by
        rw [dyadicRepairDifference_apply, sub_add_cancel]
      _ ≤ _ := norm_add_le _ _
  rw [hilbertDilation_norm] at ht
  norm_num only [Nat.cast_ofNat] at ht
  nlinarith

/-- A rational inverse bound convenient for finite approximation estimates. -/
theorem norm_le_three_dyadicRepairDifference (f : ThresholdHilbert) :
    ‖f‖ ≤ 3 * ‖dyadicRepairDifference f‖ := by
  have hs : (4 / 3 : ℝ) ≤ Real.sqrt 2 := by
    nlinarith [Real.sqrt_nonneg (2 : ℝ), Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  have hl := dyadicRepairDifference_norm_lower f
  nlinarith [mul_nonneg (sub_nonneg.mpr hs) (norm_nonneg f)]

/-- All finite signed centered dyadic corrections, with every positive dilation. -/
def dyadicCenteredRepairSpan : Submodule ℝ ThresholdHilbert :=
  Submodule.span ℝ {g | ∃ m : ℕ, ∃ hm : 0 < m, g = dyadicCenteredSeed m hm}

def dyadicCenteredRepairClosure : Submodule ℝ ThresholdHilbert :=
  dyadicCenteredRepairSpan.topologicalClosure

private theorem hilbertResidue_mem_positive_legal (m : ℕ) (hm : 0 < m) :
    hilbertResidue m hm ∈ hilbertLegalSubspace {n : ℕ | 0 < n} := by
  change hilbertSequence (hilbertResidue m hm) ∈ legalSeedSpan {n : ℕ | 0 < n}
  rw [hilbertResidue_sequence]
  exact residue_mem_legalSeedSpan _ hm

/-- Every actual centered finite correction is the difference of an actual
finite full-residue legal vector. -/
theorem dyadicCenteredRepairSpan_exists_preimage {g : ThresholdHilbert}
    (hg : g ∈ dyadicCenteredRepairSpan) :
    ∃ f : ThresholdHilbert, f ∈ hilbertLegalSubspace {n : ℕ | 0 < n} ∧
      dyadicRepairDifference f = g := by
  induction hg using Submodule.span_induction with
  | mem g hg =>
      obtain ⟨m, hm, rfl⟩ := hg
      exact ⟨hilbertResidue m hm, hilbertResidue_mem_positive_legal m hm,
        dyadicRepairDifference_residue m hm⟩
  | zero => exact ⟨0, Submodule.zero_mem _, map_zero _⟩
  | add g h hg hh ihg ihh =>
      obtain ⟨f, hf, hfg⟩ := ihg
      obtain ⟨k, hk, hkh⟩ := ihh
      exact ⟨f + k, Submodule.add_mem _ hf hk, by rw [map_add, hfg, hkh]⟩
  | smul c g hg ih =>
      obtain ⟨f, hf, hfg⟩ := ih
      exact ⟨c • f, Submodule.smul_mem _ c hf, by rw [map_smul, hfg]⟩

private theorem positive_legal_mem_hilbertResidue_span {f : ThresholdHilbert}
    (hf : f ∈ hilbertLegalSubspace {n : ℕ | 0 < n}) :
    f ∈ Submodule.span ℝ
      {g : ThresholdHilbert | ∃ m : ℕ, ∃ hm : 0 < m, g = hilbertResidue m hm} := by
  let S : Submodule ℝ ThresholdHilbert := Submodule.span ℝ
    {g : ThresholdHilbert | ∃ m : ℕ, ∃ hm : 0 < m, g = hilbertResidue m hm}
  have hspan : legalSeedSpan {n : ℕ | 0 < n} ≤ S.map hilbertSequenceLinear := by
    rw [legalSeedSpan_positive_eq_residue_span]
    apply Submodule.span_le.mpr
    rintro g ⟨m, hm, rfl⟩
    refine ⟨hilbertResidue m hm, Submodule.subset_span ⟨m, hm, rfl⟩, ?_⟩
    exact hilbertResidue_sequence m hm
  obtain ⟨v, hv, hvf⟩ := hspan hf
  have he : v = f := hilbertSequence_injective hvf
  exact he ▸ hv

theorem dyadicRepairDifference_mem_centeredSpan {f : ThresholdHilbert}
    (hf : f ∈ hilbertLegalSubspace {n : ℕ | 0 < n}) :
    dyadicRepairDifference f ∈ dyadicCenteredRepairSpan := by
  have hs := positive_legal_mem_hilbertResidue_span hf
  clear hf
  induction hs using Submodule.span_induction with
  | mem f hf =>
      obtain ⟨m, hm, rfl⟩ := hf
      rw [dyadicRepairDifference_residue]
      exact Submodule.subset_span ⟨m, hm, rfl⟩
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add f g hf hg ihf ihg =>
      rw [map_add]
      exact Submodule.add_mem _ ihf ihg
  | smul c f hf ih =>
      rw [map_smul]
      exact Submodule.smul_mem _ c ih

/-- Exact preimage characterization: centered approximation is full residue
approximation under the boundedly invertible difference on its range. -/
theorem dyadicRepairDifference_mem_centeredClosure_iff (f : ThresholdHilbert) :
    dyadicRepairDifference f ∈ dyadicCenteredRepairClosure ↔
      f ∈ hilbertLegalClosure {n : ℕ | 0 < n} := by
  constructor
  · intro h
    change dyadicRepairDifference f ∈
      closure (dyadicCenteredRepairSpan : Set ThresholdHilbert) at h
    change f ∈ closure
      (hilbertLegalSubspace {n : ℕ | 0 < n} : Set ThresholdHilbert)
    apply Metric.mem_closure_iff.mpr
    intro ε hε
    obtain ⟨g, hg, hdist⟩ := Metric.mem_closure_iff.mp h (ε / 3) (by positivity)
    obtain ⟨v, hv, hvg⟩ := dyadicCenteredRepairSpan_exists_preimage hg
    refine ⟨v, hv, ?_⟩
    have hnorm : ‖dyadicRepairDifference (f - v)‖ < ε / 3 := by
      rw [map_sub, hvg]
      simpa only [dist_eq_norm] using hdist
    rw [dist_eq_norm]
    have hb := norm_le_three_dyadicRepairDifference (f - v)
    linarith
  · intro h
    have hmap : Set.MapsTo dyadicRepairDifference
        (hilbertLegalSubspace {n : ℕ | 0 < n} : Set ThresholdHilbert)
        (dyadicCenteredRepairSpan : Set ThresholdHilbert) := by
      intro g hg
      exact dyadicRepairDifference_mem_centeredSpan hg
    exact hmap.closure dyadicRepairDifference.continuous h

/-- Approximating just this explicit complementary target already implies RH.
This theorem does not assert its hypothesis. -/
theorem riemannHypothesis_of_difference_one_mem_centeredClosure
    (h : dyadicRepairDifference hilbertOne ∈ dyadicCenteredRepairClosure) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_hilbertOne_mem_legalClosure {n : ℕ | 0 < n}
    (by intro a ha; exact ha)
  exact (dyadicRepairDifference_mem_centeredClosure_iff hilbertOne).mp h

@[simp] theorem dyadicQuotientProjection_repairDifference (f : ThresholdHilbert) :
    dyadicQuotientProjection (dyadicRepairDifference f) = 0 := by
  rw [dyadicRepairDifference_apply, map_sub,
    dyadicQuotientProjection_dilation_two, sub_self]

/-- Exhaustion of the entire complementary space is an RH-strength input. -/
theorem riemannHypothesis_of_centeredClosure_exhausts_kernel
    (h : ∀ f : ThresholdHilbert, dyadicQuotientProjection f = 0 →
      f ∈ dyadicCenteredRepairClosure) : RiemannHypothesis := by
  exact riemannHypothesis_of_difference_one_mem_centeredClosure
    (h _ (dyadicQuotientProjection_repairDifference hilbertOne))

end
end RiemannResearch.RH.Pareto
