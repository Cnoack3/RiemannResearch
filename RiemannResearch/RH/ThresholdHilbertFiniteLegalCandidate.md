# ThresholdHilbertFiniteLegal — unverified candidate

**Not verified by Lean.** No theorem in this candidate is claimed proved. See [attempt report](ThresholdOperatorComparisonAttempt.md).

```lean
import RiemannResearch.RH.ThresholdHilbertLegal
import RiemannResearch.RH.ThresholdHilbertMean
import RiemannResearch.RH.ThresholdLegalIntegrability
import RiemannResearch.RH.ThresholdHilbertProjection
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Data.PNat.Basic

/-!
# Actual finite two-seed legal projections and exact innovation covariance

Source: independently developed from Christian Noack's RH_Two_Seed_Threshold.tex
(8 September 2026), whose two-seed legal approximation problem motivates these
constructions. Projection facts use Mathlib's Hilbert projection theorem.

Every positive integer is an allowed dilation scale. The finite spaces are
spanned by actual T_m residue_2 and T_m residue_3 in the complete weighted H.
Their supremum is the previously defined actual algebraic legal subspace.
All finite projections and mixed covariance identities are constructed here;
neither legal density nor RH is assumed or concluded.
-/

namespace RiemannResearch.RH.Pareto
noncomputable section

private theorem residue_square_summable (a : ℕ+) :
    Summable (fun k => positiveWeight k * (residue a k)^2) := by
  simpa only [pow_two] using weighted_summable_of_bounded
    (bounded_product (fun k => residue_abs_le a k a.property)
      (fun k => residue_abs_le a k a.property))

/-- Actual weighted-H residue seed, with its entire infinite tail. -/
def hilbertResidue (a : ℕ+) : ThresholdHilbert :=
  sequenceHilbert (residue a) (residue_square_summable a)

@[simp] theorem hilbertResidue_sequence (a : ℕ+) :
    hilbertSequence (hilbertResidue a) = residue a := by
  apply hilbertSequence_sequenceHilbert
  simp [residue]

/-- Actual legal generator at any positive integer scale. -/
def hilbertResidueDilation (a m : ℕ+) : ThresholdHilbert :=
  hilbertDilation m m.property (hilbertResidue a)

@[simp] theorem hilbertResidueDilation_sequence (a m : ℕ+) :
    hilbertSequence (hilbertResidueDilation a m) = dilation m (residue a) := by
  rw [hilbertResidueDilation, hilbertDilation_sequence, hilbertResidue_sequence]

/-- The actual finite-dimensional two-seed legal space, with no period cutoff. -/
def finiteTwoSeedSpan (M : Finset ℕ+) : Submodule ℝ ThresholdHilbert :=
  Submodule.span ℝ
    ((hilbertResidueDilation 2 '' (M : Set ℕ+)) ∪
      (hilbertResidueDilation 3 '' (M : Set ℕ+)))

instance finiteTwoSeedSpan_finiteDimensional (M : Finset ℕ+) :
    FiniteDimensional ℝ (finiteTwoSeedSpan M) :=
  FiniteDimensional.span_of_finite ℝ
    ((M.finite_toSet.image _).union (M.finite_toSet.image _))

instance finiteTwoSeedSpan_complete (M : Finset ℕ+) :
    CompleteSpace (finiteTwoSeedSpan M) :=
  FiniteDimensional.complete ℝ (finiteTwoSeedSpan M)

instance finiteTwoSeedSpan_hasOrthogonalProjection (M : Finset ℕ+) :
    (finiteTwoSeedSpan M).HasOrthogonalProjection :=
  Submodule.HasOrthogonalProjection.ofCompleteSpace _

theorem finiteTwoSeedSpan_mono {M N : Finset ℕ+} (hMN : M ⊆ N) :
    finiteTwoSeedSpan M ≤ finiteTwoSeedSpan N := by
  apply Submodule.span_mono
  exact Set.union_subset_union (Set.image_mono hMN) (Set.image_mono hMN)

theorem hilbertResidueDilation_two_mem (M : Finset ℕ+) {m : ℕ+} (hm : m ∈ M) :
    hilbertResidueDilation 2 m ∈ finiteTwoSeedSpan M :=
  Submodule.subset_span (Or.inl ⟨m, hm, rfl⟩)

theorem hilbertResidueDilation_three_mem (M : Finset ℕ+) {m : ℕ+} (hm : m ∈ M) :
    hilbertResidueDilation 3 m ∈ finiteTwoSeedSpan M :=
  Submodule.subset_span (Or.inr ⟨m, hm, rfl⟩)

theorem finiteTwoSeedSpan_le_legal (M : Finset ℕ+) :
    finiteTwoSeedSpan M ≤ hilbertLegalSubspace ({2, 3} : Set ℕ) := by
  apply Submodule.span_le.mpr
  rintro f (hf | hf)
  · obtain ⟨m, hm, rfl⟩ := hf
    change hilbertSequence (hilbertResidueDilation 2 m) ∈ legalSeedSpan ({2, 3} : Set ℕ)
    rw [hilbertResidueDilation_sequence]
    exact dilation_generator_mem _ (by simp) m.property
  · obtain ⟨m, hm, rfl⟩ := hf
    change hilbertSequence (hilbertResidueDilation 3 m) ∈ legalSeedSpan ({2, 3} : Set ℕ)
    rw [hilbertResidueDilation_sequence]
    exact dilation_generator_mem _ (by simp) m.property

/-- No legal finite synthesis is lost by the concrete Hilbert generators. -/
theorem iSup_finiteTwoSeedSpan :
    (⨆ M : Finset ℕ+, finiteTwoSeedSpan M) =
      hilbertLegalSubspace ({2, 3} : Set ℕ) := by
  let S : Submodule ℝ ThresholdHilbert := ⨆ M : Finset ℕ+, finiteTwoSeedSpan M
  apply le_antisymm
  · exact iSup_le finiteTwoSeedSpan_le_legal
  · have hspan : legalSeedSpan ({2, 3} : Set ℕ) ≤ S.map hilbertSequenceLinear := by
      apply Submodule.span_le.mpr
      rintro f ⟨a, ha, m, hm, rfl⟩
      have ha' : a = 2 ∨ a = 3 := by simpa using ha
      rcases ha' with rfl | rfl
      · refine ⟨hilbertResidueDilation 2 ⟨m, hm⟩, ?_, ?_⟩
        · exact (le_iSup (fun M : Finset ℕ+ => finiteTwoSeedSpan M) {⟨m, hm⟩})
            (hilbertResidueDilation_two_mem _ (by simp))
        · exact hilbertResidueDilation_sequence 2 ⟨m, hm⟩
      · refine ⟨hilbertResidueDilation 3 ⟨m, hm⟩, ?_, ?_⟩
        · exact (le_iSup (fun M : Finset ℕ+ => finiteTwoSeedSpan M) {⟨m, hm⟩})
            (hilbertResidueDilation_three_mem _ (by simp))
        · exact hilbertResidueDilation_sequence 3 ⟨m, hm⟩
    intro f hf
    obtain ⟨g, hg, he⟩ := hspan hf
    have hgf : g = f := hilbertSequence_injective he
    simpa only [hgf] using hg

/-- Genuine bounded orthogonal projection onto the actual finite legal space. -/
def finiteTwoSeedProjection (M : Finset ℕ+) :
    ThresholdHilbert →L[ℝ] ThresholdHilbert :=
  (finiteTwoSeedSpan M).starProjection

theorem finiteTwoSeedProjection_mem (M : Finset ℕ+) (f : ThresholdHilbert) :
    finiteTwoSeedProjection M f ∈ finiteTwoSeedSpan M :=
  Submodule.starProjection_apply_mem _ _

theorem finiteTwoSeedProjection_fixed (M : Finset ℕ+) {f : ThresholdHilbert}
    (hf : f ∈ finiteTwoSeedSpan M) : finiteTwoSeedProjection M f = f :=
  Submodule.starProjection_eq_self_iff.mpr hf

theorem finiteTwoSeedProjection_idempotent (M : Finset ℕ+) (f : ThresholdHilbert) :
    finiteTwoSeedProjection M (finiteTwoSeedProjection M f) = finiteTwoSeedProjection M f :=
  finiteTwoSeedProjection_fixed M (finiteTwoSeedProjection_mem M f)

theorem finiteTwoSeedProjection_symmetric (M : Finset ℕ+) (f g : ThresholdHilbert) :
    inner ℝ (finiteTwoSeedProjection M f) g = inner ℝ f (finiteTwoSeedProjection M g) :=
  (finiteTwoSeedSpan M).starProjection_isSymmetric f g

theorem finiteTwoSeedProjection_orthogonal (M : Finset ℕ+) (f g : ThresholdHilbert)
    (hg : g ∈ finiteTwoSeedSpan M) :
    inner ℝ (f - finiteTwoSeedProjection M f) g = 0 :=
  Submodule.starProjection_inner_eq_zero f g hg

/-- Exact full-H best-approximation identity for every actual finite legal competitor. -/
theorem finiteTwoSeedProjection_best_approximation (M : Finset ℕ+)
    (f g : ThresholdHilbert) (hg : g ∈ finiteTwoSeedSpan M) :
    ‖f - g‖^2 = ‖f - finiteTwoSeedProjection M f‖^2 +
      ‖finiteTwoSeedProjection M f - g‖^2 := by
  have h := finiteTwoSeedProjection_orthogonal M f (finiteTwoSeedProjection M f - g)
    ((finiteTwoSeedSpan M).sub_mem (finiteTwoSeedProjection_mem M f) hg)
  have h' : inner ℝ (finiteTwoSeedProjection M f - g)
      (f - finiteTwoSeedProjection M f) = 0 := by
    rw [real_inner_comm]
    exact h
  have he : f - g = (f - finiteTwoSeedProjection M f) +
      (finiteTwoSeedProjection M f - g) := by abel
  conv_lhs => rw [he]
  rw [← real_inner_self_eq_norm_sq, inner_add_left, inner_add_right,
    inner_add_right, real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq, h, h']
  ring

/-- Enlarging the scale set removes exactly the squared innovation, with no discarded term. -/
theorem finiteTwoSeedProjection_innovation_energy {M N : Finset ℕ+} (hMN : M ⊆ N)
    (f : ThresholdHilbert) :
    ‖f - finiteTwoSeedProjection M f‖^2 = ‖f - finiteTwoSeedProjection N f‖^2 +
      ‖finiteTwoSeedProjection N f - finiteTwoSeedProjection M f‖^2 :=
  finiteTwoSeedProjection_best_approximation N f (finiteTwoSeedProjection M f)
    (finiteTwoSeedSpan_mono hMN (finiteTwoSeedProjection_mem M f))

theorem finiteTwoSeedProjection_nested {M N : Finset ℕ+} (hMN : M ⊆ N)
    (f : ThresholdHilbert) :
    finiteTwoSeedProjection M (finiteTwoSeedProjection N f) = finiteTwoSeedProjection M f := by
  have h := Submodule.starProjection_comp_starProjection_of_le (finiteTwoSeedSpan_mono hMN)
  exact congrArg (fun T : ThresholdHilbert →L[ℝ] ThresholdHilbert => T f) h

/-- Exact mixed covariance gain from actual new legal directions. -/
theorem finiteTwoSeedProjection_innovation_covariance {M N : Finset ℕ+} (hMN : M ⊆ N)
    (f g : ThresholdHilbert) :
    inner ℝ (finiteTwoSeedProjection N f) (finiteTwoSeedProjection N g) =
      inner ℝ (finiteTwoSeedProjection M f) (finiteTwoSeedProjection M g) +
      inner ℝ (finiteTwoSeedProjection N f - finiteTwoSeedProjection M f)
        (finiteTwoSeedProjection N g - finiteTwoSeedProjection M g) := by
  have hfg := finiteTwoSeedProjection_orthogonal M (finiteTwoSeedProjection N f)
    (finiteTwoSeedProjection M g) (finiteTwoSeedProjection_mem M g)
  have hgf := finiteTwoSeedProjection_orthogonal M (finiteTwoSeedProjection N g)
    (finiteTwoSeedProjection M f) (finiteTwoSeedProjection_mem M f)
  rw [finiteTwoSeedProjection_nested hMN] at hfg hgf
  rw [inner_sub_left] at hfg hgf
  have hx : inner ℝ (finiteTwoSeedProjection N f) (finiteTwoSeedProjection M g) =
      inner ℝ (finiteTwoSeedProjection M f) (finiteTwoSeedProjection M g) :=
    sub_eq_zero.mp hfg
  have hy : inner ℝ (finiteTwoSeedProjection M f) (finiteTwoSeedProjection N g) =
      inner ℝ (finiteTwoSeedProjection M f) (finiteTwoSeedProjection M g) := by
    calc
      _ = inner ℝ (finiteTwoSeedProjection N g) (finiteTwoSeedProjection M f) :=
        real_inner_comm _ _
      _ = inner ℝ (finiteTwoSeedProjection M g) (finiteTwoSeedProjection M f) :=
        sub_eq_zero.mp hgf
      _ = _ := real_inner_comm _ _
  rw [inner_sub_left, inner_sub_right, inner_sub_right]
  rw [hx, hy]
  ring

/-- The actual optimal finite legal approximation has this exact complete-tail error. -/
theorem finiteTwoSeedProjection_target_error (M : Finset ℕ+) :
    ‖hilbertOne - finiteTwoSeedProjection M hilbertOne‖^2 +
      ‖finiteTwoSeedProjection M hilbertOne‖^2 = 1 := by
  have h := finiteTwoSeedProjection_best_approximation M hilbertOne 0
    (finiteTwoSeedSpan M).zero_mem
  simpa only [sub_zero, hilbertOne_norm_sq] using h.symm

/-- The actual two-seed covariance compressed by the dilation-block projection.
This P_m is the affine block projection, not a residue-class quotient projection. -/
def twoSeedBlockCovariance (m : ℕ) (hm : 0 < m) (M : Finset ℕ+) :
    ThresholdHilbert →L[ℝ] ThresholdHilbert :=
  (hilbertBlockProjection m hm).comp
    ((finiteTwoSeedProjection M).comp (hilbertBlockProjection m hm))

/-- The complete mixed covariance, with both actual P_m and actual legal Q_M. -/
theorem twoSeedBlockCovariance_inner (m : ℕ) (hm : 0 < m) (M : Finset ℕ+)
    (f g : ThresholdHilbert) :
    inner ℝ (twoSeedBlockCovariance m hm M f) g =
      inner ℝ (finiteTwoSeedProjection M (hilbertBlockProjection m hm f))
        (finiteTwoSeedProjection M (hilbertBlockProjection m hm g)) := by
  change inner ℝ (hilbertBlockProjection m hm
    (finiteTwoSeedProjection M (hilbertBlockProjection m hm f))) g = _
  rw [hilbertBlockProjection_symmetric]
  have h := finiteTwoSeedProjection_symmetric M
    (finiteTwoSeedProjection M (hilbertBlockProjection m hm f))
    (hilbertBlockProjection m hm g)
  rw [finiteTwoSeedProjection_idempotent] at h
  exact h

/-- Diagonal covariance is an exact squared norm, before any positivity estimate. -/
theorem twoSeedBlockCovariance_energy (m : ℕ) (hm : 0 < m) (M : Finset ℕ+)
    (f : ThresholdHilbert) :
    inner ℝ (twoSeedBlockCovariance m hm M f) f =
      ‖finiteTwoSeedProjection M (hilbertBlockProjection m hm f)‖^2 := by
  rw [twoSeedBlockCovariance_inner, real_inner_self_eq_norm_sq]

theorem twoSeedBlockCovariance_nonneg (m : ℕ) (hm : 0 < m) (M : Finset ℕ+)
    (f : ThresholdHilbert) : 0 ≤ inner ℝ (twoSeedBlockCovariance m hm M f) f := by
  rw [twoSeedBlockCovariance_energy]
  exact sq_nonneg _

/-- Exact mixed innovation gain after actual affine block compression. -/
theorem twoSeedBlockCovariance_innovation (m : ℕ) (hm : 0 < m)
    {M N : Finset ℕ+} (hMN : M ⊆ N) (f g : ThresholdHilbert) :
    inner ℝ ((twoSeedBlockCovariance m hm N - twoSeedBlockCovariance m hm M) f) g =
      inner ℝ
        (finiteTwoSeedProjection N (hilbertBlockProjection m hm f) -
          finiteTwoSeedProjection M (hilbertBlockProjection m hm f))
        (finiteTwoSeedProjection N (hilbertBlockProjection m hm g) -
          finiteTwoSeedProjection M (hilbertBlockProjection m hm g)) := by
  change inner ℝ (twoSeedBlockCovariance m hm N f - twoSeedBlockCovariance m hm M f) g = _
  rw [inner_sub_left, twoSeedBlockCovariance_inner, twoSeedBlockCovariance_inner]
  linarith [finiteTwoSeedProjection_innovation_covariance hMN
    (hilbertBlockProjection m hm f) (hilbertBlockProjection m hm g)]

/-- Enlarging the legal scale set adds precisely this nonnegative compressed energy. -/
theorem twoSeedBlockCovariance_innovation_energy (m : ℕ) (hm : 0 < m)
    {M N : Finset ℕ+} (hMN : M ⊆ N) (f : ThresholdHilbert) :
    inner ℝ ((twoSeedBlockCovariance m hm N - twoSeedBlockCovariance m hm M) f) f =
      ‖finiteTwoSeedProjection N (hilbertBlockProjection m hm f) -
        finiteTwoSeedProjection M (hilbertBlockProjection m hm f)‖^2 := by
  rw [twoSeedBlockCovariance_innovation m hm hMN, real_inner_self_eq_norm_sq]

instance hilbertTwoSeedLegalClosure_hasOrthogonalProjection :
    (hilbertLegalClosure ({2, 3} : Set ℕ)).HasOrthogonalProjection := by
  unfold hilbertLegalClosure
  exact Submodule.HasOrthogonalProjection.ofCompleteSpace _

/-- Actual projection onto the complete two-seed legal closure; no density hypothesis. -/
def twoSeedLegalProjection : ThresholdHilbert →L[ℝ] ThresholdHilbert :=
  (hilbertLegalClosure ({2, 3} : Set ℕ)).starProjection

/-- Finite legal synthesis converges strongly to the actual legal projection.
The limit is Q_legal f; no assertion that Q_legal is the identity is made. -/
theorem finiteTwoSeedProjection_tendsto (f : ThresholdHilbert) :
    Filter.Tendsto (fun M : Finset ℕ+ => finiteTwoSeedProjection M f)
      Filter.atTop (nhds (twoSeedLegalProjection f)) := by
  letI : (⨆ M : Finset ℕ+, finiteTwoSeedSpan M).topologicalClosure.HasOrthogonalProjection :=
    Submodule.HasOrthogonalProjection.ofCompleteSpace _
  have h := Submodule.starProjection_tendsto_closure_iSup finiteTwoSeedSpan
    (fun M N hMN => finiteTwoSeedSpan_mono hMN) f
  simpa only [finiteTwoSeedProjection, twoSeedLegalProjection,
    hilbertLegalClosure, iSup_finiteTwoSeedSpan] using h

/-- The actual dilation-block covariance has the exact strong limit P_m Q_legal P_m. -/
theorem twoSeedBlockCovariance_tendsto (m : ℕ) (hm : 0 < m) (f : ThresholdHilbert) :
    Filter.Tendsto (fun M : Finset ℕ+ => twoSeedBlockCovariance m hm M f)
      Filter.atTop (nhds (hilbertBlockProjection m hm
        (twoSeedLegalProjection (hilbertBlockProjection m hm f)))) := by
  have h := ((hilbertBlockProjection m hm).continuous.tendsto
    (twoSeedLegalProjection (hilbertBlockProjection m hm f))).comp
      (finiteTwoSeedProjection_tendsto (hilbertBlockProjection m hm f))
  simpa only [twoSeedBlockCovariance, ContinuousLinearMap.comp_apply,
    Function.comp_def] using h

end
end RiemannResearch.RH.Pareto
```
