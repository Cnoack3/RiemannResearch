import RiemannResearch.RH.DyadicRegularizedNorm
import Mathlib.Topology.Algebra.InfiniteSum.Module

/-!
# The actual dyadic quotient on every physical tail

Source: user-provided September 10, 2026 handoff, (N1)--(N2) and Section 7.

The physical tail H_X is constructed as the orthogonal complement of the head
atoms. Its support characterization is proved. The tail quotient is the
orthogonal projection onto the vectors in H_X annihilating (I-T₂)H_X; this is
the variational definition of ker(I-(T₂|H_X)*) and involves the actual weighted
inner product. The integer transfer and full X,d norm-bound reduction are
proved for these concrete spaces and families, with no arbitrary projection
provider. The base arithmetic norm bound and its series summability remain
explicit formal-provider inputs to the final theorem.
-/

namespace RiemannResearch.RH.Pareto

open scoped BigOperators

noncomputable section

/-- Actual physical point atoms strictly before the tail boundary X. -/
def dyadicHeadAtomSpan (X : ℕ) : Submodule ℝ ThresholdHilbert :=
  Submodule.span ℝ {f | ∃ k : ℕ, ∃ hk : 0 < k, k < X ∧ f = hilbertAtom k hk}

/-- The physical tail H_X, as a closed subspace of the actual complete H. -/
def dyadicPhysicalTail (X : ℕ) : Submodule ℝ ThresholdHilbert :=
  (dyadicHeadAtomSpan X)ᗮ

theorem mem_dyadicPhysicalTail_iff (X : ℕ) (f : ThresholdHilbert) :
    f ∈ dyadicPhysicalTail X ↔ ∀ k : ℕ, k < X → hilbertSequence f k = 0 := by
  constructor
  · intro hf k hk
    by_cases hk0 : k = 0
    · subst k
      exact hilbertSequence_zero f
    · have hkp : 0 < k := Nat.pos_of_ne_zero hk0
      have h := ((dyadicHeadAtomSpan X).mem_orthogonal f).mp hf
        (hilbertAtom k hkp) (Submodule.subset_span ⟨k, hkp, hk, rfl⟩)
      rw [hilbertAtom_inner] at h
      have hw : positiveWeight k ≠ 0 := by unfold positiveWeight; positivity
      exact (mul_eq_zero.mp h).resolve_left hw
  · intro hf
    apply ((dyadicHeadAtomSpan X).mem_orthogonal f).mpr
    intro g hg
    induction hg using Submodule.span_induction with
    | mem g hg =>
        obtain ⟨k, hk, hkX, rfl⟩ := hg
        rw [hilbertAtom_inner, hf k hkX, mul_zero]
    | zero => simp
    | add u v hu hv ihu ihv => simp only [inner_add_left, ihu, ihv, add_zero]
    | smul c u hu ihu => simp only [real_inner_smul_left, ihu, mul_zero]

theorem dyadicPhysicalTail_dilation (X m : ℕ) (hm : 0 < m)
    (f : ThresholdHilbert) (hf : f ∈ dyadicPhysicalTail X) :
    hilbertDilation m hm f ∈ dyadicPhysicalTail X := by
  apply (mem_dyadicPhysicalTail_iff X _).mpr
  intro k hk
  rw [hilbertDilation_sequence]
  change (m : ℝ) * hilbertSequence f (k / m) = 0
  rw [(mem_dyadicPhysicalTail_iff X f).mp hf (k / m)
    (lt_of_le_of_lt (Nat.div_le_self k m) hk), mul_zero]

/-- Every integer dilation at least X maps the full H into the physical tail. -/
theorem hilbertDilation_mem_dyadicPhysicalTail
    (X d : ℕ) (hd : 0 < d) (hXd : X ≤ d) (f : ThresholdHilbert) :
    hilbertDilation d hd f ∈ dyadicPhysicalTail X := by
  apply (mem_dyadicPhysicalTail_iff X _).mpr
  intro k hk
  rw [hilbertDilation_sequence]
  change (d : ℝ) * hilbertSequence f (k / d) = 0
  rw [Nat.div_eq_of_lt (lt_of_lt_of_le hk hXd), hilbertSequence_zero, mul_zero]

/-- The actual range of I-T₂ on H_X, with no closed-range assumption. -/
def dyadicTailDifferenceRange (X : ℕ) : Submodule ℝ ThresholdHilbert :=
  (dyadicPhysicalTail X).map
    (ContinuousLinearMap.id ℝ ThresholdHilbert -
      hilbertDilationContinuous 2 (by norm_num)).toLinearMap

theorem dyadic_difference_mem_tailDifferenceRange (X : ℕ)
    (f : ThresholdHilbert) (hf : f ∈ dyadicPhysicalTail X) :
    f - hilbertDilation 2 (by norm_num) f ∈ dyadicTailDifferenceRange X :=
  ⟨f, hf, rfl⟩

theorem dyadicTailDifferenceRange_le_tail (X : ℕ) :
    dyadicTailDifferenceRange X ≤ dyadicPhysicalTail X := by
  rintro g ⟨f, hf, rfl⟩
  exact (dyadicPhysicalTail X).sub_mem hf
    (dyadicPhysicalTail_dilation X 2 (by norm_num) f hf)

/-- Vectors in H_X annihilating (I-T₂)H_X. The orthogonal of a supremum
constructs the closed intersection without supplying a projection hypothesis. -/
def dyadicTailQuotientSubspace (X : ℕ) : Submodule ℝ ThresholdHilbert :=
  (dyadicHeadAtomSpan X ⊔ dyadicTailDifferenceRange X)ᗮ

instance dyadicTailQuotientSubspace_hasOrthogonalProjection (X : ℕ) :
    (dyadicTailQuotientSubspace X).HasOrthogonalProjection := by
  unfold dyadicTailQuotientSubspace
  infer_instance

/-- Exact variational fixed-adjoint characterization on the actual physical tail. -/
theorem mem_dyadicTailQuotientSubspace_iff (X : ℕ) (f : ThresholdHilbert) :
    f ∈ dyadicTailQuotientSubspace X ↔
      f ∈ dyadicPhysicalTail X ∧ ∀ u ∈ dyadicPhysicalTail X,
        inner ℝ (u - hilbertDilation 2 (by norm_num) u) f = 0 := by
  constructor
  · intro hf
    have ho := ((dyadicHeadAtomSpan X ⊔ dyadicTailDifferenceRange X).mem_orthogonal f).mp hf
    constructor
    · apply ((dyadicHeadAtomSpan X).mem_orthogonal f).mpr
      intro u hu
      exact ho u ((le_sup_left : dyadicHeadAtomSpan X ≤
        dyadicHeadAtomSpan X ⊔ dyadicTailDifferenceRange X) hu)
    · intro u hu
      exact ho _ ((le_sup_right : dyadicTailDifferenceRange X ≤
        dyadicHeadAtomSpan X ⊔ dyadicTailDifferenceRange X)
          (dyadic_difference_mem_tailDifferenceRange X u hu))
  · rintro ⟨hf, hdiff⟩
    apply ((dyadicHeadAtomSpan X ⊔ dyadicTailDifferenceRange X).mem_orthogonal f).mpr
    intro g hg
    rcases Submodule.mem_sup.mp hg with ⟨u, hu, v, hv, rfl⟩
    rcases hv with ⟨w, hw, rfl⟩
    rw [inner_add_left]
    have hu0 := ((dyadicHeadAtomSpan X).mem_orthogonal f).mp hf u hu
    change inner ℝ u f + inner ℝ (w - hilbertDilation 2 (by norm_num) w) f = 0
    rw [hu0, hdiff w hw, add_zero]

/-- The genuine tail quotient projection Q_X, acting on the ambient H. -/
def dyadicTailQuotientProjection (X : ℕ) :
    ThresholdHilbert →L[ℝ] ThresholdHilbert :=
  (dyadicTailQuotientSubspace X).starProjection

theorem dyadicTailQuotientProjection_mem (X : ℕ) (f : ThresholdHilbert) :
    dyadicTailQuotientProjection X f ∈ dyadicTailQuotientSubspace X :=
  Submodule.starProjection_apply_mem _ _

theorem dyadicTailQuotientProjection_support (X : ℕ) (f : ThresholdHilbert)
    (k : ℕ) (hk : k < X) :
    hilbertSequence (dyadicTailQuotientProjection X f) k = 0 :=
  (mem_dyadicPhysicalTail_iff X _).mp
    ((mem_dyadicTailQuotientSubspace_iff X _).mp
      (dyadicTailQuotientProjection_mem X f)).1 k hk

theorem dyadicTailQuotientProjection_norm_le (X : ℕ) (f : ThresholdHilbert) :
    ‖dyadicTailQuotientProjection X f‖ ≤ ‖f‖ :=
  Submodule.norm_starProjection_apply_le _ _

theorem dyadicTailQuotientProjection_inner (X : ℕ) (f g : ThresholdHilbert) :
    inner ℝ (dyadicTailQuotientProjection X f) g =
      inner ℝ f (dyadicTailQuotientProjection X g) :=
  (dyadicTailQuotientSubspace X).starProjection_isSymmetric f g

/-- Exact quotient/complement splitting, still in the original weighted norm. -/
theorem dyadicTailQuotientProjection_pythagoras (X : ℕ) (f : ThresholdHilbert) :
    ‖f‖ ^ 2 = ‖dyadicTailQuotientProjection X f‖ ^ 2 +
      ‖f - dyadicTailQuotientProjection X f‖ ^ 2 := by
  have h := Submodule.norm_sq_eq_add_norm_sq_starProjection f (dyadicTailQuotientSubspace X)
  rw [Submodule.starProjection_orthogonal_val] at h
  exact h

private theorem dilation_dyadic_difference (d : ℕ) (hd : 0 < d) (f : ThresholdHilbert) :
    hilbertDilation d hd (f - hilbertDilation 2 (by norm_num) f) =
      hilbertDilation d hd f -
        hilbertDilation 2 (by norm_num) (hilbertDilation d hd f) := by
  have h := (hilbertDilationContinuous d hd).map_sub f
    (hilbertDilation 2 (by norm_num) f)
  simpa only [hilbertDilationContinuous_apply, hilbertDilation_comp, Nat.mul_comm] using h

/-- The transfer adjoint sends a genuine tail quotient vector to the base quotient. -/
theorem dyadicTailTransfer_adjoint_mem_base
    (X d : ℕ) (hd : 0 < d) (hXd : X ≤ d) (g : ThresholdHilbert) :
    hilbertDilationAdjoint d hd (dyadicTailQuotientProjection X g) ∈
      dyadicQuotientSubspace := by
  apply (dyadicDifferenceRange.mem_orthogonal _).mpr
  rintro u ⟨f, rfl⟩
  change inner ℝ (f - hilbertDilation 2 (by norm_num) f)
    (hilbertDilationAdjoint d hd (dyadicTailQuotientProjection X g)) = 0
  have ha := ContinuousLinearMap.adjoint_inner_right
    (hilbertDilationContinuous d hd) (f - hilbertDilation 2 (by norm_num) f)
    (dyadicTailQuotientProjection X g)
  change inner ℝ (f - hilbertDilation 2 (by norm_num) f)
      (hilbertDilationAdjoint d hd (dyadicTailQuotientProjection X g)) =
    inner ℝ (hilbertDilation d hd (f - hilbertDilation 2 (by norm_num) f))
      (dyadicTailQuotientProjection X g) at ha
  rw [dilation_dyadic_difference] at ha
  exact ha.trans
    (((mem_dyadicTailQuotientSubspace_iff X _).mp
      (dyadicTailQuotientProjection_mem X g)).2 _
      (hilbertDilation_mem_dyadicPhysicalTail X d hd hXd f))

private theorem inner_dilation_eq_adjoint_inner (d : ℕ) (hd : 0 < d)
    (f g : ThresholdHilbert) :
    inner ℝ f (hilbertDilation d hd g) =
      inner ℝ (hilbertDilationAdjoint d hd f) g := by
  calc
    inner ℝ f (hilbertDilation d hd g) = inner ℝ (hilbertDilation d hd g) f :=
      (real_inner_comm f (hilbertDilation d hd g)).symm
    _ = inner ℝ g (hilbertDilationAdjoint d hd f) :=
      (ContinuousLinearMap.adjoint_inner_right (hilbertDilationContinuous d hd) g f).symm
    _ = inner ℝ (hilbertDilationAdjoint d hd f) g :=
      (real_inner_comm g (hilbertDilationAdjoint d hd f)).symm

/-- The actual tail transfer depends only on the base dyadic quotient class. -/
theorem dyadicTailQuotientProjection_dilation_base_projection
    (X d : ℕ) (hd : 0 < d) (hXd : X ≤ d) (f : ThresholdHilbert) :
    dyadicTailQuotientProjection X (hilbertDilation d hd (dyadicQuotientProjection f)) =
      dyadicTailQuotientProjection X (hilbertDilation d hd f) := by
  apply ext_inner_left ℝ
  intro g
  have hfix : dyadicQuotientProjection
      (hilbertDilationAdjoint d hd (dyadicTailQuotientProjection X g)) =
      hilbertDilationAdjoint d hd (dyadicTailQuotientProjection X g) :=
    dyadicQuotientProjection_eq_self (dyadicTailTransfer_adjoint_mem_base X d hd hXd g)
  calc
    inner ℝ g (dyadicTailQuotientProjection X
        (hilbertDilation d hd (dyadicQuotientProjection f))) =
      inner ℝ (dyadicTailQuotientProjection X g)
        (hilbertDilation d hd (dyadicQuotientProjection f)) :=
      (dyadicTailQuotientProjection_inner X _ _).symm
    _ = inner ℝ (hilbertDilationAdjoint d hd (dyadicTailQuotientProjection X g))
        (dyadicQuotientProjection f) := inner_dilation_eq_adjoint_inner d hd _ _
    _ = inner ℝ (dyadicQuotientProjection
        (hilbertDilationAdjoint d hd (dyadicTailQuotientProjection X g))) f :=
      (dyadicQuotientProjection_inner _ _).symm
    _ = inner ℝ (hilbertDilationAdjoint d hd (dyadicTailQuotientProjection X g)) f := by
      rw [hfix]
    _ = inner ℝ (dyadicTailQuotientProjection X g) (hilbertDilation d hd f) :=
      (inner_dilation_eq_adjoint_inner d hd _ _).symm
    _ = inner ℝ g (dyadicTailQuotientProjection X (hilbertDilation d hd f)) :=
      dyadicTailQuotientProjection_inner X _ _

/-- The actual bounded transfer map from the base quotient to the physical tail quotient. -/
def dyadicTailTransfer (X d : ℕ) (hd : 0 < d) :
    ThresholdHilbert →L[ℝ] ThresholdHilbert :=
  (dyadicTailQuotientProjection X).comp (hilbertDilationContinuous d hd)

@[simp] theorem dyadicTailTransfer_apply (X d : ℕ) (hd : 0 < d) (f : ThresholdHilbert) :
    dyadicTailTransfer X d hd f =
      dyadicTailQuotientProjection X (hilbertDilation d hd f) := rfl

theorem dyadicTailTransfer_norm_sq_le (X d : ℕ) (hd : 0 < d) (f : ThresholdHilbert) :
    ‖dyadicTailTransfer X d hd f‖ ^ 2 ≤ (d : ℝ) * ‖f‖ ^ 2 :=
  contractive_projection_dilation_norm_sq_le (dyadicTailQuotientProjection X)
    (dyadicTailQuotientProjection_norm_le X) d hd f

/-- A concrete projected term of (N1) for every physical X and dilation d. -/
def dyadicTailRegularizedTerm (X d : ℕ) (hd : 0 < d) (ε : ℝ)
    (p : ℕ × ℕ) : ThresholdHilbert :=
  dyadicRegularizationCoefficient ε p.1 p.2 •
    dyadicTailQuotientProjection X
      (hilbertDilation (d * ((p.1 + 1) * 3 ^ p.2)) (by positivity)
        (hilbertResidue 3 (by norm_num)))

def dyadicTailRegularizedFamily (X d : ℕ) (hd : 0 < d) (ε : ℝ) : ThresholdHilbert :=
  dyadicRegularizationNormalization ε •
    ∑' p : ℕ × ℕ, dyadicTailRegularizedTerm X d hd ε p

theorem dyadicTailRegularizedTerm_eq_transfer
    (X d : ℕ) (hd : 0 < d) (hXd : X ≤ d) (ε : ℝ) (p : ℕ × ℕ) :
    dyadicTailRegularizedTerm X d hd ε p =
      dyadicTailTransfer X d hd (dyadicRegularizedTerm ε p) := by
  rw [dyadicRegularizedTerm, map_smul, dyadicTailTransfer_apply,
    dyadicTailQuotientProjection_dilation_base_projection X d hd hXd,
    hilbertDilation_comp]
  rfl

/-- The full target product series really converges whenever the base product
series does. Its value is never justified using the default unsummable tsum. -/
theorem dyadicTailRegularizedTerm_summable
    (X d : ℕ) (hd : 0 < d) (hXd : X ≤ d) (ε : ℝ)
    (hs : Summable (dyadicRegularizedTerm ε)) :
    Summable (dyadicTailRegularizedTerm X d hd ε) := by
  have h := (dyadicTailTransfer X d hd).summable hs
  apply h.congr
  intro p
  exact (dyadicTailRegularizedTerm_eq_transfer X d hd hXd ε p).symm

/-- Exact transfer of the full projected arithmetic series, after establishing
summability of the base series. No raw infinite H lift is asserted. -/
theorem dyadicTailRegularizedFamily_eq_transfer
    (X d : ℕ) (hd : 0 < d) (hXd : X ≤ d) (ε : ℝ)
    (hs : Summable (dyadicRegularizedTerm ε)) :
    dyadicTailRegularizedFamily X d hd ε =
      dyadicTailTransfer X d hd (dyadicRegularizedFamily ε) := by
  have hseries : (∑' p : ℕ × ℕ, dyadicTailRegularizedTerm X d hd ε p) =
      dyadicTailTransfer X d hd (∑' p : ℕ × ℕ, dyadicRegularizedTerm ε p) := by
    rw [(dyadicTailTransfer X d hd).map_tsum hs]
    apply tsum_congr
    intro p
    exact dyadicTailRegularizedTerm_eq_transfer X d hd hXd ε p
  rw [dyadicTailRegularizedFamily, hseries, dyadicRegularizedFamily, map_smul]

/-- The full original norm obligation, with concrete X,d families and every
quantifier retained. This proposition is not introduced as an axiom. -/
def DyadicTailRegularizedNormBound : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ X d (hX : 0 < X) (hXd : X ≤ d),
    ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 2 →
      ‖dyadicTailRegularizedFamily X d (Nat.lt_of_lt_of_le hX hXd) ε‖ ^ 2 ≤ C * d

/-- Series convergence, stated separately from the full norm obligation. -/
def DyadicTailRegularizedSeriesSummable : Prop :=
  ∀ X d (hX : 0 < X) (hXd : X ≤ d), ∀ ε : ℝ, 0 < ε → ε ≤ 1 / 2 →
    Summable (dyadicTailRegularizedTerm X d (Nat.lt_of_lt_of_le hX hXd) ε)

theorem dyadicTailRegularizedSeriesSummable_of_base
    (hseries : DyadicRegularizedSeriesSummable) : DyadicTailRegularizedSeriesSummable := by
  intro X d hX hXd ε hε hεhalf
  exact dyadicTailRegularizedTerm_summable X d (Nat.lt_of_lt_of_le hX hXd) hXd ε
    (hseries ε hε hεhalf).2

/-- The complete X,d transfer is now an actual theorem. Only the base
arithmetic summability and norm estimate remain input formal providers. -/
theorem dyadicTailRegularizedNormBound_of_base
    (hseries : DyadicRegularizedSeriesSummable) (hbase : DyadicRegularizedNormBound) :
    DyadicTailRegularizedNormBound := by
  obtain ⟨C, hC, hbound⟩ := hbase
  refine ⟨C, hC, ?_⟩
  intro X d hX hXd ε hε hεhalf
  rw [dyadicTailRegularizedFamily_eq_transfer X d (Nat.lt_of_lt_of_le hX hXd)
    hXd ε ((hseries ε hε hεhalf).2)]
  calc
    _ ≤ (d : ℝ) * ‖dyadicRegularizedFamily ε‖ ^ 2 :=
      dyadicTailTransfer_norm_sq_le X d (Nat.lt_of_lt_of_le hX hXd) _
    _ ≤ (d : ℝ) * C :=
      mul_le_mul_of_nonneg_left (hbound ε hε hεhalf) (Nat.cast_nonneg d)
    _ = C * d := mul_comm _ _

end
end RiemannResearch.RH.Pareto
