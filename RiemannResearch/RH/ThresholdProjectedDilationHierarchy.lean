import RiemannResearch.Analysis.OrthogonalDilationCompression
import RiemannResearch.RH.ThresholdHilbertProjection
import RiemannResearch.RH.ParetoUnscaledDilation
import RiemannResearch.RH.ParetoNormalizedResidueHilbert
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Native projected hierarchy on the actual Pareto Hilbert space

Source: user-provided CRT and Four Improvements continuation, 6–7 October 2026.
The extensions retain complete signed identities and correction squares.


The paper's unscaled dilation is the existing bounded physical Hilbert
dilation divided by its positive integer conductor. Its exact inner scaling
discharges the sole physical input to the native compression assembly.
-/

namespace RiemannResearch.RH.Pareto
noncomputable section
open scoped InnerProductSpace BigOperators
open RiemannResearch.Analysis.OrthogonalDilationCompression
open RiemannResearch.Analysis.FiniteProjectedDilationHierarchy

/-- The actual unscaled paper dilation, as a bounded Hilbert operator. -/
def hilbertUnscaledDilationContinuous (m : ℕ) (hm : 0 < m) :
    ThresholdHilbert →L[ℝ] ThresholdHilbert :=
  (1 / (m : ℝ)) • hilbertDilationContinuous m hm

/-- Exact physical pair scaling on every actual Pareto Hilbert vector. -/
theorem hilbertUnscaledDilationContinuous_inner (m : ℕ) (hm : 0 < m)
    (f g : ThresholdHilbert) :
    (m : ℝ) *
      ⟪hilbertUnscaledDilationContinuous m hm f,
        hilbertUnscaledDilationContinuous m hm g⟫_ℝ = ⟪f, g⟫_ℝ := by
  change (m : ℝ) *
    ⟪(1 / (m : ℝ)) • hilbertDilation m hm f,
      (1 / (m : ℝ)) • hilbertDilation m hm g⟫_ℝ = _
  rw [real_inner_smul_left, real_inner_smul_right, hilbertDilation_inner]
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hm)
  field_simp [hm0]

/-- The bounded normalized residue atoms are genuine Hilbert vectors for every
integer conductor, including the harmless totalized zero conductor. -/
theorem normalizedAtom_square_summable (d : ℕ) :
    Summable (fun k => positiveWeight k * normalizedAtom d k ^ 2) := by
  have hb : ∀ k, |normalizedAtom d k| ≤ 1 := by
    intro k
    by_cases hd : 0 < d
    · exact normalizedAtom_abs_le_one d k hd
    · have hd0 : d = 0 := Nat.eq_zero_of_not_pos hd
      simp [hd0, normalizedAtom]
  simpa only [pow_two] using weighted_summable_of_bounded (bounded_product hb hb)

/-- The literal normalized residue atom in the physical Pareto Hilbert space. -/
def hilbertNormalizedAtom (d : ℕ) : ThresholdHilbert :=
  sequenceHilbert (normalizedAtom d) (normalizedAtom_square_summable d)

@[simp] theorem hilbertSequence_hilbertNormalizedAtom (d : ℕ) :
    hilbertSequence (hilbertNormalizedAtom d) = normalizedAtom d :=
  hilbertSequence_sequenceHilbert _ _ (normalizedAtom_zero d)

@[simp] theorem hilbertNormalizedAtom_zero : hilbertNormalizedAtom 0 = 0 := by
  apply hilbertSequence_injective
  have hz : hilbertSequence (0 : ThresholdHilbert) = 0 := hilbertSequenceLinear.map_zero
  rw [hilbertSequence_hilbertNormalizedAtom, hz]
  funext k
  simp [normalizedAtom]

/-- The constructed atom is exactly the repository's existing physical
normalized residue vector, in the same Hilbert space and with the same weights. -/
theorem hilbertNormalizedAtom_eq_normalizedResidueHilbert (d : ℕ) (hd : 0 < d) :
    hilbertNormalizedAtom d = normalizedResidueHilbert d hd := by
  apply hilbertSequence_injective
  rw [hilbertSequence_hilbertNormalizedAtom, normalizedResidueHilbert_sequence]
  rfl

/-- The bundled native operator is exactly the paper's sequence dilation. -/
theorem hilbertUnscaledDilationContinuous_sequence (m : ℕ) (hm : 0 < m)
    (f : ThresholdHilbert) :
    hilbertSequence (hilbertUnscaledDilationContinuous m hm f) =
      unscaledDilation m (hilbertSequence f) := by
  change hilbertSequence ((1 / (m : ℝ)) • hilbertDilation m hm f) = _
  rw [hilbertSequence_smul, hilbertDilation_sequence]
  funext k
  change (1 / (m : ℝ)) * dilation m (hilbertSequence f) k = _
  exact (congrFun (unscaledDilation_eq_scaled m (hilbertSequence f) hm) k).symm

/-- Exact native Hilbert atom bridge. No primality, squarefreeness, or finite
weight truncation is required. -/
theorem hilbertUnscaledDilationContinuous_atom (m d : ℕ) (hm : 0 < m) :
    hilbertUnscaledDilationContinuous m hm (hilbertNormalizedAtom d) =
      hilbertNormalizedAtom (m * d) - (1 / (d : ℝ)) • hilbertNormalizedAtom m := by
  by_cases hd : 0 < d
  · apply hilbertSequence_injective
    have hsub : hilbertSequence
        (hilbertNormalizedAtom (m * d) - (1 / (d : ℝ)) • hilbertNormalizedAtom m) =
        hilbertSequence (hilbertNormalizedAtom (m * d)) -
          hilbertSequence ((1 / (d : ℝ)) • hilbertNormalizedAtom m) :=
      hilbertSequenceLinear.map_sub _ _
    rw [hilbertUnscaledDilationContinuous_sequence, hsub,
      hilbertSequence_smul, hilbertSequence_hilbertNormalizedAtom,
      hilbertSequence_hilbertNormalizedAtom, hilbertSequence_hilbertNormalizedAtom]
    funext k
    change unscaledDilation m (normalizedAtom d) k =
      normalizedAtom (m * d) k - (1 / (d : ℝ)) * normalizedAtom m k
    rw [unscaledDilation_normalizedAtom m d k hm hd]
    ring
  · have hd0 : d = 0 := Nat.eq_zero_of_not_pos hd
    simp [hd0]

/-- The exact atom bridge stated directly with the original normalized-residue
API used by the existing approximation and Gram results. -/
theorem hilbertUnscaledDilationContinuous_normalizedResidue (m d : ℕ)
    (hm : 0 < m) (hd : 0 < d) :
    hilbertUnscaledDilationContinuous m hm (normalizedResidueHilbert d hd) =
      normalizedResidueHilbert (m * d) (Nat.mul_pos hm hd) -
        (1 / (d : ℝ)) • normalizedResidueHilbert m hm := by
  rw [← hilbertNormalizedAtom_eq_normalizedResidueHilbert d hd,
    ← hilbertNormalizedAtom_eq_normalizedResidueHilbert (m * d) (Nat.mul_pos hm hd),
    ← hilbertNormalizedAtom_eq_normalizedResidueHilbert m hm]
  exact hilbertUnscaledDilationContinuous_atom m d hm

/-- The finite legal normalized-residue span, also defined for arbitrary sets. -/
def hilbertNormalizedAtomSpan (A : Set ℕ) : Submodule ℝ ThresholdHilbert :=
  Submodule.span ℝ (hilbertNormalizedAtom '' A)

/-- Positive-conductor spans are literally the existing normalized-residue
spans; no representation change or approximation transfer is involved. -/
theorem hilbertNormalizedAtomSpan_eq_normalizedResidue_span (A : Set ℕ)
    (hA : ∀ d ∈ A, 0 < d) :
    hilbertNormalizedAtomSpan A = Submodule.span ℝ
      {f : ThresholdHilbert | ∃ d, ∃ hd : 0 < d,
        d ∈ A ∧ normalizedResidueHilbert d hd = f} := by
  unfold hilbertNormalizedAtomSpan
  apply congrArg (Submodule.span ℝ)
  ext f
  constructor
  · rintro ⟨d, hdA, rfl⟩
    exact ⟨d, hA d hdA, hdA,
      (hilbertNormalizedAtom_eq_normalizedResidueHilbert d (hA d hdA)).symm⟩
  · rintro ⟨d, hd, hdA, rfl⟩
    exact ⟨d, hdA, hilbertNormalizedAtom_eq_normalizedResidueHilbert d hd⟩

theorem hilbertNormalizedAtom_mem_span (A : Set ℕ) {d : ℕ} (hd : d ∈ A) :
    hilbertNormalizedAtom d ∈ hilbertNormalizedAtomSpan A :=
  Submodule.subset_span ⟨d, hd, rfl⟩

/-- Dilation of every finite legal linear combination lies in the literal
enlarged-conductor span. This discharges the hierarchy's dilated legality input. -/
theorem hilbertUnscaledDilationContinuous_atomSpan (m : ℕ) (hm : 0 < m)
    (A : Set ℕ) {f : ThresholdHilbert} (hf : f ∈ hilbertNormalizedAtomSpan A) :
    hilbertUnscaledDilationContinuous m hm f ∈
      hilbertNormalizedAtomSpan (insert m ((fun d => m * d) '' A)) := by
  let S := hilbertNormalizedAtomSpan (insert m ((fun d => m * d) '' A))
  have hspan : hilbertNormalizedAtomSpan A ≤
      S.comap (hilbertUnscaledDilationContinuous m hm).toLinearMap := by
    apply Submodule.span_le.mpr
    rintro f ⟨d, hd, rfl⟩
    change hilbertUnscaledDilationContinuous m hm (hilbertNormalizedAtom d) ∈ S
    rw [hilbertUnscaledDilationContinuous_atom]
    apply S.sub_mem
    · apply hilbertNormalizedAtom_mem_span
      exact Set.mem_insert_of_mem m ⟨d, hd, rfl⟩
    · apply S.smul_mem
      apply hilbertNormalizedAtom_mem_span
      exact Set.mem_insert m _
  exact hspan hf

instance hilbertNormalizedAtomSpan_finiteDimensional (A : Finset ℕ) :
    FiniteDimensional ℝ (hilbertNormalizedAtomSpan (A : Set ℕ)) :=
  FiniteDimensional.span_of_finite ℝ (A.finite_toSet.image hilbertNormalizedAtom)

instance hilbertNormalizedAtomSpan_completeSpace (A : Finset ℕ) :
    CompleteSpace (hilbertNormalizedAtomSpan (A : Set ℕ)) :=
  FiniteDimensional.complete ℝ (hilbertNormalizedAtomSpan (A : Set ℕ))

variable (W U : Submodule ℝ ThresholdHilbert) [CompleteSpace W] [CompleteSpace U]

/-- The pair identity for the actual physical residualized dilation has no
unproved scaling, adjoint, or projection law left as an input. -/
theorem physical_residualized_pair_identity (m : ℕ) (hm : 0 < m) (x y : W) :
    (m : ℝ) *
      ⟪residualizedDilation W U (hilbertUnscaledDilationContinuous m hm) x,
        residualizedDilation W U (hilbertUnscaledDilationContinuous m hm) y⟫_ℝ =
      ⟪x, y - compression W U (hilbertUnscaledDilationContinuous m hm) (m : ℝ) y⟫_ℝ := by
  exact residualized_pair_identity W U (hilbertUnscaledDilationContinuous m hm) (m : ℝ)
    (hilbertUnscaledDilationContinuous_inner m hm) x y

/-- Exact finite hierarchy from the literal Hilbert dilation and native source.
The old optimizer's ordinary residual orthogonality is the only residual input. -/
theorem physical_native_hierarchy_gain (m : ℕ) (hm : 0 < m)
    (r : ThresholdHilbert) (horth : ∀ z ∈ U, ⟪r, z⟫_ℝ = 0) (k : ℕ) :
    ‖r‖ ^ 2 -
      ‖residualIter
        (residualizedDilation W U (hilbertUnscaledDilationContinuous m hm))
        (compression W U (hilbertUnscaledDilationContinuous m hm) (m : ℝ))
        (m : ℝ) r (initialSource W (hilbertUnscaledDilationContinuous m hm) r) k‖ ^ 2 =
      (m : ℝ) * ∑ j ∈ Finset.range k,
        (‖sourceIter (compression W U (hilbertUnscaledDilationContinuous m hm) (m : ℝ))
            (initialSource W (hilbertUnscaledDilationContinuous m hm) r) j‖ ^ 2 +
          ⟪sourceIter (compression W U (hilbertUnscaledDilationContinuous m hm) (m : ℝ))
              (initialSource W (hilbertUnscaledDilationContinuous m hm) r) j,
            compression W U (hilbertUnscaledDilationContinuous m hm) (m : ℝ)
              (sourceIter (compression W U (hilbertUnscaledDilationContinuous m hm) (m : ℝ))
                (initialSource W (hilbertUnscaledDilationContinuous m hm) r) j)⟫_ℝ) := by
  exact native_hierarchy_gain W U (hilbertUnscaledDilationContinuous m hm) (m : ℝ) r
    (hilbertUnscaledDilationContinuous_inner m hm) horth k

end
end RiemannResearch.RH.Pareto
