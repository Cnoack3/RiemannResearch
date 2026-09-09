import RiemannResearch.RH.DilationWaveletAlgebra

/-!
# Equality of the complete legal and wavelet closed spaces

Source: user-provided argument `analytic_wavelet_foothold.md`, §2.
The geometric remainder is discharged for the actual weighted Hilbert norm.
The equality allows every positive integer dilation and holds for any set
of seed integers strictly greater than one. It asserts no fixed-conductor
span equality and assumes no form of RH.
-/

open scoped BigOperators
namespace RiemannResearch.RH.Pareto
noncomputable section

/-- The complete finite wavelet span, allowing every positive integer scale. -/
def hilbertWaveletSpan (A : Set ℕ) : Submodule ℝ ThresholdHilbert :=
  Submodule.span ℝ {f | ∃ a ∈ A, ∃ ha : 0 < a, ∃ m : ℕ, ∃ hm : 0 < m,
    f = dilationWaveletHilbert a m ha hm}

def hilbertWaveletClosure (A : Set ℕ) : Submodule ℝ ThresholdHilbert :=
  (hilbertWaveletSpan A).topologicalClosure

/-- Exact tails tend to zero for every fixed legal generator, with the scale
factor proved by arithmetic rather than supplied as an extra hypothesis. -/
theorem digitHilbert_wavelet_error_sq_tendsto (a m : ℕ)
    (ha : 1 < a) (hm : 0 < m) :
    Filter.Tendsto (fun N =>
      ‖digitHilbert a m (by omega) hm -
        (∑ j ∈ Finset.range N, dilationWaveletHilbert a (a^j*m) (by omega)
          (Nat.mul_pos (pow_pos (by omega) j) hm))‖^2)
      Filter.atTop (nhds 0) := by
  have haR : (1 : ℝ) < a := by exact_mod_cast ha
  have hg := tendsto_pow_atTop_nhds_zero_of_lt_one
    (show (0 : ℝ) ≤ 1 / (a : ℝ) by positivity)
    (show 1 / (a : ℝ) < 1 by exact (div_lt_one (by positivity)).2 haR)
  simpa only [digitHilbert_wavelet_error_sq, zero_mul] using
    hg.mul_const (‖digitHilbert a m (by omega) hm‖^2)

/-- The finite, actual legal wavelet expansions converge in H. -/
theorem digitHilbert_wavelet_tendsto (a m : ℕ) (ha : 1 < a) (hm : 0 < m) :
    Filter.Tendsto (fun N =>
      ∑ j ∈ Finset.range N, dilationWaveletHilbert a (a^j*m) (by omega)
        (Nat.mul_pos (pow_pos (by omega) j) hm))
      Filter.atTop (nhds (digitHilbert a m (by omega) hm)) := by
  have hs := digitHilbert_wavelet_error_sq_tendsto a m ha hm
  apply Metric.tendsto_nhds.2
  intro ε hε
  have he := hs.eventually (gt_mem_nhds (sq_pos_of_pos hε))
  filter_upwards [he] with N hN
  rw [dist_eq_norm, norm_sub_rev]
  nlinarith [norm_nonneg (digitHilbert a m (by omega) hm -
    ∑ j ∈ Finset.range N, dilationWaveletHilbert a (a^j*m) (by omega)
      (Nat.mul_pos (pow_pos (by omega) j) hm))]

theorem dilationWaveletHilbert_mem_legal (A : Set ℕ) (a m : ℕ)
    (haA : a ∈ A) (ha : 0 < a) (hm : 0 < m) :
    dilationWaveletHilbert a m ha hm ∈ hilbertLegalSubspace A := by
  change hilbertSequence (dilationWaveletHilbert a m ha hm) ∈ legalSeedSpan A
  rw [hilbertSequence_dilationWaveletHilbert, dilationWaveletSequence_generator a m ha hm]
  exact (legalSeedSpan A).sub_mem
    ((legalSeedSpan A).smul_mem _ (dilation_generator_mem A haA hm))
    ((legalSeedSpan A).smul_mem _ (dilation_generator_mem A haA (Nat.mul_pos ha hm)))

theorem digitHilbert_mem_waveletClosure (A : Set ℕ) (a m : ℕ)
    (haA : a ∈ A) (ha : 1 < a) (hm : 0 < m) :
    digitHilbert a m (by omega) hm ∈ hilbertWaveletClosure A := by
  apply (hilbertWaveletSpan A).isClosed_topologicalClosure.mem_of_tendsto
    (digitHilbert_wavelet_tendsto a m ha hm)
  apply Filter.Eventually.of_forall
  intro N
  apply (hilbertWaveletSpan A).le_topologicalClosure
  apply (hilbertWaveletSpan A).sum_mem
  intro j hj
  exact Submodule.subset_span ⟨a, haA, by omega, a^j*m,
    Nat.mul_pos (pow_pos (by omega) j) hm, rfl⟩

/-- Unconditional equality of the actual closed Hilbert spaces. -/
theorem hilbertWaveletClosure_eq_legal (A : Set ℕ) (hA : ∀ a ∈ A, 1 < a) :
    hilbertWaveletClosure A = hilbertLegalClosure A := by
  apply le_antisymm
  · apply Submodule.topologicalClosure_mono
    apply Submodule.span_le.2
    rintro f ⟨a, haA, ha, m, hm, rfl⟩
    exact dilationWaveletHilbert_mem_legal A a m haA ha hm
  · have hlegal : legalSeedSpan A ≤
        (hilbertWaveletClosure A).map hilbertSequenceLinear := by
      apply Submodule.span_le.2
      rintro f ⟨a, haA, m, hm, rfl⟩
      refine ⟨(m : ℝ) • digitHilbert a m (by have := hA a haA; omega) hm,
        (hilbertWaveletClosure A).smul_mem _
          (digitHilbert_mem_waveletClosure A a m haA (hA a haA) hm), ?_⟩
      change hilbertSequence ((m : ℝ) • digitHilbert a m _ hm) = _
      rw [hilbertSequence_smul, hilbertSequence_digitHilbert,
        digitSequence_eq_scaled_generator a m hm, smul_smul]
      have hm0 : (m : ℝ) ≠ 0 := by positivity
      simp [hm0]
    have hsub : (hilbertLegalSubspace A : Set ThresholdHilbert) ⊆
        (hilbertWaveletClosure A : Set ThresholdHilbert) := by
      intro f hf
      obtain ⟨g, hg, hgf⟩ := hlegal hf
      have he : g = f := hilbertSequence_injective hgf
      exact he ▸ hg
    exact closure_minimal hsub (hilbertWaveletSpan A).isClosed_topologicalClosure

/-- The two-seed specialization retains all positive integer scales. -/
theorem twoSeed_waveletClosure_eq_legal :
    hilbertWaveletClosure {2, 3} = hilbertLegalClosure {2, 3} := by
  apply hilbertWaveletClosure_eq_legal
  intro a ha
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
  rcases ha with rfl | rfl <;> norm_num

end
end RiemannResearch.RH.Pareto
