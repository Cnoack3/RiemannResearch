import RiemannResearch.Analysis.FrequencyCutoffMatrix
import RiemannResearch.RH.ResidueOrthonormalCoordinates
import RiemannResearch.RH.MellinCriticalPoint

/-!
# Actual residue-mode frequency regularizations

Source: user-provided Hilbert--Polya discussion, 2026-09-20. The matrices
below use actual Mellin integrals of the actual residue Gram--Schmidt modes.
Boundedness of every finite arithmetic combination gives continuity of each
mode transform and convergence of every compact-cutoff entry integral.
Their Hermitian symmetry and real spectrum are unconditional. No spectral
identification with Xi, convergence of spectral determinants, or limiting
unbounded operator is asserted.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace RiemannResearch.RH.Pareto.MellinFrequency
open CoefficientStabilization
open RiemannResearch.Analysis.FiniteHilbertGram

private theorem residueAtom_sequence_abs_le_one (i k : ℕ) :
    |hilbertSequence (residueAtom i) k| ≤ 1 := by
  rw [residueAtom, normalizedResidueHilbert_sequence]
  unfold ArithmeticCumulative.residueFraction
  rw [abs_of_nonneg (by positivity)]
  apply (div_le_one (by positivity : (0 : ℝ) < ((i + 2 : ℕ) : ℝ))).mpr
  exact_mod_cast (Nat.le_of_lt (Nat.mod_lt k (by omega : 0 < i + 2)))

theorem finiteSpace_sequence_bounded (n : ℕ) (f : ThresholdHilbert)
    (hf : f ∈ finiteSpace n) :
    ∃ C : ℝ, ∀ k, |hilbertSequence f k| ≤ C := by
  obtain ⟨a, ha⟩ := finiteSpace_expansion n f hf
  refine ⟨∑ i : Fin n, |a i|, ?_⟩
  intro k
  rw [ha]
  change |hilbertSequenceLinear (∑ i : Fin n, a i • residueAtom i.val) k| ≤ _
  simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro i hi
  rw [abs_mul]
  change |a i| * |hilbertSequence (residueAtom i.val) k| ≤ |a i|
  simpa using mul_le_mul_of_nonneg_left
    (residueAtom_sequence_abs_le_one i.val k) (abs_nonneg (a i))

theorem residueMode_sequence_bounded (j : ℕ) :
    ∃ C : ℝ, ∀ k, |hilbertSequence (residueMode j) k| ≤ C := by
  apply finiteSpace_sequence_bounded (j + 1)
  rw [← residueMode_finiteSpace (j + 1)]
  exact Submodule.subset_span ⟨⟨j, Nat.lt_succ_self j⟩, rfl⟩

def modeFeature (j : ℕ) (t : ℝ) : ℂ :=
  paretoMellin (residueMode j) (criticalPoint t)

theorem modeFeature_continuous (j : ℕ) : Continuous (modeFeature j) := by
  obtain ⟨C, hC⟩ := residueMode_sequence_bounded j
  have hcrit : Continuous criticalPoint :=
    continuous_const.add (Complex.continuous_ofReal.mul continuous_const)
  apply continuous_iff_continuousAt.mpr
  intro t
  exact (paretoMellin_differentiableAt_of_bounded (residueMode j) hC
    (criticalPoint t) (by simp)).continuousAt.comp hcrit.continuousAt

def regularization (n : ℕ) (R : ℝ) : Matrix (Fin n) (Fin n) ℂ :=
  Analysis.FrequencyCutoff.matrix (fun i : Fin n => modeFeature i.val) R

theorem regularization_entry_integrable (n : ℕ) (R : ℝ) (i j : Fin n) :
    IntegrableOn (fun t => ((t / (2 * Real.pi) : ℝ) : ℂ) *
      star (modeFeature i.val t) * modeFeature j.val t) (Set.Icc (-R) R) :=
  Analysis.FrequencyCutoff.entry_integrable _
    (fun i : Fin n => modeFeature_continuous i.val) R i j

theorem regularization_isHermitian (n : ℕ) (R : ℝ) :
    (regularization n R).IsHermitian :=
  Analysis.FrequencyCutoff.matrix_isHermitian _ R

theorem regularization_spectrum_im_eq_zero (n : ℕ) (R : ℝ) {z : ℂ}
    (hz : z ∈ spectrum ℂ (regularization n R)) : z.im = 0 :=
  Analysis.FrequencyCutoff.spectrum_im_eq_zero _ R hz

end RiemannResearch.RH.Pareto.MellinFrequency
