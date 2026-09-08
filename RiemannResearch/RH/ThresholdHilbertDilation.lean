import RiemannResearch.RH.ThresholdHilbertSpace
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# Bounded all-integer dilations of the actual weighted Hilbert space

Source: Christian Noack, RH_Two_Seed_Threshold.tex, September 8, 2026,
Lemma 2.1 and Section 11.2. This bundles the previously proved complete
weighted sums into bounded linear operators with genuine Hilbert adjoints.
Every positive integer is admitted. No approximation or RH input is used.
-/
namespace RiemannResearch.RH.Pareto
noncomputable section

@[simp] theorem hilbertSequence_add (f g : ThresholdHilbert) :
    hilbertSequence (f+g) = hilbertSequence f + hilbertSequence g :=
  hilbertSequenceLinear.map_add f g

@[simp] theorem hilbertSequence_smul (c : ℝ) (f : ThresholdHilbert) :
    hilbertSequence (c • f) = c • hilbertSequence f :=
  hilbertSequenceLinear.map_smul c f

def hilbertDilation (m : ℕ) (hm : 0 < m) (f : ThresholdHilbert) : ThresholdHilbert :=
  sequenceHilbert (dilation m (hilbertSequence f))
    (weighted_square_dilation_summable (hilbertSequence_square_summable f) m hm)

@[simp] theorem hilbertDilation_sequence (m : ℕ) (hm : 0 < m) (f : ThresholdHilbert) :
    hilbertSequence (hilbertDilation m hm f) = dilation m (hilbertSequence f) := by
  apply hilbertSequence_sequenceHilbert
  simp [dilation]

def hilbertDilationLinear (m : ℕ) (hm : 0 < m) : ThresholdHilbert →ₗ[ℝ] ThresholdHilbert where
  toFun := hilbertDilation m hm
  map_add' f g := by
    apply hilbertSequence_injective
    simp only [hilbertDilation_sequence, hilbertSequence_add]
    exact dilation_add m (hilbertSequence f) (hilbertSequence g)
  map_smul' c f := by
    apply hilbertSequence_injective
    simp only [hilbertDilation_sequence, hilbertSequence_smul]
    exact dilation_smul m c (hilbertSequence f)

/-- Exact squared norm on every vector of H. -/
theorem hilbertDilation_norm_sq (m : ℕ) (hm : 0 < m) (f : ThresholdHilbert) :
    ‖hilbertDilation m hm f‖^2 = (m : ℝ) * ‖f‖^2 := by
  rw [hilbert_norm_weighted_sq, hilbertDilation_sequence, hilbert_norm_weighted_sq]
  exact weighted_square_dilation (hilbertSequence_square_summable f)
    (hilbertSequence_zero f) m hm

theorem hilbertDilation_norm (m : ℕ) (hm : 0 < m) (f : ThresholdHilbert) :
    ‖hilbertDilation m hm f‖ = Real.sqrt m * ‖f‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
  rw [hilbertDilation_norm_sq, mul_pow, Real.sq_sqrt (Nat.cast_nonneg m)]

/-- Bounded scaled dilation T_m with its actual norm bound sqrt(m). -/
def hilbertDilationContinuous (m : ℕ) (hm : 0 < m) :
    ThresholdHilbert →L[ℝ] ThresholdHilbert :=
  (hilbertDilationLinear m hm).mkContinuous (Real.sqrt m) (fun f => by
    exact le_of_eq (hilbertDilation_norm m hm f))

@[simp] theorem hilbertDilationContinuous_apply (m : ℕ) (hm : 0 < m)
    (f : ThresholdHilbert) : hilbertDilationContinuous m hm f = hilbertDilation m hm f := rfl

theorem hilbertDilation_comp (m n : ℕ) (hm : 0 < m) (hn : 0 < n)
    (f : ThresholdHilbert) :
    hilbertDilation m hm (hilbertDilation n hn f) =
      hilbertDilation (m*n) (Nat.mul_pos hm hn) f := by
  apply hilbertSequence_injective
  simp only [hilbertDilation_sequence]
  exact dilation_comp m n (hilbertSequence f)

theorem hilbertDilation_one (f : ThresholdHilbert) :
    hilbertDilation 1 Nat.zero_lt_one f = f := by
  apply hilbertSequence_injective
  rw [hilbertDilation_sequence, dilation_one]

/-- The Hilbert adjoint is an actual bounded operator, not an assumed provider. -/
def hilbertDilationAdjoint (m : ℕ) (hm : 0 < m) :
    ThresholdHilbert →L[ℝ] ThresholdHilbert :=
  (hilbertDilationContinuous m hm).adjoint


/-- The normalized weighted dilation is an actual linear isometry. -/
def hilbertNormalizedDilation (m : ℕ) (hm : 0 < m) :
    ThresholdHilbert →ₗᵢ[ℝ] ThresholdHilbert where
  toLinearMap := (1 / Real.sqrt (m : ℝ)) • hilbertDilationLinear m hm
  norm_map' f := by
    change ‖(1 / Real.sqrt (m : ℝ)) • hilbertDilation m hm f‖ = ‖f‖
    rw [norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (by positivity : 0 ≤ 1 / Real.sqrt (m : ℝ)), hilbertDilation_norm]
    have hn : Real.sqrt (m : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by exact_mod_cast hm))
    field_simp

/-- Complete mean preservation now stated for bundled Hilbert vectors. -/
theorem hilbertDilation_mean (m : ℕ) (hm : 0 < m) (f : ThresholdHilbert) :
    paretoMean (hilbertSequence (hilbertDilation m hm f)) =
      paretoMean (hilbertSequence f) := by
  rw [hilbertDilation_sequence]
  exact paretoMean_dilation_of_square (hilbertSequence_square_summable f)
    (hilbertSequence_zero f) m hm

end
end RiemannResearch.RH.Pareto
