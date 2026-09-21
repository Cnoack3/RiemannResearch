import RiemannResearch.RH.FirstCoordinateTailGap
import Mathlib.Analysis.Complex.Basic

/-!
# Genuine complexification of the sharp signed tail bound

Source: user-provided real/imaginary splitting argument. Complex vectors are
actual elements of complex `lp` at exponent two, in the same weighted physical
coordinate realization as `ThresholdHilbert`. No positive coercivity constant
is assumed except where `UniformTailCoercivity` is an explicit hypothesis.
-/

noncomputable section
open scoped BigOperators

namespace RiemannResearch.RH.Pareto

/-- The actual complex Hilbert space, with Pareto weights absorbed into its
coordinates exactly as for the existing real `ThresholdHilbert`. -/
abbrev ComplexThresholdHilbert := lp (fun _ : ℕ => ℂ) 2

private theorem complex_norm_sq_parts (z : ℂ) :
    ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  ring

/-- The genuine complex vector with prescribed real and imaginary parts. -/
def complexHilbertOfParts (f g : ThresholdHilbert) : ComplexThresholdHilbert :=
  ⟨fun k => (f k : ℂ) + (g k : ℂ) * Complex.I, by
    apply (memℓp_gen_iff (show 0 < (2 : ENNReal).toReal by norm_num)).2
    simpa only [ENNReal.toReal_ofNat, Real.rpow_two,
      complex_norm_sq_parts, Complex.add_re, Complex.ofReal_re,
      Complex.mul_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
      Complex.add_im, Complex.mul_im, mul_zero, zero_mul, mul_one,
      sub_zero, add_zero, zero_add] using
      (hilbert_coordinate_square_summable f).add
        (hilbert_coordinate_square_summable g)⟩

@[simp] theorem complexHilbertOfParts_apply (f g : ThresholdHilbert) (k : ℕ) :
    complexHilbertOfParts f g k = (f k : ℂ) + (g k : ℂ) * Complex.I := rfl

/-- Real isometric embedding into the genuine complex Hilbert space. -/
def realHilbertComplexify (f : ThresholdHilbert) : ComplexThresholdHilbert :=
  complexHilbertOfParts f 0

@[simp] theorem realHilbertComplexify_apply (f : ThresholdHilbert) (k : ℕ) :
    realHilbertComplexify f k = (f k : ℂ) := by
  simp [realHilbertComplexify]

theorem complexHilbert_norm_sq (f : ComplexThresholdHilbert) :
    ‖f‖ ^ 2 = ∑' k, ‖f k‖ ^ 2 := by
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
    lp.norm_rpow_eq_tsum (show 0 < (2 : ENNReal).toReal by norm_num) f

theorem complexHilbertOfParts_norm_sq (f g : ThresholdHilbert) :
    ‖complexHilbertOfParts f g‖ ^ 2 = ‖f‖ ^ 2 + ‖g‖ ^ 2 := by
  calc
    _ = ∑' k, ((f k) ^ 2 + (g k) ^ 2) := by
      rw [complexHilbert_norm_sq]
      apply tsum_congr
      intro k
      simp [complex_norm_sq_parts]
    _ = ‖f‖ ^ 2 + ‖g‖ ^ 2 := by
      rw [(hilbert_coordinate_square_summable f).tsum_add
        (hilbert_coordinate_square_summable g),
        ← hilbert_norm_sq f, ← hilbert_norm_sq g]

/-- Physical positive coordinates of the complex weighted space. -/
def complexHilbertSequence (f : ComplexThresholdHilbert) : ℕ → ℂ
  | 0 => 0
  | k + 1 => f k / (Real.sqrt (paretoWeight k) : ℂ)

theorem complexHilbertSequence_weighted_square
    (f : ComplexThresholdHilbert) (k : ℕ) :
    positiveWeight (k + 1) * ‖complexHilbertSequence f (k + 1)‖ ^ 2 =
      ‖f k‖ ^ 2 := by
  rw [complexHilbertSequence, positiveWeight_succ, norm_div, div_pow,
    Complex.norm_real, Real.norm_eq_abs, sq_abs,
    Real.sq_sqrt (paretoWeight_pos k).le]
  field_simp [ne_of_gt (paretoWeight_pos k)]

theorem complexHilbertSequence_square_summable (f : ComplexThresholdHilbert) :
    Summable (fun k => positiveWeight k * ‖complexHilbertSequence f k‖ ^ 2) := by
  apply (summable_nat_add_iff 1).mp
  simp_rw [complexHilbertSequence_weighted_square]
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using
    Memℓp.summable (show 0 < (2 : ENNReal).toReal by norm_num) f.property

theorem complexHilbert_norm_weighted_sq (f : ComplexThresholdHilbert) :
    ‖f‖ ^ 2 = ∑' k, positiveWeight k * ‖complexHilbertSequence f k‖ ^ 2 := by
  calc
    _ = ∑' k, ‖f k‖ ^ 2 := complexHilbert_norm_sq f
    _ = ∑' k, positiveWeight (k + 1) *
        ‖complexHilbertSequence f (k + 1)‖ ^ 2 := by
      simp_rw [complexHilbertSequence_weighted_square]
    _ = _ := by
      rw [(complexHilbertSequence_square_summable f).tsum_eq_zero_add]
      simp [complexHilbertSequence]

namespace CoefficientStabilization.TailCapacity

/-- Actual complex linear combination of the same complete tail atoms. -/
def complexTailCombination (n : ℕ) (c : Fin n → ℂ) : ComplexThresholdHilbert :=
  Fintype.linearCombination ℂ
    (fun i : Fin n => realHilbertComplexify (tailAtom i.val)) c

def complexReciprocalSource (n : ℕ) (c : Fin n → ℂ) : ℂ :=
  ∑ i, c i * (reciprocalSource n i : ℂ)

theorem complexTailCombination_eq_parts (n : ℕ) (c : Fin n → ℂ) :
    complexTailCombination n c = complexHilbertOfParts
      (Fintype.linearCombination ℝ (fun i : Fin n => tailAtom i.val)
        (fun i => (c i).re))
      (Fintype.linearCombination ℝ (fun i : Fin n => tailAtom i.val)
        (fun i => (c i).im)) := by
  apply lp.ext
  funext k
  simp only [complexTailCombination, Fintype.linearCombination_apply,
    lp.coeFn_sum, lp.coeFn_smul, Finset.sum_apply, Pi.smul_apply,
    complexHilbertOfParts_apply, realHilbertComplexify_apply,
    smul_eq_mul]
  apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im]

/-- Exact norm decomposition, retaining every signed Gram cross term. -/
theorem complexTailCombination_norm_sq (n : ℕ) (c : Fin n → ℂ) :
    ‖complexTailCombination n c‖ ^ 2 =
      ‖Fintype.linearCombination ℝ (fun i : Fin n => tailAtom i.val)
        (fun i => (c i).re)‖ ^ 2 +
      ‖Fintype.linearCombination ℝ (fun i : Fin n => tailAtom i.val)
        (fun i => (c i).im)‖ ^ 2 := by
  rw [complexTailCombination_eq_parts, complexHilbertOfParts_norm_sq]

theorem complexReciprocalSource_norm_sq (n : ℕ) (c : Fin n → ℂ) :
    ‖complexReciprocalSource n c‖ ^ 2 =
      (∑ i, (c i).re * reciprocalSource n i) ^ 2 +
      (∑ i, (c i).im * reciprocalSource n i) ^ 2 := by
  simp [complex_norm_sq_parts, complexReciprocalSource,
    Complex.mul_re, Complex.mul_im]

/-- Complexification preserves each coercivity constant exactly. -/
theorem complex_tail_bound_iff_real (ε : ℝ) :
    (∀ (n : ℕ) (c : Fin n → ℂ),
      ε * ‖complexReciprocalSource n c‖ ^ 2 ≤ ‖complexTailCombination n c‖ ^ 2) ↔
    (∀ (n : ℕ) (c : Fin n → ℝ),
      ε * (∑ i, c i * reciprocalSource n i) ^ 2 ≤
        ‖Fintype.linearCombination ℝ (fun i : Fin n => tailAtom i.val) c‖ ^ 2) := by
  constructor
  · intro h n c
    have h' := h n (fun i => (c i : ℂ))
    simpa [complexTailCombination_norm_sq, complexReciprocalSource_norm_sq,
      Fintype.linearCombination_apply] using h'
  · intro h n c
    rw [complexTailCombination_norm_sq, complexReciprocalSource_norm_sq, mul_add]
    exact add_le_add (h n (fun i => (c i).re)) (h n (fun i => (c i).im))

def ComplexUniformTailCoercivity : Prop :=
  ∃ ε : ℝ, 0 < ε ∧ ∀ (n : ℕ) (c : Fin n → ℂ),
    ε * ‖complexReciprocalSource n c‖ ^ 2 ≤ ‖complexTailCombination n c‖ ^ 2

theorem complexUniformTailCoercivity_iff_real :
    ComplexUniformTailCoercivity ↔ UniformTailCoercivity := by
  simp only [ComplexUniformTailCoercivity, UniformTailCoercivity,
    complex_tail_bound_iff_real]

/-- The same sharp infimum controls every complex finite coefficient vector. -/
theorem firstCoordinateTailGap_controls_complex (n : ℕ) (c : Fin n → ℂ) :
    firstCoordinateTailGap * ‖complexReciprocalSource n c‖ ^ 2 ≤
      ‖complexTailCombination n c‖ ^ 2 :=
  (complex_tail_bound_iff_real firstCoordinateTailGap).mpr
    firstCoordinateTailGap_controls_all n c

/-- No larger constant is valid on the complexified arithmetic dictionary. -/
theorem complex_uniform_tail_constant_le_gap (ε : ℝ)
    (h : ∀ (n : ℕ) (c : Fin n → ℂ),
      ε * ‖complexReciprocalSource n c‖ ^ 2 ≤ ‖complexTailCombination n c‖ ^ 2) :
    ε ≤ firstCoordinateTailGap :=
  uniform_tail_constant_le_gap ε ((complex_tail_bound_iff_real ε).mp h)

theorem firstCoordinateTailGap_pos_iff_complex_coercivity :
    0 < firstCoordinateTailGap ↔ ComplexUniformTailCoercivity :=
  firstCoordinateTailGap_pos_iff_coercivity.trans
    complexUniformTailCoercivity_iff_real.symm

end CoefficientStabilization.TailCapacity
end RiemannResearch.RH.Pareto
