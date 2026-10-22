import RiemannResearch.RH.QDivisorWaveletDensity
import RiemannResearch.RH.QDivisorWaveletFactorization
import RiemannResearch.RH.QExpectationIntegral
import RiemannResearch.RH.QResidueMoments
import RiemannResearch.RH.QCovarianceInverse
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# The arithmetic Hilbert basis and full Parseval identity under Q

Source: user-provided inverse-Gram research argument. Prime-power
orthogonality supplies the exact Jordan diagonal; finite triangular
Möbius inversion supplies totality. The resulting Hilbert basis is
unconditional. Residue approximation, and hence RH, remains the separate
problem of controlling the resulting arithmetic coefficient energy.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators

namespace RiemannResearch.RH.QDivisorHilbert
open ZetaTwoHilbert ZetaTwoProbability QDivisibilityDensity

/-- The actual Hilbert Gram matrix has the full arithmetic Jordan diagonal. -/
theorem divisorWavelet_inner (r s : ℕ+) :
    inner ℝ (divisorWavelet (r : ℕ)) (divisorWavelet (s : ℕ)) =
      if r = s then qJordanTwo (r : ℕ) else 0 := by
  rw [qInner_eq_inversePowerMean]
  have hcoord :
      inversePowerMean 0
        (fun n => qSequence (divisorWavelet (r : ℕ)) n *
          qSequence (divisorWavelet (s : ℕ)) n) =
      inversePowerMean 0 (fun n => qDivisorWavelet (r : ℕ) n * qDivisorWavelet (s : ℕ) n) := by
    unfold inversePowerMean
    apply tsum_congr
    intro n
    simp only [qSequence_divisorWavelet_succ]
  rw [hcoord, inversePowerMean_zero_eq_integral _
    (Pareto.bounded_product (qDivisorWavelet_abs_le (r : ℕ))
      (qDivisorWavelet_abs_le (s : ℕ))),
    qDivisorWavelet_inner_integral (r : ℕ) (s : ℕ) (ne_of_gt r.pos) (ne_of_gt s.pos)]
  by_cases hrs : r = s
  · subst s
    simp
  · have hnat : (r : ℕ) ≠ (s : ℕ) := fun h => hrs (Subtype.ext h)
    simp [hrs, hnat]

/-- Jordan-normalized arithmetic wavelet. -/
def normalizedDivisorWavelet (r : ℕ+) : QHilbert :=
  (Real.sqrt (qJordanTwo (r : ℕ)))⁻¹ • divisorWavelet (r : ℕ)

theorem normalizedDivisorWavelet_orthonormal :
    Orthonormal ℝ normalizedDivisorWavelet := by
  rw [orthonormal_iff_ite]
  intro r s
  simp only [normalizedDivisorWavelet, real_inner_smul_left, inner_smul_right]
  rw [divisorWavelet_inner]
  by_cases h : r = s
  · subst s
    simp only [↓reduceIte]
    have hpos := qJordanTwo_pos (r : ℕ) r.pos
    have hs0 : Real.sqrt (qJordanTwo (r : ℕ)) ≠ 0 :=
      ne_of_gt (Real.sqrt_pos.mpr hpos)
    have hs := Real.sq_sqrt hpos.le
    field_simp [hs0]
    nlinarith [hs]
  · simp [h]

theorem divisorWavelet_eq_normalized_smul (r : ℕ+) :
    divisorWavelet (r : ℕ) =
      Real.sqrt (qJordanTwo (r : ℕ)) • normalizedDivisorWavelet r := by
  have hs0 : Real.sqrt (qJordanTwo (r : ℕ)) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.mpr (qJordanTwo_pos (r : ℕ) r.pos))
  simp [normalizedDivisorWavelet, smul_smul, hs0]

theorem normalizedDivisorWavelet_span_dense :
    (Submodule.span ℝ (Set.range normalizedDivisorWavelet)).topologicalClosure = ⊤ := by
  have hle :
      Submodule.span ℝ (Set.range (fun r : ℕ+ => divisorWavelet (r : ℕ))) ≤
        Submodule.span ℝ (Set.range normalizedDivisorWavelet) := by
    apply Submodule.span_le.mpr
    rintro x ⟨r, rfl⟩
    change divisorWavelet (r : ℕ) ∈ Submodule.span ℝ (Set.range normalizedDivisorWavelet)
    rw [divisorWavelet_eq_normalized_smul r]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨r, rfl⟩)
  apply le_antisymm le_top
  rw [← divisorWavelet_span_dense]
  exact Submodule.topologicalClosure_mono hle

/-- A complete orthonormal arithmetic basis for the actual Q Hilbert space. -/
def divisorHilbertBasis : HilbertBasis ℕ+ ℝ QHilbert :=
  HilbertBasis.mk normalizedDivisorWavelet_orthonormal
    (by rw [normalizedDivisorWavelet_span_dense])

@[simp] theorem divisorHilbertBasis_apply (r : ℕ+) :
    divisorHilbertBasis r = normalizedDivisorWavelet r := by
  simp only [divisorHilbertBasis, HilbertBasis.coe_mk]

/-- Full infinite Gram reconstruction; there is no discarded arithmetic tail. -/
theorem divisorWavelet_parseval_inner (f g : QHilbert) :
    (∑' r : ℕ+, inner ℝ f (divisorWavelet (r : ℕ)) *
      inner ℝ (divisorWavelet (r : ℕ)) g / qJordanTwo (r : ℕ)) = inner ℝ f g := by
  have h := divisorHilbertBasis.tsum_inner_mul_inner f g
  calc
    (∑' r : ℕ+, inner ℝ f (divisorWavelet (r : ℕ)) *
        inner ℝ (divisorWavelet (r : ℕ)) g / qJordanTwo (r : ℕ)) =
        ∑' r : ℕ+, inner ℝ f (divisorHilbertBasis r) * inner ℝ (divisorHilbertBasis r) g := by
      apply tsum_congr
      intro r
      simp only [divisorHilbertBasis_apply, normalizedDivisorWavelet,
        inner_smul_right, real_inner_smul_left]
      have hpos := qJordanTwo_pos (r : ℕ) r.pos
      have hs := Real.sq_sqrt hpos.le
      have hs0 : Real.sqrt (qJordanTwo (r : ℕ)) ≠ 0 :=
        ne_of_gt (Real.sqrt_pos.mpr hpos)
      have hprod := congrArg
        (fun x : ℝ => inner ℝ f (divisorWavelet (r : ℕ)) *
          inner ℝ (divisorWavelet (r : ℕ)) g * x) hs
      field_simp [hs0, ne_of_gt hpos]
      nlinarith [hprod]
    _ = inner ℝ f g := h

/-- Parseval's identity as an exact sum of nonnegative arithmetic energies. -/
theorem divisorWavelet_parseval_norm (f : QHilbert) :
    (∑' r : ℕ+, (inner ℝ f (divisorWavelet (r : ℕ))) ^ 2 /
      qJordanTwo (r : ℕ)) = ‖f‖ ^ 2 := by
  simpa only [real_inner_comm (divisorWavelet _) f, ← pow_two,
    real_inner_self_eq_norm_sq] using divisorWavelet_parseval_inner f f

/-- The empty prime-power mode is exactly the target constant. -/
theorem divisorWavelet_one : divisorWavelet 1 = qOne := by
  apply qSequence_injective
  funext n
  cases n with
  | zero => simp
  | succ n =>
    rw [qSequence_divisorWavelet_succ, qSequence_qOne]
    simp [qDivisorWavelet, qScaledDivisibilitySum, qOneSequence]

theorem qOne_divisorWavelet_inner (r : ℕ+) :
    inner ℝ qOne (divisorWavelet (r : ℕ)) = if r = 1 then 1 else 0 := by
  have h := divisorWavelet_inner (1 : ℕ+) r
  simpa [divisorWavelet_one, qJordanTwo, eq_comm] using h

/-- The finite Möbius differences from the residue calculation are the exact
Hilbert basis coefficients before Jordan normalization. -/
theorem qResidue_divisorWavelet_inner (d r : ℕ) :
    inner ℝ (qResidue d) (divisorWavelet r) = qResidueDivisorCoefficient d r := by
  rw [qInner_eq_inversePowerMean, qSequence_qResidue]
  calc
    inversePowerMean 0 (fun n => ArithmeticCumulative.residueFraction d n *
        qSequence (divisorWavelet r) n) =
        inversePowerMean 0 (fun n => ArithmeticCumulative.residueFraction d n *
          qDivisorWavelet r n) := by
      unfold inversePowerMean
      apply tsum_congr
      intro n
      simp only [qSequence_divisorWavelet_succ]
    _ = qResidueDivisorCoefficient d r := residue_divisor_wavelet_mean d r

/-- Exact reconstruction of every residue Gram entry in arithmetic coordinates. -/
theorem qResidue_gram_parseval (d e : ℕ) :
    (∑' r : ℕ+, qResidueDivisorCoefficient d (r : ℕ) *
      qResidueDivisorCoefficient e (r : ℕ) / qJordanTwo (r : ℕ)) =
      inner ℝ (qResidue d) (qResidue e) := by
  have hrev (r : ℕ+) : inner ℝ (divisorWavelet (r : ℕ)) (qResidue e) =
      qResidueDivisorCoefficient e (r : ℕ) := by
    rw [real_inner_comm, qResidue_divisorWavelet_inner]
  simpa only [hrev, qResidue_divisorWavelet_inner] using
      divisorWavelet_parseval_inner (qResidue d) (qResidue e)

/-- Exact arithmetic error energy, including the constant mode. The absence
of a uniform estimate for these sums is the remaining approximation problem. -/
theorem qSynthesis_error_parseval {ι : Type*} [Fintype ι]
    (d : ι → ℕ) (c : ι → ℝ) :
    (∑' r : ℕ+, ((if r = 1 then (1 : ℝ) else 0) -
      ∑ i, c i * qResidueDivisorCoefficient (d i) (r : ℕ)) ^ 2 /
        qJordanTwo (r : ℕ)) = ‖qOne - QCovarianceInverse.qSynthesis d c‖ ^ 2 := by
  have h := divisorWavelet_parseval_norm (qOne - QCovarianceInverse.qSynthesis d c)
  simpa only [inner_sub_left, qOne_divisorWavelet_inner, QCovarianceInverse.qSynthesis,
    sum_inner, real_inner_smul_left, qResidue_divisorWavelet_inner] using h

end RiemannResearch.RH.QDivisorHilbert
