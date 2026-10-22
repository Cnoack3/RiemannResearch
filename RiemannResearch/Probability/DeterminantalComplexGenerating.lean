import RiemannResearch.Probability.FiniteDeterminantalGenerating
import RiemannResearch.Probability.DeterminantalWindow
import RiemannResearch.Probability.ContinuousProjectionCompression
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Misc
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic.Ring

/-!
# Complex generating functions and positive feature determinants

Source: user-provided Q-basis/DPP/Hilbert--Polya discussion, 13 October 2026.
The row-multilinearity argument extends the existing real finite-law generating
identity to complex parameters, keeping the actual probability weights real.
Finite windows of arbitrary countable DPPs are included. An infinite
multiplicative statistic and its identification with Xi are separate obligations.
-/

noncomputable section
open Matrix MeasureTheory
open scoped BigOperators Classical ComplexOrder

namespace RiemannResearch.Probability.DPP
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem sum_exactWeight_generating_complex (K : Matrix ι ι ℝ) (w : ι → ℂ) :
    (∑ S : Finset ι,
      (∏ i : ι, if i ∈ S then w i else 1) * (exactWeight K S : ℂ)) =
      (Matrix.diagonal w * K.map (fun x : ℝ => (x : ℂ)) +
        (1 - K.map (fun x : ℝ => (x : ℂ)))).det := by
  let Kc : Matrix ι ι ℂ := K.map (fun x : ℝ => (x : ℂ))
  let A := Matrix.diagonal w * Kc
  let B : Matrix ι ι ℂ := 1 - Kc
  have hterm (S : Finset ι) :
      Matrix.det (Matrix.of (S.piecewise A.row B.row)) =
        (∏ i : ι, if i ∈ S then w i else 1) * (exactWeight K S : ℂ) := by
    have he : Matrix.of (S.piecewise A.row B.row) =
        Matrix.diagonal (fun i => if i ∈ S then w i else 1) *
          (mixedRows K S).map (fun x : ℝ => (x : ℂ)) := by
      ext i j
      by_cases hi : i ∈ S <;>
        simp [A, B, Kc, mixedRows, Finset.piecewise, Matrix.diagonal_mul,
          Matrix.one_apply, hi] <;>
        by_cases hij : i = j <;> simp [hij]
    rw [he, Matrix.det_mul, Matrix.det_diagonal]
    congr 1
    exact (Complex.ofRealHom.map_det (mixedRows K S)).symm
  have h := (Matrix.detRowAlternating (R := ℂ) (n := ι)).map_add_univ A.row B.row
  change Matrix.det (A + B) =
    ∑ S : Finset ι, Matrix.det (Matrix.of (S.piecewise A.row B.row)) at h
  calc
    _ = ∑ S : Finset ι, Matrix.det (Matrix.of (S.piecewise A.row B.row)) := by
      apply Finset.sum_congr rfl
      intro S hS
      exact (hterm S).symm
    _ = (A + B).det := h.symm
    _ = _ := rfl

/-- Orthonormal columns give a genuine finite determinantal probability law. -/
theorem orthonormalFeature_exactWeight_nonneg {κ : Type*} [Fintype κ] [DecidableEq κ]
    (A : Matrix ι κ ℝ)
    (hA : A.transpose * A = 1) (S : Finset ι) :
    0 ≤ exactWeight (A * A.transpose) S := by
  have ha : A.conjTranspose = A.transpose := by
    ext i j
    simp [Matrix.conjTranspose_apply]
  have hk : (A * A.transpose).PosSemidef := by
    simpa only [ha] using Matrix.posSemidef_self_mul_conjTranspose A
  have hkk : (A * A.transpose) * (A * A.transpose) = A * A.transpose := by
    calc
      _ = A * (A.transpose * A) * A.transpose := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [hA, Matrix.mul_one]
  have hc : (1 - A * A.transpose).conjTranspose = 1 - A * A.transpose := by
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, hk.isHermitian]
  have hcc : (1 - A * A.transpose) * (1 - A * A.transpose) =
      1 - A * A.transpose := by
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one,
      hkk, sub_self, sub_zero]
  have hi : (1 - A * A.transpose).PosSemidef := by
    have h := Matrix.posSemidef_self_mul_conjTranspose (1 - A * A.transpose)
    rwa [hc, hcc] at h
  exact exactWeight_nonneg _ hk hi S


/-- Complex multiplicative expectation under the actual finite DPP PMF. -/
theorem finiteLaw_generating_complex (K : Matrix ι ι ℝ)
    (hpos : ∀ S, 0 ≤ exactWeight K S) (w : ι → ℂ) :
    (∑ S : Finset ι,
      (∏ i : ι, if i ∈ S then w i else 1) *
        (((finiteLaw K hpos) S).toReal : ℂ)) =
      (Matrix.diagonal w * K.map (fun x : ℝ => (x : ℂ)) +
        (1 - K.map (fun x : ℝ => (x : ℂ)))).det := by
  have hp (S : Finset ι) : ((finiteLaw K hpos) S).toReal = exactWeight K S := by
    change (ENNReal.ofReal (exactWeight K S)).toReal = _
    exact ENNReal.toReal_ofReal (hpos S)
  simp_rw [hp]
  exact sum_exactWeight_generating_complex K w

section FiniteLaw
variable [MeasurableSpace (Finset ι)] [MeasurableSingletonClass (Finset ι)]

theorem finiteLaw_generating_integral_complex (K : Matrix ι ι ℝ)
    (hpos : ∀ S, 0 ≤ exactWeight K S) (w : ι → ℂ) :
    (∫ S, ∏ i : ι, if i ∈ S then w i else 1 ∂(finiteLaw K hpos).toMeasure) =
      (Matrix.diagonal w * K.map (fun x : ℝ => (x : ℂ)) +
        (1 - K.map (fun x : ℝ => (x : ℂ)))).det := by
  rw [PMF.integral_eq_sum]
  calc
    _ = ∑ S : Finset ι, (∏ i : ι, if i ∈ S then w i else 1) *
        (((finiteLaw K hpos) S).toReal : ℂ) := by
      apply Finset.sum_congr rfl
      intro S hS
      rw [Algebra.smul_def]
      change (((finiteLaw K hpos) S).toReal : ℂ) *
        (∏ i : ι, if i ∈ S then w i else 1) = _
      exact mul_comm _ _
    _ = _ := finiteLaw_generating_complex K hpos w
end FiniteLaw

theorem finiteBoolLaw_generating_integral_complex (K : Matrix ι ι ℝ)
    (hpos : ∀ S, 0 ≤ exactWeight K S) (w : ι → ℂ) :
    (∫ x, ∏ i : ι, if x i = true then w i else 1 ∂(finiteBoolLaw K hpos).toMeasure) =
      (Matrix.diagonal w * K.map (fun x : ℝ => (x : ℂ)) +
        (1 - K.map (fun x : ℝ => (x : ℂ)))).det := by
  letI : MeasurableSpace (Finset ι) := ⊤
  let b : Finset ι → (ι → Bool) := fun S i => decide (i ∈ S)
  let F : (ι → Bool) → ℂ := fun x => ∏ i : ι, if x i = true then w i else 1
  have hb : Measurable b := measurable_of_finite b
  have hF : Measurable F := measurable_of_finite F
  change (∫ x, F x ∂((finiteLaw K hpos).map b).toMeasure) = _
  rw [← PMF.toMeasure_map b (finiteLaw K hpos) hb]
  rw [integral_map hb.aemeasurable hF.aestronglyMeasurable]
  simpa [F, b] using finiteLaw_generating_integral_complex K hpos w

/-- Complex finite-window generating identity for an actual DPP law. -/
theorem IsDPP.window_generating_complex
    {α Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {X : Ω → Set α} {K : α → α → ℝ} (h : IsDPP μ X K) (e : ι ↪ α)
    (hpos : ∀ S, 0 ≤ exactWeight (Matrix.of (fun i j : ι => K (e i) (e j))) S)
    (w : ι → ℂ) :
    (∫ ω, ∏ i : ι, if e i ∈ X ω then w i else 1 ∂μ) =
      (Matrix.diagonal w *
        (Matrix.of (fun i j : ι => K (e i) (e j))).map (fun x : ℝ => (x : ℂ)) +
        (1 - (Matrix.of (fun i j : ι => K (e i) (e j))).map
          (fun x : ℝ => (x : ℂ)))).det := by
  let r : Ω → (ι → Bool) := fun ω i => decide (e i ∈ X ω)
  let F : (ι → Bool) → ℂ := fun x => ∏ i : ι, if x i = true then w i else 1
  have hr : Measurable r := by
    apply measurable_pi_lambda
    intro i
    change Measurable (({ω | e i ∈ X ω} : Set Ω).piecewise
      (fun _ => true) (fun _ => false))
    exact measurable_const.piecewise (h.measurable_occupancy (e i)) measurable_const
  have hF : Measurable F := measurable_of_finite F
  have hp := finiteBoolLaw_generating_integral_complex
    (Matrix.of (fun i j : ι => K (e i) (e j))) hpos w
  rw [← h.finite_restriction_law e hpos] at hp
  change (∫ x, F x ∂μ.map r) = _ at hp
  rw [integral_map hr.aemeasurable hF.aestronglyMeasurable] at hp
  simpa [F, r] using hp
end RiemannResearch.Probability.DPP

namespace Matrix
variable {ι κ : Type*} [Fintype ι] [Fintype κ]
  [DecidableEq ι] [DecidableEq κ]

/-- Complex feature compression of multiplication by a real site weight. -/
def weightedComplexFeatureGram (A : Matrix ι κ ℂ) (v : ι → ℝ) : Matrix κ κ ℂ :=
  A.conjTranspose * Matrix.diagonal (fun i => (v i : ℂ)) * A

theorem weightedComplexFeatureGram_posSemidef (A : Matrix ι κ ℂ)
    (v : ι → ℝ) (hv : ∀ i, 0 ≤ v i) :
    (weightedComplexFeatureGram A v).PosSemidef := by
  have hd : (Matrix.diagonal (fun i => (v i : ℂ))).PosSemidef := by
    apply Matrix.PosSemidef.diagonal
    intro i
    exact RCLike.nonneg_iff.mpr ⟨by simpa using hv i, by simp⟩
  exact hd.conjTranspose_mul_mul_same A

/-- Exact complex determinant ratio, retaining the original Gram matrix. -/
theorem weightedComplexFeature_determinant_ratio (A : Matrix ι κ ℂ)
    (G : Matrix κ κ ℂ) (hG : IsUnit G.det) (v : ι → ℝ) (t : ℂ) :
    (1 - Matrix.diagonal (fun i => t * (v i : ℂ)) *
      (A * G⁻¹ * A.conjTranspose)).det =
      (G - t • weightedComplexFeatureGram A v).det / G.det := by
  let D : Matrix ι ι ℂ := Matrix.diagonal (fun i => t * (v i : ℂ))
  have hd : D = t • Matrix.diagonal (fun i => (v i : ℂ)) := by
    ext i j
    by_cases hij : i = j
    · subst j
      simp [D]
    · simp [D, Matrix.diagonal, hij]
  have hgram : A.conjTranspose * (D * A) = t • weightedComplexFeatureGram A v := by
    rw [← Matrix.mul_assoc, hd, Matrix.mul_smul, Matrix.smul_mul]
    rfl
  have hdet : (G - A.conjTranspose * (D * A)).det =
      G.det * (1 - (D * A) * G⁻¹ * A.conjTranspose).det := by
    simpa only [sub_eq_add_neg, Matrix.neg_mul, Matrix.mul_neg] using
      (Matrix.det_add_mul (-A.conjTranspose) (D * A) hG)
  have hratio : (G - A.conjTranspose * (D * A)).det / G.det =
      (1 - (D * A) * G⁻¹ * A.conjTranspose).det := by
    rw [hdet]
    exact mul_div_cancel_left₀ _ (isUnit_iff_ne_zero.mp hG)
  rw [hgram] at hratio
  simpa only [D, Matrix.mul_assoc] using hratio.symm
end Matrix

namespace RiemannResearch.Probability.DPP
variable {ι κ : Type*} [Fintype ι] [Fintype κ]
  [DecidableEq ι] [DecidableEq κ]

theorem finiteLaw_weighted_square_gram_ratio_complex (K : Matrix ι ι ℝ)
    (hpos : ∀ S, 0 ≤ exactWeight K S)
    (A : Matrix ι κ ℂ) (G : Matrix κ κ ℂ) (hG : IsUnit G.det)
    (hK : K.map (fun x : ℝ => (x : ℂ)) = A * G⁻¹ * A.conjTranspose)
    (v : ι → ℝ) (z : ℂ) :
    (∑ S : Finset ι,
      (∏ i : ι, if i ∈ S then 1 - z ^ 2 * (v i : ℂ) else 1) *
        (((finiteLaw K hpos) S).toReal : ℂ)) =
      (G - z ^ 2 • Matrix.weightedComplexFeatureGram A v).det / G.det := by
  rw [finiteLaw_generating_complex]
  have hm : Matrix.diagonal (fun i => 1 - z ^ 2 * (v i : ℂ)) *
        K.map (fun x : ℝ => (x : ℂ)) +
        (1 - K.map (fun x : ℝ => (x : ℂ))) =
      1 - Matrix.diagonal (fun i => z ^ 2 * (v i : ℂ)) *
        K.map (fun x : ℝ => (x : ℂ)) := by
    ext i j
    simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.diagonal_mul]
    ring
  rw [hm, hK]
  exact Matrix.weightedComplexFeature_determinant_ratio A G hG v (z ^ 2)

theorem finiteLaw_weighted_square_feature_determinant_complex (K : Matrix ι ι ℝ)
    (hpos : ∀ S, 0 ≤ exactWeight K S) (A : Matrix ι κ ℂ)
    (hK : K.map (fun x : ℝ => (x : ℂ)) = A * A.conjTranspose)
    (v : ι → ℝ) (z : ℂ) :
    (∑ S : Finset ι,
      (∏ i : ι, if i ∈ S then 1 - z ^ 2 * (v i : ℂ) else 1) *
        (((finiteLaw K hpos) S).toReal : ℂ)) =
      (1 - z ^ 2 • Matrix.weightedComplexFeatureGram A v).det := by
  have hK' : K.map (fun x : ℝ => (x : ℂ)) =
      A * (1 : Matrix κ κ ℂ)⁻¹ * A.conjTranspose := by
    simpa using hK
  have h := finiteLaw_weighted_square_gram_ratio_complex K hpos A
    (1 : Matrix κ κ ℂ) (by simp) hK' v z
  simpa using h

theorem finiteLaw_weighted_square_spectral_complex (K : Matrix ι ι ℝ)
    (hpos : ∀ S, 0 ≤ exactWeight K S) (A : Matrix ι κ ℂ)
    (hK : K.map (fun x : ℝ => (x : ℂ)) = A * A.conjTranspose)
    (v : ι → ℝ) (hv : ∀ i, 0 ≤ v i) (z : ℂ) :
    (∑ S : Finset ι,
      (∏ i : ι, if i ∈ S then 1 - z ^ 2 * (v i : ℂ) else 1) *
        (((finiteLaw K hpos) S).toReal : ℂ)) =
      ∏ j : κ, (1 - z ^ 2 *
        ((Matrix.weightedComplexFeatureGram_posSemidef A v hv).isHermitian.eigenvalues j : ℂ)) := by
  rw [finiteLaw_weighted_square_feature_determinant_complex K hpos A hK]
  have h := (Matrix.weightedComplexFeatureGram_posSemidef A v hv).isHermitian.det_one_add_smul_eq_prod_complex (-(z ^ 2))
  simpa only [neg_smul, sub_eq_add_neg, neg_mul] using h

/-- Real zeros of the actual complex DPP generating polynomial. -/
theorem finiteLaw_weighted_square_zero_im_eq_zero (K : Matrix ι ι ℝ)
    (hpos : ∀ S, 0 ≤ exactWeight K S) (A : Matrix ι κ ℂ)
    (hK : K.map (fun x : ℝ => (x : ℂ)) = A * A.conjTranspose)
    (v : ι → ℝ) (hv : ∀ i, 0 ≤ v i) (z : ℂ)
    (hz : (∑ S : Finset ι,
      (∏ i : ι, if i ∈ S then 1 - z ^ 2 * (v i : ℂ) else 1) *
        (((finiteLaw K hpos) S).toReal : ℂ)) = 0) : z.im = 0 := by
  rw [finiteLaw_weighted_square_feature_determinant_complex K hpos A hK] at hz
  exact (Matrix.weightedComplexFeatureGram_posSemidef A v hv).det_one_sub_sq_smul_zero_im_eq_zero z hz

end RiemannResearch.Probability.DPP
