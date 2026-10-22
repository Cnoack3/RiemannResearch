import RiemannResearch.RH.DerivativeCRT
import RiemannResearch.RH.WeilConverse
import RiemannResearch.RH.SmoothWeilMatrix
import RiemannResearch.Analysis.BilateralLaplaceTranslation
import RiemannResearch.Analysis.SuperexponentialTranslation

/-!
# The actual correction primitive in finite and mixed Weil forms

Source: user-directed Abel/CRT/Weil continuation, 29 September 2026.
This assembles the repository's actual smooth explicit formula and single-zero
tests. The endpoint, reflected square defect, and full signed transfer
discrepancy are retained. Every RH implication has an explicit open arithmetic
provider; no positivity or growing-sum limit exchange is assumed.
-/

noncomputable section
open scoped BigOperators ComplexConjugate



namespace RiemannResearch.RH.Pareto.CoefficientStabilization.DerivativeCompatibility

open MeasureTheory MeasureTheory.BilateralLaplace RiemannResearch.Analysis
open RiemannResearch.Analysis.SignedAbel
open RiemannResearch.RH.SignedWeilCorrelation

/-- Mellin character on the same legal conductor j+2. -/
def conductorMellinKernel (s : ℂ) (j : ℕ) : ℂ :=
  Complex.exp (-(s - 1 / 2) * (Real.log (j + 2) : ℂ))

/-- The original correction primitive, tested against a Mellin character. -/
def correctionMellinAbel (n : ℕ) (s : ℂ) : ℂ :=
  complexValue (correctionCoefficient n) (conductorMellinKernel s) n

/-- Each finite family consists of actual translates of one admissible smooth seed. -/
def correctionTranslatedFamily (f : ℝ → ℂ) (n : ℕ) : Fin n → ℝ → ℂ :=
  fun j x => f (x - Real.log (j.val + 2))

def correctionWeilCoefficients (n : ℕ) : Fin n → ℂ :=
  fun j => (correctionCoefficient n j.val : ℂ)

/-- No limit is passed through the growing coefficient family. -/
theorem correctionWeilTransform_eq_abel (f : ℝ → ℂ) (n : ℕ) (s : ℂ) :
    smoothWeilTransform (correctionTranslatedFamily f n) (correctionWeilCoefficients n) s =
      correctionMellinAbel n s * centeredTransform f s := by
  unfold smoothWeilTransform correctionTranslatedFamily correctionWeilCoefficients
  simp only [centeredTransform_translate]
  simp_rw [← mul_assoc]
  rw [← Finset.sum_mul]
  congr 1
  rw [correctionMellinAbel, ← sum_eq_complexValue, ← Fin.sum_univ_eq_sum_range]
  rfl

/-- Exact finite Weil form using the same Abel primitive as the derivative row.
All actual zero multiplicities and the reflected transform are retained. -/
theorem correctionWeilQuadratic_eq_abel_zero_sum {f : ℝ → ℂ}
    (hf : SmoothSuperexponentialDecay f) (n : ℕ) :
    smoothWeilMatrixQuadratic (correctionTranslatedFamily f n) (correctionWeilCoefficients n) =
      ∑' ρ : Zeta23.zetaZeroConfig.carrier,
        (Zeta23.zeroMult ρ : ℂ) *
          conj (correctionMellinAbel n (1 - conj (ρ : ℂ)) *
            centeredTransform f (1 - conj (ρ : ℂ))) *
          (correctionMellinAbel n (ρ : ℂ) * centeredTransform f (ρ : ℂ)) := by
  rw [smoothWeilMatrix_quadratic_zero_sum
    (f := correctionTranslatedFamily f n)
    (fun j : Fin n => hf.translate (Real.log (j.val + 2)))]
  simp only [correctionWeilTransform_eq_abel]

/-- Real part of an individual spectral pairing; the complete defect square survives. -/
private theorem weighted_reflection_pair_exact (m : ℕ) (u v : ℂ) :
    ((m : ℂ) * conj u * v).re =
      (m : ℝ) / 2 * (Complex.normSq u + Complex.normSq v - Complex.normSq (u - v)) := by
  simp only [Complex.mul_re, Complex.mul_im, Complex.natCast_re,
    Complex.natCast_im, Complex.conj_re, Complex.conj_im, Complex.normSq_apply,
    Complex.sub_re, Complex.sub_im]
  ring

/-- The combined summand keeps both squares and the reflected-difference square.
The infinite sum is never split into separately unproved summable pieces. -/
theorem correctionWeilQuadratic_real_eq_signed_squares {f : ℝ → ℂ}
    (hf : SmoothSuperexponentialDecay f) (n : ℕ) :
    (smoothWeilMatrixQuadratic (correctionTranslatedFamily f n)
      (correctionWeilCoefficients n)).re =
      ∑' ρ : Zeta23.zetaZeroConfig.carrier,
        (Zeta23.zeroMult ρ : ℝ) / 2 *
          (Complex.normSq (correctionMellinAbel n (1 - conj (ρ : ℂ)) *
              centeredTransform f (1 - conj (ρ : ℂ))) +
            Complex.normSq (correctionMellinAbel n (ρ : ℂ) * centeredTransform f (ρ : ℂ)) -
            Complex.normSq (correctionMellinAbel n (1 - conj (ρ : ℂ)) *
              centeredTransform f (1 - conj (ρ : ℂ)) -
              correctionMellinAbel n (ρ : ℂ) * centeredTransform f (ρ : ℂ))) := by
  obtain ⟨hs, he⟩ := smoothWeilMatrix_spectral_data
    (fun j : Fin n => hf.translate (Real.log (j.val + 2))) (correctionWeilCoefficients n)
  change Summable (fun ρ : Zeta23.zetaZeroConfig.carrier =>
    (Zeta23.zeroMult ρ : ℂ) *
      conj (smoothWeilTransform (correctionTranslatedFamily f n)
        (correctionWeilCoefficients n) (1 - conj (ρ : ℂ))) *
      smoothWeilTransform (correctionTranslatedFamily f n)
        (correctionWeilCoefficients n) (ρ : ℂ)) at hs
  rw [correctionWeilQuadratic_eq_abel_zero_sum hf n]
  simp only [correctionWeilTransform_eq_abel] at hs
  change Complex.reCLM _ = _
  rw [Complex.reCLM.map_tsum hs]
  apply tsum_congr
  intro ρ
  exact weighted_reflection_pair_exact _ _ _

end RiemannResearch.RH.Pareto.CoefficientStabilization.DerivativeCompatibility

-- Append after importing RiemannResearch.RH.WeilConverse to the Weil bridge module.
namespace RiemannResearch.RH.SignedWeilCorrelation
open MeasureTheory MeasureTheory.BilateralLaplace RiemannResearch.Analysis
open WeilExplicitFormula
open scoped ComplexConjugate BigOperators

/-- An actual mixed Weil entry realizes each Mellin character at an actual zero.
The two smooth seeds exist unconditionally; no simplicity or off-line hypothesis is used. -/
theorem exists_mixed_weil_mellin_character (ρ : Zeta23.zetaZeroConfig.carrier) :
    ∃ h g : ℝ → ℂ, SmoothSuperexponentialDecay h ∧
      SmoothSuperexponentialDecay g ∧
      ∀ t : ℝ,
        arithmeticWeilPairing h (fun x => g (x - t)) =
          (Zeta23.zeroMult ρ : ℂ) * Complex.exp (-((ρ : ℂ) - 1 / 2) * (t : ℂ)) := by
  obtain ⟨g, hg, hgρ, hgz⟩ := exists_smooth_single_actual_zero_test ρ
  obtain ⟨h, hh, hhr, _⟩ := exists_smooth_single_actual_zero_test (actualZeroReflect ρ)
  refine ⟨h, g, hh, hg, ?_⟩
  intro t
  rw [arithmeticWeilPairing_of_single_zero hh (hg.translate t) ρ (by
    intro σ hσ
    rw [centeredTransform_translate, hgz σ hσ, mul_zero])]
  change (Zeta23.zeroMult ρ : ℂ) *
    conj (centeredTransform h (actualZeroReflect ρ : ℂ)) *
    centeredTransform (fun x => g (x - t)) (ρ : ℂ) = _
  rw [hhr, map_one, mul_one, centeredTransform_translate, hgρ, mul_one]

end RiemannResearch.RH.SignedWeilCorrelation

namespace RiemannResearch.RH.Pareto.CoefficientStabilization.DerivativeCompatibility
open MeasureTheory MeasureTheory.BilateralLaplace RiemannResearch.Analysis
open RiemannResearch.Analysis.SignedAbel
open RiemannResearch.RH.SignedWeilCorrelation
open scoped ComplexConjugate BigOperators

/-- The actual coefficient-weighted mixed Weil row recovers the complete
signed correction Abel transform at any actual zero, including its endpoint. -/
theorem exists_mixed_weil_correctionMellinAbel
    (ρ : Zeta23.zetaZeroConfig.carrier) :
    ∃ h g : ℝ → ℂ, SmoothSuperexponentialDecay h ∧
      SmoothSuperexponentialDecay g ∧
      ∀ n : ℕ,
        (∑ j : Fin n, (correctionCoefficient n j.val : ℂ) *
          arithmeticWeilPairing h (correctionTranslatedFamily g n j)) =
            (Zeta23.zeroMult ρ : ℂ) * correctionMellinAbel n (ρ : ℂ) := by
  obtain ⟨h, g, hh, hg, hentry⟩ := exists_mixed_weil_mellin_character ρ
  refine ⟨h, g, hh, hg, ?_⟩
  intro n
  unfold correctionTranslatedFamily
  simp_rw [hentry]
  rw [correctionMellinAbel, ← sum_eq_complexValue, ← Fin.sum_univ_eq_sum_range,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  unfold conductorMellinKernel
  ring

end RiemannResearch.RH.Pareto.CoefficientStabilization.DerivativeCompatibility

-- Append inside the bridge module after the already checked Weil definitions.
namespace RiemannResearch.RH.Pareto.CoefficientStabilization.DerivativeCompatibility

open Filter
open RiemannResearch.Analysis.SignedAbel
open scoped Topology BigOperators

theorem correctionMellinAbel_re (n : ℕ) (s : ℂ) :
    (correctionMellinAbel n s).re =
      ∑ j : Fin n, correctionCoefficient n j.val * (conductorMellinKernel s j.val).re := by
  rw [correctionMellinAbel, ← sum_eq_complexValue, ← Fin.sum_univ_eq_sum_range]
  change Complex.reCLM (∑ j : Fin n,
    (correctionCoefficient n j.val : ℂ) * conductorMellinKernel s j.val) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro j _
  change ((correctionCoefficient n j.val : ℂ) * conductorMellinKernel s j.val).re = _
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]

theorem correctionMellinAbel_im (n : ℕ) (s : ℂ) :
    (correctionMellinAbel n s).im =
      ∑ j : Fin n, correctionCoefficient n j.val * (conductorMellinKernel s j.val).im := by
  rw [correctionMellinAbel, ← sum_eq_complexValue, ← Fin.sum_univ_eq_sum_range]
  change Complex.imCLM (∑ j : Fin n,
    (correctionCoefficient n j.val : ℂ) * conductorMellinKernel s j.val) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro j _
  change ((correctionCoefficient n j.val : ℂ) * conductorMellinKernel s j.val).im = _
  simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]

/-- A finite real kernel built from actual-zero Mellin characters. -/
def mellinProxyKernel {L : ℕ} (ρ : Fin L → Zeta23.zetaZeroConfig.carrier)
    (a b : Fin L → ℝ) (j : ℕ) : ℝ :=
  ∑ l, (a l * (conductorMellinKernel (ρ l : ℂ) j).re +
    b l * (conductorMellinKernel (ρ l : ℂ) j).im)

/-- Complete signed combination of the actual mixed-Weil-recoverable Abel samples. -/
def mellinProxyValue {L : ℕ} (n : ℕ) (ρ : Fin L → Zeta23.zetaZeroConfig.carrier)
    (a b : Fin L → ℝ) : ℝ :=
  ∑ l, (a l * (correctionMellinAbel n (ρ l : ℂ)).re +
    b l * (correctionMellinAbel n (ρ l : ℂ)).im)

/-- The full signed coefficient-weighted discrepancy, before taking absolute values. -/
def mellinProxyDiscrepancy {L : ℕ} (n i : ℕ)
    (ρ : Fin L → Zeta23.zetaZeroConfig.carrier) (a b : Fin L → ℝ) : ℝ :=
  ∑ j : Fin n, correctionCoefficient n j.val *
    (derivativeRowKernel i j.val - mellinProxyKernel ρ a b j.val)

theorem mellinProxyValue_eq_signed_sum {L : ℕ} (n : ℕ)
    (ρ : Fin L → Zeta23.zetaZeroConfig.carrier) (a b : Fin L → ℝ) :
    mellinProxyValue n ρ a b =
      ∑ j : Fin n, correctionCoefficient n j.val * mellinProxyKernel ρ a b j.val := by
  unfold mellinProxyValue mellinProxyKernel
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro l _
  rw [correctionMellinAbel_re, correctionMellinAbel_im,
    Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- Exact signed transfer: the discrepancy is not discarded or made coefficientwise absolute. -/
theorem signedCorrectionRow_eq_mellinProxy_add_discrepancy {L : ℕ} (n i : ℕ)
    (ρ : Fin L → Zeta23.zetaZeroConfig.carrier) (a b : Fin L → ℝ) :
    signedCorrectionRow n i =
      mellinProxyValue n ρ a b + mellinProxyDiscrepancy n i ρ a b := by
  rw [mellinProxyValue_eq_signed_sum]
  unfold mellinProxyDiscrepancy
  rw [← Finset.sum_add_distrib]
  unfold signedCorrectionRow
  apply Finset.sum_congr rfl
  intro j _
  simp only [correctionCoefficient, dif_pos j.isLt, derivativeRowKernel]
  ring

/-- The complete signed discrepancy has its own exact Abel boundary and interior. -/
theorem mellinProxyDiscrepancy_eq_abel {L : ℕ} (n i : ℕ)
    (ρ : Fin L → Zeta23.zetaZeroConfig.carrier) (a b : Fin L → ℝ) :
    mellinProxyDiscrepancy n i ρ a b =
      primitive (correctionCoefficient n) n *
        (derivativeRowKernel i n - mellinProxyKernel ρ a b n) -
      ∑ k ∈ Finset.range n, primitive (correctionCoefficient n) (k + 1) *
        ((derivativeRowKernel i (k + 1) - mellinProxyKernel ρ a b (k + 1)) -
          (derivativeRowKernel i k - mellinProxyKernel ρ a b k)) := by
  have h := sum_eq_value (correctionCoefficient n)
    (fun j => derivativeRowKernel i j - mellinProxyKernel ρ a b j) n
  rw [← Fin.sum_univ_eq_sum_range] at h
  exact h

/-- Both squares and their signed cross term survive the transfer. -/
theorem signedCorrectionRow_sq_mellinProxy_exact {L : ℕ} (n i : ℕ)
    (ρ : Fin L → Zeta23.zetaZeroConfig.carrier) (a b : Fin L → ℝ) :
    signedCorrectionRow n i ^ 2 =
      mellinProxyValue n ρ a b ^ 2 +
        2 * mellinProxyValue n ρ a b * mellinProxyDiscrepancy n i ρ a b +
        mellinProxyDiscrepancy n i ρ a b ^ 2 := by
  rw [signedCorrectionRow_eq_mellinProxy_add_discrepancy n i ρ a b]
  ring


/-- Weakest complete signed transfer criterion supplied by this exact
decomposition: cancellation between the proxy and discrepancy is allowed. -/
theorem mellinProxy_cofinal_iff_residual_zero
    (L : ℕ → ℕ → ℕ)
    (ρ : ∀ i n, Fin (L i n) → Zeta23.zetaZeroConfig.carrier)
    (a b : ∀ i n, Fin (L i n) → ℝ) :
    (∀ i : ℕ, ∀ ε : ℝ, 0 < ε → ∃ᶠ n : ℕ in atTop,
      |mellinProxyValue n (ρ i n) (a i n) (b i n) +
        mellinProxyDiscrepancy n i (ρ i n) (a i n) (b i n)| < ε) ↔
      limitResidual = 0 := by
  have he (n i : ℕ) := signedCorrectionRow_eq_mellinProxy_add_discrepancy
    n i (ρ i n) (a i n) (b i n)
  simpa only [he] using signedCorrectionRow_cofinal_iff_residual_zero

/-- CONDITIONAL RESEARCH REDUCTION. The two budgets must hold at the same
cofinal stages. Their existence is not supplied by the exact identities.
All finite families and weights may depend on the row and the stage. -/
theorem residual_zero_of_joint_mellinProxy_budgets
    (L : ℕ → ℕ → ℕ)
    (ρ : ∀ i n, Fin (L i n) → Zeta23.zetaZeroConfig.carrier)
    (a b : ∀ i n, Fin (L i n) → ℝ)
    (h : ∀ i : ℕ, ∀ ε : ℝ, 0 < ε → ∃ᶠ n : ℕ in atTop,
      |mellinProxyValue n (ρ i n) (a i n) (b i n)| < ε / 2 ∧
      |mellinProxyDiscrepancy n i (ρ i n) (a i n) (b i n)| < ε / 2) :
    limitResidual = 0 := by
  apply signedCorrectionRow_cofinal_iff_residual_zero.mp
  intro i ε hε
  apply (h i ε hε).mono
  intro n hn
  rw [signedCorrectionRow_eq_mellinProxy_add_discrepancy n i (ρ i n) (a i n) (b i n)]
  exact lt_of_le_of_lt (abs_add_le _ _) (by linarith [hn.1, hn.2])

theorem riemannHypothesis_of_joint_mellinProxy_budgets
    (L : ℕ → ℕ → ℕ)
    (ρ : ∀ i n, Fin (L i n) → Zeta23.zetaZeroConfig.carrier)
    (a b : ∀ i n, Fin (L i n) → ℝ)
    (h : ∀ i : ℕ, ∀ ε : ℝ, 0 < ε → ∃ᶠ n : ℕ in atTop,
      |mellinProxyValue n (ρ i n) (a i n) (b i n)| < ε / 2 ∧
      |mellinProxyDiscrepancy n i (ρ i n) (a i n) (b i n)| < ε / 2) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_cofinal_signedCorrectionRow
  exact signedCorrectionRow_cofinal_iff_residual_zero.mpr
    (residual_zero_of_joint_mellinProxy_budgets L ρ a b h)

end RiemannResearch.RH.Pareto.CoefficientStabilization.DerivativeCompatibility
