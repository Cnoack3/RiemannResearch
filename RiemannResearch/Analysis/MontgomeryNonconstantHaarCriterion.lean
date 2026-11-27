import RiemannResearch.Analysis.MontgomerySignedHaarCriterion
import RiemannResearch.Analysis.RoundedFourierZeroCell
import RiemannResearch.Analysis.ActualRationalFMZLimits

/-! # Nonzero Fourier orders in the physical PCC test

Deleting the zero word from the absolutely convergent signed square series
costs exactly its cell mass times the squared actual count. The complete
equal-height collision correction stays in the statistic. On the common fine
three-prime mesh, the deleted term tends to zero for every smooth compact test.
-/

noncomputable section
open Filter MeasureTheory Zeta23
open scoped FourierTransform Topology ContDiff

namespace RiemannResearch.Analysis.RoundedFourierCellParseval

open MontgomeryAllPairWordRounding MontgomeryPositiveGap MontgomeryEvenFourierTests
open ActualZeroOrdinate OrdinateCollisionCertificate

/-- Every nonzero integer Fourier order, with the full equal-height
subtraction. At each height the erased signed series is absolutely convergent
for any integrable weight. -/
def nonconstantHaarStatistic (T h : ℝ) (w : ℝ → ℝ) (f₀ : ℝ) : ℝ :=
  ((∑' k : ℤ, if k = 0 then 0 else cellMass (roundedOrder T h) w k *
      ‖ordinateSum T ((k : ℝ) * h)‖^2) -
    (occurrenceCollision (copyOrdinate T) : ℝ) * f₀) /
    (2 * (T * Real.log T / (2 * Real.pi)))

/-- Signed squares over the nonzero cells sum to the difference of the two
Haar energies minus the single constant-order cell. -/
theorem hasSum_nonconstant_squares (T h : ℝ) {w : ℝ → ℝ} (hw : Integrable w) :
    let J := roundedOrder T h
    let A := fun k : ℤ => ordinateSum T ((k : ℝ) * h)
    HasSum (fun k : ℤ => if k = 0 then 0 else cellMass J w k * ‖A k‖^2)
      (‖cellWave (cellMass J w) A‖^2 - ‖cellWave (fun k => -cellMass J w k) A‖^2 -
        cellMass J w 0 * (Ncount 0 T : ℝ)^2) := by
  let J := roundedOrder T h
  let A := fun k : ℤ => ordinateSum T ((k : ℝ) * h)
  let E := fun k : ℤ => ‖A k‖^2
  have hm : Measurable J := by
    change Measurable (roundedOrder T h)
    unfold roundedOrder
    simp_rw [round_eq]
    exact Int.measurable_floor.comp (((measurable_const.mul measurable_id).div_const h).add_const _)
  have hB (k : ℤ) : ‖A k‖ ≤ (Ncount 0 T : ℝ) := norm_ordinateSum_le_count T _
  have hE (k : ℤ) : |E k| ≤ (Ncount 0 T : ℝ)^2 := by
    rw [abs_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (norm_nonneg _) (hB k) 2
  have hi := hasSum_cells hm hw E hE
  have henergy : (∫ v, w v * E (J v)) =
      ‖cellWave (cellMass J w) A‖^2 - ‖cellWave (fun k => -cellMass J w k) A‖^2 := by
    simpa only [E, sub_zero, zero_mul] using signed_cell_energy hm hw A hB 0
  rw [henergy] at hi
  have h₀ : E 0 = (Ncount 0 T : ℝ)^2 := by simp [E, A, ordinateSum_zero]
  simpa only [h₀] using hasSum_ite_sub_hasSum hi (0 : ℤ)

theorem nonconstantHaarStatistic_eq_sub (T h : ℝ) {w : ℝ → ℝ} (hw : Integrable w)
    (f₀ : ℝ) :
    nonconstantHaarStatistic T h w f₀ = signedHaarStatistic T h w f₀ -
      centralWordContribution T h w := by
  unfold nonconstantHaarStatistic signedHaarStatistic centralWordContribution
  rw [(hasSum_nonconstant_squares T h hw).tsum_eq]
  ring

/-- Deleting the constant cell preserves each proposed limit on the fine
mesh. The weight itself may have either sign. -/
theorem tendsto_nonconstantHaarStatistic_iff {h : ℝ → ℝ}
    (hh : ∀ᶠ T in atTop, 0 < h T ∧ h T ≤ 1 / T^3)
    {w : ℝ → ℝ} (hw : Integrable w) {C : ℝ} (hC : ∀ v, |w v| ≤ C)
    (f₀ L : ℝ) :
    Tendsto (fun T => nonconstantHaarStatistic T (h T) w f₀) atTop (𝓝 L) ↔
    Tendsto (fun T => signedHaarStatistic T (h T) w f₀) atTop (𝓝 L) := by
  have hzero := centralWordContribution_tendsto_zero hh w hC
  constructor
  · intro H
    simpa only [nonconstantHaarStatistic_eq_sub _ _ hw, sub_add_cancel, add_zero] using H.add hzero
  · intro H
    simpa only [nonconstantHaarStatistic_eq_sub _ _ hw, sub_zero] using H.sub hzero

/-- A common bound on the real Fourier weight over all physical frequencies. -/
theorem abs_re_fourier_le_integral_norm (f : ℝ → ℝ) (v : ℝ) :
      |(𝓕 (fun x => (f x : ℂ)) v).re| ≤ ∫ x, ‖(f x : ℂ)‖ :=
    (Complex.abs_re_le_norm _).trans
      (VectorFourier.norm_fourierIntegral_le_integral_norm 𝐞 volume (innerₗ ℝ)
        (fun x => (f x : ℂ)) v)

/-- On one common two-three-five mesh, ordinary positive-gap PCC is
equivalent to the sine law for the signed nonconstant square series. -/
theorem exists_two_three_five_nonconstantHaar_pcc_criterion :
    let p : Nat.Primes := ⟨2, by decide⟩
    let q : Nat.Primes := ⟨3, by decide⟩
    let r : Nat.Primes := ⟨5, by decide⟩
    ∃ a b : ℝ → ℤ,
      (∀ᶠ T in atTop, 0 < meshFrequency p q r (a T) (b T) ∧
        meshFrequency p q r (a T) (b T) < 1 / T^3) ∧
      (PositiveGapPCC ↔ ∀ f : ℝ → ℝ, HasCompactSupport f → ContDiff ℝ ∞ f →
        (∀ x, f (-x) = f x) → ∀ R : ℝ, 0 < R → (∀ x, R ≤ |x| → f x = 0) →
        Tendsto (fun T => nonconstantHaarStatistic T (meshFrequency p q r (a T) (b T))
          (fun v => (𝓕 (fun x => (f x : ℂ)) v).re) (f 0)) atTop
          (𝓝 (∫ x in (0:ℝ)..R, f x * (1 - Real.sinc (Real.pi*x)^2)))) := by
  dsimp only
  obtain ⟨a, b, hmesh, hcriterion⟩ := exists_two_three_five_signedHaar_pcc_criterion
  refine ⟨a, b, hmesh, hcriterion.trans ?_⟩
  have hmesh' := hmesh.mono (fun _ ht => And.intro ht.1 ht.2.le)
  constructor
  · intro H f hc hs he R hR hcut
    exact (tendsto_nonconstantHaarStatistic_iff hmesh'
      (compact_smooth_even_fourier_test f hc hs he).1 (abs_re_fourier_le_integral_norm f) _ _).mpr (H f hc hs he R hR hcut)
  · intro H f hc hs he R hR hcut
    exact (tendsto_nonconstantHaarStatistic_iff hmesh'
      (compact_smooth_even_fourier_test f hc hs he).1 (abs_re_fourier_le_integral_norm f) _ _).mp (H f hc hs he R hR hcut)

end RiemannResearch.Analysis.RoundedFourierCellParseval
