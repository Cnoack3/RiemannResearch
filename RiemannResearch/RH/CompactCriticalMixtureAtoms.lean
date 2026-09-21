import RiemannResearch.RH.CompactFrequencyMellinEntire
import Mathlib.NumberTheory.LSeries.ZetaZeros
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure

/-!
# Finite atomic reduction of compact critical-line mixtures

Source: user-provided compact-frequency rigidity argument, 2026-09-21,
Sections 3--4. Compact vertical segments contain finitely many zeta zeros.
An annihilating complex density, after the rigidity theorem, is supported
on those zeros. Its coordinate integral is therefore an exact finite sum
of critical Mellin modes with its actual atom coefficients.
-/

noncomputable section
open MeasureTheory Filter Set
open scoped BigOperators
namespace RiemannResearch.RH.Pareto.SpectralObstruction

/-- The ordinates of actual zeta zeros in the closed critical-line segment. -/
def criticalZeroBand (T : ℝ) : Set ℝ :=
  {t | |t| ≤ T ∧ riemannZeta (MellinFrequency.criticalPoint t) = 0}

theorem criticalPoint_injective : Function.Injective MellinFrequency.criticalPoint := by
  intro s t h
  have hi := congrArg Complex.im h
  simpa [MellinFrequency.criticalPoint] using hi

/-- There are finitely many actual zeta-zero ordinates in each bounded segment. -/
theorem criticalZeroBand_finite (T : ℝ) : (criticalZeroBand T).Finite := by
  have hc : Continuous MellinFrequency.criticalPoint := by
    unfold MellinFrequency.criticalPoint
    fun_prop
  have hcompact : IsCompact (MellinFrequency.criticalPoint '' Icc (-T) T) :=
    (isCompact_Icc : IsCompact (Icc (-T) T)).image hc
  have hfin := hcompact.inter_riemannZetaZeros_finite
  have hpre := Set.Finite.preimage criticalPoint_injective.injOn hfin
  apply hpre.subset
  intro t ht
  change MellinFrequency.criticalPoint t ∈
    (MellinFrequency.criticalPoint '' Icc (-T) T) ∩ riemannZetaZeros
  exact ⟨⟨t, abs_le.mp ht.1, rfl⟩, ht.2⟩

def criticalZeroFinset (T : ℝ) : Finset ℝ := (criticalZeroBand_finite T).toFinset

@[simp] theorem mem_criticalZeroFinset (T t : ℝ) :
    t ∈ criticalZeroFinset T ↔
      |t| ≤ T ∧ riemannZeta (MellinFrequency.criticalPoint t) = 0 := by
  simp [criticalZeroFinset, criticalZeroBand]

/-- The actual complex coefficient of a point atom in `a dμ`. -/
def densityAtomCoefficient (μ : Measure ℝ) (a : ℝ → ℂ) (t : ℝ) : ℂ :=
  (μ.real {t} : ℂ) * a t

/-- Every kernel pairing of a finitely supported complex density is exactly
its finite sum of atom coefficients. No continuity of the kernel is required. -/
theorem integral_mul_eq_finite_atoms (μ : Measure ℝ) [IsFiniteMeasure μ]
    (a k : ℝ → ℂ) (S : Finset ℝ)
    (hzero : ∀ᵐ t ∂μ, t ∉ S → a t = 0) :
    (∫ t, a t * k t ∂μ) = ∑ t ∈ S, densityAtomCoefficient μ a t * k t := by
  have he : (∫ t in (S : Set ℝ), a t * k t ∂μ) = ∫ t, a t * k t ∂μ := by
    apply setIntegral_eq_integral_of_ae_compl_eq_zero
    filter_upwards [hzero] with t ht hnot
    simp [ht hnot]
  rw [← he, setIntegral_finset S IntegrableOn.finset]
  apply Finset.sum_congr rfl
  intro t ht
  simp [densityAtomCoefficient, Complex.real_smul, mul_assoc]

/-- If all actual atom coefficients of a finitely supported integrable
complex density vanish, the density vanishes almost everywhere. -/
theorem density_zero_of_finite_atom_coefficients (μ : Measure ℝ) [IsFiniteMeasure μ]
    (a : ℝ → ℂ) (ha : Integrable a μ) (S : Finset ℝ)
    (hzero : ∀ᵐ t ∂μ, t ∉ S → a t = 0)
    (hatom : ∀ t ∈ S, densityAtomCoefficient μ a t = 0) : a =ᵐ[μ] 0 := by
  have he : (∫ t in (S : Set ℝ), ‖a t‖ ∂μ) = ∫ t, ‖a t‖ ∂μ := by
    apply setIntegral_eq_integral_of_ae_compl_eq_zero
    filter_upwards [hzero] with t ht hnot
    simp [ht hnot]
  have hint : (∫ t, ‖a t‖ ∂μ) = 0 := by
    rw [← he, setIntegral_finset S IntegrableOn.finset]
    apply Finset.sum_eq_zero
    intro t ht
    have h := congrArg norm (hatom t ht)
    have hm : 0 ≤ μ.real {t} := measureReal_nonneg
    simpa [densityAtomCoefficient, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg hm, smul_eq_mul] using h
  have hn := (integral_eq_zero_iff_of_nonneg (fun t => norm_nonneg (a t)) ha.norm).mp hint
  filter_upwards [hn] with t ht
  exact norm_eq_zero.mp ht

/-- Rigidity concentrates the original density on the finite set of actual
critical-line zeta-zero ordinates. -/
theorem critical_density_supported_on_finite_zeros
    (T : ℝ) (μ : Measure ℝ) (a : ℝ → ℂ)
    (hdata : CompactFrequencyData (1 / 2) T μ a)
    (hweighted : zetaWeightedDensity (1 / 2) a =ᵐ[μ] 0) :
    ∀ᵐ t ∂μ, t ∉ criticalZeroFinset T → a t = 0 := by
  have hsupp := hdata.2.2.2.2.2
  filter_upwards [hsupp, hweighted] with t ht hw hnot
  by_contra hane
  have hz : riemannZeta (MellinFrequency.criticalPoint t) = 0 := by
    have hp : riemannZeta (MellinFrequency.criticalPoint t) * a t = 0 := by
      simpa only [zetaWeightedDensity, Pi.zero_apply, verticalPoint_half] using hw
    exact (mul_eq_zero.mp hp).resolve_right hane
  exact hnot ((mem_criticalZeroFinset T t).mpr ⟨ht, hz⟩)

/-- Exact finite atomic representation of the continuum critical-line mixture. -/
theorem continuumMixture_eq_finite_zero_modes
    (T : ℝ) (μ : Measure ℝ) (a : ℝ → ℂ)
    (hdata : CompactFrequencyData (1 / 2) T μ a)
    (hweighted : zetaWeightedDensity (1 / 2) a =ᵐ[μ] 0) (n : ℕ) :
    continuumMixture (1 / 2) μ a n =
      ∑ t ∈ criticalZeroFinset T, densityAtomCoefficient μ a t *
        mellinMode (MellinFrequency.criticalPoint t) n := by
  letI : IsFiniteMeasure μ := hdata.2.2.2.1
  have hsupp := critical_density_supported_on_finite_zeros T μ a hdata hweighted
  have h := integral_mul_eq_finite_atoms μ a
    (fun t => mellinMode (verticalPoint (1 / 2) t) n) (criticalZeroFinset T) hsupp
  simpa only [continuumMixture, verticalPoint_half] using h

end RiemannResearch.RH.Pareto.SpectralObstruction
