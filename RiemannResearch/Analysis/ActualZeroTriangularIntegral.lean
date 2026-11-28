import RiemannResearch.Analysis.OrdinateTriangularIntegral
import RiemannResearch.Analysis.ActualZeroCollisionCertificate
import RiemannResearch.Analysis.ActualZeroCountAsymptotics

/-!
# Exact triangular integral certificate for actual zeta-zero sums

The ordinate sum below is the repository's actual multiplicity-weighted
`riemannZeta` zero sum. No unproved zero-sampling input, RH or simplicity
hypothesis enters the Fourier identity or its finite certificate.
-/

noncomputable section
open scoped BigOperators
open Filter Zeta23

namespace RiemannResearch.Analysis.ActualZeroCollisionCertificate

open ActualZeroOrdinate OrdinateCollisionCertificate

theorem actual_occurrenceAmplitude (T u : ℝ) :
    occurrenceAmplitude (copyOrdinate T) u = ordinateSum T u := by
  unfold occurrenceAmplitude ordinateSum
  rw [sum_eq_copies]
  rfl

/-- The exact triangular Fourier integral of the actual ordinate sum. -/
def actualTriangularEnergy (T R : ℝ) : ℝ :=
  (1 / R) * ∫ u in (-R)..R,
    (1 - |u| / R) * Complex.normSq (ordinateSum T u)

theorem actualTriangularEnergy_eq_finiteBandEnergy (T : ℝ) {R : ℝ} (hR : 0 < R) :
    actualTriangularEnergy T R = finiteBandEnergy T R := by
  have h := triangularBandEnergy_eq_sincEnergy (copyOrdinate T) hR
  simpa only [triangularBandEnergy, actual_occurrenceAmplitude,
    actualTriangularEnergy, finiteBandEnergy] using h

/-- A finite integral bounds every actual off-critical-line occurrence. -/
theorem offCount_le_actualTriangular_excess (T : ℝ) {R : ℝ} (hR : 0 < R) :
    (offCount T : ℝ) ≤ actualTriangularEnergy T R - (Ncount 0 T : ℝ) := by
  rw [actualTriangularEnergy_eq_finiteBandEnergy T hR]
  exact offCount_le_finiteBand_excess T R

/-- The exact finite-band integral certificate stated in the paper. -/
theorem actualTriangular_certificate (T : ℝ) {R : ℝ} (hR : 0 < R)
    (hsmall : actualTriangularEnergy T R < (Ncount 0 T : ℝ) + 2) :
    ∀ ρ ∈ cutoff T, ρ.re = 1 / 2 ∧ zeroMult ρ = 1 := by
  apply finiteBand_certificate T R
  rwa [actualTriangularEnergy_eq_finiteBandEnergy T hR] at hsmall

/-- Quantitative bandwidth obstruction for the simplicity certificate. -/
theorem actualTriangularEnergy_coherent_lower {T R a : ℝ} (hT : 0 ≤ T)
    (hR : 0 < R) (ha : 0 ≤ a) (hband : a ≤ R / 2) (hscale : T * a ≤ 1) :
    a * (Ncount 0 T : ℝ) ^ 2 / (2 * R) ≤ actualTriangularEnergy T R := by
  have hdiam (i j : Copies T) : |copyOrdinate T i - copyOrdinate T j| ≤ T := by
    obtain ⟨_, hi, hi'⟩ := mem_cutoff_iff_zeta.mp i.1.2
    obtain ⟨_, hj, hj'⟩ := mem_cutoff_iff_zeta.mp j.1.2
    change |i.1.1.im - j.1.1.im| ≤ T
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have h := triangularBandEnergy_coherent_lower (copyOrdinate T) hR ha hband hT hscale hdiam
  rw [triangularBandEnergy_eq_sincEnergy _ hR, card_copies] at h
  rw [actualTriangularEnergy_eq_finiteBandEnergy T hR]
  exact h

/-- Once six copies are present, a successful finite certificate forces
bandwidth-times-height to exceed a quantity asymptotic to half the zero count. -/
theorem bandwidth_necessary_for_actualTriangular_certificate {T R : ℝ}
    (hT : 0 < T) (hR : 0 < R) (hN : 6 ≤ Ncount 0 T)
    (hcert : actualTriangularEnergy T R < (Ncount 0 T : ℝ) + 2) :
    (Ncount 0 T : ℝ) ^ 2 < 2 * R * T * ((Ncount 0 T : ℝ) + 2) := by
  have hn : (6 : ℝ) ≤ (Ncount 0 T : ℝ) := by exact_mod_cast hN
  by_cases hscale : T * (R / 2) ≤ 1
  · have h := (actualTriangularEnergy_coherent_lower hT.le hR (by positivity)
        (le_refl (R / 2)) hscale).trans_lt hcert
    have he : (R / 2) * (Ncount 0 T : ℝ) ^ 2 / (2 * R) = (Ncount 0 T : ℝ) ^ 2 / 4 := by
      field_simp; ring
    rw [he] at h
    nlinarith [mul_nonneg (sub_nonneg.mpr hn) (show 0 ≤ (Ncount 0 T : ℝ) + 2 by positivity)]
  · have hband : 1 / T ≤ R / 2 := (div_le_iff₀ hT).mpr (by linarith)
    have h := (actualTriangularEnergy_coherent_lower hT.le hR (by positivity) hband
      (by field_simp <;> norm_num)).trans_lt hcert
    have hh := (div_lt_iff₀ (show 0 < 2 * R by positivity)).mp h
    have hmul := mul_lt_mul_of_pos_right hh hT
    calc
      (Ncount 0 T : ℝ) ^ 2 = (1 / T * (Ncount 0 T : ℝ) ^ 2) * T := by field_simp
      _ < ((Ncount 0 T : ℝ) + 2) * (2 * R) * T := hmul
      _ = _ := by ring

/-- At large heights every physical band of width at most c log T fails
the strict certificate whenever 0 < c < 1/(4π). -/
theorem eventually_log_band_fails_certificate {c : ℝ} (hc : 0 < c)
    (hc' : c < 1 / (4 * Real.pi)) :
    ∀ᶠ T : ℝ in Filter.atTop, ∀ R : ℝ, 0 < R → R ≤ c * Real.log T →
      (Ncount 0 T : ℝ) + 2 ≤ actualTriangularEnergy T R := by
  have h2c : 2 * c < 1 / (2 * Real.pi) := by
    have h' := (lt_div_iff₀ (show 0 < 4 * Real.pi by positivity)).mp hc'
    exact (lt_div_iff₀ (by positivity)).mpr (by linarith)
  obtain ⟨q, hqc, hq⟩ := exists_between h2c
  have hqp : 0 < q := by linarith
  have hgap : 0 < q - 2 * c := by linarith
  filter_upwards [eventually_count_ge_log_of_lt hq, Filter.eventually_gt_atTop (0 : ℝ),
    Filter.eventually_ge_atTop (6 / q), Filter.eventually_gt_atTop (2 / (q - 2 * c)),
    Real.tendsto_log_atTop.eventually_ge_atTop 1] with T hN hT h6 h2 hl
  intro R hR hr
  have h6q : 6 ≤ q * T := by simpa only [mul_comm] using (div_le_iff₀ hqp).mp h6
  have h6N : (6 : ℝ) ≤ (Ncount 0 T : ℝ) := h6q.trans
    ((le_mul_of_one_le_right (mul_nonneg hqp.le hT.le) hl).trans hN)
  have h2T : 2 < (q - 2 * c) * T := by simpa only [mul_comm] using (div_lt_iff₀ hgap).mp h2
  have h2L := h2T.trans_le (le_mul_of_one_le_right (mul_nonneg hgap.le hT.le) hl)
  by_contra! hcert
  have hfull := bandwidth_necessary_for_actualTriangular_certificate hT hR
    (by exact_mod_cast h6N) hcert
  have hsmall : 2 * R * T ≤ (Ncount 0 T : ℝ) - 2 := by
    have hh := mul_le_mul_of_nonneg_right hr hT.le
    linarith only [hN, h2L, hh]
  have hh := mul_le_mul_of_nonneg_right hsmall (show 0 ≤ (Ncount 0 T : ℝ) + 2 by positivity)
  nlinarith

end RiemannResearch.Analysis.ActualZeroCollisionCertificate
