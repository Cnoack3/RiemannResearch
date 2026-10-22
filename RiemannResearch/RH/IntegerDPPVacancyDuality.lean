import RiemannResearch.RH.IntegerDPPClosure
import RiemannResearch.RH.CanonicalTailCapacityGeometry

/-!
# Sharp dual bounds for the limiting first-site vacancy

Source: user-requested decisive vacancy criterion (2026-09-20).
The quantitative deductions use the existing Pareto tail-capacity duality
and canonical certificate energy geometry.

Every genuine Hilbert tail certificate gives a positive lower bound on the
actual limiting vacancy. The canonical certificate attains this bound, and
attainment characterizes it uniquely. Thus zero vacancy is equivalent to
excluding all tail certificates. No exclusion or zero-vacancy proof is supplied.
-/

noncomputable section
open Filter
open scoped Topology
namespace RiemannResearch.RH.Pareto.IntegerDPP
open CoefficientStabilization
open CoefficientStabilization.TailCapacity
open RiemannResearch.Analysis.ExhaustiveWalk

/-- Any tail certificate forces a quantitative positive vacancy. -/
theorem certificate_vacancy_lower_bound (z : ThresholdHilbert)
    (hz : IsResidueTailCertificate z) :
    2 / (‖z‖ ^ 2 + 2) ≤ limitingVacancy := by
  apply ge_of_tendsto vacancy_tendsto
  apply Eventually.of_forall
  intro n
  rw [vacancy_eq_capacity]
  have hden : 0 < tailCapacity n + 2 := by
    linarith [tailCapacity_nonneg n]
  apply (div_le_div_iff₀ (by positivity : 0 < ‖z‖ ^ 2 + 2) hden).mpr
  nlinarith [tailCapacity_le_certificate_energy z hz n]

private theorem pointDualResidual_ne_zero_of_limitingVacancy_pos
    (h : 0 < limitingVacancy) : pointDualResidual ≠ 0 := by
  intro hr
  have hv : limitingVacancy = 0 := by
    change 2 * ‖pointDualResidual‖ ^ 2 = 0
    simp [hr]
  linarith

/-- A positive vacancy is exactly the existence of a genuine tail certificate. -/
theorem limitingVacancy_pos_iff_exists_certificate :
    0 < limitingVacancy ↔
      ∃ z : ThresholdHilbert, IsResidueTailCertificate z := by
  constructor
  · intro h
    exact ⟨canonicalTailCertificate, canonicalTailCertificate_isCertificate
      (pointDualResidual_ne_zero_of_limitingVacancy_pos h)⟩
  · rintro ⟨z, hz⟩
    exact lt_of_lt_of_le (div_pos (by norm_num) (by positivity))
      (certificate_vacancy_lower_bound z hz)

/-- The missing zero-vacancy step is precisely the exclusion of all certificates. -/
theorem limitingVacancy_zero_iff_no_certificate :
    limitingVacancy = 0 ↔
      ¬ ∃ z : ThresholdHilbert, IsResidueTailCertificate z := by
  constructor
  · intro hv hz
    have hp := limitingVacancy_pos_iff_exists_certificate.mpr hz
    linarith
  · intro hz
    rcases lt_or_eq_of_le limitingVacancy_nonneg with hp | he
    · exact (hz (limitingVacancy_pos_iff_exists_certificate.mp hp)).elim
    · exact he.symm

/-- In the obstruction case, the vacancy determines the minimum certificate energy. -/
theorem canonicalTailCertificate_energy_eq_vacancy (h : 0 < limitingVacancy) :
    ‖canonicalTailCertificate‖ ^ 2 = 2 / limitingVacancy - 2 := by
  have hr := pointDualResidual_ne_zero_of_limitingVacancy_pos h
  have hE : ‖pointDualResidual‖ ^ 2 ≠ 0 :=
    pow_ne_zero 2 (norm_ne_zero_iff.mpr hr)
  rw [canonicalTailCertificate_norm_sq hr]
  change 1 / ‖pointDualResidual‖ ^ 2 - 2 =
    2 / (2 * ‖pointDualResidual‖ ^ 2) - 2
  field_simp [hE]

/-- The lower bound is attained by the actual canonical certificate. -/
theorem canonicalTailCertificate_attains_vacancy_bound (h : 0 < limitingVacancy) :
    2 / (‖canonicalTailCertificate‖ ^ 2 + 2) = limitingVacancy := by
  rw [canonicalTailCertificate_energy_eq_vacancy h]
  rw [sub_add_cancel]
  have hv : limitingVacancy ≠ 0 := ne_of_gt h
  field_simp [hv]

/-- Among all certificates, equality in the vacancy bound singles out the
canonical minimum-energy certificate. -/
theorem certificate_vacancy_bound_eq_iff (z : ThresholdHilbert)
    (hz : IsResidueTailCertificate z) :
    2 / (‖z‖ ^ 2 + 2) = limitingVacancy ↔ z = canonicalTailCertificate := by
  have hp := limitingVacancy_pos_iff_exists_certificate.mpr ⟨z, hz⟩
  have hr := pointDualResidual_ne_zero_of_limitingVacancy_pos hp
  have hc := canonicalTailCertificate_attains_vacancy_bound hp
  constructor
  · intro he
    have hzden : ‖z‖ ^ 2 + 2 ≠ 0 := by positivity
    have hcden : ‖canonicalTailCertificate‖ ^ 2 + 2 ≠ 0 := by positivity
    have heq : 2 / (‖z‖ ^ 2 + 2) =
        2 / (‖canonicalTailCertificate‖ ^ 2 + 2) := he.trans hc.symm
    have hequal : ‖z‖ ^ 2 + 2 = ‖canonicalTailCertificate‖ ^ 2 + 2 := by
      field_simp [hzden, hcden] at heq
      linarith
    have hsplit := certificate_canonical_energy_split hr z hz
    have hnorm : ‖z - canonicalTailCertificate‖ ^ 2 = 0 := by linarith
    exact sub_eq_zero.mp (norm_eq_zero.mp (sq_eq_zero_iff.mp hnorm))
  · intro he
    simpa only [he] using hc

end RiemannResearch.RH.Pareto.IntegerDPP
