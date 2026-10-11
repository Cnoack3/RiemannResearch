import RiemannResearch.Analysis.OrdinateTriangularIntegral
import RiemannResearch.Analysis.ActualZeroCollisionCertificate

/-!
# Exact triangular integral certificate for actual zeta-zero sums

The ordinate sum below is the repository's actual multiplicity-weighted
`riemannZeta` zero sum. No unproved zero-sampling input, RH or simplicity
hypothesis enters the Fourier identity or its finite certificate.
-/

noncomputable section
open scoped BigOperators
open Zeta23

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

end RiemannResearch.Analysis.ActualZeroCollisionCertificate
