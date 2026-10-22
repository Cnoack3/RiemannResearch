import RiemannResearch.Analysis.OrdinateCollisionCertificate
import RiemannResearch.Analysis.ActualZeroOrdinate

/-!
# Sinc-squared collision certificates for actual zeta-zero occurrences

The finite occurrence type and reflection facts are imported from
`ActualZeroOrdinate`. This file assumes neither RH nor zero simplicity.
The energy is its explicit finite sinc-squared sum. The separate identity
equating that sum with the triangular Fourier integral is not claimed here.
-/

noncomputable section
open scoped BigOperators
open Zeta23

namespace RiemannResearch.Analysis.ActualZeroCollisionCertificate

open ActualZeroOrdinate OrdinateCollisionCertificate

/-- Every off-critical-line occurrence, retaining analytic multiplicity. -/
def offCopies (T : ℝ) : Finset (Copies T) := by
  classical
  exact Finset.univ.filter (fun c => c.1.1.re ≠ 1 / 2)

def offCount (T : ℝ) : ℕ := (offCopies T).card

theorem offCopies_has_companion (T : ℝ) :
    ∀ c ∈ offCopies T, ∃ d : Copies T,
      c ≠ d ∧ copyOrdinate T c = copyOrdinate T d := by
  classical
  intro c hc
  have hoff : c.1.1.re ≠ 1 / 2 := (Finset.mem_filter.mp hc).2
  let d : Copies T :=
    ⟨⟨reflect c.1.1, reflect_mem c.1.2⟩,
      ⟨0, multiplicity_pos (reflect_mem c.1.2)⟩⟩
  refine ⟨d, ?_, ?_⟩
  · intro hcd
    have hre := congrArg (fun x : Copies T => x.1.1.re) hcd
    change c.1.1.re = (reflect c.1.1).re at hre
    rw [reflect_re] at hre
    exact hoff (by linarith)
  · exact (reflect_im c.1.1).symm

/-- The actual finite sum over all ordered pairs of zero occurrences. -/
def finiteBandEnergy (T R : ℝ) : ℝ := sincEnergy (copyOrdinate T) R

/-- The finite-band estimate for all off-line zero occurrences. -/
theorem offCount_le_finiteBand_excess (T R : ℝ) :
    (offCount T : ℝ) ≤ finiteBandEnergy T R - (Ncount 0 T : ℝ) := by
  have h := selected_count_le_kernel_excess (copyOrdinate T) (sincSquared R)
    (sincSquared_nonneg R) (sincSquared_zero R)
    (offCopies T) (offCopies_has_companion T)
  simpa only [offCount, finiteBandEnergy, sincEnergy, card_copies] using h

/-- This concrete finite sinc-squared inequality suffices for criticality and simplicity. -/
theorem finiteBand_certificate (T R : ℝ)
    (hsmall : finiteBandEnergy T R < (Ncount 0 T : ℝ) + 2) :
    ∀ ρ ∈ cutoff T, ρ.re = 1 / 2 ∧ zeroMult ρ = 1 := by
  apply (copyOrdinate_injective_iff T).mp
  apply sinc_certificate (copyOrdinate T) R
  simpa only [finiteBandEnergy, card_copies] using hsmall

end RiemannResearch.Analysis.ActualZeroCollisionCertificate
