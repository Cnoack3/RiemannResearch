import RiemannResearch.RH.ParetoAtomMellinSignature
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-!
# The actual Mellin obstruction for the normalized Pareto atom closure

Source: the classical Mellin necessity argument for the Nyman--Beurling
criterion, as adapted in the user-provided Beurling/digamma continuation,
7 October 2026. The actual Bochner integral, its continuity and Cauchy
estimate are imported from `ParetoMellinFunctional`; the normalized atom
signature is imported from `ParetoAtomMellinSignature`.

Every conclusion below uses the literal complete Pareto Hilbert norm.
The only arithmetic hypothesis is an explicitly stated actual zeta zero.
No Mellin identity, boundedness provider, or RH approximation is assumed.
-/

noncomputable section
open Filter
open scoped Topology

namespace RiemannResearch.RH.ParetoBeurlingMellinObstruction
open RiemannResearch.RH.Pareto
open RiemannResearch.RH.ParetoAtomMellinSignature

/-- All legal normalized atoms, viewed in the actual Pareto Hilbert space. -/
def normalizedResidueAtoms : Set ThresholdHilbert :=
  Set.range (fun d : {d : ℕ // 2 ≤ d} =>
    normalizedResidueHilbert d.1 (by omega))

/-- Finite real linear combinations of the literal normalized residue atoms. -/
def normalizedResidueSpan : Submodule ℝ ThresholdHilbert :=
  Submodule.span ℝ normalizedResidueAtoms

/-- Closure is taken in the complete physical Pareto norm. -/
def normalizedResidueClosure : Set ThresholdHilbert :=
  closure (normalizedResidueSpan : Set ThresholdHilbert)

/-- An actual off-critical zeta zero annihilates every finite legal combination. -/
theorem paretoMellin_zero_on_normalizedResidueSpan
    (s : ℂ) (hs : (1 / 2 : ℝ) < s.re) (hs1 : s ≠ 1)
    (hz : riemannZeta s = 0) (f : ThresholdHilbert)
    (hf : f ∈ normalizedResidueSpan) : paretoMellin f s = 0 := by
  have hsub : normalizedResidueSpan ≤
      LinearMap.ker (paretoMellinContinuous s hs).toLinearMap := by
    apply Submodule.span_le.mpr
    rintro g ⟨d, rfl⟩
    change paretoMellin (normalizedResidueHilbert d.1 (by omega)) s = 0
    exact paretoMellin_normalizedResidue_zero_of_zeta_zero d.1 (by omega)
      s (by linarith) hs1 hz
  exact hsub hf

/-- The actual bounded functional transports complete signed annihilation
through physical norm closure. -/
theorem paretoMellin_zero_on_normalizedResidueClosure
    (s : ℂ) (hs : (1 / 2 : ℝ) < s.re) (hs1 : s ≠ 1)
    (hz : riemannZeta s = 0) (f : ThresholdHilbert)
    (hf : f ∈ normalizedResidueClosure) : paretoMellin f s = 0 := by
  have hclosed : IsClosed {g : ThresholdHilbert | paretoMellin g s = 0} :=
    isClosed_eq (paretoMellinContinuous s hs).continuous continuous_const
  have hsub : (normalizedResidueSpan : Set ThresholdHilbert) ⊆
      {g : ThresholdHilbert | paretoMellin g s = 0} := by
    intro g hg
    exact paretoMellin_zero_on_normalizedResidueSpan s hs hs1 hz g hg
  exact (closure_minimal hsub hclosed) hf

/-- The error retains the exact target Mellin value, before taking any norm. -/
theorem paretoMellin_normalizedResidue_error_identity
    (s : ℂ) (hs : (1 / 2 : ℝ) < s.re) (hs1 : s ≠ 1)
    (hz : riemannZeta s = 0) (f : ThresholdHilbert)
    (hf : f ∈ normalizedResidueClosure) :
    paretoMellin (hilbertOne - f) s = 1 / s := by
  change paretoMellinContinuous s hs (hilbertOne - f) = 1 / s
  rw [map_sub]
  change paretoMellin hilbertOne s - paretoMellin f s = 1 / s
  rw [paretoMellin_one s hs,
    paretoMellin_zero_on_normalizedResidueClosure s hs hs1 hz f hf, sub_zero]

/-- Explicit uniform positive distance forced by an actual right-half-plane
zeta zero. The full physical approximation error is retained. -/
theorem normalizedResidue_error_sq_lower_bound_of_zeta_zero
    (s : ℂ) (hs : (1 / 2 : ℝ) < s.re) (hs1 : s ≠ 1)
    (hz : riemannZeta s = 0) (f : ThresholdHilbert)
    (hf : f ∈ normalizedResidueClosure) :
    (2 * s.re - 1) / ‖s‖ ^ 2 ≤ ‖hilbertOne - f‖ ^ 2 := by
  have hp : 0 < 2 * s.re - 1 := by linarith
  have hbound := paretoMellin_norm_sq_le (hilbertOne - f) s hs
  rw [paretoMellin_normalizedResidue_error_identity s hs hs1 hz f hf,
    norm_div, norm_one, div_pow, one_pow] at hbound
  have hmul := (le_div_iff₀ hp).mp hbound
  simpa only [one_div, mul_comm, div_eq_mul_inv, mul_one] using hmul

/-- An actual off-critical zero separates the target from the physical closure. -/
theorem hilbertOne_not_mem_normalizedResidueClosure_of_zeta_zero
    (s : ℂ) (hs : (1 / 2 : ℝ) < s.re) (hs1 : s ≠ 1)
    (hz : riemannZeta s = 0) : hilbertOne ∉ normalizedResidueClosure := by
  intro hmem
  have hzero := paretoMellin_zero_on_normalizedResidueClosure s hs hs1 hz hilbertOne hmem
  rw [paretoMellin_one s hs] at hzero
  have hs0 : s ≠ 0 := by
    intro h
    norm_num [h] at hs
  exact (div_ne_zero one_ne_zero hs0) hzero

/-- Every physical approximation by legal atoms rules out all zeros in the
continuity half-plane except the removable point, without a converse premise. -/
theorem zeta_ne_zero_of_hilbertOne_mem_normalizedResidueClosure
    (hmem : hilbertOne ∈ normalizedResidueClosure)
    (s : ℂ) (hs : (1 / 2 : ℝ) < s.re) (hs1 : s ≠ 1) :
    riemannZeta s ≠ 0 := by
  intro hz
  exact hilbertOne_not_mem_normalizedResidueClosure_of_zeta_zero s hs hs1 hz hmem

end RiemannResearch.RH.ParetoBeurlingMellinObstruction
