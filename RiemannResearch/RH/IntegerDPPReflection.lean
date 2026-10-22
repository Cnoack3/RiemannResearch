import RiemannResearch.Analysis.DoubleHilbertReflection
import RiemannResearch.RH.IntegerDPPClosure

/-!
# Reflected copies of the actual arithmetic residue closure

Source: user-provided reciprocal Mellin DPP construction (2026-09-20).
The two coordinates represent the original Pareto space and its reciprocal
copy. The product is used for its submodule structure; its default norm is
not asserted to be the Hilbert direct-sum norm.

The doubled full-space condition is exactly the original condition. The RH
consequence uses the project's existing checked implication. No RH converse,
density, or disappearance of holes is assumed or proved here.
-/

noncomputable section
open Filter
open scoped Topology

namespace RiemannResearch.RH.Pareto.IntegerDPP
open CoefficientStabilization
open RiemannResearch.Analysis.ReflectedProjection

/-- The relative doubled ambient retains both copies of the arithmetic closure. -/
def reflectedClosedSpace : Submodule ℝ (ThresholdHilbert × ThresholdHilbert) :=
  closedSpace.prod closedSpace

theorem reflectedClosedSpace_eq_top_iff :
    reflectedClosedSpace = ⊤ ↔ closedSpace = ⊤ :=
  prod_eq_top_iff closedSpace

theorem swap_mem_reflectedClosedSpace_iff (f : ThresholdHilbert × ThresholdHilbert) :
    Prod.swap f ∈ reflectedClosedSpace ↔ f ∈ reflectedClosedSpace :=
  swap_mem_prod_iff closedSpace f

/-- The actual completed arithmetic projection on the Hilbert direct sum. -/
def reflectedFiniteProjection (n : ℕ) :
    Analysis.DoubleHilbertReflection.DoubleHilbert ThresholdHilbert →L[ℝ]
      Analysis.DoubleHilbertReflection.DoubleHilbert ThresholdHilbert :=
  Analysis.DoubleHilbertReflection.completed (finiteSpace n)

theorem reflectedFiniteProjection_isStarProjection (n : ℕ) :
    IsStarProjection (reflectedFiniteProjection n) :=
  Analysis.DoubleHilbertReflection.completed_isStarProjection (finiteSpace n)

theorem reflectedFiniteProjection_commutes (n : ℕ) :
    reflectedFiniteProjection n * Analysis.DoubleHilbertReflection.reflection =
      Analysis.DoubleHilbertReflection.reflection * reflectedFiniteProjection n :=
  Analysis.DoubleHilbertReflection.completed_commutes (finiteSpace n)

/-- The limiting completed operator is full exactly under the original
arithmetic density condition. -/
theorem reflectedLimitingProjection_eq_one_iff :
    Analysis.DoubleHilbertReflection.completed closedSpace = 1 ↔
      closedSpace = ⊤ :=
  Analysis.DoubleHilbertReflection.completed_eq_one_iff closedSpace

/-- Adjoining a reciprocal copy preserves the original vacancy obstruction. -/
theorem reflectedClosedSpace_eq_top_iff_limitingVacancy_zero :
    reflectedClosedSpace = ⊤ ↔ limitingVacancy = 0 :=
  reflectedClosedSpace_eq_top_iff.trans limitingVacancy_zero_iff_top.symm

theorem reflectedClosedSpace_eq_top_iff_vacancy_tendsto_zero :
    reflectedClosedSpace = ⊤ ↔ Tendsto vacancy atTop (𝓝 0) :=
  reflectedClosedSpace_eq_top_iff.trans vacancy_tendsto_zero_iff_top.symm

theorem riemannHypothesis_of_reflectedClosedSpace_eq_top
    (h : reflectedClosedSpace = ⊤) : RiemannHypothesis :=
  riemannHypothesis_of_vacancy_tendsto_zero
    (reflectedClosedSpace_eq_top_iff_vacancy_tendsto_zero.mp h)

theorem reflectedClosedSpace_ne_top_of_not_RH (h : ¬ RiemannHypothesis) :
    reflectedClosedSpace ≠ ⊤ :=
  fun hd => h (riemannHypothesis_of_reflectedClosedSpace_eq_top hd)

end RiemannResearch.RH.Pareto.IntegerDPP
