import RiemannResearch.RH.IntegerDPPExistence
import RiemannResearch.Probability.DeterminantalLimit
import RiemannResearch.Probability.ScalarVacancyCoupling

/-!
# Arithmetic coupling: kernel order, union law, and one-site realization

Source: user-provided vacancy/hazard construction. Kernel order is proved by
orthogonal projection differences. A supplied spatial monotone coupling has
the actual limiting DPP as its union and the exact never-entry vacancy.
Separately, a uniform threshold construction supplies the first-site monotone
coupling and hazard interpretation unconditionally.

The full spatial monotone coupling is still a formalization obligation here:
Lyons, arXiv:math/0204325, Theorems 6.2 and 7.1 with Strassen's theorem give it
mathematically, but those transport proofs are not assumed or formalized below.
No zero-vacancy or RH assertion is made without its stated hypothesis.
-/

noncomputable section
open MeasureTheory
open scoped Topology Classical
namespace RiemannResearch.RH.Pareto.IntegerDPP
open CoefficientStabilization
open RiemannResearch.Analysis.ProjectionDPP
open RiemannResearch.Analysis.ExhaustiveWalk

theorem integerKernel_principal_monotone (r s : ℕ) (hrs : r ≤ s)
    (m : ℕ) (a : Fin m → ℕ) :
    (Matrix.of (fun i j => integerKernel s (a i) (a j) -
      integerKernel r (a i) (a j))).PosSemidef :=
  nested_principal_difference_posSemidef (finiteSpace r) (finiteSpace s)
    (walkSpan_mono residueAtom id hrs) countingBasis a

theorem integerKernel_le_limitingKernel (n m : ℕ) (a : Fin m → ℕ) :
    (Matrix.of (fun i j => limitingKernel (a i) (a j) -
      integerKernel n (a i) (a j))).PosSemidef :=
  nested_principal_difference_posSemidef (finiteSpace n) closedSpace
    ((walkSpan_le residueAtom id n).trans
      (Submodule.le_topologicalClosure _)) countingBasis a

section
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (Z : ℕ → Ω → Set ℕ)
    (hZ : ∀ n, RiemannResearch.Probability.DPP.IsDPP μ (Z n) (integerKernel n))
    (hmono : ∀ n ω, Z n ω ⊆ Z (n+1) ω)

include hZ hmono

theorem increasingUnion_isDPP :
    RiemannResearch.Probability.DPP.IsDPP μ
      (RiemannResearch.Probability.DPP.increasingUnion Z) limitingKernel :=
  RiemannResearch.Probability.DPP.isDPP_increasingUnion
    Z integerKernel limitingKernel hZ hmono integerKernel_tendsto

theorem never_enter_first_site_probability :
    μ.real {ω | ∀ n, 0 ∉ Z n ω} = limitingVacancy := by
  have h := limiting_dpp_first_site_vacancy (increasingUnion_isDPP Z hZ hmono)
  simpa [RiemannResearch.Probability.DPP.increasingUnion] using h

end
end RiemannResearch.RH.Pareto.IntegerDPP

namespace RiemannResearch.RH.Pareto.IntegerDPP
open RiemannResearch.Probability.DPP
open MeasureTheory
open scoped unitInterval

def firstSiteVacancyThreshold (n : ℕ) : I :=
  ⟨vacancy n, (vacancy_pos n).le, vacancy_le_one n⟩

theorem firstSiteVacancyThreshold_antitone : Antitone firstSiteVacancyThreshold :=
  fun _ _ h => vacancy_antitone h

def firstSiteHole (n : ℕ) : Set I := scalarHoleEvent (firstSiteVacancyThreshold n)
def firstSiteOccupied (n : ℕ) : Set I := scalarOccupiedEvent (firstSiteVacancyThreshold n)

theorem firstSiteHole_probability (n : ℕ) :
    (volume : Measure I).real (firstSiteHole n) = vacancy n :=
  scalarHoleEvent_probability _

theorem firstSiteOccupied_probability (n : ℕ) :
    (volume : Measure I).real (firstSiteOccupied n) = 1 - vacancy n :=
  scalarOccupiedEvent_probability _

theorem firstSiteOccupied_monotone : Monotone firstSiteOccupied :=
  scalarOccupiedEvent_monotone _ firstSiteVacancyThreshold_antitone

theorem firstSite_entry_ratio (n : ℕ) :
    (volume : Measure I).real (firstSiteOccupied (n+1) \ firstSiteOccupied n) /
      (volume : Measure I).real (firstSiteHole n) = hazard n :=
  scalarEntry_ratio _ _ (vacancy_antitone (Nat.le_succ n)) (vacancy_pos n)

end RiemannResearch.RH.Pareto.IntegerDPP
