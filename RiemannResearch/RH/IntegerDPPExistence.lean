import RiemannResearch.Probability.DeterminantalExistence
import RiemannResearch.RH.IntegerDPPReduction

/-!
# Unconditional arithmetic DPP existence

The actual finite-rank and closed residue projections give positive-contraction
kernels on the full countable set of integer coordinates. The general proved
construction supplies their laws with every correlation determinant.
No RH, odd-carry membership, density, or vacancy-decay hypothesis is used for
existence. Source: the user's arithmetic DPP construction; the generic
existence statement follows the discrete DPP terminology of Lyons,
arXiv:math/0204325. The final RH implication retains its occupation hypothesis.
-/

noncomputable section
open MeasureTheory
open scoped Classical

namespace RiemannResearch.RH.Pareto.IntegerDPP
open CoefficientStabilization
open RiemannResearch.Analysis.ProjectionDPP
open RiemannResearch.Analysis.ExhaustiveWalk

theorem countingBasis_inner (i j : ℕ) :
    inner ℝ (countingBasis i) (countingBasis j) = if i = j then 1 else 0 := by
  by_cases hij : i = j
  · subst j
    simp [countingBasis, lp.inner_single_left]
  · simp [countingBasis, lp.inner_single_left, hij]

theorem integerKernel_principal_complement_posSemidef
    (n m : ℕ) (a : Fin m ↪ ℕ) :
    (1 - Matrix.of (fun i j => integerKernel n (a i) (a j))).PosSemidef := by
  apply identity_sub_principal_posSemidef (finiteSpace n) countingBasis a
  intro i j
  simp [countingBasis_inner, a.injective.eq_iff]

theorem limitingKernel_principal_complement_posSemidef
    (m : ℕ) (a : Fin m ↪ ℕ) :
    (1 - Matrix.of (fun i j => limitingKernel (a i) (a j))).PosSemidef := by
  apply identity_sub_principal_posSemidef closedSpace countingBasis a
  intro i j
  simp [countingBasis_inner, a.injective.eq_iff]

end RiemannResearch.RH.Pareto.IntegerDPP

namespace RiemannResearch.RH.Pareto.IntegerDPP
open CoefficientStabilization
open RiemannResearch.Analysis.ProjectionDPP
open RiemannResearch.Probability.DPP

def integerLaw (n : ℕ) : Measure (ℕ → Bool) :=
  contractionDPP (integerKernel n)
    (fun I => principal_posSemidef (finiteSpace n) countingBasis (fun i : I => i.1))
    (fun I => by
      have h := identity_sub_principal_posSemidef (finiteSpace n) countingBasis
        (fun i : I => i.1) (by intro i j; simp [countingBasis_inner])
      convert h using 1 <;> ext i j <;>
        simp [Matrix.sub_apply, Matrix.one_apply, integerKernel, kernel])

instance integerLaw_probability (n : ℕ) : IsProbabilityMeasure (integerLaw n) := by
  unfold integerLaw
  exact contractionDPP_probability _ _ _

theorem integerLaw_isDPP (n : ℕ) :
    IsDPP (integerLaw n) (fun x => {i | x i = true}) (integerKernel n) :=
  contractionDPP_isDPP _ _ _

def limitingLaw : Measure (ℕ → Bool) :=
  contractionDPP limitingKernel
    (fun I => principal_posSemidef closedSpace countingBasis (fun i : I => i.1))
    (fun I => by
      have h := identity_sub_principal_posSemidef closedSpace countingBasis
        (fun i : I => i.1) (by intro i j; simp [countingBasis_inner])
      convert h using 1 <;> ext i j <;>
        simp [Matrix.sub_apply, Matrix.one_apply, limitingKernel, kernel])

instance limitingLaw_probability : IsProbabilityMeasure limitingLaw := by
  unfold limitingLaw
  exact contractionDPP_probability _ _ _

theorem limitingLaw_isDPP :
    IsDPP limitingLaw (fun x => {i | x i = true}) limitingKernel :=
  contractionDPP_isDPP _ _ _

theorem integerLaw_first_site_vacancy (n : ℕ) :
    (integerLaw n).real {x | x 0 = false} = vacancy n := by
  simpa using dpp_first_site_vacancy n (integerLaw_isDPP n)

theorem limitingLaw_first_site_vacancy :
    limitingLaw.real {x | x 0 = false} = limitingVacancy := by
  simpa using limiting_dpp_first_site_vacancy limitingLaw_isDPP

theorem riemannHypothesis_of_limitingLaw_first_site_ae
    (h : ∀ᵐ x ∂limitingLaw, x 0 = true) : RiemannHypothesis :=
  riemannHypothesis_of_dpp_first_site_ae limitingLaw_isDPP h

end RiemannResearch.RH.Pareto.IntegerDPP
