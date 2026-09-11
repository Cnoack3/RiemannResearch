import RiemannResearch.Analysis.DyadicMomentEvaluation
import RiemannResearch.RH.RamanujanLaguerreResearchTargets

/-!
# Actual dyadic feasibility from explicit analytic providers

Source: `RH_Ramanujan_Laguerre_Schur_Continuation_20260911.md`, §6.
The linear algebra is supplied by `DyadicMomentEvaluation`. This module connects
it to the actual integral coefficients and actual finite legal packets.
The polynomial coefficient identity and the continuous Pareto realization are
explicit hypotheses. The theorem does not supply either analytic provider and
does not assert a uniform norm bound.
-/
noncomputable section
open MeasureTheory
open scoped BigOperators

namespace RiemannResearch.RH.Pareto.RamanujanLaguerre
open RiemannResearch.Analysis
open RiemannResearch.Analysis.DyadicMomentEvaluation

/-- The genuine binary generator at a dyadic dilation. -/
def dyadicPacket (v : ℕ) : ℕ → ℝ := dilation (2 ^ v) (residue 2)

theorem dyadicPacket_mem_budget (K : ℕ) (v : Fin (K + 1)) :
    dyadicPacket v ∈ FiniteTwoSeedCompletion.budgetSpan (2 ^ K) := by
  apply FiniteTwoSeedCompletion.generator_mem (2 ^ K) 2 (2 ^ (v : ℕ)) (Or.inl rfl)
  · exact pow_pos (by norm_num) _
  · exact Nat.pow_le_pow_right (by norm_num) (Nat.le_of_lt_succ v.isLt)

/-- The actual Laguerre integrand is integrable when all ordinary log moments
are integrable. This justifies all finite integral exchanges below. -/
theorem coefficient_integrable (F : ℕ → ℝ) (hF : AllMomentsIntegrable F) (k : ℕ) :
    IntegrableOn (fun t => exponentialLift F t * laguerreValue k t * Real.exp (-t))
      (Set.Ici 0) := by
  have heq : (fun t => exponentialLift F t * laguerreValue k t * Real.exp (-t)) =
      fun t => ∑ j ∈ Finset.range (k + 1),
        laguerreCoefficient k j * (exponentialLift F t * t ^ j * Real.exp (-t)) := by
    funext t
    unfold laguerreValue
    rw [Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  rw [heq]
  exact integrable_finsetSum _ (fun j _ => (hF j).const_mul _)

theorem allMomentsIntegrable_finite_synthesis {ι : Type*} [Fintype ι]
    (b : ι → ℕ → ℝ) (c : ι → ℝ) (hb : ∀ i, AllMomentsIntegrable (b i)) :
    AllMomentsIntegrable (∑ i, c i • b i) := by
  intro j
  have heq : (fun t => exponentialLift (∑ i, c i • b i) t * t ^ j * Real.exp (-t)) =
      fun t => ∑ i, c i * (exponentialLift (b i) t * t ^ j * Real.exp (-t)) := by
    funext t
    simp [exponentialLift, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      Finset.sum_mul, mul_assoc]
  rw [heq]
  exact integrable_finsetSum _ (fun i _ => (hb i j).const_mul _)

/-- Finite coefficient synthesis retains every signed coefficient exactly. -/
theorem coefficient_finite_synthesis {ι : Type*} [Fintype ι]
    (b : ι → ℕ → ℝ) (c : ι → ℝ) (hb : ∀ i, AllMomentsIntegrable (b i)) (k : ℕ) :
    coefficient (∑ i, c i • b i) k = ∑ i, c i * coefficient (b i) k := by
  unfold coefficient
  have heq : (fun t => exponentialLift (∑ i, c i • b i) t *
      laguerreValue k t * Real.exp (-t)) =
      fun t => ∑ i, c i * (exponentialLift (b i) t * laguerreValue k t * Real.exp (-t)) := by
    funext t
    simp [exponentialLift, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      Finset.sum_mul, mul_assoc]
  rw [heq, integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro i hi
    exact integral_const_mul _ _
  · intro i hi
    exact (coefficient_integrable (b i) (hb i) k).const_mul _

/-- The precise remaining polynomial identity, on actual dyadic generators
and their actual continuous Pareto Laguerre integrals. -/
def DyadicCoefficientPolynomialProvider : Prop :=
  ∀ K : ℕ, ∃ C : Matrix (Fin (K + 1)) (Fin (K + 1)) ℝ,
    C.IsLowerTriangular ∧
    (∀ j, C j j = dyadicLeading j) ∧
    ∀ j v : Fin (K + 1), coefficient (dyadicPacket v) j =
      ∑ i : Fin (K + 1), C j i * (v : ℝ) ^ (i : ℕ)

/-- Conditional, actual-packet feasibility at every prescribed dilation
budget. Finite invertibility is proved, not assumed. The remaining analytic
providers occur explicitly in the theorem type. -/
theorem everyBudgetFeasible_of_polynomial_and_realization
    (hpoly : DyadicCoefficientPolynomialProvider)
    (hreal : ContinuousParetoRealizationTarget) : EveryBudgetFeasibleTarget := by
  intro K
  obtain ⟨C, hC, hdiag, heval⟩ := hpoly K
  let target : Fin (K + 1) → ℝ := fun j => if (j : ℕ) = 0 then 1 else 0
  obtain ⟨c, hc⟩ := exists_dyadic_coefficients K C hC hdiag target
  let b : Fin (K + 1) → ℕ → ℝ := fun v => dyadicPacket v
  let F : ℕ → ℝ := ∑ v, c v • b v
  have hmem : F ∈ FiniteTwoSeedCompletion.budgetSpan (2 ^ K) := by
    apply Submodule.sum_mem
    intro v hv
    exact (FiniteTwoSeedCompletion.budgetSpan (2 ^ K)).smul_mem _
      (dyadicPacket_mem_budget K v)
  have hb : ∀ v, AllMomentsIntegrable (b v) := by
    intro v
    exact (hreal (b v)
      (FiniteTwoSeedCompletion.budgetSpan_le_legal (2 ^ K)
        (dyadicPacket_mem_budget K v))).1
  have hFI : AllMomentsIntegrable F := allMomentsIntegrable_finite_synthesis b c hb
  have hcoeff : ∀ j : Fin (K + 1), coefficient F j = target j := by
    intro j
    rw [coefficient_finite_synthesis b c hb]
    simpa only [b, heval, mul_comm] using hc j
  refine ⟨F, hmem, hFI, ?_, ?_⟩
  · have hz : coefficient F 0 = 1 := by
      simpa [target] using hcoeff (0 : Fin (K + 1))
    have hmean := (hreal F (FiniteTwoSeedCompletion.budgetSpan_le_legal (2 ^ K) hmem)).2.1
    rw [coefficient_eq_momentTransform F hFI, laguerreMomentTransform_zero] at hz
    rw [hmean] at hz
    simpa [target] using hz
  · intro j hj hjK
    have hz := hcoeff ⟨j, Nat.lt_succ_of_le hjK⟩
    simpa [target, Nat.ne_of_gt hj] using hz

end RiemannResearch.RH.Pareto.RamanujanLaguerre
