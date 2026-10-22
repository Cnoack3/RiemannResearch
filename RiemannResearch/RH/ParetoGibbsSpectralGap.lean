import RiemannResearch.Analysis.PositiveQuadraticNorm
import RiemannResearch.RH.ParetoGibbsTailMatrix
import RiemannResearch.RH.ParetoGibbsSchurEnergy
import RiemannResearch.RH.ParetoGibbsHilbertEnergy
import RiemannResearch.RH.ParetoGibbsRepair
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-!
# The unconditional pi/4 contraction on the actual mean-zero Hilbert space

The complete tail basis, actual operator matrix, exact infinite Schur row
bound, and positivity of the Gibbs operator are combined here. Finite sums
are an intermediate dense domain; continuity transfers their uniform bound
to the whole actual mean-zero space. No spectral-gap assumption remains.
-/

open Filter
open scoped BigOperators Topology

namespace RiemannResearch.RH.Pareto
noncomputable section

theorem tailBasis_sum_norm_sq (s : Finset ℕ) (v : ℕ → ℝ) :
    ‖∑ n ∈ s, v n • tailBasisHilbert n‖ ^ 2 = ∑ n ∈ s, (v n)^2 := by
  rw [← real_inner_self_eq_norm_sq]
  simp only [sum_inner, inner_sum, inner_smul_left, inner_smul_right,
    RCLike.conj_to_real, tailBasis_inner]
  apply Finset.sum_congr rfl
  intro n hn
  simp [mul_ite, hn, pow_two]

theorem tailBasis_sum_gibbs_quadratic (s : Finset ℕ) (v : ℕ → ℝ) :
    inner ℝ (∑ n ∈ s, v n • tailBasisHilbert n)
      (hilbertGibbs (∑ n ∈ s, v n • tailBasisHilbert n)) =
        ∑ n ∈ s, ∑ m ∈ s, v n * v m * gibbsComplementKernel n m := by
  change inner ℝ (∑ n ∈ s, v n • tailBasisHilbert n)
    (hilbertGibbsLinear (∑ n ∈ s, v n • tailBasisHilbert n)) = _
  rw [map_sum]
  simp only [map_smul]
  change inner ℝ (∑ n ∈ s, v n • tailBasisHilbert n)
    (∑ n ∈ s, v n • hilbertGibbs (tailBasisHilbert n)) = _
  simp only [sum_inner, inner_sum, inner_smul_left, inner_smul_right,
    RCLike.conj_to_real, tailBasis_gibbs_inner]
  apply Finset.sum_congr rfl
  intro n hn
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m hm
  rw [gibbsComplementKernel_symm m n]
  ring

theorem tailBasisSpan_gibbs_quadratic_le (f : ThresholdHilbert) (hf : f ∈ tailBasisSpan) :
    inner ℝ f (hilbertGibbs f) ≤ (Real.pi / 4) * ‖f‖ ^ 2 := by
  change f ∈ Submodule.span ℝ (Set.range tailBasisHilbert) at hf
  obtain ⟨c, rfl⟩ := Finsupp.mem_span_range_iff_exists_finsupp.1 hf
  change inner ℝ (∑ n ∈ c.support, c n • tailBasisHilbert n)
    (hilbertGibbs (∑ n ∈ c.support, c n • tailBasisHilbert n)) ≤
      (Real.pi / 4) * ‖∑ n ∈ c.support, c n • tailBasisHilbert n‖ ^ 2
  rw [tailBasis_sum_norm_sq, tailBasis_sum_gibbs_quadratic]
  exact gibbsComplementKernel_quadratic_le c.support c

/-- The finite uniform quadratic estimate extends to every actual mean-zero
vector, using the proved density of the orthonormal tail basis. -/
theorem hilbertGibbs_meanZero_quadratic_le (f : ThresholdHilbert)
    (hf : inner ℝ f hilbertOne = 0) :
    inner ℝ f (hilbertGibbs f) ≤ (Real.pi / 4) * ‖f‖ ^ 2 := by
  have hfc : f ∈ tailBasisSpan.topologicalClosure := by
    rw [tailBasisSpan_closure]
    exact Submodule.mem_orthogonal_singleton_iff_inner_left.2 hf
  have hc : Continuous (fun x : ThresholdHilbert => inner ℝ x (hilbertGibbs x)) := by
    exact continuous_id.inner hilbertGibbsContinuous.continuous
  have hd : Continuous (fun x : ThresholdHilbert => (Real.pi / 4) * ‖x‖ ^ 2) :=
    continuous_const.mul (continuous_norm.pow 2)
  have hclosed : IsClosed {x : ThresholdHilbert |
      inner ℝ x (hilbertGibbs x) ≤ (Real.pi / 4) * ‖x‖ ^ 2} := isClosed_le hc hd
  have hsub : (tailBasisSpan : Set ThresholdHilbert) ⊆
      {x | inner ℝ x (hilbertGibbs x) ≤ (Real.pi / 4) * ‖x‖ ^ 2} :=
    fun x hx => tailBasisSpan_gibbs_quadratic_le x hx
  exact closure_minimal hsub hclosed hfc

/-- The actual pi/4 bound follows from positive-form Cauchy--Schwarz. -/
theorem hilbertGibbs_meanZero_norm_le (f : ThresholdHilbert)
    (hf : inner ℝ f hilbertOne = 0) :
    ‖hilbertGibbs f‖ ≤ (Real.pi / 4) * ‖f‖ := by
  have hsym : ∀ x y : ThresholdHilbert,
      inner ℝ x (hilbertGibbsLinear y) = inner ℝ y (hilbertGibbsLinear x) := by
    intro x y
    calc
      inner ℝ x (hilbertGibbs y) = inner ℝ (hilbertGibbs x) y :=
        (hilbertGibbs_pairing_symm x y).symm
      _ = inner ℝ y (hilbertGibbs x) := real_inner_comm _ _
  apply Analysis.PositiveQuadraticNorm.norm_apply_le_of_quadratic_bounds
    hilbertGibbsLinear hsym hilbertGibbs_inner_nonneg f (Real.pi / 4) (by positivity)
  · exact hilbertGibbs_meanZero_quadratic_le f hf
  · apply hilbertGibbs_meanZero_quadratic_le
    change inner ℝ (hilbertGibbs f) hilbertOne = 0
    rw [hilbertGibbs_mean_inner, hf]

/-- The spectral-gap proposition introduced as an open target is discharged
by a proof on the actual infinite operator. -/
theorem paretoGibbsSharpGap : ParetoGibbsSharpGap := by
  intro f hf
  apply hilbertGibbs_meanZero_norm_le
  rw [hilbertGibbs_inner_one]
  exact hf

/-- The only remaining hypothesis here is a genuinely vanishing sequence of
actual arithmetic repairs; the analytic contraction is now proved. -/
theorem hilbertGibbs_repair_convergence (F : ℕ → ThresholdHilbert)
    (hm : ∀ n, hilbertMeanContinuous (F n) = 1)
    (he : Tendsto (Analysis.ContractiveRepair.repairError hilbertGibbsLinear F)
      atTop (𝓝 0)) : Tendsto F atTop (𝓝 hilbertOne) :=
  hilbertGibbs_tendsto_of_vanishing_repair paretoGibbsSharpGap F hm he

/-- Arithmetic repair existence is exactly the original closed approximation
condition, with the actual operator's contraction supplied unconditionally. -/
theorem hilbertGibbs_legal_repair_iff_closure_unconditional :
    Analysis.ContractiveRepair.HasVanishingRepairOrbit
      (hilbertLegalSubspace {2, 3}) hilbertGibbsContinuous hilbertMeanContinuous ↔
        hilbertOne ∈ hilbertLegalClosure {2, 3} :=
  hilbertGibbs_legal_repair_iff_closure paretoGibbsSharpGap

end
end RiemannResearch.RH.Pareto
