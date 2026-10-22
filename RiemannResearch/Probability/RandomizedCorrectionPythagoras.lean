import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Tactic

/-!
# Randomized coefficients and exact expected Hilbert loss

Source: user-provided conditional-iid/Cesaro handoff, Section 9, and its
mathematical completion, Section 12. The ordinary argument was completed in
`RandomCoefficientPythagorasProof.md` before this Lean candidate was drafted.

All random vectors below satisfy actual `MemLp ... 2` hypotheses. In particular,
the Bochner means, mixed terms, and squared losses are genuinely integrable.
There is no independence hypothesis and no omitted signed cross term.
Source awaits coordinator verification.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false

namespace RiemannResearch.Probability.RandomizedCorrection

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

section Banach
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- Scalar coefficients with second moments give vector-valued L² multiples. -/
theorem memLp_smul_fixed {a : Ω → ℝ} (ha : MemLp a 2 μ) (w : E) :
    MemLp (fun ω => a ω • w) 2 μ := by
  simpa using ha.continuousLinearMap_comp ((ContinuousLinearMap.id ℝ ℝ).smulRight w)

/-- A fixed finite synthesis is L² under coordinatewise second moments. -/
theorem finite_synthesis_memLp {ι : Type*} (s : Finset ι) (w : ι → E)
    (A : ι → Ω → ℝ) (hA : ∀ i ∈ s, MemLp (A i) 2 μ) :
    MemLp (fun ω => ∑ i ∈ s, A i ω • w i) 2 μ :=
  memLp_finset_sum s (fun i hi => memLp_smul_fixed (hA i hi) (w i))

/-- The mean synthesis is the synthesis of the actual scalar means. -/
theorem integral_finite_synthesis {ι : Type*} (s : Finset ι) (w : ι → E)
    (A : ι → Ω → ℝ) (hA : ∀ i ∈ s, MemLp (A i) 2 μ) :
    (∫ ω, (∑ i ∈ s, A i ω • w i) ∂μ) =
      ∑ i ∈ s, (∫ ω, A i ω ∂μ) • w i := by
  rw [integral_finset_sum]
  · apply Finset.sum_congr rfl
    intro i hi
    exact integral_smul_const (A i) (w i)
  · intro i hi
    exact (memLp_smul_fixed (hA i hi) (w i)).integrable one_le_two

/-- Almost-sure affine constraints on finite coefficients survive taking their means. -/
theorem mean_coefficients_preserve_constraint {ι : Type*} (s : Finset ι) (v : ι → E)
    (A : ι → Ω → ℝ) (hA : ∀ i ∈ s, MemLp (A i) 2 μ) (b : E)
    (hconstraint : ∀ᵐ ω ∂μ, (∑ i ∈ s, A i ω • v i) = b) :
    (∑ i ∈ s, (∫ ω, A i ω ∂μ) • v i) = b := by
  rw [← integral_finite_synthesis s v A hA]
  calc
    _ = ∫ _ω : Ω, b ∂μ := integral_congr_ae hconstraint
    _ = b := by simp

end Banach

section Hilbert
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The quadratic loss is integrable before any integral expansion is performed. -/
theorem quadratic_loss_integrable {X : Ω → E} (hX : MemLp X 2 μ) (e : E) :
    Integrable (fun ω => ‖e - X ω‖ ^ 2) μ :=
  ((memLp_const e).sub hX).norm.integrable_sq

/-- Exact Hilbert bias/variance identity, proved from its signed cross term. -/
theorem expected_quadratic_loss_decomposition {X : Ω → E}
    (hX : MemLp X 2 μ) (e : E) :
    (∫ ω, ‖e - X ω‖ ^ 2 ∂μ) =
      ‖e - ∫ ω, X ω ∂μ‖ ^ 2 +
        ∫ ω, ‖X ω - ∫ η, X η ∂μ‖ ^ 2 ∂μ := by
  let m : E := ∫ ω, X ω ∂μ
  have hXi : Integrable X μ := hX.integrable one_le_two
  have hZ : MemLp (fun ω => X ω - m) 2 μ := hX.sub (memLp_const m)
  have hZi : Integrable (fun ω => X ω - m) μ := hZ.integrable one_le_two
  have hZsq : Integrable (fun ω => ‖X ω - m‖ ^ 2) μ := hZ.norm.integrable_sq
  have hcross : Integrable (fun ω => inner ℝ (e - m) (X ω - m)) μ :=
    Integrable.const_inner (e - m) hZi
  have hmean : (∫ ω, (X ω - m) ∂μ) = 0 := by
    rw [integral_sub hXi (integrable_const m)]
    simp [m]
  have hcross_zero : (∫ ω, inner ℝ (e - m) (X ω - m) ∂μ) = 0 := by
    rw [integral_inner hZi, hmean]
    simp
  have hpoint : (fun ω => ‖e - X ω‖ ^ 2) =
      (fun ω => (‖e - m‖ ^ 2 + ‖X ω - m‖ ^ 2) -
        2 * inner ℝ (e - m) (X ω - m)) := by
    funext ω
    have he : e - X ω = (e - m) - (X ω - m) := by abel
    rw [he, norm_sub_sq_real]
    ring
  have hconst : Integrable (fun _ω : Ω => ‖e - m‖ ^ 2) μ := integrable_const _
  have hsum : Integrable (fun ω => ‖e - m‖ ^ 2 + ‖X ω - m‖ ^ 2) μ :=
    hconst.add hZsq
  have htwocross : Integrable (fun ω => 2 * inner ℝ (e - m) (X ω - m)) μ :=
    hcross.const_mul 2
  rw [hpoint, integral_sub hsum htwocross,
    integral_add hconst hZsq, integral_const_mul, hcross_zero]
  simp [m]

/-- Randomization cannot improve expected squared loss over the deterministic mean. -/
theorem deterministic_mean_loss_le {X : Ω → E} (hX : MemLp X 2 μ) (e : E) :
    ‖e - ∫ ω, X ω ∂μ‖ ^ 2 ≤ ∫ ω, ‖e - X ω‖ ^ 2 ∂μ := by
  rw [expected_quadratic_loss_decomposition hX e]
  exact le_add_of_nonneg_right (integral_nonneg (fun _ => sq_nonneg _))

/-- Exact finite-coefficient version, with every covariance retained inside the norm. -/
theorem finite_coefficient_loss_decomposition {ι : Type*} (s : Finset ι)
    (w : ι → E) (A : ι → Ω → ℝ) (hA : ∀ i ∈ s, MemLp (A i) 2 μ) (e : E) :
    (∫ ω, ‖e - ∑ i ∈ s, A i ω • w i‖ ^ 2 ∂μ) =
      ‖e - ∑ i ∈ s, (∫ ω, A i ω ∂μ) • w i‖ ^ 2 +
        ∫ ω, ‖∑ i ∈ s, (A i ω - ∫ η, A i η ∂μ) • w i‖ ^ 2 ∂μ := by
  have h := expected_quadratic_loss_decomposition (finite_synthesis_memLp s w A hA) e
  rw [integral_finite_synthesis s w A hA] at h
  have he (ω : Ω) :
      (∑ i ∈ s, A i ω • w i) - (∑ i ∈ s, (∫ η, A i η ∂μ) • w i) =
        ∑ i ∈ s, (A i ω - ∫ η, A i η ∂μ) • w i := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    rw [sub_smul]
  simpa only [he] using h

/-- Both terms in the finite-coefficient quadratic comparison are actual integrals. -/
theorem finite_coefficient_loss_integrable {ι : Type*} (s : Finset ι)
    (w : ι → E) (A : ι → Ω → ℝ) (hA : ∀ i ∈ s, MemLp (A i) 2 μ) (e : E) :
    Integrable (fun ω => ‖e - ∑ i ∈ s, A i ω • w i‖ ^ 2) μ :=
  quadratic_loss_integrable (finite_synthesis_memLp s w A hA) e

/-- The deterministic mean coefficients achieve no larger loss. -/
theorem finite_mean_coefficients_loss_le {ι : Type*} (s : Finset ι)
    (w : ι → E) (A : ι → Ω → ℝ) (hA : ∀ i ∈ s, MemLp (A i) 2 μ) (e : E) :
    ‖e - ∑ i ∈ s, (∫ ω, A i ω ∂μ) • w i‖ ^ 2 ≤
      ∫ ω, ‖e - ∑ i ∈ s, A i ω • w i‖ ^ 2 ∂μ := by
  rw [finite_coefficient_loss_decomposition s w A hA e]
  exact le_add_of_nonneg_right (integral_nonneg (fun _ => sq_nonneg _))

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]

/-- The exact same identity survives any continuous linear smoothing operator. -/
theorem smoothed_expected_loss_decomposition (C : E →L[ℝ] H)
    {X : Ω → E} (hX : MemLp X 2 μ) (e : E) :
    (∫ ω, ‖C (e - X ω)‖ ^ 2 ∂μ) =
      ‖C (e - ∫ ω, X ω ∂μ)‖ ^ 2 +
        ∫ ω, ‖C (X ω - ∫ η, X η ∂μ)‖ ^ 2 ∂μ := by
  have h := expected_quadratic_loss_decomposition (hX.continuousLinearMap_comp C) (C e)
  rw [C.integral_comp_comm (hX.integrable one_le_two)] at h
  simpa only [map_sub] using h

/-- Finite randomized corrections after the actual conditional-mean map can be
instantiated here with its continuous linear Hilbert-space realization. -/
theorem smoothed_finite_coefficient_loss_decomposition (C : E →L[ℝ] H)
    {ι : Type*} (s : Finset ι) (w : ι → E) (A : ι → Ω → ℝ)
    (hA : ∀ i ∈ s, MemLp (A i) 2 μ) (e : E) :
    (∫ ω, ‖C (e - ∑ i ∈ s, A i ω • w i)‖ ^ 2 ∂μ) =
      ‖C (e - ∑ i ∈ s, (∫ ω, A i ω ∂μ) • w i)‖ ^ 2 +
        ∫ ω, ‖C (∑ i ∈ s, (A i ω - ∫ η, A i η ∂μ) • w i)‖ ^ 2 ∂μ := by
  simpa only [map_sub, map_sum, map_smul] using
    finite_coefficient_loss_decomposition s (fun i => C (w i)) A hA (C e)

end Hilbert
end RiemannResearch.Probability.RandomizedCorrection
