import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Diagonal coordinate recovery and sampled gauge completeness

Source: V_Zeta_Vector_Spaces_Research_2026-09-16.md, Sections 2--3.
The analytic equidistribution input is motivated by Ford--Zaharescu,
https://arxiv.org/abs/math/0405459, equations (1.1) and (3.8).
This module proves the Hilbert-space deduction from explicit phase-average
limits. It does not prove equidistribution of actual zeta-zero ordinates.
-/

noncomputable section
open Filter
open scoped Topology BigOperators
namespace RiemannResearch.Analysis.SampledGauge

abbrev Space (ι : Type*) := lp (fun _ : ι => ℂ) 2

theorem norm_sq_eq_tsum {ι : Type*} (h : Space ι) :
    ‖h‖ ^ 2 = ∑' i, ‖h i‖ ^ 2 := by
  simpa using lp.norm_rpow_eq_tsum (p := 2) (by norm_num) h

theorem summable_norm_sq {ι : Type*} (h : Space ι) :
    Summable (fun i => ‖h i‖ ^ 2) := by
  simpa using Memℓp.summable (p := 2) (by norm_num) (lp.memℓp h)

/-- Dominated coordinate filters recover a single coordinate in norm. -/
theorem coordinate_recovery {ι : Type*} [DecidableEq ι]
    (h : Space ι) (q : ι) (u : ℕ → Space ι) (A : ℕ → ι → ℂ)
    (hval : ∀ n i, u n i = h i * A n i)
    (hbound : ∀ n i, ‖A n i‖ ≤ 1)
    (hlim : ∀ i, Tendsto (fun n => A n i) atTop
      (𝓝 (if i = q then 1 else 0))) :
    Tendsto u atTop (𝓝 (lp.single 2 q (h q))) := by
  let v : Space ι := lp.single 2 q (h q)
  have hpoint : ∀ i, Tendsto (fun n => u n i) atTop (𝓝 (v i)) := by
    intro i
    have ht := (hlim i).const_mul (h i)
    by_cases hi : i = q
    · subst i
      simpa [v, hval] using ht
    · simpa [v, hval, lp.single_apply, hi] using ht
  have hdom : ∀ n i, ‖u n i - v i‖ ^ 2 ≤ 4 * ‖h i‖ ^ 2 := by
    intro n i
    have hu : ‖u n i‖ ≤ ‖h i‖ := by
      rw [hval, norm_mul]
      simpa using mul_le_mul_of_nonneg_left (hbound n i) (norm_nonneg (h i))
    have hv : ‖v i‖ ≤ ‖h i‖ := by
      by_cases hi : i = q
      · subst i
        simp [v]
      · simp [v, lp.single_apply, hi]
    have hn := norm_sub_le (u n i) (v i)
    nlinarith [norm_nonneg (u n i - v i), norm_nonneg (h i)]
  have ht := tendsto_tsum_of_dominated_convergence
    (f := fun n i => ‖u n i - v i‖ ^ 2) (g := fun _ : ι => (0 : ℝ))
    ((summable_norm_sq h).mul_left 4)
    (fun i => by simpa using ((hpoint i).sub_const (v i)).norm.pow 2)
    (Filter.Eventually.of_forall (fun n i => by
      simpa only [Real.norm_eq_abs, abs_pow, abs_norm] using hdom n i))
  have hs : Tendsto (fun n => ‖u n - v‖ ^ 2) atTop (𝓝 (0 : ℝ)) := by
    simpa only [norm_sq_eq_tsum, lp.coeFn_sub, Pi.sub_apply, tsum_zero] using ht
  have hn := Real.continuous_sqrt.continuousAt.tendsto.comp hs
  have hn' : Tendsto (fun n => ‖u n - v‖) atTop (𝓝 (0 : ℝ)) := by
    simpa only [Function.comp_def, Real.sqrt_sq_eq_abs, abs_norm, Real.sqrt_zero] using hn
  exact tendsto_iff_norm_sub_tendsto_zero.mpr hn'

/-- Recovery inside a closed subspace implies the coordinate is in that subspace. -/
theorem single_mem_of_recovery {ι : Type*} [DecidableEq ι]
    (S : Submodule ℂ (Space ι)) (hS : IsClosed (S : Set (Space ι)))
    (h : Space ι) (q : ι) (u : ℕ → Space ι) (A : ℕ → ι → ℂ)
    (hmem : ∀ n, u n ∈ S)
    (hval : ∀ n i, u n i = h i * A n i)
    (hbound : ∀ n i, ‖A n i‖ ≤ 1)
    (hlim : ∀ i, Tendsto (fun n => A n i) atTop
      (𝓝 (if i = q then 1 else 0))) : lp.single 2 q (h q) ∈ S :=
  hS.mem_of_tendsto (coordinate_recovery h q u A hval hbound hlim)
    (Filter.Eventually.of_forall hmem)

/-- A closed subspace containing nonzero multiples of every coordinate is all of l2. -/
theorem eq_top_of_contains_coordinates {ι : Type*} [DecidableEq ι]
    (S : Submodule ℂ (Space ι)) (hS : IsClosed (S : Set (Space ι)))
    (h : Space ι) (hsupport : ∀ i, h i ≠ 0)
    (hmem : ∀ i, lp.single 2 i (h i) ∈ S) : S = ⊤ := by
  apply top_unique
  intro f hf
  have hsingle : ∀ i, lp.single 2 i (f i) ∈ S := by
    intro i
    have hm := S.smul_mem ((f i) / (h i)) (hmem i)
    rw [← lp.single_smul] at hm
    simpa only [smul_eq_mul, div_mul_cancel₀ _ (hsupport i)] using hm
  exact hS.mem_of_tendsto (lp.hasSum_single (by norm_num : (2 : ENNReal) ≠ ⊤) f)
    (Filter.Eventually.of_forall (fun s => S.sum_mem (fun i hi => hsingle i)))

/-- The finite phase covariance used to demodulate coordinate `q`. -/
def sampleKernel {ι : Type*} (phase : ℕ → ι → ℂ) (q i : ι) (n : ℕ) : ℂ :=
  (n : ℂ)⁻¹ * ∑ j ∈ Finset.range n, star (phase j q) * phase j i

/-- Finite linear combinations of the actual sampled orbit. -/
def sampleAverage {ι : Type*} (phase : ℕ → ι → ℂ) (orbit : ℕ → Space ι)
    (q : ι) (n : ℕ) : Space ι :=
  (n : ℂ)⁻¹ • ∑ j ∈ Finset.range n, star (phase j q) • orbit j

theorem sampleAverage_apply {ι : Type*} (phase : ℕ → ι → ℂ)
    (orbit : ℕ → Space ι) (h : Space ι)
    (horbit : ∀ n i, orbit n i = h i * phase n i) (q i : ι) (n : ℕ) :
    sampleAverage phase orbit q n i = h i * sampleKernel phase q i n := by
  simp only [sampleAverage, sampleKernel, lp.coeFn_smul, lp.coeFn_sum,
    Finset.sum_apply, Pi.smul_apply, smul_eq_mul, horbit,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  ring

theorem sampleKernel_norm_le_one {ι : Type*} (phase : ℕ → ι → ℂ)
    (hphase : ∀ n i, ‖phase n i‖ ≤ 1) (q i : ι) (n : ℕ) :
    ‖sampleKernel phase q i n‖ ≤ 1 := by
  by_cases hn : n = 0
  · simp [sampleKernel, hn]
  have hsum : ‖∑ j ∈ Finset.range n, star (phase j q) * phase j i‖ ≤ (n : ℝ) := by
    calc
      _ ≤ ∑ j ∈ Finset.range n, ‖star (phase j q) * phase j i‖ := norm_sum_le _ _
      _ ≤ ∑ j ∈ Finset.range n, (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro j hj
        rw [norm_mul, norm_star]
        nlinarith [hphase j q, hphase j i, norm_nonneg (phase j q),
          norm_nonneg (phase j i)]
      _ = _ := by simp
  rw [sampleKernel, norm_mul]
  calc
    _ ≤ ‖(n : ℂ)⁻¹‖ * (n : ℝ) :=
      mul_le_mul_of_nonneg_left hsum (norm_nonneg _)
    _ = 1 := by simp [norm_inv, hn]

/-- Conditional research reduction: phase-average equidistribution, together
with the concrete diagonal orbit formula, implies sampled-orbit completeness.
No completeness or coordinate-recovery conclusion is assumed as an input. -/
theorem sampled_orbit_dense {ι : Type*} [DecidableEq ι]
    (h : Space ι) (phase : ℕ → ι → ℂ) (orbit : ℕ → Space ι)
    (hsupport : ∀ i, h i ≠ 0)
    (horbit : ∀ n i, orbit n i = h i * phase n i)
    (hphase : ∀ n i, ‖phase n i‖ ≤ 1)
    (hequid : ∀ q i, Tendsto (sampleKernel phase q i) atTop
      (𝓝 (if i = q then 1 else 0))) :
    (Submodule.span ℂ (Set.range orbit)).topologicalClosure = ⊤ := by
  let S := (Submodule.span ℂ (Set.range orbit)).topologicalClosure
  have hclosed : IsClosed (S : Set (Space ι)) :=
    (Submodule.span ℂ (Set.range orbit)).isClosed_topologicalClosure
  apply eq_top_of_contains_coordinates S hclosed h hsupport
  intro q
  apply single_mem_of_recovery S hclosed h q (sampleAverage phase orbit q)
    (fun n i => sampleKernel phase q i n)
  · intro n
    apply S.smul_mem
    apply S.sum_mem
    intro j hj
    apply S.smul_mem
    exact (Submodule.span ℂ (Set.range orbit)).le_topologicalClosure
      (Submodule.subset_span ⟨j, rfl⟩)
  · intro n i
    exact sampleAverage_apply phase orbit h horbit q i n
  · intro n i
    exact sampleKernel_norm_le_one phase hphase q i n
  · exact hequid q

/-- The diagonal action is constructed in l2 using exact preservation of
coordinate magnitudes, rather than postulated as an abstract orbit. -/
def diagonalOrbit {ι : Type*} (h : Space ι) (phase : ℕ → ι → ℂ)
    (hphase : ∀ n i, ‖phase n i‖ = 1) (n : ℕ) : Space ι :=
  ⟨fun i => h i * phase n i, by
    apply Memℓp.of_norm
    simpa only [norm_mul, hphase, mul_one] using (lp.memℓp h).norm⟩

theorem diagonalOrbit_dense {ι : Type*} [DecidableEq ι]
    (h : Space ι) (phase : ℕ → ι → ℂ)
    (hphase : ∀ n i, ‖phase n i‖ = 1)
    (hsupport : ∀ i, h i ≠ 0)
    (hequid : ∀ q i, Tendsto (sampleKernel phase q i) atTop
      (𝓝 (if i = q then 1 else 0))) :
    (Submodule.span ℂ (Set.range (diagonalOrbit h phase hphase))).topologicalClosure = ⊤ :=
  sampled_orbit_dense h phase (diagonalOrbit h phase hphase) hsupport
    (fun _ _ => rfl) (fun n i => le_of_eq (hphase n i)) hequid

/-- At prime-power coordinates take `frequency q = log q`; for the
application the sampling times enumerate the positive zero ordinates. -/
def gaugePhase {ι : Type*} (frequency : ι → ℝ) (times : ℕ → ℝ)
    (n : ℕ) (i : ι) : ℂ :=
  Complex.exp ((times n * frequency i : ℝ) * Complex.I)

theorem gaugePhase_norm {ι : Type*} (frequency : ι → ℝ) (times : ℕ → ℝ)
    (n : ℕ) (i : ι) : ‖gaugePhase frequency times n i‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I _

def gaugeOrbit {ι : Type*} (h : Space ι) (frequency : ι → ℝ) (times : ℕ → ℝ) :=
  diagonalOrbit h (gaugePhase frequency times) (gaugePhase_norm frequency times)

/-- The only analytic sampling input is the explicitly displayed normalized
phase covariance limit. In particular, RH is not a hypothesis. -/
theorem gaugeOrbit_dense_of_phase_limits {ι : Type*} [DecidableEq ι]
    (h : Space ι) (frequency : ι → ℝ) (times : ℕ → ℝ)
    (hsupport : ∀ i, h i ≠ 0)
    (hequid : ∀ q i, Tendsto (sampleKernel (gaugePhase frequency times) q i) atTop
      (𝓝 (if i = q then 1 else 0))) :
    (Submodule.span ℂ (Set.range (gaugeOrbit h frequency times))).topologicalClosure = ⊤ :=
  diagonalOrbit_dense h _ (gaugePhase_norm frequency times) hsupport hequid

/-- The limiting diagonal covariance has no positive lower bound. Even an
arbitrary fixed finite rescaling cannot repair its vanishing eigenvalues. -/
theorem no_positive_coordinate_lower_bound (h : Space ℕ) (W A : ℝ) (hA : 0 < A) :
    ¬ ∀ i, A ≤ W * ‖h i‖ ^ 2 := by
  intro hb
  have ht : Tendsto (fun i => W * ‖h i‖ ^ 2) atTop (𝓝 (0 : ℝ)) := by
    simpa using ((summable_norm_sq h).tendsto_atTop_zero).const_mul W
  have hle : A ≤ 0 := ge_of_tendsto ht (Filter.Eventually.of_forall hb)
  exact (not_le_of_gt hA) hle

end RiemannResearch.Analysis.SampledGauge
