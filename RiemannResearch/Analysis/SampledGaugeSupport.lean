import RiemannResearch.Analysis.SampledGaugeCompleteness
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Tactic.NormNum

/-!
# Exact support closure and scalar weighting obstruction

Source: user-provided `V_vector_space_RH.pdf`, Sections 2--3, equations
(2.3)--(2.4). This module strengthens the previous full-support reduction to
the exact support subspace and formalizes the obstruction for arbitrary scalar
weights using finite partial energies. The normalized phase-limit assumption
remains explicit; it is not a formal proof of the actual-zero analytic input.
-/

noncomputable section
open Filter
open scoped Topology BigOperators
namespace RiemannResearch.Analysis.SampledGauge

/-- The coordinate subspace supported wherever `h` is nonzero. -/
def supportSubspace {ι : Type*} (h : Space ι) : Submodule ℂ (Space ι) where
  carrier := {f | ∀ i, h i = 0 → f i = 0}
  zero_mem' := by simp
  add_mem' := by
    intro f g hf hg i hi
    simp [hf i hi, hg i hi]
  smul_mem' := by
    intro c f hf i hi
    simp [hf i hi]

theorem supportSubspace_isClosed {ι : Type*} (h : Space ι) :
    IsClosed (supportSubspace h : Set (Space ι)) := by
  change IsClosed {f : Space ι | ∀ i, h i = 0 → f i = 0}
  simp only [Set.ofPred_forall]
  exact isClosed_iInter (fun i => isClosed_iInter (fun _ =>
    isClosed_eq ((lp.evalCLM ℂ (fun _ : ι => ℂ) 2 i).continuous) continuous_const))

/-- Exact version of the sampled-span theorem, including zero coordinates. -/
theorem sampled_orbit_closure_eq_support {ι : Type*} [DecidableEq ι]
    (h : Space ι) (phase : ℕ → ι → ℂ) (orbit : ℕ → Space ι)
    (horbit : ∀ n i, orbit n i = h i * phase n i)
    (hphase : ∀ n i, ‖phase n i‖ ≤ 1)
    (hequid : ∀ q i, Tendsto (sampleKernel phase q i) atTop
      (𝓝 (if i = q then 1 else 0))) :
    (Submodule.span ℂ (Set.range orbit)).topologicalClosure = supportSubspace h := by
  let S := (Submodule.span ℂ (Set.range orbit)).topologicalClosure
  have hclosed : IsClosed (S : Set (Space ι)) :=
    (Submodule.span ℂ (Set.range orbit)).isClosed_topologicalClosure
  apply le_antisymm
  · apply Submodule.topologicalClosure_minimal
    · apply Submodule.span_le.mpr
      rintro _ ⟨n, rfl⟩ i hi
      simp [horbit, hi]
    · exact supportSubspace_isClosed h
  · intro f hf
    have hrecover (q : ι) : lp.single 2 q (h q) ∈ S := by
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
    have hsingle : ∀ i, lp.single 2 i (f i) ∈ S := by
      intro i
      by_cases hi : h i = 0
      · have hfi : f i = 0 := hf i hi
        simp [hfi]
      · have hm := S.smul_mem ((f i) / (h i)) (hrecover i)
        rw [← lp.single_smul] at hm
        simpa only [smul_eq_mul, div_mul_cancel₀ _ hi] using hm
    exact hclosed.mem_of_tendsto
      (lp.hasSum_single (by norm_num : (2 : ENNReal) ≠ ⊤) f)
      (Filter.Eventually.of_forall (fun s => S.sum_mem (fun i _ => hsingle i)))

/-- Finite weighted sample energy of a normalized coordinate test vector. -/
def coordinateSampleEnergy {ι : Type*} (w : ℕ → ℝ)
    (orbit : ℕ → Space ι) (i : ι) (n : ℕ) : ℝ :=
  ∑ j ∈ Finset.range n, w j * ‖orbit j i‖ ^ 2

theorem coordinateSampleEnergy_eq {ι : Type*} (w : ℕ → ℝ)
    (orbit : ℕ → Space ι) (h : Space ι)
    (hmag : ∀ n i, ‖orbit n i‖ = ‖h i‖) (i : ι) (n : ℕ) :
    coordinateSampleEnergy w orbit i n =
      (∑ j ∈ Finset.range n, w j) * ‖h i‖ ^ 2 := by
  simp only [coordinateSampleEnergy, hmag, Finset.sum_mul]

/-- No scalar weighting can have both a uniform upper bound on one nonzero
coordinate and a positive eventual lower bound on every coordinate. The use
of finite sums avoids any a priori summability assumption on the weights. -/
theorem no_scalar_weighted_coordinate_frame
    (w : ℕ → ℝ) (orbit : ℕ → Space ℕ) (h : Space ℕ)
    (hmag : ∀ n i, ‖orbit n i‖ = ‖h i‖)
    (q : ℕ) (hq : h q ≠ 0) (A B : ℝ) (hA : 0 < A)
    (hupper : ∀ n, coordinateSampleEnergy w orbit q n ≤ B) :
    ¬ ∀ i, ∃ n, A ≤ coordinateSampleEnergy w orbit i n := by
  intro hlower
  have hqpos : 0 < ‖h q‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hq)
  have hw (n : ℕ) : (∑ j ∈ Finset.range n, w j) ≤ B / ‖h q‖ ^ 2 := by
    apply (le_div_iff₀ hqpos).mpr
    simpa only [coordinateSampleEnergy_eq w orbit h hmag] using hupper n
  apply no_positive_coordinate_lower_bound h (B / ‖h q‖ ^ 2) A hA
  intro i
  obtain ⟨n, hn⟩ := hlower i
  rw [coordinateSampleEnergy_eq w orbit h hmag] at hn
  exact hn.trans (mul_le_mul_of_nonneg_right (hw n) (sq_nonneg _))

/-- The Hilbert-space dual contains exactly the coordinates absent from the
sampled support. The statement does not claim a stable inverse. -/
theorem mem_supportSubspace_orthogonal_iff {ι : Type*}
    (h v : Space ι) :
    v ∈ (supportSubspace h)ᗮ ↔ ∀ i, h i ≠ 0 → v i = 0 := by
  classical
  rw [Submodule.mem_orthogonal]
  constructor
  · intro hv i hi
    have hm : lp.single 2 i (1 : ℂ) ∈ supportSubspace h := by
      intro j hj
      have hji : j ≠ i := by
        intro he
        subst j
        exact hi hj
      simp [lp.single_apply, hji]
    have he := hv (lp.single 2 i (1 : ℂ)) hm
    simpa [lp.inner_single_left, RCLike.inner_apply] using he
  · intro hv u hu
    rw [lp.inner_eq_tsum]
    have hh : ∀ i, inner ℂ (u i) (v i) = 0 := by
      intro i
      by_cases hi : h i = 0
      · rw [hu i hi]
        simp
      · rw [hv i hi]
        simp
    simp only [hh, tsum_zero]

/-- Exact dual of the closed sampled span. -/
theorem mem_sampled_orbit_orthogonal_iff {ι : Type*} [DecidableEq ι]
    (h : Space ι) (phase : ℕ → ι → ℂ) (orbit : ℕ → Space ι)
    (horbit : ∀ n i, orbit n i = h i * phase n i)
    (hphase : ∀ n i, ‖phase n i‖ ≤ 1)
    (hequid : ∀ q i, Tendsto (sampleKernel phase q i) atTop
      (𝓝 (if i = q then 1 else 0))) (v : Space ι) :
    v ∈ ((Submodule.span ℂ (Set.range orbit)).topologicalClosure)ᗮ ↔
      ∀ i, h i ≠ 0 → v i = 0 := by
  rw [sampled_orbit_closure_eq_support h phase orbit horbit hphase hequid]
  exact mem_supportSubspace_orthogonal_iff h v

/-- The unweighted orbit already fails the Bessel upper bound on one nonzero
coordinate; no completeness or equidistribution input is needed. -/
theorem unweighted_coordinate_not_bounded
    (orbit : ℕ → Space ℕ) (h : Space ℕ)
    (hmag : ∀ n i, ‖orbit n i‖ = ‖h i‖)
    (q : ℕ) (hq : h q ≠ 0) :
    ¬ ∃ B : ℝ, ∀ n, coordinateSampleEnergy (fun _ => 1) orbit q n ≤ B := by
  rintro ⟨B, hB⟩
  have hp : 0 < ‖h q‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hq)
  obtain ⟨n, hn⟩ := exists_nat_gt (B / ‖h q‖ ^ 2)
  have hn' : B < (n:ℝ) * ‖h q‖ ^ 2 := (div_lt_iff₀ hp).mp hn
  have hb := hB n
  rw [coordinateSampleEnergy_eq (fun _ => 1) orbit h hmag q n] at hb
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one] at hb
  exact (not_le_of_gt hn') hb

/-- Square summability rules out a positive rescaled coordinate lower bound
even when it is required only on an arbitrary infinite nonzero support. -/
theorem no_positive_lower_bound_on_infinite_support
    (h : Space ℕ) (hinfinite : Set.Infinite {i | h i ≠ 0})
    (W A : ℝ) (hA : 0 < A) :
    ¬ ∀ i, h i ≠ 0 → A ≤ W * ‖h i‖ ^ 2 := by
  intro hb
  have ht : Tendsto (fun i => W * ‖h i‖ ^ 2) atTop (𝓝 (0 : ℝ)) := by
    simpa using ((summable_norm_sq h).tendsto_atTop_zero).const_mul W
  have he : ∀ᶠ i in atTop, W * ‖h i‖ ^ 2 < A :=
    ht.eventually (Iio_mem_nhds hA)
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp he
  have hsub : {i | h i ≠ 0} ⊆ (Finset.range N : Set ℕ) := by
    intro i hi
    apply Finset.mem_range.mpr
    by_contra hlt
    have hNi : N ≤ i := Nat.le_of_not_gt hlt
    exact (not_lt_of_ge (hb i hi)) (hN i hNi)
  exact hinfinite ((Finset.range N).finite_toSet.subset hsub)

/-- The scalar-frame obstruction on the actual support, including sparse
infinite supports. The upper bound is needed at only one nonzero coordinate. -/
theorem no_scalar_weighted_frame_on_infinite_support
    (w : ℕ → ℝ) (orbit : ℕ → Space ℕ) (h : Space ℕ)
    (hmag : ∀ n i, ‖orbit n i‖ = ‖h i‖)
    (hinfinite : Set.Infinite {i | h i ≠ 0})
    (q : ℕ) (hq : h q ≠ 0) (A B : ℝ) (hA : 0 < A)
    (hupper : ∀ n, coordinateSampleEnergy w orbit q n ≤ B) :
    ¬ ∀ i, h i ≠ 0 → ∃ n, A ≤ coordinateSampleEnergy w orbit i n := by
  intro hlower
  have hqpos : 0 < ‖h q‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hq)
  have hw (n : ℕ) : (∑ j ∈ Finset.range n, w j) ≤ B / ‖h q‖ ^ 2 := by
    apply (le_div_iff₀ hqpos).mpr
    simpa only [coordinateSampleEnergy_eq w orbit h hmag] using hupper n
  apply no_positive_lower_bound_on_infinite_support h hinfinite
    (B / ‖h q‖ ^ 2) A hA
  intro i hi
  obtain ⟨n, hn⟩ := hlower i hi
  rw [coordinateSampleEnergy_eq w orbit h hmag] at hn
  exact hn.trans (mul_le_mul_of_nonneg_right (hw n) (sq_nonneg _))

end RiemannResearch.Analysis.SampledGauge
