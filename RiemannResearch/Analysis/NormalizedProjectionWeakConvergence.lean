import RiemannResearch.Analysis.WeakConvergenceDenseTests
import RiemannResearch.Analysis.ExhaustiveProjectionWalk

/-!
# Canonical normalized optimizer residuals converge weakly to zero

Source: standard Hilbert-space projection geometry used in the exact optimizer
cancellation continuation, 8 October 2026. The dense-test extension is the
existing `WeakConvergenceDenseTests` theorem.

When legal approximants converge strongly to the target, that target lies in
the closed dictionary span. Their normalized orthogonal residuals stay in the
same closed span and are eventually orthogonal to every fixed generator.
Uniform unit norm therefore gives all weak pairings by density. Orthogonal
projection of an arbitrary test onto the closed span extends the result to
all of the ambient Hilbert space. No assumption that the dictionary spans the
entire ambient space is made.
-/

noncomputable section
open Filter
open scoped Topology

namespace RiemannResearch.Analysis.NormalizedProjectionWeakConvergence

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Unit normalization of a nonzero residual. -/
def normalizedResidual (r : H) : H := ‖r‖⁻¹ • r

theorem normalizedResidual_norm_eq_one (r : H) (hr : r ≠ 0) :
    ‖normalizedResidual r‖ = 1 := by
  rw [normalizedResidual, norm_smul, Real.norm_eq_abs, abs_inv,
    abs_of_nonneg (norm_nonneg r), inv_mul_cancel₀ (norm_ne_zero_iff.mpr hr)]

variable [CompleteSpace H]

/-- Dense fixed atom tests control normalized residuals in the actual closed
span; ambient tests are projected onto that span. -/
theorem normalizedResidual_inner_tendsto_zero
    {ι : Type*} (v : ι → H) (x : H) (p : ℕ → H)
    (hp : ∀ n, p n ∈ Submodule.span ℝ (Set.range v))
    (hr : Tendsto (fun n => x - p n) atTop (𝓝 0))
    (hne : ∀ n, x - p n ≠ 0)
    (horth : ∀ i, ∀ᶠ n in atTop, inner ℝ (v i) (x - p n) = 0)
    (y : H) :
    Tendsto (fun n => inner ℝ y (normalizedResidual (x - p n))) atTop (𝓝 0) := by
  let C : Submodule ℝ H := (Submodule.span ℝ (Set.range v)).topologicalClosure
  letI : C.HasOrthogonalProjection := by dsimp [C]; infer_instance
  have hclosed : IsClosed (C : Set H) :=
    (Submodule.span ℝ (Set.range v)).isClosed_topologicalClosure
  have hpC : ∀ n, p n ∈ C := fun n =>
    (Submodule.span ℝ (Set.range v)).le_topologicalClosure (hp n)
  have hpLimit : Tendsto p atTop (𝓝 x) := by
    have h := (tendsto_const_nhds (x := x)).sub hr
    have heq : (fun n => x - (x - p n)) = p := by
      funext n
      abel
    simpa only [sub_zero, heq] using h
  have hx : x ∈ C :=
    hclosed.mem_of_tendsto hpLimit (Eventually.of_forall hpC)
  let u : ℕ → H := fun n => normalizedResidual (x - p n)
  have huC : ∀ n, u n ∈ C := by
    intro n
    exact C.smul_mem _ (C.sub_mem hx (hpC n))
  have hbound : ∀ᶠ n in atTop, ‖u n‖ ≤ (1 : ℝ) := by
    apply Eventually.of_forall
    intro n
    change ‖normalizedResidual (x - p n)‖ ≤ 1
    rw [normalizedResidual_norm_eq_one _ (hne n)]
  have hgen : ∀ w ∈ Set.range v,
      Tendsto (fun n => inner ℝ w (u n)) atTop (𝓝 0) := by
    rintro w ⟨i, rfl⟩
    apply (tendsto_const_nhds :
      Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0)).congr'
    filter_upwards [horth i] with n hn
    simp [u, normalizedResidual, inner_smul_right, hn]
  have htest : Tendsto (fun n => inner ℝ (C.starProjection y) (u n))
      atTop (𝓝 0) :=
    tendsto_inner_zero_of_mem_closure_span (by norm_num) hbound hgen
      (C.starProjection_apply_mem y)
  have heq : (fun n => inner ℝ y (u n)) =
      (fun n => inner ℝ (C.starProjection y) (u n)) := by
    funext n
    have ho : inner ℝ (y - C.starProjection y) (u n) = 0 := by
      rw [real_inner_comm]
      exact (C.mem_orthogonal _).mp
        (Submodule.sub_starProjection_mem_orthogonal y) _ (huC n)
    rw [inner_sub_left] at ho
    exact sub_eq_zero.mp ho
  change Tendsto (fun n => inner ℝ y (u n)) atTop (𝓝 0)
  rw [heq]
  exact htest

open RiemannResearch.Analysis.ExhaustiveWalk

/-- For cumulative canonical finite projections all membership and fixed-atom
orthogonality premises are discharged by the established projection API. -/
theorem normalizedWalkResidual_inner_tendsto_zero
    (v : ℕ → H) (x : H)
    (hr : Tendsto (fun n => x - (walkSpan v id n).starProjection x) atTop (𝓝 0))
    (hne : ∀ n, x - (walkSpan v id n).starProjection x ≠ 0)
    (y : H) :
    Tendsto (fun n => inner ℝ y
      (normalizedResidual (x - (walkSpan v id n).starProjection x))) atTop (𝓝 0) := by
  apply normalizedResidual_inner_tendsto_zero v x
    (fun n => (walkSpan v id n).starProjection x)
    (fun n => walkSpan_le v id n ((walkSpan v id n).starProjection_apply_mem x))
    hr hne ?_ y
  intro i
  filter_upwards [eventually_gt_atTop i] with n hn
  have hi : v i ∈ walkSpan v id n :=
    Submodule.subset_span ⟨⟨i, hn⟩, rfl⟩
  exact ((walkSpan v id n).mem_orthogonal _).mp
    (Submodule.sub_starProjection_mem_orthogonal x) _ hi

end RiemannResearch.Analysis.NormalizedProjectionWeakConvergence
