import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Tactic

/-!
# Exhaustive cumulative projection walks

Source: user-requested randomized exploration of the Nyman--Pareto--CRT program
(2026-09-17). The convergence proof specializes Mathlib's
Submodule.starProjection_tendsto_closure_iSup; energy identities are elementary
Hilbert-space Pythagoras. No novelty claim is made.
Randomness is not an assumption: every surjective ordering has the same limit.
IID full-support exhaustion and the separate rank-one stochastic walk theorem
are proved in the companion RH_Random_Walk_Nyman_Pareto_CRT_2026-09-17.md;
those probability statements are not formalized here.
-/

noncomputable section
open Filter
open scoped Topology BigOperators
namespace RiemannResearch.Analysis.ExhaustiveWalk
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable {ι : Type*}

def walkSpan (v : ι → H) (draw : ℕ → ι) (n : ℕ) : Submodule ℝ H :=
  Submodule.span ℝ (Set.range (fun i : Fin n => v (draw i)))

instance walkSpan_finiteDimensional (v : ι → H) (draw : ℕ → ι) (n : ℕ) :
    FiniteDimensional ℝ (walkSpan v draw n) :=
  FiniteDimensional.span_of_finite ℝ (Set.finite_range _)

theorem walkSpan_mono (v : ι → H) (draw : ℕ → ι) :
    Monotone (walkSpan v draw) := by
  intro m n hmn
  apply Submodule.span_mono
  rintro _ ⟨i, rfl⟩
  exact ⟨⟨i, lt_of_lt_of_le i.isLt hmn⟩, rfl⟩

theorem walkSpan_le (v : ι → H) (draw : ℕ → ι) (n : ℕ) :
    walkSpan v draw n ≤ Submodule.span ℝ (Set.range v) := by
  apply Submodule.span_le.mpr
  rintro _ ⟨i, rfl⟩
  exact Submodule.subset_span ⟨draw i, rfl⟩

theorem iSup_walkSpan (v : ι → H) (draw : ℕ → ι)
    (hexhaust : Function.Surjective draw) :
    (⨆ n, walkSpan v draw n) = Submodule.span ℝ (Set.range v) := by
  apply le_antisymm
  · exact iSup_le (walkSpan_le v draw)
  · apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    obtain ⟨k, hk⟩ := hexhaust i
    apply (le_iSup (walkSpan v draw) (k + 1))
    apply Submodule.subset_span
    exact ⟨⟨k, Nat.lt_succ_self k⟩, congrArg v hk⟩

def dictionaryClosure (v : ι → H) : Submodule ℝ H :=
  (Submodule.span ℝ (Set.range v)).topologicalClosure

variable [CompleteSpace H]

instance dictionaryClosure_hasOrthogonalProjection (v : ι → H) :
    (dictionaryClosure v).HasOrthogonalProjection := by
  unfold dictionaryClosure
  infer_instance

theorem walkProjection_tendsto (v : ι → H) (draw : ℕ → ι)
    (hexhaust : Function.Surjective draw) (x : H) :
    Tendsto (fun n => (walkSpan v draw n).starProjection x) atTop
      (𝓝 ((dictionaryClosure v).starProjection x)) := by
  have h := Submodule.starProjection_tendsto_closure_iSup
    (walkSpan v draw) (walkSpan_mono v draw) x
  simpa only [iSup_walkSpan v draw hexhaust, dictionaryClosure] using h

def walkError (v : ι → H) (draw : ℕ → ι) (x : H) (n : ℕ) : ℝ :=
  ‖x - (walkSpan v draw n).starProjection x‖ ^ 2

def limitingError (v : ι → H) (x : H) : ℝ :=
  ‖x - (dictionaryClosure v).starProjection x‖ ^ 2

theorem walkError_tendsto (v : ι → H) (draw : ℕ → ι)
    (hexhaust : Function.Surjective draw) (x : H) :
    Tendsto (walkError v draw x) atTop (𝓝 (limitingError v x)) := by
  exact (tendsto_const_nhds.sub (walkProjection_tendsto v draw hexhaust x)).norm.pow 2

theorem limitingError_eq_zero_iff (v : ι → H) (x : H) :
    limitingError v x = 0 ↔ x ∈ dictionaryClosure v := by
  unfold limitingError
  rw [sq_eq_zero_iff, norm_eq_zero, sub_eq_zero, eq_comm,
    Submodule.starProjection_eq_self_iff]

theorem walkError_tendsto_zero_iff (v : ι → H) (draw : ℕ → ι)
    (hexhaust : Function.Surjective draw) (x : H) :
    Tendsto (walkError v draw x) atTop (𝓝 0) ↔ x ∈ dictionaryClosure v := by
  constructor
  · intro hz
    exact (limitingError_eq_zero_iff v x).mp
      (tendsto_nhds_unique (walkError_tendsto v draw hexhaust x) hz)
  · intro hx
    simpa only [(limitingError_eq_zero_iff v x).mpr hx] using
      walkError_tendsto v draw hexhaust x

omit [CompleteSpace H] in
theorem nested_projection_energy (K L : Submodule ℝ H)
    [K.HasOrthogonalProjection] [L.HasOrthogonalProjection] (hKL : K ≤ L) (x : H) :
    ‖x - K.starProjection x‖ ^ 2 =
      ‖x - L.starProjection x‖ ^ 2 +
      ‖L.starProjection x - K.starProjection x‖ ^ 2 := by
  have hp : L.starProjection x - K.starProjection x ∈ L :=
    L.sub_mem (L.starProjection_apply_mem x) (hKL (K.starProjection_apply_mem x))
  have ho : inner ℝ (x - L.starProjection x)
      (L.starProjection x - K.starProjection x) = 0 := by
    rw [real_inner_comm]
    exact (L.mem_orthogonal _).mp (Submodule.sub_starProjection_mem_orthogonal x) _ hp
  have he : x - K.starProjection x =
      (x - L.starProjection x) + (L.starProjection x - K.starProjection x) := by abel
  rw [he, norm_add_sq_real, ho]
  ring

omit [CompleteSpace H] in
theorem walkError_step (v : ι → H) (draw : ℕ → ι) (x : H) (n : ℕ) :
    walkError v draw x n = walkError v draw x (n+1) +
      ‖(walkSpan v draw (n+1)).starProjection x -
        (walkSpan v draw n).starProjection x‖ ^ 2 :=
  nested_projection_energy _ _ (walkSpan_mono v draw (Nat.le_succ n)) x

omit [CompleteSpace H] in
theorem walkError_antitone (v : ι → H) (draw : ℕ → ι) (x : H) :
    Antitone (walkError v draw x) := by
  intro m n hmn
  have h := nested_projection_energy _ _ (walkSpan_mono v draw hmn) x
  have hs := sq_nonneg ‖(walkSpan v draw n).starProjection x -
    (walkSpan v draw m).starProjection x‖
  change ‖x - (walkSpan v draw n).starProjection x‖ ^ 2 ≤
    ‖x - (walkSpan v draw m).starProjection x‖ ^ 2
  linarith

omit [CompleteSpace H] in
theorem covered_subspace_error_le (v : ι → H) (draw : ℕ → ι) (x : H) (n : ℕ)
    (K : Submodule ℝ H) [K.HasOrthogonalProjection] (hK : K ≤ walkSpan v draw n) :
    walkError v draw x n ≤ ‖x - K.starProjection x‖ ^ 2 := by
  have h := nested_projection_energy K (walkSpan v draw n) hK x
  have hs := sq_nonneg ‖(walkSpan v draw n).starProjection x - K.starProjection x‖
  unfold walkError
  linarith

omit [CompleteSpace H] in
theorem accumulated_gain (v : ι → H) (draw : ℕ → ι) (x : H) (N : ℕ) :
    (∑ n ∈ Finset.range N,
      ‖(walkSpan v draw (n+1)).starProjection x -
        (walkSpan v draw n).starProjection x‖ ^ 2) =
      walkError v draw x 0 - walkError v draw x N := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, ih]
    linarith [walkError_step v draw x N]

theorem accumulated_gain_tendsto (v : ι → H) (draw : ℕ → ι)
    (hexhaust : Function.Surjective draw) (x : H) :
    Tendsto (fun N => ∑ n ∈ Finset.range N,
      ‖(walkSpan v draw (n+1)).starProjection x -
        (walkSpan v draw n).starProjection x‖ ^ 2) atTop
      (𝓝 (‖x‖ ^ 2 - limitingError v x)) := by
  have hzero : walkError v draw x 0 = ‖x‖ ^ 2 := by
    simp [walkError, walkSpan]
  have ht : Tendsto (fun N => ‖x‖ ^ 2 - walkError v draw x N) atTop
      (𝓝 (‖x‖ ^ 2 - limitingError v x)) :=
    tendsto_const_nhds.sub (walkError_tendsto v draw hexhaust x)
  simpa only [accumulated_gain, hzero] using ht

end RiemannResearch.Analysis.ExhaustiveWalk
