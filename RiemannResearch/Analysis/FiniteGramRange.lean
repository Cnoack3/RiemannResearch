import RiemannResearch.Analysis.FiniteHilbertGram
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.Analysis.InnerProductSpace.Symmetric
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional

/-!
# Solvability of a finite, possibly singular Gram system

Source: the attached Pareto_Direct_Attempt_Sublinear_Energy_2026-09-22_Continued
handoff, Section 9. Tail null vectors have total coefficient sum zero. This
module converts that exact compatibility condition into solvability of C z = 1;
no positive definiteness or nonsingularity assumption is introduced.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.Analysis.FiniteHilbertGram

/-- Finite-dimensional self-adjoint range solvability, proved directly by
orthogonal complements. The symmetry hypothesis is written explicitly to
avoid any convention about which argument of an inner product is linear. -/
theorem exists_preimage_of_kernel_orthogonal
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    (T : E →ₗ[ℝ] E)
    (hT : ∀ x y, inner ℝ (T x) y = inner ℝ x (T y))
    (b : E) (hb : ∀ x, T x = 0 → inner ℝ x b = 0) :
    ∃ z, T z = b := by
  have hm : b ∈ (LinearMap.range T)ᗮᗮ := by
    rw [Submodule.mem_orthogonal]
    intro x hx
    have hx' := (Submodule.mem_orthogonal (LinearMap.range T) x).mp hx
    have hn : inner ℝ (T x) (T x) = 0 := by
      rw [← hT (T x) x]
      exact hx' (T (T x)) ⟨T x, rfl⟩
    have hz : T x = 0 := by
      apply norm_eq_zero.mp
      rw [real_inner_self_eq_norm_sq] at hn
      nlinarith [norm_nonneg (T x)]
    exact hb x hz
  rw [Submodule.orthogonal_orthogonal] at hm
  exact hm

variable {ι H : Type*} [Fintype ι] [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- The same actual Gram map, transported to the Euclidean coefficient space. -/
def gramEuclidean (v : ι → H) :
    EuclideanSpace ℝ ι →ₗ[ℝ] EuclideanSpace ℝ ι where
  toFun x := WithLp.toLp 2 (gram v x.ofLp)
  map_add' x y := by
    ext i
    exact congrFun ((gram v).map_add x.ofLp y.ofLp) i
  map_smul' a x := by
    ext i
    exact congrFun ((gram v).map_smul a x.ofLp) i

/-- The Gram pairing is exactly the Hilbert pairing of the two synthesized
vectors, including all signed mixed terms. -/
theorem gramEuclidean_pairing (v : ι → H) (x y : EuclideanSpace ℝ ι) :
    inner ℝ x (gramEuclidean v y) =
      inner ℝ (Fintype.linearCombination ℝ v x.ofLp)
        (Fintype.linearCombination ℝ v y.ofLp) := by
  rw [PiLp.inner_apply, inner_synthesis_left]
  apply Finset.sum_congr rfl
  intro i _
  simp only [RCLike.inner_apply', starRingEnd_apply, star_trivial]
  change x.ofLp i * gram v y.ofLp i =
    x.ofLp i * inner ℝ (v i) (Fintype.linearCombination ℝ v y.ofLp)
  rfl

/-- Kernel compatibility alone gives an actual solution to C z = 1, even
when the finite covariance is singular. -/
theorem exists_gram_eq_one_of_synthesis_null_sum_zero (v : ι → H)
    (hnull : ∀ c : ι → ℝ,
      Fintype.linearCombination ℝ v c = 0 → ∑ i, c i = 0) :
    ∃ z : ι → ℝ, gram v z = fun _ => 1 := by
  let b : EuclideanSpace ℝ ι := WithLp.toLp 2 (fun _ => 1)
  have hsym : ∀ x y, inner ℝ (gramEuclidean v x) y =
      inner ℝ x (gramEuclidean v y) := by
    intro x y
    calc
      _ = inner ℝ y (gramEuclidean v x) := real_inner_comm _ _
      _ = inner ℝ (Fintype.linearCombination ℝ v y.ofLp)
          (Fintype.linearCombination ℝ v x.ofLp) := gramEuclidean_pairing v y x
      _ = inner ℝ (Fintype.linearCombination ℝ v x.ofLp)
          (Fintype.linearCombination ℝ v y.ofLp) := real_inner_comm _ _
      _ = _ := (gramEuclidean_pairing v x y).symm
  have hb : ∀ x, gramEuclidean v x = 0 → inner ℝ x b = 0 := by
    intro x hx
    have he := gramEuclidean_pairing v x x
    rw [hx, inner_zero_right, real_inner_self_eq_norm_sq] at he
    have hz : Fintype.linearCombination ℝ v x.ofLp = 0 := by
      apply norm_eq_zero.mp
      nlinarith [norm_nonneg (Fintype.linearCombination ℝ v x.ofLp)]
    have hs := hnull x.ofLp hz
    rw [PiLp.inner_apply]
    simpa [RCLike.inner_apply', b] using hs
  obtain ⟨z, hz⟩ := exists_preimage_of_kernel_orthogonal (gramEuclidean v) hsym b hb
  refine ⟨z.ofLp, ?_⟩
  exact congrArg WithLp.ofLp hz

end RiemannResearch.Analysis.FiniteHilbertGram
