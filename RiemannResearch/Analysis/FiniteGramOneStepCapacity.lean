/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.Analysis.FiniteGramCapacityIncrement
import RiemannResearch.Analysis.FiniteGramRange
import Mathlib.Data.Fintype.BigOperators

/-!
# Singular-safe one-vector capacity increments

Source: the Pareto affine-exhaustion handoff motivates tracking the exact
signed source remaining after screening a new complete-tail vector. All
Gram forms below are actual Hilbert Gram forms. Screening exists even for
singular old families. A zero Schur denominator gives zero source and gain.
-/

noncomputable section
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
namespace RiemannResearch.Analysis.FiniteHilbertGram

variable {ι H : Type*} [Fintype ι]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- The cross-observation of any vector lies in the range of the actual Gram
map. This does not require linear independence of the old family. -/
theorem exists_gram_eq_cross (v : ι → H) (f : H) :
    ∃ c : ι → ℝ, gram v c = cross v f := by
  let b : EuclideanSpace ℝ ι := WithLp.toLp 2 (cross v f)
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
    have hinner : inner ℝ x b =
        inner ℝ (Fintype.linearCombination ℝ v x.ofLp) f := by
      rw [PiLp.inner_apply, inner_synthesis_left]
      apply Finset.sum_congr rfl
      intro i _
      simp only [RCLike.inner_apply', starRingEnd_apply, star_trivial]
      change x.ofLp i * cross v f i = x.ofLp i * inner ℝ (v i) f
      rfl
    rw [hinner, hz, inner_zero_left]
  obtain ⟨z, hz⟩ := exists_preimage_of_kernel_orthogonal (gramEuclidean v) hsym b hb
  exact ⟨z.ofLp, congrArg WithLp.ofLp hz⟩

/-- An actual screening solution; its synthesized vector is independent of
the choice of solution even when the coefficient vector is not unique. -/
def screeningCoeff (v : ι → H) (f : H) : ι → ℝ :=
  Classical.choose (exists_gram_eq_cross v f)

theorem screeningCoeff_normal (v : ι → H) (f : H) :
    gram v (screeningCoeff v f) = cross v f :=
  Classical.choose_spec (exists_gram_eq_cross v f)

def screenedVector (v : ι → H) (f : H) : H :=
  f - Fintype.linearCombination ℝ v (screeningCoeff v f)

theorem screenedVector_orthogonal (v : ι → H) (f : H) (a : ι → ℝ) :
    inner ℝ (Fintype.linearCombination ℝ v a) (screenedVector v f) = 0 := by
  rw [inner_synthesis_left]
  apply Finset.sum_eq_zero
  intro i _
  have hi := congrFun (screeningCoeff_normal v f) i
  change inner ℝ (v i)
    (Fintype.linearCombination ℝ v (screeningCoeff v f)) = inner ℝ (v i) f at hi
  simp only [screenedVector, inner_sub_right, hi, sub_self, mul_zero]

/-- Actual Schur denominator, with all signed cross terms retained. -/
theorem screenedVector_energy (v : ι → H) (f : H) :
    ‖screenedVector v f‖ ^ 2 = ‖f‖ ^ 2 -
      ∑ i, screeningCoeff v f i * cross v f i := by
  have hss : ‖Fintype.linearCombination ℝ v (screeningCoeff v f)‖ ^ 2 =
      ∑ i, screeningCoeff v f i * cross v f i := by
    rw [gram_quadratic, screeningCoeff_normal]
  have hfs : inner ℝ f (Fintype.linearCombination ℝ v (screeningCoeff v f)) =
      ∑ i, screeningCoeff v f i * cross v f i := by
    rw [real_inner_comm, inner_synthesis_left]
    rfl
  rw [screenedVector, norm_sub_sq_real, hss, hfs]
  ring

/-- Under the old normal equations, the screened source defect is precisely
one minus the sum of the actual screening coefficients. -/
theorem screeningCoeff_source (v : ι → H) (f : H) (z : ι → ℝ)
    (hz : gram v z = fun _ => 1) :
    inner ℝ f (Fintype.linearCombination ℝ v z) =
      ∑ i, screeningCoeff v f i := by
  have ho : inner ℝ (screenedVector v f) (Fintype.linearCombination ℝ v z) = 0 := by
    rw [real_inner_comm]
    exact screenedVector_orthogonal v f z
  rw [screenedVector, inner_sub_left] at ho
  have hp : inner ℝ (Fintype.linearCombination ℝ v (screeningCoeff v f))
      (Fintype.linearCombination ℝ v z) = ∑ i, screeningCoeff v f i := by
    rw [inner_synthesis_left]
    change (∑ i, screeningCoeff v f i * gram v z i) = _
    rw [hz]
    simp only [mul_one]
  linarith

/-- A single new vector can alter the normal vector only along its screened
residual. This statement includes singular old and enlarged Gram systems. -/
theorem one_step_normal_difference
    (v : ι → H) (f : H) (z : ι → ℝ) (u : ι ⊕ Unit → ℝ)
    (hz : gram v z = fun _ => 1)
    (hu : gram (Sum.elim v (fun _ : Unit => f)) u = fun _ => 1) :
    Fintype.linearCombination ℝ (Sum.elim v (fun _ : Unit => f)) u -
      Fintype.linearCombination ℝ v z = u (Sum.inr ()) • screenedVector v f := by
  let d := Fintype.linearCombination ℝ (Sum.elim v (fun _ : Unit => f)) u -
    Fintype.linearCombination ℝ v z
  let t := u (Sum.inr ())
  let a : ι → ℝ := (fun i => u (Sum.inl i)) - z + t • screeningCoeff v f
  have hs : Fintype.linearCombination ℝ (Sum.elim v (fun _ : Unit => f)) u =
      Fintype.linearCombination ℝ v (fun i => u (Sum.inl i)) + t • f := by
    simp only [Fintype.linearCombination_apply, Fintype.sum_sum_type,
      Sum.elim_inl, Sum.elim_inr, Fintype.sum_unique, t]
  have hd : d = Fintype.linearCombination ℝ v a + t • screenedVector v f := by
    dsimp [d, a]
    rw [hs, map_add, map_sub, map_smul, screenedVector, smul_sub]
    abel
  have horth : inner ℝ (Fintype.linearCombination ℝ v a) d = 0 :=
    normal_increment_orthogonal_old_synthesis v
      (Sum.elim v (fun _ : Unit => f)) z a u hz hu Sum.inl (fun _ => rfl)
  rw [hd, inner_add_right, inner_smul_right,
    screenedVector_orthogonal, mul_zero, add_zero,
    real_inner_self_eq_norm_sq] at horth
  have ha : Fintype.linearCombination ℝ v a = 0 :=
    norm_eq_zero.mp (sq_eq_zero_iff.mp horth)
  change d = t • screenedVector v f
  rw [hd, ha, zero_add]

/-- The exact one-vector Schur gain. Division by zero is harmless here:
zero residual norm forces both the source defect and the gain to vanish. -/
theorem one_step_normal_mass_increment
    (v : ι → H) (f : H) (z : ι → ℝ) (u : ι ⊕ Unit → ℝ)
    (hz : gram v z = fun _ => 1)
    (hu : gram (Sum.elim v (fun _ : Unit => f)) u = fun _ => 1) :
    (∑ j, u j) - (∑ i, z i) =
      (1 - inner ℝ f (Fintype.linearCombination ℝ v z)) ^ 2 /
        ‖screenedVector v f‖ ^ 2 := by
  let d := Fintype.linearCombination ℝ (Sum.elim v (fun _ : Unit => f)) u -
    Fintype.linearCombination ℝ v z
  let t := u (Sum.inr ())
  have hd : d = t • screenedVector v f := one_step_normal_difference v f z u hz hu
  have hgain : (∑ j, u j) - (∑ i, z i) = ‖d‖ ^ 2 :=
    normal_mass_increment_of_family_map v
      (Sum.elim v (fun _ : Unit => f)) z u hz hu Sum.inl (fun _ => rfl)
  have hsource : inner ℝ (screenedVector v f) d =
      1 - inner ℝ f (Fintype.linearCombination ℝ v z) := by
    have ho := normal_increment_orthogonal_old_synthesis v
      (Sum.elim v (fun _ : Unit => f)) z (screeningCoeff v f) u hz hu
      Sum.inl (fun _ => rfl)
    change inner ℝ (Fintype.linearCombination ℝ v (screeningCoeff v f)) d = 0 at ho
    rw [screenedVector, inner_sub_left, ho, sub_zero]
    change inner ℝ f
      (Fintype.linearCombination ℝ (Sum.elim v (fun _ : Unit => f)) u -
        Fintype.linearCombination ℝ v z) = _
    rw [inner_sub_right]
    have hn := congrFun hu (Sum.inr ())
    change inner ℝ f
      (Fintype.linearCombination ℝ (Sum.elim v (fun _ : Unit => f)) u) = 1 at hn
    rw [hn]
  have heta : 1 - inner ℝ f (Fintype.linearCombination ℝ v z) =
      t * ‖screenedVector v f‖ ^ 2 := by
    rw [hd, inner_smul_right, real_inner_self_eq_norm_sq] at hsource
    exact hsource.symm
  rw [hgain, hd, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs, heta]
  by_cases hσ : ‖screenedVector v f‖ ^ 2 = 0
  · simp [hσ]
  · field_simp [hσ]

/-- The degenerate Schur case is a genuine zero-gain step. -/
theorem one_step_zero_schur
    (v : ι → H) (f : H) (z : ι → ℝ) (u : ι ⊕ Unit → ℝ)
    (hz : gram v z = fun _ => 1)
    (hu : gram (Sum.elim v (fun _ : Unit => f)) u = fun _ => 1)
    (hσ : ‖screenedVector v f‖ ^ 2 = 0) :
    (∑ j, u j) = (∑ i, z i) ∧
      inner ℝ f (Fintype.linearCombination ℝ v z) = 1 := by
  have hgain := one_step_normal_mass_increment v f z u hz hu
  rw [hσ, div_zero] at hgain
  have heq : (∑ j, u j) = ∑ i, z i := sub_eq_zero.mp hgain
  refine ⟨heq, ?_⟩
  exact (normal_mass_eq_iff_new_normal_equations v
    (Sum.elim v (fun _ : Unit => f)) z u hz hu Sum.inl (fun _ => rfl)).mp
      heq (Sum.inr ())

end RiemannResearch.Analysis.FiniteHilbertGram
