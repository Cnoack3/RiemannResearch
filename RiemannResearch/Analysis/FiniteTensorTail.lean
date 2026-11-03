/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.Analysis.FiniteHilbertGram
import RiemannResearch.Analysis.FiniteHilbertGramProjection
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Analysis.Real.Sqrt

/-!
# Complete finite orthonormal-row tail certificates

Source: Prime Tensor CRT RH Research Project (2 November 2026), section 6,
for the requested certificate; standard orthogonal projection and triangle
inequality for the proofs. The residual Gram is the actual complete tail,
not a matrix of truncated physical moments. The signed-anchor, row-addition,
block, and diagonal-majorant continuation follows section 4 of
`RiemannResearch/RH/PrimeTensorCRTResults20261102.md` (user-supplied
memorandum); these are standard Hilbert-space arguments, with no novelty
claim. RH application: use arithmetic
divisor-wavelet rows and legal residue columns.
-/
noncomputable section
open scoped BigOperators
namespace RiemannResearch.Analysis.FiniteTensorTail
open RiemannResearch.Analysis.FiniteHilbertGram
variable {ι κ H : Type*} [Fintype ι] [Fintype κ]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H]

def tailMap (v : κ → H) : H →ₗ[ℝ] H :=
  LinearMap.id - (synthesisSpan v).starProjection.toLinearMap

theorem split_error (v : κ → H) (hv : Orthonormal ℝ v) (x : H) :
    ‖x‖^2 = (∑ k, (inner ℝ (v k) x)^2) + ‖tailMap v x‖^2 := by
  have h := projection_error_eq_orthonormal_sum hv x
  change ‖x - (synthesisSpan v).starProjection x‖^2 = _ at h
  change _ = _ + ‖x - (synthesisSpan v).starProjection x‖^2
  linarith

theorem column_bound (v : κ → H) (a : ι → H) (c : ι → ℝ) :
    ‖tailMap v (Fintype.linearCombination ℝ a c)‖ ≤
      ∑ i, |c i| * ‖tailMap v (a i)‖ := by
  rw [Fintype.linearCombination_apply, map_sum]
  simpa only [map_smul, norm_smul, Real.norm_eq_abs] using
    norm_sum_le Finset.univ (fun i => c i • tailMap v (a i))

/-- All signed cross terms of the complete residual Gram. -/
theorem tail_gram_exact (v : κ → H) (a : ι → H) (c : ι → ℝ) :
    (∑ i, ∑ j, c i * c j * inner ℝ (tailMap v (a i)) (tailMap v (a j))) =
      ‖tailMap v (Fintype.linearCombination ℝ a c)‖^2 := by
  rw [Fintype.linearCombination_apply, map_sum, ← real_inner_self_eq_norm_sq, sum_inner]
  simp only [map_smul, real_inner_smul_left, inner_sum, inner_smul_right]
  congr 1
  funext i
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem tail_gram_nonneg (v : κ → H) (a : ι → H) (c : ι → ℝ) :
    0 ≤ ∑ i, ∑ j, c i * c j *
      inner ℝ (tailMap v (a i)) (tailMap v (a j)) := by
  rw [tail_gram_exact]
  exact sq_nonneg _

theorem column_tail_sq (v : κ → H) (hv : Orthonormal ℝ v) (a : H) :
    ‖tailMap v a‖^2 = ‖a‖^2 - ∑ k, (inner ℝ (v k) a)^2 := by
  linarith [split_error v hv a]

/-- The target must be a retained mode; this is not a density assumption. -/
theorem column_certificate (v : κ → H) (hv : Orthonormal ℝ v)
    (a : ι → H) (c : ι → ℝ) (target : H) (ht : target ∈ synthesisSpan v) :
    ‖target - Fintype.linearCombination ℝ a c‖^2 ≤
      (∑ k, (inner ℝ (v k) (target-Fintype.linearCombination ℝ a c))^2) +
      (∑ i, |c i| * ‖tailMap v (a i)‖)^2 := by
  have hz : tailMap v target = 0 := by
    change target - (synthesisSpan v).starProjection target = 0
    rw [Submodule.starProjection_eq_self_iff.mpr ht, sub_self]
  rw [split_error v hv, map_sub, hz, zero_sub, norm_neg]
  have hb := column_bound v a c
  apply add_le_add_right
  simpa only [pow_two] using mul_self_le_mul_self (norm_nonneg _) hb

/-- Exact anchored decomposition. Source: supplied memorandum, section 4;
standard orthogonal-projection bias-variance identity. -/
theorem anchored_split (v : κ → H) (hv : Orthonormal ℝ v)
    (x b : H) (hb : b ∈ synthesisSpan v) :
    ‖x - b‖ ^ 2 = ‖tailMap v x‖ ^ 2 +
      ∑ k, (inner ℝ (v k) (x - b)) ^ 2 := by
  have hz : tailMap v b = 0 := by
    change b - (synthesisSpan v).starProjection b = 0
    rw [Submodule.starProjection_eq_self_iff.mpr hb, sub_self]
  rw [split_error v hv, map_sub, hz, sub_zero]
  ring

/-- An anchor in the retained subspace gives a true quadratic tail majorant. -/
theorem anchored_tail_le (v : κ → H) (hv : Orthonormal ℝ v)
    (x b : H) (hb : b ∈ synthesisSpan v) :
    ‖tailMap v x‖ ^ 2 ≤ ‖x - b‖ ^ 2 := by
  rw [anchored_split v hv x b hb]
  exact le_add_of_nonneg_right (Finset.sum_nonneg (fun k _ => sq_nonneg _))

private theorem planar_dot_le (a b c d t u : ℝ) (ht : 0 ≤ t) (hu : 0 ≤ u)
    (h1 : a ^ 2 + b ^ 2 ≤ t ^ 2) (h2 : c ^ 2 + d ^ 2 ≤ u ^ 2) :
    a * c + b * d ≤ t * u := by
  have hprod : (a ^ 2 + b ^ 2) * (c ^ 2 + d ^ 2) ≤ t ^ 2 * u ^ 2 :=
    mul_le_mul h1 h2 (by positivity) (sq_nonneg t)
  have hsq : (a * c + b * d) ^ 2 ≤ (t * u) ^ 2 := by
    nlinarith [sq_nonneg (a * d - b * c)]
  nlinarith [mul_nonneg ht hu, sq_nonneg (a * c + b * d - t * u)]

private theorem planar_sum_sq_le {α : Type*} (s : Finset α) (a b t : α → ℝ)
    (ht : ∀ i ∈ s, 0 ≤ t i)
    (h : ∀ i ∈ s, (a i) ^ 2 + (b i) ^ 2 ≤ (t i) ^ 2) :
    (∑ i ∈ s, a i) ^ 2 + (∑ i ∈ s, b i) ^ 2 ≤ (∑ i ∈ s, t i) ^ 2 := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    have hts : ∀ j ∈ s, 0 ≤ t j := fun j hj => ht j (Finset.mem_insert_of_mem hj)
    have hs : ∀ j ∈ s, (a j) ^ 2 + (b j) ^ 2 ≤ (t j) ^ 2 :=
      fun j hj => h j (Finset.mem_insert_of_mem hj)
    have hsum := ih hts hs
    have hcross := planar_dot_le (a i) (b i) (∑ j ∈ s, a j)
      (∑ j ∈ s, b j) (t i) (∑ j ∈ s, t j)
      (ht i (Finset.mem_insert_self i s)) (Finset.sum_nonneg hts)
      (h i (Finset.mem_insert_self i s)) hsum
    simp only [Finset.sum_insert hi]
    nlinarith [h i (Finset.mem_insert_self i s)]

/-- Adding one orthonormal analysis row splits each old tail exactly. -/
theorem tail_sq_add_row (v : Option κ → H) (hv : Orthonormal ℝ v) (x : H) :
    ‖tailMap (fun k => v (some k)) x‖ ^ 2 =
      (inner ℝ (v none) x) ^ 2 + ‖tailMap v x‖ ^ 2 := by
  have h0 := split_error (fun k => v (some k)) (hv.comp some (Option.some_injective κ)) x
  have h1 := split_error v hv x
  rw [Fintype.sum_option] at h1
  linarith

/-- Full column certificate, with an arbitrary retained target. -/
def columnCertificate (v : κ → H) (a : ι → H) (c : ι → ℝ) (target : H) : ℝ :=
  (∑ k, (inner ℝ (v k) (target - Fintype.linearCombination ℝ a c)) ^ 2) +
    (∑ i, |c i| * ‖tailMap v (a i)‖) ^ 2

/-- Signed, anchored synthesis retains all within-family covariance. -/
theorem anchored_synthesis_split (v : κ → H) (hv : Orthonormal ℝ v)
    (a b : ι → H) (hb : ∀ i, b i ∈ synthesisSpan v) (c : ι → ℝ) :
    ‖Fintype.linearCombination ℝ a c - Fintype.linearCombination ℝ b c‖ ^ 2 =
      ‖tailMap v (Fintype.linearCombination ℝ a c)‖ ^ 2 +
      ∑ k, (inner ℝ (v k)
        (Fintype.linearCombination ℝ a c - Fintype.linearCombination ℝ b c)) ^ 2 := by
  apply anchored_split v hv
  rw [Fintype.linearCombination_apply]
  exact (synthesisSpan v).sum_mem (fun i _ => (synthesisSpan v).smul_mem _ (hb i))

/-- A complete certificate using the signed anchor error, without absolute
coefficient estimates. -/
theorem anchored_certificate (v : κ → H) (hv : Orthonormal ℝ v)
    (a b : ι → H) (hb : ∀ i, b i ∈ synthesisSpan v) (c : ι → ℝ)
    (target : H) (ht : target ∈ synthesisSpan v) :
    ‖target - Fintype.linearCombination ℝ a c‖ ^ 2 ≤
      (∑ k, (inner ℝ (v k) (target - Fintype.linearCombination ℝ a c)) ^ 2) +
      ‖Fintype.linearCombination ℝ a c - Fintype.linearCombination ℝ b c‖ ^ 2 := by
  have hz : tailMap v target = 0 := by
    change target - (synthesisSpan v).starProjection target = 0
    rw [Submodule.starProjection_eq_self_iff.mpr ht, sub_self]
  rw [split_error v hv, map_sub, hz, zero_sub, norm_neg]
  apply add_le_add_right
  rw [anchored_synthesis_split v hv a b hb c]
  exact le_add_of_nonneg_right (Finset.sum_nonneg (fun k _ => sq_nonneg _))

/-- The column certificate cannot increase when one orthonormal row is
added. The target must already lie in the old retained space. -/
theorem columnCertificate_add_row_le (v : Option κ → H) (hv : Orthonormal ℝ v)
    (a : ι → H) (c : ι → ℝ) (target : H)
    (ht : target ∈ synthesisSpan (fun k => v (some k))) :
    columnCertificate v a c target ≤
      columnCertificate (fun k => v (some k)) a c target := by
  have het : inner ℝ (v none) target = 0 := by
    induction ht using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      exact hv.inner_eq_zero (by simp)
    | zero => simp
    | add x y hx hy ihx ihy => simp only [inner_add_right, ihx, ihy, add_zero]
    | smul r x hx ih => simp only [inner_smul_right, ih, mul_zero]
  have hs := planar_sum_sq_le Finset.univ
    (fun i => c i * inner ℝ (v none) (a i))
    (fun i => |c i| * ‖tailMap v (a i)‖)
    (fun i => |c i| * ‖tailMap (fun k => v (some k)) (a i)‖)
    (fun i _ => mul_nonneg (abs_nonneg _) (norm_nonneg _))
    (by
      intro i _
      simp only [mul_pow, sq_abs]
      rw [tail_sq_add_row v hv]
      ring_nf
      exact le_rfl)
  have he : inner ℝ (v none) (target - Fintype.linearCombination ℝ a c) =
      -(∑ i, c i * inner ℝ (v none) (a i)) := by
    rw [inner_sub_right, het, zero_sub, Fintype.linearCombination_apply, inner_sum]
    simp only [inner_smul_right]
  unfold columnCertificate
  rw [Fintype.sum_option, he, neg_sq]
  linarith

/-- The complete tail Gram has a diagonal PSD majorant for every positive
weight family. Source: supplied memorandum, section 4, weighted
Cauchy-Schwarz. This is a quadratic-form statement for every signed c. -/
theorem weighted_diagonal_majorant (v : κ → H) (a : ι → H) (c u : ι → ℝ)
    (hu : ∀ i, 0 < u i) :
    ‖tailMap v (Fintype.linearCombination ℝ a c)‖ ^ 2 ≤
      (∑ i, ‖tailMap v (a i)‖ ^ 2 / u i) * ∑ i, u i * (c i) ^ 2 := by
  have hs : ∀ i, (Real.sqrt (u i)) ^ 2 = u i :=
    fun i => Real.sq_sqrt (hu i).le
  have hp : ∀ i, Real.sqrt (u i) ≠ 0 :=
    fun i => ne_of_gt (Real.sqrt_pos.mpr (hu i))
  have hcauchy := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun i => |c i| * Real.sqrt (u i))
    (fun i => ‖tailMap v (a i)‖ / Real.sqrt (u i))
  have he : (∑ i, (|c i| * Real.sqrt (u i)) *
      (‖tailMap v (a i)‖ / Real.sqrt (u i))) =
      ∑ i, |c i| * ‖tailMap v (a i)‖ := by
    apply Finset.sum_congr rfl
    intro i _
    field_simp [hp i]
  rw [he] at hcauchy
  simp only [mul_pow, sq_abs, div_pow, hs] at hcauchy
  have hcol := column_bound v a c
  have hcolsq : ‖tailMap v (Fintype.linearCombination ℝ a c)‖ ^ 2 ≤
      (∑ i, |c i| * ‖tailMap v (a i)‖) ^ 2 := by
    simpa only [pow_two] using mul_self_le_mul_self (norm_nonneg _) hcol
  calc
    _ ≤ (∑ i, |c i| * ‖tailMap v (a i)‖) ^ 2 := hcolsq
    _ ≤ (∑ i, (c i) ^ 2 * u i) * ∑ i, ‖tailMap v (a i)‖ ^ 2 / u i := hcauchy
    _ = _ := by simp only [mul_comm]

/-- Entrywise identity K = G - Aᵀ A for the actual complete tail. -/
theorem tail_inner_eq (v : κ → H) (hv : Orthonormal ℝ v) (x y : H) :
    inner ℝ (tailMap v x) (tailMap v y) =
      inner ℝ x y - ∑ k, inner ℝ (v k) x * inner ℝ (v k) y := by
  have hn (a b : H) : ‖a + b‖ ^ 2 =
      ‖a‖ ^ 2 + 2 * inner ℝ a b + ‖b‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq]
    simp only [inner_add_left, inner_add_right, real_inner_self_eq_norm_sq,
      real_inner_comm b a]
    ring
  have h1 := split_error v hv x
  have h2 := split_error v hv y
  have h3 := split_error v hv (x + y)
  simp only [map_add, hn, inner_add_right, add_sq, Finset.sum_add_distrib,
    mul_assoc, ← Finset.mul_sum] at h3
  linarith

/-- Exact covariance is kept inside each block; only the block tails are
combined by a triangle inequality. -/
theorem block_certificate {β : Type*} [Fintype β]
    (v : κ → H) (hv : Orthonormal ℝ v) (a : β → ι → H)
    (c : β → ι → ℝ) (target : H) (ht : target ∈ synthesisSpan v) :
    ‖target - ∑ j, Fintype.linearCombination ℝ (a j) (c j)‖ ^ 2 ≤
      (∑ k, (inner ℝ (v k)
        (target - ∑ j, Fintype.linearCombination ℝ (a j) (c j))) ^ 2) +
      (∑ j, ‖tailMap v (Fintype.linearCombination ℝ (a j) (c j))‖) ^ 2 := by
  simpa only [Fintype.linearCombination_apply, one_smul, abs_one, one_mul] using
    column_certificate v hv (fun j => Fintype.linearCombination ℝ (a j) (c j))
      (fun _ => (1 : ℝ)) target ht

/-- Merging two residual blocks decreases their squared triangle penalty. -/
theorem merge_blocks_le (v : κ → H) (x y : H) (other : ℝ) (hother : 0 ≤ other) :
    (other + ‖tailMap v (x + y)‖) ^ 2 ≤
      (other + ‖tailMap v x‖ + ‖tailMap v y‖) ^ 2 := by
  rw [map_add]
  have h := norm_add_le (tailMap v x) (tailMap v y)
  have hbase : 0 ≤ other + ‖tailMap v x + tailMap v y‖ :=
    add_nonneg hother (norm_nonneg _)
  have hle : other + ‖tailMap v x + tailMap v y‖ ≤
      other + ‖tailMap v x‖ + ‖tailMap v y‖ := by linarith
  simpa only [pow_two] using mul_self_le_mul_self hbase hle

end RiemannResearch.Analysis.FiniteTensorTail
