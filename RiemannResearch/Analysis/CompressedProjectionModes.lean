/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.Analysis.ProjectionCompressionDefect
import RiemannResearch.LinearAlgebra.SourceSpectralMass

/-!
# Full Hilbert realization of compressed projection modes

Source: independently developed continuation of the two-seed source spectral
problem, 15 September 2026. For an orthonormal family of head eigenvectors,
projection into an actual subspace realizes all signed modal norm and error
identities. The synthesis vector belongs to that subspace by construction.
For RH, the subspace is a finite legal span. No vanishing source-mass estimate
is assumed or proved. The eigenvector equations are geometric hypotheses,
not replacements for an arithmetic approximation estimate.
-/

open scoped BigOperators
namespace RiemannResearch.Analysis.CompressedProjectionModes
open RiemannResearch.LinearAlgebra.SpectralCutoff
open RiemannResearch.Analysis.ProjectionCompression
noncomputable section

variable {H ι : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable [Fintype ι] [DecidableEq ι]
variable (P Q : Submodule ℝ H) [P.HasOrthogonalProjection] [Q.HasOrthogonalProjection]
variable (e : ι → H) (lam : ι → ℝ)
variable (he : ∀ i j, inner ℝ (e i) (e j) = if i = j then 1 else 0)
variable (hQ : ∀ i, e i ∈ Q)
variable (hEig : ∀ i, Q.starProjection (P.starProjection (e i)) = lam i • e i)

omit [Fintype ι] in
include he hQ hEig in
/-- Cross pairings follow from the actual compressed eigenvector equation. -/
theorem mode_cross (i j : ι) :
    inner ℝ (e i) (P.starProjection (e j)) = if i = j then lam i else 0 := by
  have h := Submodule.starProjection_inner_eq_zero (P.starProjection (e j)) (e i) (hQ i)
  rw [inner_sub_left, hEig j, real_inner_smul_left] at h
  have hc := real_inner_comm (e i) (P.starProjection (e j))
  rw [he j i] at h
  by_cases hij : i = j
  · subst j
    simp only [↓reduceIte, mul_one] at h ⊢
    linarith
  · have hji : j ≠ i := Ne.symm hij
    simp only [hij, hji, ↓reduceIte, mul_zero] at h ⊢
    linarith

omit [Fintype ι] in
include he hQ hEig in
/-- The diagonal Gram identity is derived, not supplied as a norm assumption. -/
theorem projected_mode_gram (i j : ι) :
    inner ℝ (P.starProjection (e i)) (P.starProjection (e j)) =
      if i = j then lam i else 0 := by
  have h := Submodule.starProjection_inner_eq_zero (e i) (P.starProjection (e j))
    (Submodule.starProjection_apply_mem P (e j))
  rw [inner_sub_left, mode_cross P Q e lam he hQ hEig] at h
  linarith

omit [Fintype ι] in
include he hQ hEig in
theorem mode_eigenvalue_bounds (i : ι) : 0 ≤ lam i ∧ lam i ≤ 1 := by
  have hp := projected_mode_gram P Q e lam he hQ hEig i i
  simp only [↓reduceIte, real_inner_self_eq_norm_sq] at hp
  have hn := Submodule.norm_starProjection_apply_le P (e i)
  have he1 := he i i
  simp only [↓reduceIte, real_inner_self_eq_norm_sq] at he1
  constructor
  · nlinarith [sq_nonneg ‖P.starProjection (e i)‖]
  · nlinarith [norm_nonneg (P.starProjection (e i)), norm_nonneg (e i)]

def source (c : ι → ℝ) : H := ∑ i, c i • e i

def synthesis (c a : ι → ℝ) : H := ∑ i, (a i * c i) • P.starProjection (e i)

omit [DecidableEq ι] in
theorem synthesis_mem (c a : ι → ℝ) : synthesis P e c a ∈ P := by
  apply P.sum_mem
  intro i hi
  exact P.smul_mem _ (Submodule.starProjection_apply_mem P (e i))

private theorem norm_of_diagonal_gram (v : ι → H) (w c : ι → ℝ)
    (hv : ∀ i j, inner ℝ (v i) (v j) = if i = j then w i else 0) :
    ‖∑ i, c i • v i‖ ^ 2 = ∑ i, w i * (c i) ^ 2 := by
  rw [← real_inner_self_eq_norm_sq]
  simp_rw [sum_inner, inner_sum, real_inner_smul_left, real_inner_smul_right, hv]
  simp only [mul_ite, mul_zero]
  apply Finset.sum_congr rfl
  intro i hi
  simp [pow_two, mul_comm, mul_left_comm]

include he in
theorem source_norm_sq (c : ι → ℝ) : ‖source e c‖ ^ 2 = ∑ i, (c i) ^ 2 := by
  simpa only [source, one_mul] using norm_of_diagonal_gram e (fun _ => 1) c he

include he hQ hEig in
/-- Full synthesis norm, including all coordinates beyond the prescribed head. -/
theorem synthesis_norm_sq (c a : ι → ℝ) :
    ‖synthesis P e c a‖ ^ 2 = diagonalNorm Finset.univ 0 lam (fun i => (c i) ^ 2) a := by
  rw [synthesis, norm_of_diagonal_gram _ _ _ (projected_mode_gram P Q e lam he hQ hEig)]
  simp only [diagonalNorm, zero_add, modalNorm]
  apply Finset.sum_congr rfl
  intro i hi
  ring

include he hQ hEig in
theorem source_synthesis_inner (c a : ι → ℝ) :
    inner ℝ (source e c) (synthesis P e c a) =
      ∑ i, lam i * a i * (c i) ^ 2 := by
  unfold source synthesis
  simp_rw [sum_inner, inner_sum, real_inner_smul_left, real_inner_smul_right,
    mode_cross P Q e lam he hQ hEig]
  simp only [mul_ite, mul_zero]
  apply Finset.sum_congr rfl
  intro i hi
  simp [pow_two, mul_comm, mul_left_comm]

include he hQ hEig in
/-- Exact signed error realizes the previously abstract diagonal model. -/
theorem synthesis_error_sq (c a : ι → ℝ) :
    ‖source e c - synthesis P e c a‖ ^ 2 =
      diagonalError Finset.univ lam (fun i => (c i) ^ 2) a := by
  have h := RiemannResearch.LinearAlgebra.TwoChannelCancellation.norm_add_sq
    (source e c) (-synthesis P e c a)
  simp only [norm_neg, inner_neg_right, ← sub_eq_add_neg] at h
  rw [h, source_norm_sq e he, synthesis_norm_sq P Q e lam he hQ hEig,
    source_synthesis_inner P Q e lam he hQ hEig]
  simp only [diagonalNorm, zero_add, modalNorm, diagonalError, modalError]
  simp only [mul_neg, ← sub_eq_add_neg]
  rw [← Finset.sum_add_distrib, Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  ring

/-- Actual finite-subspace witness obtained by inverting only retained modes. -/
def cutoffWitness (c : ι → ℝ) (τ : ℝ) : H :=
  synthesis P e c (fun i => cutoffAmplitude τ (lam i))

omit [DecidableEq ι] in
theorem cutoffWitness_mem (c : ι → ℝ) (τ : ℝ) : cutoffWitness P e lam c τ ∈ P :=
  synthesis_mem P e c _

include he hQ hEig in
/-- Uniform norm control is unconditional; small error still requires small omitted mass. -/
theorem cutoffWitness_bounds (c : ι → ℝ) {τ : ℝ} (hτ : 0 < τ) :
    ‖cutoffWitness P e lam c τ‖ ^ 2 ≤ (∑ i, (c i) ^ 2) / τ ∧
      ‖source e c - cutoffWitness P e lam c τ‖ ^ 2 ≤
        omittedMass Finset.univ τ lam (fun i => (c i) ^ 2) +
          polarization Finset.univ lam (fun i => (c i) ^ 2) / τ ^ 2 := by
  have hl0 : ∀ i ∈ (Finset.univ : Finset ι), 0 ≤ lam i :=
    fun i _ => (mode_eigenvalue_bounds P Q e lam he hQ hEig i).1
  have hl1 : ∀ i ∈ (Finset.univ : Finset ι), lam i ≤ 1 :=
    fun i _ => (mode_eigenvalue_bounds P Q e lam he hQ hEig i).2
  have hm : ∀ i ∈ (Finset.univ : Finset ι), 0 ≤ (c i) ^ 2 := fun i _ => sq_nonneg _
  constructor
  · rw [cutoffWitness, synthesis_norm_sq P Q e lam he hQ hEig,
      diagonalNorm_cutoff Finset.univ 0 lam (fun i => (c i) ^ 2) hτ]
    exact cutoffNorm_le_mass_div _ _ _ hτ hm
  · rw [cutoffWitness, synthesis_error_sq P Q e lam he hQ hEig,
      diagonalError_cutoff _ _ _ hτ]
    exact cutoffError_le_mass_add_polarization _ _ _ hτ hl0 hl1 hm

omit [DecidableEq ι] in
theorem projected_source (c : ι → ℝ) :
    P.starProjection (source e c) = synthesis P e c (fun _ => 1) := by
  simp [source, synthesis, map_sum]

omit [DecidableEq ι] in
include hEig in
theorem compressed_source (c : ι → ℝ) :
    Q.starProjection (P.starProjection (source e c)) = source e (fun i => lam i * c i) := by
  simp only [source, map_sum, map_smul, hEig, smul_smul]
  apply Finset.sum_congr rfl
  intro i hi
  rw [mul_comm]

include he hQ hEig in
/-- Source polarization is identified with the actual full Hilbert tail. -/
theorem polarization_eq_leakage (c : ι → ℝ) :
    polarization Finset.univ lam (fun i => (c i) ^ 2) =
      ‖P.starProjection (source e c) -
        Q.starProjection (P.starProjection (source e c))‖ ^ 2 := by
  have hp := projection_pythagoras Q (P.starProjection (source e c))
  have heq : polarization Finset.univ lam (fun i => (c i) ^ 2) =
      ‖P.starProjection (source e c)‖ ^ 2 -
        ‖Q.starProjection (P.starProjection (source e c))‖ ^ 2 := by
    rw [compressed_source P Q e lam hEig, source_norm_sq e he,
      projected_source P e, synthesis_norm_sq P Q e lam he hQ hEig]
    simp only [polarization, polarizationTerm, diagonalNorm, zero_add, modalNorm,
      one_pow, mul_one]
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  linarith

include he hQ hEig in
/-- The source-weighted first defect moment equals the full projection residual. -/
theorem optimalError_eq_projection_defect (c : ι → ℝ) :
    optimalError Finset.univ lam (fun i => (c i) ^ 2) =
      ‖source e c - P.starProjection (source e c)‖ ^ 2 := by
  rw [projected_source P e, synthesis_error_sq P Q e lam he hQ hEig]
  simp only [optimalError, optimalTerm, diagonalError, modalError, one_pow, mul_one]
  apply Finset.sum_congr rfl
  intro i hi
  ring

include he hQ hEig in
/-- The cutoff estimate now uses actual Hilbert norms, with no modal norm provider. -/
theorem cutoffWitness_geometric_bounds (c : ι → ℝ) {τ : ℝ} (hτ : 0 < τ) :
    ‖cutoffWitness P e lam c τ‖ ^ 2 ≤ ‖source e c‖ ^ 2 / τ ∧
      ‖source e c - cutoffWitness P e lam c τ‖ ^ 2 ≤
        omittedMass Finset.univ τ lam (fun i => (c i) ^ 2) +
          ‖P.starProjection (source e c) -
            Q.starProjection (P.starProjection (source e c))‖ ^ 2 / τ ^ 2 := by
  have h := cutoffWitness_bounds P Q e lam he hQ hEig c hτ
  rwa [← source_norm_sq e he c, polarization_eq_leakage P Q e lam he hQ hEig c] at h

omit [DecidableEq ι] [Q.HasOrthogonalProjection] in
include hQ in
theorem source_mem (c : ι → ℝ) : source e c ∈ Q := by
  apply Q.sum_mem
  intro i hi
  exact Q.smul_mem _ (hQ i)

include he hQ hEig in
/-- Quantitative comparison between the half-cutoff mass and the full source defect. -/
theorem half_mass_full_defect_bound (c : ι → ℝ) (t : H) (ht : t ∈ Qᗮ) :
    |omittedMass Finset.univ (1 / 2) lam (fun i => (c i) ^ 2) -
      ‖(source e c + t) - P.starProjection (source e c + t)‖ ^ 2| ≤
      2 * ‖P.starProjection (source e c) -
          Q.starProjection (P.starProjection (source e c))‖ ^ 2 +
        2 * ‖t‖ * ‖P.starProjection (source e c) -
          Q.starProjection (P.starProjection (source e c))‖ + ‖t‖ ^ 2 := by
  have hs := half_mass_defect_bound Finset.univ lam (fun i => (c i) ^ 2)
    (fun i _ => (mode_eigenvalue_bounds P Q e lam he hQ hEig i).1)
    (fun i _ => (mode_eigenvalue_bounds P Q e lam he hQ hEig i).2)
    (fun i _ => sq_nonneg _)
  rw [optimalError_eq_projection_defect P Q e lam he hQ hEig c,
    polarization_eq_leakage P Q e lam he hQ hEig c] at hs
  have hf := full_source_defect_error P Q (source e c) t (source_mem Q e hQ c) ht
  have ha := abs_sub_le
    (omittedMass Finset.univ (1 / 2) lam (fun i => (c i) ^ 2))
    (‖source e c - P.starProjection (source e c)‖ ^ 2)
    (‖(source e c + t) - P.starProjection (source e c + t)‖ ^ 2)
  rw [abs_sub_comm
    (‖source e c - P.starProjection (source e c)‖ ^ 2)
    (‖(source e c + t) - P.starProjection (source e c + t)‖ ^ 2)] at ha
  linarith

end
end RiemannResearch.Analysis.CompressedProjectionModes
