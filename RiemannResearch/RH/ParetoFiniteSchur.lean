import RiemannResearch.RH.ParetoFiniteGram
import RiemannResearch.RH.ParetoNoiseSignal
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# Exact finite control optimization for the complete Pareto law

Verified continuation of the preserved 9 September 2026 candidate.
Source: RH_Candid_Assessment_Pareto_Green_CRT_2026-09-07.md, section 9.

Every Gram entry below is the existing full infinite `paretoInner`.
Boundedness proves the required summability. No mixed entry is discarded.
The inverse is represented by an explicit linear equivalence whose action
is the actual Gram matrix. Thus existence of a nonsingular control block
is an explicit hypothesis, not an asserted theorem or a pseudoinverse.
-/

open scoped BigOperators
namespace RiemannResearch.RH.Pareto.FiniteSchur
noncomputable section

variable {ι : Type*} [Fintype ι]

/-- Synthesis of a finite control coefficient vector. -/
def combination (z : ι → ℕ → ℝ) (b : ι → ℝ) (k : ℕ) : ℝ :=
  ∑ i, b i * z i k

/-- The actual complete Pareto Gram matrix applied to a vector. -/
def gramApply (z : ι → ℕ → ℝ) (b : ι → ℝ) (i : ι) : ℝ :=
  ∑ j, paretoInner (z i) (z j) * b j

/-- For zero-mean controls this is also the vector of covariances with `f`. -/
def cross (z : ι → ℕ → ℝ) (f : ℕ → ℝ) (i : ι) : ℝ :=
  paretoInner (z i) f

/-- The coefficient subtracted from the signal; the additive optimizer is its negative. -/
def inverseCoeff (e : (ι → ℝ) ≃ₗ[ℝ] (ι → ℝ))
    (z : ι → ℕ → ℝ) (f : ℕ → ℝ) : ι → ℝ :=
  e.symm (cross z f)

theorem combination_bounded {z : ι → ℕ → ℝ} {B : ι → ℝ}
    (hz : ∀ i k, |z i k| ≤ B i) (b : ι → ℝ) :
    ∀ k, |combination z b k| ≤ ∑ i, |b i| * B i := by
  simpa [combination] using bounded_finsetCombination Finset.univ b hz

theorem combination_sub (z : ι → ℕ → ℝ) (b d : ι → ℝ) (k : ℕ) :
    combination z (fun i => b i - d i) k =
      combination z b k - combination z d k := by
  simp [combination, sub_mul, Finset.sum_sub_distrib]

theorem inner_combination_left {z : ι → ℕ → ℝ} {B : ι → ℝ}
    {f : ℕ → ℝ} {C : ℝ} (hz : ∀ i k, |z i k| ≤ B i)
    (hf : ∀ k, |f k| ≤ C) (b : ι → ℝ) :
    paretoInner (combination z b) f = ∑ i, b i * paretoInner (z i) f := by
  unfold combination
  rw [paretoInner_finsetSum_left Finset.univ
    (fun i => bounded_const_mul (hz i) (b i)) hf]
  apply Finset.sum_congr rfl
  intro i _
  exact paretoInner_const_mul_left (hz i) hf (b i)

theorem inner_combination_right {z : ι → ℕ → ℝ} {B : ι → ℝ}
    {f : ℕ → ℝ} {C : ℝ} (hz : ∀ i k, |z i k| ≤ B i)
    (hf : ∀ k, |f k| ≤ C) (b : ι → ℝ) :
    paretoInner f (combination z b) = ∑ i, b i * paretoInner f (z i) := by
  rw [paretoInner_comm, inner_combination_left hz hf b]
  apply Finset.sum_congr rfl
  intro i _
  rw [paretoInner_comm (z i) f]

theorem gramApply_eq_inner {z : ι → ℕ → ℝ} {B : ι → ℝ}
    (hz : ∀ i k, |z i k| ≤ B i) (b : ι → ℝ) (i : ι) :
    gramApply z b i = paretoInner (z i) (combination z b) := by
  rw [inner_combination_right hz (hz i) b]
  unfold gramApply
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- The inverse of the actual Gram action supplies all normal equations. -/
theorem inverseCoeff_normal {z : ι → ℕ → ℝ} {B : ι → ℝ}
    (hz : ∀ i k, |z i k| ≤ B i)
    (e : (ι → ℝ) ≃ₗ[ℝ] (ι → ℝ))
    (he : ∀ b i, e b i = gramApply z b i) (f : ℕ → ℝ) :
    ∀ i, paretoInner (z i) (combination z (inverseCoeff e z f)) =
      paretoInner (z i) f := by
  intro i
  rw [← gramApply_eq_inner hz, ← he]
  simp [inverseCoeff, cross]

/-- Invertibility makes the normal-equation coefficient vector unique. -/
theorem inverseCoeff_unique_normal {z : ι → ℕ → ℝ} {B : ι → ℝ}
    (hz : ∀ i k, |z i k| ≤ B i)
    (e : (ι → ℝ) ≃ₗ[ℝ] (ι → ℝ))
    (he : ∀ b i, e b i = gramApply z b i) (f : ℕ → ℝ) (d : ι → ℝ)
    (hd : ∀ i, paretoInner (z i) (combination z d) = paretoInner (z i) f) :
    d = inverseCoeff e z f := by
  apply e.injective
  funext i
  rw [he, he, gramApply_eq_inner hz, gramApply_eq_inner hz,
    hd i, inverseCoeff_normal hz e he f i]

/-- The residual is orthogonal to every control combination, not just each coordinate. -/
theorem residual_orthogonal {z : ι → ℕ → ℝ} {B : ι → ℝ}
    {f : ℕ → ℝ} {C : ℝ} (hz : ∀ i k, |z i k| ≤ B i)
    (hf : ∀ k, |f k| ≤ C) (d : ι → ℝ)
    (hd : ∀ i, paretoInner (z i) (combination z d) = paretoInner (z i) f)
    (b : ι → ℝ) :
    paretoInner (fun k => f k - combination z d k) (combination z b) = 0 := by
  rw [inner_combination_right hz (bounded_sub hf (combination_bounded hz d)) b]
  apply Finset.sum_eq_zero
  intro i _
  have hi : paretoInner (fun k => f k - combination z d k) (z i) = 0 := by
    rw [paretoInner_comm, paretoInner_sub_right (hz i) hf
      (combination_bounded hz d), hd i, sub_self]
  rw [hi, mul_zero]

/-- Exact completion of the finite Gram quadratic, with the full remainder norm. -/
theorem residual_completion {z : ι → ℕ → ℝ} {B : ι → ℝ}
    {f : ℕ → ℝ} {C : ℝ} (hz : ∀ i k, |z i k| ≤ B i)
    (hf : ∀ k, |f k| ≤ C) (d : ι → ℝ)
    (hd : ∀ i, paretoInner (z i) (combination z d) = paretoInner (z i) f)
    (b : ι → ℝ) :
    paretoInner (fun k => f k - combination z b k)
      (fun k => f k - combination z b k) =
    paretoInner (fun k => f k - combination z d k)
      (fun k => f k - combination z d k) +
    paretoInner (combination z (fun i => b i - d i))
      (combination z (fun i => b i - d i)) := by
  have hs : (fun k => f k - combination z b k) =
      (fun k => (f k - combination z d k) -
        combination z (fun i => b i - d i) k) := by
    funext k
    rw [combination_sub]
    ring
  rw [hs]
  have h := paretoInner_residual_polynomial
    (bounded_sub hf (combination_bounded hz d))
    (combination_bounded hz (fun i => b i - d i)) (1 : ℝ)
  rw [residual_orthogonal hz hf d hd (fun i => b i - d i)] at h
  simpa only [one_mul, one_pow, mul_zero, sub_zero] using h

/-- Explicit Schur value for the minimum complete Pareto square norm. -/
theorem residual_schur_value {z : ι → ℕ → ℝ} {B : ι → ℝ}
    {f : ℕ → ℝ} {C : ℝ} (hz : ∀ i k, |z i k| ≤ B i)
    (hf : ∀ k, |f k| ≤ C) (d : ι → ℝ)
    (hd : ∀ i, paretoInner (z i) (combination z d) = paretoInner (z i) f) :
    paretoInner (fun k => f k - combination z d k)
      (fun k => f k - combination z d k) =
      paretoInner f f - ∑ i, d i * paretoInner (z i) f := by
  have hgg : paretoInner (combination z d) (combination z d) =
      ∑ i, d i * paretoInner (z i) f := by
    rw [inner_combination_left hz (combination_bounded hz d) d]
    apply Finset.sum_congr rfl
    intro i _
    rw [hd i]
  have hfg : paretoInner f (combination z d) =
      ∑ i, d i * paretoInner (z i) f := by
    rw [paretoInner_comm, inner_combination_left hz hf d]
  have h := paretoInner_residual_polynomial hf (combination_bounded hz d) (1 : ℝ)
  simp only [one_mul, one_pow, hgg, hfg] at h
  calc
    _ = _ := h
    _ = _ := by ring

/-- Arbitrary simultaneous coefficients cannot improve on the normal-equation residual. -/
theorem residual_minimizes {z : ι → ℕ → ℝ} {B : ι → ℝ}
    {f : ℕ → ℝ} {C : ℝ} (hz : ∀ i k, |z i k| ≤ B i)
    (hf : ∀ k, |f k| ≤ C) (d : ι → ℝ)
    (hd : ∀ i, paretoInner (z i) (combination z d) = paretoInner (z i) f)
    (b : ι → ℝ) :
    paretoInner (fun k => f k - combination z d k)
      (fun k => f k - combination z d k) ≤
    paretoInner (fun k => f k - combination z b k)
      (fun k => f k - combination z b k) := by
  rw [residual_completion hz hf d hd b]
  exact le_add_of_nonneg_right (paretoInner_self_nonneg _)

/-- Actual zero-mean controls preserve the signal for every coefficient vector. -/
theorem mean_residual {z : ι → ℕ → ℝ} {B : ι → ℝ}
    {f : ℕ → ℝ} {C : ℝ} (hz : ∀ i k, |z i k| ≤ B i)
    (hf : ∀ k, |f k| ≤ C) (hm : ∀ i, paretoMean (z i) = 0)
    (b : ι → ℝ) :
    paretoMean (fun k => f k - combination z b k) = paretoMean f := by
  have h1 : ∀ k : ℕ, |(1 : ℝ)| ≤ 1 := by intro k; norm_num
  have hb : paretoMean (combination z b) = 0 := by
    rw [← paretoInner_one_right, inner_combination_left hz h1 b]
    simp only [paretoInner_one_right, hm, mul_zero, Finset.sum_const_zero]
  rw [paretoMean_sub hf (combination_bounded hz b), hb, sub_zero]

/-- Exact variance completion for the complete infinite Pareto law. -/
theorem variance_completion {z : ι → ℕ → ℝ} {B : ι → ℝ}
    {f : ℕ → ℝ} {C : ℝ} (hz : ∀ i k, |z i k| ≤ B i)
    (hf : ∀ k, |f k| ≤ C) (hm : ∀ i, paretoMean (z i) = 0)
    (d : ι → ℝ)
    (hd : ∀ i, paretoInner (z i) (combination z d) = paretoInner (z i) f)
    (b : ι → ℝ) :
    paretoVariance (fun k => f k - combination z b k) =
      paretoVariance (fun k => f k - combination z d k) +
      paretoInner (combination z (fun i => b i - d i))
        (combination z (fun i => b i - d i)) := by
  rw [paretoVariance_eq (bounded_sub hf (combination_bounded hz b)),
    paretoVariance_eq (bounded_sub hf (combination_bounded hz d)),
    mean_residual hz hf hm b, mean_residual hz hf hm d,
    residual_completion hz hf d hd b]
  ring

/-- Directional covariance Schur complement with the actual Gram inverse.
The minimum is attained by additive control coefficients `-inverseCoeff e z f`. -/
theorem inverse_variance_schur_value {z : ι → ℕ → ℝ} {B : ι → ℝ}
    {f : ℕ → ℝ} {C : ℝ} (hz : ∀ i k, |z i k| ≤ B i)
    (hf : ∀ k, |f k| ≤ C) (hm : ∀ i, paretoMean (z i) = 0)
    (e : (ι → ℝ) ≃ₗ[ℝ] (ι → ℝ))
    (he : ∀ b i, e b i = gramApply z b i) :
    paretoVariance (fun k => f k - combination z (inverseCoeff e z f) k) =
      paretoVariance f - ∑ i, inverseCoeff e z f i * cross z f i := by
  rw [paretoVariance_eq (bounded_sub hf (combination_bounded hz _)),
    mean_residual hz hf hm, residual_schur_value hz hf _
      (inverseCoeff_normal hz e he f), paretoVariance_eq hf]
  unfold cross
  ring

/-- A simultaneous finite-control optimizer, with no coordinatewise greedy assumption. -/
theorem inverse_variance_minimizes {z : ι → ℕ → ℝ} {B : ι → ℝ}
    {f : ℕ → ℝ} {C : ℝ} (hz : ∀ i k, |z i k| ≤ B i)
    (hf : ∀ k, |f k| ≤ C) (hm : ∀ i, paretoMean (z i) = 0)
    (e : (ι → ℝ) ≃ₗ[ℝ] (ι → ℝ))
    (he : ∀ b i, e b i = gramApply z b i) (b : ι → ℝ) :
    paretoVariance (fun k => f k - combination z (inverseCoeff e z f) k) ≤
      paretoVariance (fun k => f k - combination z b k) := by
  rw [variance_completion hz hf hm _ (inverseCoeff_normal hz e he f) b]
  exact le_add_of_nonneg_right (paretoInner_self_nonneg _)

/-- Full signed matrix expansion of the exact excess variance. -/
theorem inverse_variance_completion_matrix {z : ι → ℕ → ℝ} {B : ι → ℝ}
    {f : ℕ → ℝ} {C : ℝ} (hz : ∀ i k, |z i k| ≤ B i)
    (hf : ∀ k, |f k| ≤ C) (hm : ∀ i, paretoMean (z i) = 0)
    (e : (ι → ℝ) ≃ₗ[ℝ] (ι → ℝ))
    (he : ∀ b i, e b i = gramApply z b i) (b : ι → ℝ) :
    paretoVariance (fun k => f k - combination z b k) =
      paretoVariance f - ∑ i, inverseCoeff e z f i * cross z f i +
      ∑ i, ∑ j, (b i - inverseCoeff e z f i) *
        (b j - inverseCoeff e z f j) * paretoInner (z i) (z j) := by
  rw [variance_completion hz hf hm _ (inverseCoeff_normal hz e he f) b,
    inverse_variance_schur_value hz hf hm e he]
  congr 1
  unfold RiemannResearch.RH.Pareto.FiniteSchur.combination
  exact paretoInner_finsetCombination Finset.univ
    (fun i => b i - inverseCoeff e z f i) hz

/-- For zero-mean controls the stored mixed entry is exactly centered covariance. -/
theorem cross_eq_covariance {z : ι → ℕ → ℝ} {B : ι → ℝ}
    {f : ℕ → ℝ} {C : ℝ} (hz : ∀ i k, |z i k| ≤ B i)
    (hf : ∀ k, |f k| ≤ C) (hm : ∀ i, paretoMean (z i) = 0) (i : ι) :
    cross z f i =
      paretoInner (fun k => z i k - paretoMean (z i))
        (fun k => f k - paretoMean f) := by
  have h1 : ∀ k : ℕ, |(1 : ℝ)| ≤ 1 := by intro k; norm_num
  have hconst : paretoInner (z i) (fun _ => paretoMean f) = 0 := by
    have h := paretoInner_const_mul_right (hz i) h1 (paretoMean f)
    simpa only [mul_one, paretoInner_one_right, hm i, mul_zero] using h
  rw [hm i]
  simp only [sub_zero]
  rw [paretoInner_sub_right (hz i) hf (fun _ => le_rfl), hconst, sub_zero]
  rfl

/-- All remaining terms in simultaneous coefficient-and-scale optimization.
The finite control excess and the scalar excess are separate exact nonnegative terms. -/
theorem inverse_joint_completion {z : ι → ℕ → ℝ} {B : ι → ℝ}
    {f : ℕ → ℝ} {C : ℝ} (hz : ∀ i k, |z i k| ≤ B i)
    (hf : ∀ k, |f k| ≤ C) (hm : ∀ i, paretoMean (z i) = 0)
    (hs : paretoMean f ≠ 0)
    (e : (ι → ℝ) ≃ₗ[ℝ] (ι → ℝ))
    (he : ∀ b i, e b i = gramApply z b i) (b : ι → ℝ) (a : ℝ) :
    let d := inverseCoeff e z f
    let r := fun k => f k - combination z d k
    paretoError (fun k => a * (f k - combination z b k)) =
      paretoVariance r / (paretoVariance r + (paretoMean f)^2) +
      (paretoVariance r + (paretoMean f)^2) *
        (a - paretoMean f / (paretoVariance r + (paretoMean f)^2))^2 +
      a^2 * paretoInner (combination z (fun i => b i - d i))
        (combination z (fun i => b i - d i)) := by
  let d := inverseCoeff e z f
  let r := fun k => f k - combination z d k
  change paretoError (fun k => a * (f k - combination z b k)) =
    paretoVariance r / (paretoVariance r + (paretoMean f)^2) +
    (paretoVariance r + (paretoMean f)^2) *
      (a - paretoMean f / (paretoVariance r + (paretoMean f)^2))^2 +
    a^2 * paretoInner (combination z (fun i => b i - d i))
      (combination z (fun i => b i - d i))
  have hr := bounded_sub hf (combination_bounded hz d)
  have hrm : paretoMean r = paretoMean f := mean_residual hz hf hm d
  have hrnz : paretoMean r ≠ 0 := by rw [hrm]; exact hs
  have hd := inverseCoeff_normal hz e he f
  have hdiff : paretoError (fun k => a * (f k - combination z b k)) =
      paretoError (fun k => a * r k) +
      a^2 * paretoInner (combination z (fun i => b i - d i))
        (combination z (fun i => b i - d i)) := by
    rw [paretoError_scale (bounded_sub hf (combination_bounded hz b)),
      paretoError_scale hr, mean_residual hz hf hm b, hrm,
      variance_completion hz hf hm d hd b]
    change _ = 1 - 2 * a * paretoMean f +
      a^2 * (paretoVariance (fun k => f k - combination z d k) +
        (paretoMean f)^2) + _
    ring
  rw [hdiff, paretoError_scale_completion hr hrnz, hrm]

/-- The explicit joint minimum is attained; the mean of the repaired signal stays nonzero. -/
theorem inverse_joint_value {z : ι → ℕ → ℝ} {B : ι → ℝ}
    {f : ℕ → ℝ} {C : ℝ} (hz : ∀ i k, |z i k| ≤ B i)
    (hf : ∀ k, |f k| ≤ C) (hm : ∀ i, paretoMean (z i) = 0)
    (hs : paretoMean f ≠ 0)
    (e : (ι → ℝ) ≃ₗ[ℝ] (ι → ℝ))
    (he : ∀ b i, e b i = gramApply z b i) :
    let d := inverseCoeff e z f
    let r := fun k => f k - combination z d k
    paretoError (fun k => (paretoMean f /
      (paretoVariance r + (paretoMean f)^2)) * r k) =
      paretoVariance r / (paretoVariance r + (paretoMean f)^2) := by
  let d := inverseCoeff e z f
  let r := fun k => f k - combination z d k
  have hr := bounded_sub hf (combination_bounded hz d)
  have hrm : paretoMean r = paretoMean f := mean_residual hz hf hm d
  have hrnz : paretoMean r ≠ 0 := by rw [hrm]; exact hs
  have h := paretoError_scale_completion hr hrnz
    (paretoMean f / (paretoVariance r + (paretoMean f)^2))
  rw [hrm] at h
  simpa only [r, d, sub_self, zero_pow (by decide : 2 ≠ 0), mul_zero, add_zero] using h

/-- The joint value is a lower bound for every simultaneous control vector and scale. -/
theorem inverse_joint_minimizes {z : ι → ℕ → ℝ} {B : ι → ℝ}
    {f : ℕ → ℝ} {C : ℝ} (hz : ∀ i k, |z i k| ≤ B i)
    (hf : ∀ k, |f k| ≤ C) (hm : ∀ i, paretoMean (z i) = 0)
    (hs : paretoMean f ≠ 0)
    (e : (ι → ℝ) ≃ₗ[ℝ] (ι → ℝ))
    (he : ∀ b i, e b i = gramApply z b i) (b : ι → ℝ) (a : ℝ) :
    let r := fun k => f k - combination z (inverseCoeff e z f) k
    paretoVariance r / (paretoVariance r + (paretoMean f)^2) ≤
      paretoError (fun k => a * (f k - combination z b k)) := by
  dsimp only
  rw [inverse_joint_completion hz hf hm hs e he b a]
  have hscale : 0 ≤ (paretoVariance (fun k => f k -
      combination z (inverseCoeff e z f) k) + (paretoMean f)^2) *
      (a - paretoMean f / (paretoVariance (fun k => f k -
        combination z (inverseCoeff e z f) k) + (paretoMean f)^2))^2 :=
    mul_nonneg (add_nonneg (paretoVariance_nonneg _) (sq_nonneg _)) (sq_nonneg _)
  have hcontrol : 0 ≤ a^2 *
      paretoInner (combination z (fun i => b i - inverseCoeff e z f i))
        (combination z (fun i => b i - inverseCoeff e z f i)) :=
    mul_nonneg (sq_nonneg _) (paretoInner_self_nonneg _)
  linarith

end
end RiemannResearch.RH.Pareto.FiniteSchur
