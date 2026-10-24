import RiemannResearch.LinearAlgebra.CenteredCauchyInverseProduct
import RiemannResearch.RH.ParetoMellinNonsingular
import RiemannResearch.RH.ParetoMellinGramOptimization
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Centered finite Mellin interpolation capacities

Source: user-requested fourth Ramanujan development, October 2026.
The mixed centered Cauchy determinant identity evaluates the complete finite
capacity for a reproducing-kernel source at every strict-half-plane center.
The center may coincide with an interpolation node; no avoidance hypothesis
is imposed, and in that case the product automatically vanishes.
-/

noncomputable section
open scoped BigOperators Matrix

namespace RiemannResearch.RH.Pareto
open RiemannResearch.LinearAlgebra RiemannResearch.LinearAlgebra.CauchyProduct
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def mellinCenteredProduct (s : ι → ℂ) (w : ℂ) : ℝ :=
  ∏ i, ‖(w - s i) / (w + starRingEnd ℂ (s i) - 1)‖ ^ 2

theorem mellinCenteredProduct_nonneg (s : ι → ℂ) (w : ℂ) :
    0 ≤ mellinCenteredProduct s w :=
  Finset.prod_nonneg (fun _ _ => sq_nonneg _)

/-- Exact finite kernel capacity at an arbitrary half-plane center. -/
theorem mellinInverseCapacity_centered_product (s : ι → ℂ) (w : ℂ)
    (hs : ∀ i, (1 / 2 : ℝ) < (s i).re) (hw : (1 / 2 : ℝ) < w.re)
    (hinj : Function.Injective s) :
    mellinInverseCapacity s (fun i => 1 / (s i + starRingEnd ℂ w - 1)) =
      (1 - mellinCenteredProduct s w) / (2 * w.re - 1) := by
  classical
  have hconj (z : ℂ) : starRingEnd ℂ (starRingEnd ℂ z) = z := by
    change star (star z) = z
    exact star_star z
  have hden (a b : ℂ) (ha : (1 / 2 : ℝ) < a.re)
      (hb : (1 / 2 : ℝ) < b.re) : a + starRingEnd ℂ b - 1 ≠ 0 := by
    intro hz
    have h := congrArg Complex.re hz
    simp only [Complex.sub_re, Complex.add_re, Complex.conj_re,
      Complex.one_re, Complex.zero_re] at h
    linarith
  have hm : cauchyMatrix s (fun i => starRingEnd ℂ (s i) - 1) =
      mellinCauchyGram s := by
    funext i j
    dsimp [cauchyMatrix, mellinCauchyGram]
    congr 1
    ring
  have hxy : ∀ i j, s i + (starRingEnd ℂ (s j) - 1) ≠ 0 := by
    intro i j
    simpa only [← add_sub_assoc] using hden (s i) (s j) (hs i) (hs j)
  have hxv : ∀ i, s i + (starRingEnd ℂ w - 1) ≠ 0 := by
    intro i
    simpa only [← add_sub_assoc] using hden (s i) w (hs i) hw
  have huy : ∀ j, w + (starRingEnd ℂ (s j) - 1) ≠ 0 := by
    intro j
    simpa only [← add_sub_assoc] using hden w (s j) hw (hs j)
  have hdet : (cauchyMatrix s (fun i => starRingEnd ℂ (s i) - 1)).det ≠ 0 := by
    rw [hm]
    exact (mellinCauchyGram_det_ne_zero_iff_injective s hs).mpr hinj
  have hp := cauchy_centered_inverse_pairing_mul s
    (fun i => starRingEnd ℂ (s i) - 1) w (starRingEnd ℂ w - 1)
    hxy hxv huy hdet
  rw [hm] at hp
  simp only [← add_sub_assoc] at hp
  have hnum (i : ι) : (starRingEnd ℂ (s i) - 1) - (starRingEnd ℂ w - 1) =
      starRingEnd ℂ (s i) - starRingEnd ℂ w := by ring
  simp_rw [hnum] at hp
  let c := mellinInverseCoefficients s (fun i => 1 / (s i + starRingEnd ℂ w - 1))
  change (w + starRingEnd ℂ w - 1) *
      (∑ i, (1 / (w + starRingEnd ℂ (s i) - 1)) * c i) =
    1 - (∏ i, (s i - w) / (s i + starRingEnd ℂ w - 1)) *
      (∏ i, (starRingEnd ℂ (s i) - starRingEnd ℂ w) /
        (w + starRingEnd ℂ (s i) - 1)) at hp
  have hsource (i : ι) :
      starRingEnd ℂ (1 / (w + starRingEnd ℂ (s i) - 1)) =
      1 / (s i + starRingEnd ℂ w - 1) := by
    simp only [map_div₀, map_one, map_sub, map_add, hconj]
    congr 1
    ring
  have hc : starRingEnd ℂ
      (∑ i, (1 / (w + starRingEnd ℂ (s i) - 1)) * c i) =
      ∑ i, starRingEnd ℂ (c i) * (1 / (s i + starRingEnd ℂ w - 1)) := by
    simp only [map_sum, map_mul, hsource]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hleft : mellinInverseCapacity s
      (fun i => 1 / (s i + starRingEnd ℂ w - 1)) =
      (∑ i, (1 / (w + starRingEnd ℂ (s i) - 1)) * c i).re := by
    have h := congrArg Complex.re hc
    simpa only [Complex.conj_re, mellinInverseCapacity, c] using h.symm
  have hdenconj (i : ι) : starRingEnd ℂ (s i + starRingEnd ℂ w - 1) =
      w + starRingEnd ℂ (s i) - 1 := by
    simp only [map_sub, map_add, map_one, hconj]
    ring
  have hfactor (i : ι) : ‖(s i - w) / (s i + starRingEnd ℂ w - 1)‖ ^ 2 =
      ‖(w - s i) / (w + starRingEnd ℂ (s i) - 1)‖ ^ 2 := by
    have hn : ‖s i + starRingEnd ℂ w - 1‖ =
        ‖w + starRingEnd ℂ (s i) - 1‖ := by
      rw [← hdenconj i]
      exact (Complex.norm_conj _).symm
    rw [norm_div, norm_div, norm_sub_rev (s i) w, hn]
  have hnorm (t : Finset ι) :
      ‖∏ i ∈ t, (s i - w) / (s i + starRingEnd ℂ w - 1)‖ ^ 2 =
        ∏ i ∈ t, ‖(w - s i) / (w + starRingEnd ℂ (s i) - 1)‖ ^ 2 := by
    induction t using Finset.induction_on with
    | empty => simp
    | @insert i t hi ih =>
      rw [Finset.prod_insert hi, Finset.prod_insert hi, norm_mul, mul_pow, hfactor, ih]
  have hprod : ((∏ i, (s i - w) / (s i + starRingEnd ℂ w - 1)) *
      (∏ i, (starRingEnd ℂ (s i) - starRingEnd ℂ w) /
        (w + starRingEnd ℂ (s i) - 1))).re = mellinCenteredProduct s w := by
    have he : (∏ i, (starRingEnd ℂ (s i) - starRingEnd ℂ w) /
        (w + starRingEnd ℂ (s i) - 1)) =
        starRingEnd ℂ (∏ i, (s i - w) / (s i + starRingEnd ℂ w - 1)) := by
      rw [map_prod]
      apply Finset.prod_congr rfl
      intro i _
      simp only [map_div₀, map_sub, hdenconj]
    rw [he, Complex.mul_conj, Complex.ofReal_re, ← Complex.sq_norm]
    exact hnorm Finset.univ
  have hscalar : w + starRingEnd ℂ w - 1 = ((2 * w.re - 1 : ℝ) : ℂ) := by
    apply Complex.ext <;>
      simp only [Complex.sub_re, Complex.add_re, Complex.conj_re, Complex.one_re,
        Complex.ofReal_re, Complex.sub_im, Complex.add_im, Complex.conj_im,
        Complex.one_im, Complex.ofReal_im] <;> ring
  have h := congrArg Complex.re hp
  rw [Complex.sub_re, Complex.one_re, hprod, hscalar, Complex.mul_re,
    Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, ← hleft] at h
  have hd : 2 * w.re - 1 ≠ 0 := by linarith
  field_simp [hd]
  nlinarith [h]

end RiemannResearch.RH.Pareto
