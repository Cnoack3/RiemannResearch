import RiemannResearch.RH.ParetoMellinCenteredProduct
import RiemannResearch.RH.ParetoMellinSchurProduct
import Mathlib.Tactic.FieldSimp

/-!
# The complete complex screened Mellin kernel

Source: user-requested fifth Ramanujan transfer program, October 2026.
The mixed centered Cauchy identity retains the phases of both independent
centers. Its diagonal is the earlier centered capacity remainder, and an
interpolation node annihilates the complete screened kernel.
-/

noncomputable section
open scoped BigOperators Matrix

namespace RiemannResearch.RH.Pareto
open RiemannResearch.LinearAlgebra RiemannResearch.LinearAlgebra.CauchyProduct
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def mellinScreeningProduct (s : ι → ℂ) (w : ℂ) : ℂ :=
  ∏ i, (w - s i) / (w + starRingEnd ℂ (s i) - 1)

def mellinScreenedKernel (s : ι → ℂ) (w v : ℂ) : ℂ :=
  1 / (w + starRingEnd ℂ v - 1) -
    (fun i => 1 / (w + starRingEnd ℂ (s i) - 1)) ⬝ᵥ
      ((mellinCauchyGram s)⁻¹ *ᵥ
        (fun i => 1 / (s i + starRingEnd ℂ v - 1)))

theorem mellinScreeningProduct_norm_sq (s : ι → ℂ) (w : ℂ) :
    ‖mellinScreeningProduct s w‖ ^ 2 = mellinCenteredProduct s w := by
  classical
  have h (t : Finset ι) :
      ‖∏ i ∈ t, (w - s i) / (w + starRingEnd ℂ (s i) - 1)‖ ^ 2 =
        ∏ i ∈ t, ‖(w - s i) / (w + starRingEnd ℂ (s i) - 1)‖ ^ 2 := by
    induction t using Finset.induction_on with
    | empty => simp
    | @insert i t hi ih =>
      rw [Finset.prod_insert hi, Finset.prod_insert hi, norm_mul, mul_pow, ih]
  exact h Finset.univ

theorem mellinScreeningProduct_eq_zero_of_mem (s : ι → ℂ) (w : ℂ)
    (hmem : ∃ i, s i = w) : mellinScreeningProduct s w = 0 := by
  classical
  obtain ⟨i, hi⟩ := hmem
  unfold mellinScreeningProduct
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  simp only [hi, sub_self, zero_div]

/-- Both centers are independent; the right side keeps the complete complex phase. -/
theorem mellinScreenedKernel_product (s : ι → ℂ) (w v : ℂ)
    (hs : ∀ i, (1 / 2 : ℝ) < (s i).re)
    (hw : (1 / 2 : ℝ) < w.re) (hv : (1 / 2 : ℝ) < v.re)
    (hinj : Function.Injective s) :
    mellinScreenedKernel s w v =
      (1 / (w + starRingEnd ℂ v - 1)) *
        mellinScreeningProduct s w * starRingEnd ℂ (mellinScreeningProduct s v) := by
  classical
  have hden (a b : ℂ) (ha : (1 / 2 : ℝ) < a.re)
      (hb : (1 / 2 : ℝ) < b.re) : a + starRingEnd ℂ b - 1 ≠ 0 := by
    intro hz
    have h := congrArg Complex.re hz
    simp only [Complex.sub_re, Complex.add_re, Complex.conj_re,
      Complex.one_re, Complex.zero_re] at h
    linarith
  have hconj (z : ℂ) : starRingEnd ℂ (starRingEnd ℂ z) = z := by
    change star (star z) = z
    exact star_star z
  have hm : cauchyMatrix s (fun i => starRingEnd ℂ (s i) - 1) =
      mellinCauchyGram s := by
    funext i j
    dsimp [cauchyMatrix, mellinCauchyGram]
    congr 1
    ring
  have hxy : ∀ i j, s i + (starRingEnd ℂ (s j) - 1) ≠ 0 := by
    intro i j
    simpa only [← add_sub_assoc] using hden (s i) (s j) (hs i) (hs j)
  have hxv : ∀ i, s i + (starRingEnd ℂ v - 1) ≠ 0 := by
    intro i
    simpa only [← add_sub_assoc] using hden (s i) v (hs i) hv
  have huy : ∀ j, w + (starRingEnd ℂ (s j) - 1) ≠ 0 := by
    intro j
    simpa only [← add_sub_assoc] using hden w (s j) hw (hs j)
  have hdet : (cauchyMatrix s (fun i => starRingEnd ℂ (s i) - 1)).det ≠ 0 := by
    rw [hm]
    exact (mellinCauchyGram_det_ne_zero_iff_injective s hs).mpr hinj
  have hp := cauchy_centered_inverse_pairing_mul s
    (fun i => starRingEnd ℂ (s i) - 1) w (starRingEnd ℂ v - 1)
    hxy hxv huy hdet
  rw [hm] at hp
  simp only [← add_sub_assoc] at hp
  have hnum (i : ι) : (starRingEnd ℂ (s i) - 1) - (starRingEnd ℂ v - 1) =
      starRingEnd ℂ (s i) - starRingEnd ℂ v := by ring
  simp_rw [hnum] at hp
  have hprod :
      (∏ i, (s i - w) / (s i + starRingEnd ℂ v - 1)) *
        (∏ i, (starRingEnd ℂ (s i) - starRingEnd ℂ v) /
          (w + starRingEnd ℂ (s i) - 1)) =
      mellinScreeningProduct s w * starRingEnd ℂ (mellinScreeningProduct s v) := by
    unfold mellinScreeningProduct
    rw [map_prod, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i _
    simp only [map_div₀, map_sub, map_add, map_one, hconj]
    have hvden : starRingEnd ℂ v + s i - 1 = s i + starRingEnd ℂ v - 1 := by ring
    rw [hvden]
    field_simp [hden (s i) v (hs i) hv, hden w (s i) hw (hs i)] <;> ring
  rw [hprod] at hp
  have hdot : (fun i => 1 / (w + starRingEnd ℂ (s i) - 1)) ⬝ᵥ
      ((mellinCauchyGram s)⁻¹ *ᵥ
        (fun i => 1 / (s i + starRingEnd ℂ v - 1))) =
      (1 - mellinScreeningProduct s w * starRingEnd ℂ (mellinScreeningProduct s v)) /
        (w + starRingEnd ℂ v - 1) := by
    apply (eq_div_iff (hden w v hw hv)).mpr
    simpa only [mul_comm] using hp
  rw [mellinScreenedKernel, hdot]
  ring

theorem mellinScreenedKernel_diagonal (s : ι → ℂ) (w : ℂ)
    (hs : ∀ i, (1 / 2 : ℝ) < (s i).re) (hw : (1 / 2 : ℝ) < w.re)
    (hinj : Function.Injective s) :
    mellinScreenedKernel s w w =
      ((mellinCenteredProduct s w / (2 * w.re - 1) : ℝ) : ℂ) := by
  have hscalar : w + starRingEnd ℂ w - 1 = ((2 * w.re - 1 : ℝ) : ℂ) := by
    apply Complex.ext <;>
      simp only [Complex.sub_re, Complex.add_re, Complex.conj_re, Complex.one_re,
        Complex.ofReal_re, Complex.sub_im, Complex.add_im, Complex.conj_im,
        Complex.one_im, Complex.ofReal_im] <;> ring
  rw [mellinScreenedKernel_product s w w hs hw hw hinj, mul_assoc,
    Complex.mul_conj, ← Complex.sq_norm, mellinScreeningProduct_norm_sq,
    hscalar, Complex.ofReal_div]
  ring

theorem mellinScreenedKernel_eq_zero_of_left_mem (s : ι → ℂ) (w v : ℂ)
    (hs : ∀ i, (1 / 2 : ℝ) < (s i).re)
    (hw : (1 / 2 : ℝ) < w.re) (hv : (1 / 2 : ℝ) < v.re)
    (hinj : Function.Injective s) (hmem : ∃ i, s i = w) :
    mellinScreenedKernel s w v = 0 := by
  rw [mellinScreenedKernel_product s w v hs hw hv hinj,
    mellinScreeningProduct_eq_zero_of_mem s w hmem, mul_zero, zero_mul]

theorem mellinScreenedKernel_eq_zero_of_right_mem (s : ι → ℂ) (w v : ℂ)
    (hs : ∀ i, (1 / 2 : ℝ) < (s i).re)
    (hw : (1 / 2 : ℝ) < w.re) (hv : (1 / 2 : ℝ) < v.re)
    (hinj : Function.Injective s) (hmem : ∃ i, s i = v) :
    mellinScreenedKernel s w v = 0 := by
  rw [mellinScreenedKernel_product s w v hs hw hv hinj,
    mellinScreeningProduct_eq_zero_of_mem s v hmem, map_zero, mul_zero]

end RiemannResearch.RH.Pareto
