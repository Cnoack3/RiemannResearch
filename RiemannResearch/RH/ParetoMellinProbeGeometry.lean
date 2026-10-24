import RiemannResearch.RH.ParetoMellinScreenedKernel
import RiemannResearch.RH.ParetoMellinGramDeterminant
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-!
# Quantitative geometry of half-plane Mellin probes

Source: direct algebra of the half-plane Cauchy kernel, assembled for the
sixth Ramanujan transfer program, 24 October 2026. These exact pair defects
and determinant bounds are used by the screened Ramanujan probe certificates.
The full complex kernel is retained before its norm is estimated.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.Pareto

/-- The half-plane kernel denominator has an exact positive excess. -/
theorem mellin_pair_denominator_excess (w v : ℂ) :
    ‖w + starRingEnd ℂ v - 1‖ ^ 2 - ‖w - v‖ ^ 2 =
      (2 * w.re - 1) * (2 * v.re - 1) := by
  simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re,
    Complex.add_re, Complex.conj_re, Complex.one_re, Complex.sub_im,
    Complex.add_im, Complex.conj_im, Complex.one_im]
  ring

theorem mellin_pair_denominator_ne_zero (w v : ℂ)
    (hw : (1 / 2 : ℝ) < w.re) (hv : (1 / 2 : ℝ) < v.re) :
    w + starRingEnd ℂ v - 1 ≠ 0 := by
  intro hz
  have h := congrArg Complex.re hz
  simp only [Complex.sub_re, Complex.add_re, Complex.conj_re,
    Complex.one_re, Complex.zero_re] at h
  linarith

/-- Exact pseudohyperbolic defect; no real or imaginary contribution is lost. -/
theorem mellin_pair_factor_defect (w v : ℂ)
    (hw : (1 / 2 : ℝ) < w.re) (hv : (1 / 2 : ℝ) < v.re) :
    1 - ‖(w - v) / (w + starRingEnd ℂ v - 1)‖ ^ 2 =
      (2 * w.re - 1) * (2 * v.re - 1) / ‖w + starRingEnd ℂ v - 1‖ ^ 2 := by
  have hd : ‖w + starRingEnd ℂ v - 1‖ ^ 2 ≠ 0 :=
    pow_ne_zero 2 (norm_ne_zero_iff.mpr (mellin_pair_denominator_ne_zero w v hw hv))
  rw [norm_div, div_pow, ← mellin_pair_denominator_excess w v,
    sub_div, div_self hd]

theorem mellin_pair_factor_lt_one (w v : ℂ)
    (hw : (1 / 2 : ℝ) < w.re) (hv : (1 / 2 : ℝ) < v.re) :
    ‖(w - v) / (w + starRingEnd ℂ v - 1)‖ ^ 2 < 1 := by
  have he := mellin_pair_factor_defect w v hw hv
  have hp : 0 < (2 * w.re - 1) * (2 * v.re - 1) /
      ‖w + starRingEnd ℂ v - 1‖ ^ 2 :=
    div_pos (mul_pos (by linarith) (by linarith))
      (sq_pos_of_pos (norm_pos_iff.mpr (mellin_pair_denominator_ne_zero w v hw hv)))
  linarith

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem mellinCenteredProduct_le_one (s : ι → ℂ) (w : ℂ)
    (hs : ∀ i, (1 / 2 : ℝ) < (s i).re) (hw : (1 / 2 : ℝ) < w.re) :
    mellinCenteredProduct s w ≤ 1 := by
  apply Finset.prod_le_one
  · intro i _; exact sq_nonneg _
  · intro i _; exact (mellin_pair_factor_lt_one w (s i) hw (hs i)).le

theorem mellinCenteredProduct_lt_one [Nonempty ι] (s : ι → ℂ) (w : ℂ)
    (hs : ∀ i, (1 / 2 : ℝ) < (s i).re) (hw : (1 / 2 : ℝ) < w.re) :
    mellinCenteredProduct s w < 1 := by
  let a : ι := Classical.choice inferInstance
  let f : ι → ℝ := fun i => ‖(w - s i) / (w + starRingEnd ℂ (s i) - 1)‖ ^ 2
  have htail : (∏ i ∈ Finset.univ.erase a, f i) ≤ 1 := by
    apply Finset.prod_le_one
    · intro i _; exact sq_nonneg _
    · intro i _; exact (mellin_pair_factor_lt_one w (s i) hw (hs i)).le
  change (∏ i, f i) < 1
  rw [← Finset.mul_prod_erase Finset.univ f (Finset.mem_univ a)]
  exact (mul_le_mul_of_nonneg_left htail (sq_nonneg _)).trans_lt
    (by simpa only [mul_one] using mellin_pair_factor_lt_one w (s a) hw (hs a))

/-- The complete volume is bounded by the product of diagonal kernel energies,
without any distinctness assumption. -/
theorem mellinGramVolume_le_diagonal (n : ℕ) (s : Fin n → ℂ)
    (hs : ∀ i, (1 / 2 : ℝ) < (s i).re) :
    mellinGramVolume s ≤ ∏ i : Fin n, 1 / (2 * (s i).re - 1) := by
  unfold mellinGramVolume
  apply Finset.prod_le_prod
  · intro i _
    exact div_nonneg (mellinCenteredProduct_nonneg _ _) (by linarith [hs i])
  · intro i _
    exact div_le_div_of_nonneg_right
      (mellinCenteredProduct_le_one
        (fun j : Fin i.val => s ⟨j.val, lt_trans j.isLt i.isLt⟩) (s i)
        (fun j => hs ⟨j.val, lt_trans j.isLt i.isLt⟩) (hs i)) (by linarith [hs i])

/-- Exact off-diagonal screened-kernel energy, retaining both complete products. -/
theorem mellinScreenedKernel_norm_sq_exact (s : ι → ℂ) (w v : ℂ)
    (hs : ∀ i, (1 / 2 : ℝ) < (s i).re)
    (hw : (1 / 2 : ℝ) < w.re) (hv : (1 / 2 : ℝ) < v.re)
    (hinj : Function.Injective s) :
    ‖mellinScreenedKernel s w v‖ ^ 2 =
      mellinCenteredProduct s w * mellinCenteredProduct s v /
        ‖w + starRingEnd ℂ v - 1‖ ^ 2 := by
  rw [mellinScreenedKernel_product s w v hs hw hv hinj]
  simp only [norm_mul, norm_div, norm_one, Complex.norm_conj, mul_pow, div_pow,
    mellinScreeningProduct_norm_sq]
  ring

end RiemannResearch.RH.Pareto
