import RiemannResearch.RH.ParetoMellinSchurProduct
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Complete finite Mellin Gram determinants

Source: user-requested fifth Ramanujan transfer program, October 2026.
The Schur product is iterated into the full squared-Vandermonde quotient.
Repeated nodes are allowed in the exact formula: both sides then vanish.
For arbitrary finite indexing the formula can be read in any enumeration.
-/

noncomputable section
open scoped BigOperators Matrix

namespace RiemannResearch.RH.Pareto

def mellinGramVolume {n : ℕ} (s : Fin n → ℂ) : ℝ :=
  ∏ j : Fin n,
    mellinCenteredProduct
      (fun i : Fin j.val => s ⟨i.val, lt_trans i.isLt j.isLt⟩) (s j) /
      (2 * (s j).re - 1)

def mellinGramVandermonde {n : ℕ} (s : Fin n → ℂ) : ℝ :=
  ∏ j : Fin n, ∏ i : Fin j.val,
    ‖s j - s ⟨i.val, lt_trans i.isLt j.isLt⟩‖ ^ 2

def mellinGramCrossDenominator {n : ℕ} (s : Fin n → ℂ) : ℝ :=
  ∏ j : Fin n, ∏ i : Fin j.val,
    ‖s j + starRingEnd ℂ (s ⟨i.val, lt_trans i.isLt j.isLt⟩) - 1‖ ^ 2

theorem mellinGramVolume_succ {n : ℕ} (s : Fin (n + 1) → ℂ) :
    mellinGramVolume s = mellinGramVolume (fun i : Fin n => s i.castSucc) *
      (mellinCenteredProduct (fun i : Fin n => s i.castSucc) (s (Fin.last n)) /
        (2 * (s (Fin.last n)).re - 1)) := by
  unfold mellinGramVolume
  rw [Fin.prod_univ_castSucc]
  rfl

/-- The full finite determinant, including the singular repeated-node case. -/
theorem mellinCauchyGram_det_full_product (n : ℕ) (s : Fin n → ℂ)
    (hs : ∀ i, (1 / 2 : ℝ) < (s i).re) :
    (mellinCauchyGram s).det = (mellinGramVolume s : ℂ) := by
  classical
  induction n with
  | zero => simp [mellinCauchyGram, mellinGramVolume]
  | succ n ih =>
    let t : Fin n → ℂ := fun i => s i.castSucc
    let w : ℂ := s (Fin.last n)
    have ht : ∀ i, (1 / 2 : ℝ) < (t i).re := fun i => hs i.castSucc
    have hw : (1 / 2 : ℝ) < w.re := hs (Fin.last n)
    have he : (mellinCauchyGram s).det =
        (mellinCauchyGram (mellinAppend t w)).det := by
      have hm : (mellinCauchyGram s).submatrix finSuccEquivLast.symm
          finSuccEquivLast.symm = mellinCauchyGram (mellinAppend t w) := by
        ext i j
        cases i <;> cases j <;>
          simp [mellinCauchyGram, mellinAppend, t, w,
            finSuccEquivLast_symm_some, finSuccEquivLast_symm_none]
      rw [← Matrix.det_submatrix_equiv_self finSuccEquivLast.symm
        (mellinCauchyGram s), hm]
    rw [he, mellinGramVolume_succ, Complex.ofReal_mul]
    change (mellinCauchyGram (mellinAppend t w)).det =
      (mellinGramVolume t : ℂ) *
        ((mellinCenteredProduct t w / (2 * w.re - 1) : ℝ) : ℂ)
    by_cases hinj : Function.Injective t
    · rw [mellinCauchyGram_det_append_product t w ht hw hinj, ih t ht]
    · have hsmall : (mellinCauchyGram t).det = 0 := by
        by_contra hz
        exact hinj ((mellinCauchyGram_det_ne_zero_iff_injective t ht).mp hz)
      have happ : ∀ i, (1 / 2 : ℝ) < (mellinAppend t w i).re := by
        intro i
        cases i with
        | none => exact hw
        | some i => exact ht i
      have hlarge : (mellinCauchyGram (mellinAppend t w)).det = 0 := by
        by_contra hz
        have hi := (mellinCauchyGram_det_ne_zero_iff_injective
          (mellinAppend t w) happ).mp hz
        apply hinj
        intro i j hij
        apply Option.some.inj
        apply hi
        exact hij
      rw [hlarge, ← ih t ht, hsmall, zero_mul]

/-- A closed squared-Vandermonde quotient, with no inverse matrix remaining. -/
theorem mellinGramVolume_vandermonde {n : ℕ} (s : Fin n → ℂ) :
    mellinGramVolume s = mellinGramVandermonde s /
      ((∏ j : Fin n, (2 * (s j).re - 1)) * mellinGramCrossDenominator s) := by
  unfold mellinGramVolume mellinCenteredProduct
    mellinGramVandermonde mellinGramCrossDenominator
  simp_rw [norm_div, div_pow, Finset.prod_div_distrib]
  rw [div_div, mul_comm]

theorem mellinCauchyGram_det_vandermonde (n : ℕ) (s : Fin n → ℂ)
    (hs : ∀ i, (1 / 2 : ℝ) < (s i).re) :
    (mellinCauchyGram s).det =
      ((mellinGramVandermonde s /
        ((∏ j : Fin n, (2 * (s j).re - 1)) *
          mellinGramCrossDenominator s) : ℝ) : ℂ) := by
  rw [mellinCauchyGram_det_full_product n s hs, mellinGramVolume_vandermonde]

theorem mellinGramVolume_nonneg {n : ℕ} (s : Fin n → ℂ)
    (hs : ∀ i, (1 / 2 : ℝ) < (s i).re) : 0 ≤ mellinGramVolume s := by
  unfold mellinGramVolume
  apply Finset.prod_nonneg
  intro j _
  exact div_nonneg (mellinCenteredProduct_nonneg _ _) (by linarith [hs j])

theorem mellinGramVolume_pos_iff {n : ℕ} (s : Fin n → ℂ)
    (hs : ∀ i, (1 / 2 : ℝ) < (s i).re) :
    0 < mellinGramVolume s ↔ Function.Injective s := by
  constructor
  · intro hp
    apply (mellinCauchyGram_det_ne_zero_iff_injective s hs).mp
    rw [mellinCauchyGram_det_full_product n s hs]
    exact Complex.ofReal_ne_zero.mpr (ne_of_gt hp)
  · intro hi
    have hn : mellinGramVolume s ≠ 0 := by
      intro hz
      have hd := (mellinCauchyGram_det_ne_zero_iff_injective s hs).mpr hi
      apply hd
      rw [mellinCauchyGram_det_full_product n s hs, hz, Complex.ofReal_zero]
    exact lt_of_le_of_ne (mellinGramVolume_nonneg s hs) (Ne.symm hn)

theorem mellinGramVolume_eq_zero_iff {n : ℕ} (s : Fin n → ℂ)
    (hs : ∀ i, (1 / 2 : ℝ) < (s i).re) :
    mellinGramVolume s = 0 ↔ ¬ Function.Injective s := by
  constructor
  · intro hz hi
    have hp := (mellinGramVolume_pos_iff s hs).mpr hi
    rw [hz] at hp
    exact (lt_irrefl 0) hp
  · intro hi
    by_contra hz
    have hp := lt_of_le_of_ne (mellinGramVolume_nonneg s hs) (Ne.symm hz)
    exact hi ((mellinGramVolume_pos_iff s hs).mp hp)

theorem mellinCauchyGram_det_re_nonneg (n : ℕ) (s : Fin n → ℂ)
    (hs : ∀ i, (1 / 2 : ℝ) < (s i).re) : 0 ≤ (mellinCauchyGram s).det.re := by
  rw [mellinCauchyGram_det_full_product n s hs, Complex.ofReal_re]
  exact mellinGramVolume_nonneg s hs

theorem mellinCauchyGram_det_im_eq_zero (n : ℕ) (s : Fin n → ℂ)
    (hs : ∀ i, (1 / 2 : ℝ) < (s i).re) : (mellinCauchyGram s).det.im = 0 := by
  rw [mellinCauchyGram_det_full_product n s hs, Complex.ofReal_im]

theorem mellinCauchyGram_det_re_pos_iff (n : ℕ) (s : Fin n → ℂ)
    (hs : ∀ i, (1 / 2 : ℝ) < (s i).re) :
    0 < (mellinCauchyGram s).det.re ↔ Function.Injective s := by
  rw [mellinCauchyGram_det_full_product n s hs, Complex.ofReal_re]
  exact mellinGramVolume_pos_iff s hs

/-- Every enumeration of an arbitrary finite node family gives the same volume. -/
theorem mellinCauchyGram_det_enumerated_product
    {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}
    (s : ι → ℂ) (e : Fin n ≃ ι)
    (hs : ∀ i, (1 / 2 : ℝ) < (s i).re) :
    (mellinCauchyGram s).det = (mellinGramVolume (s ∘ e) : ℂ) := by
  have hm : mellinCauchyGram (s ∘ e) = (mellinCauchyGram s).submatrix e e := rfl
  rw [← Matrix.det_submatrix_equiv_self e (mellinCauchyGram s), ← hm]
  exact mellinCauchyGram_det_full_product n (s ∘ e) (fun i => hs (e i))

end RiemannResearch.RH.Pareto
