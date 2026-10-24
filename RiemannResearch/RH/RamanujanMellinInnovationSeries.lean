import RiemannResearch.RH.ParetoMellinReindexing
import RiemannResearch.RH.ParetoMellinSchurProduct
import RiemannResearch.RH.QRamanujanMellinCertificates
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Ordered Mellin innovations with an order-independent total

Source: finite Schur telescoping, assembled from verified source identities,
24 October 2026. Each innovation retains its exact inverse screening product.
The complete prefix sum equals the inverse-Gram capacity and is invariant
under every finite reordering of the same probes and sources.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.Pareto

def mellinPrefixCapacity (z b : ℕ → ℂ) (N : ℕ) : ℝ :=
  mellinInverseCapacity (fun i : Fin N => z i.val) (fun i => b i.val)

def mellinPrefixInnovation (z b : ℕ → ℂ) (n : ℕ) : ℝ :=
  (2 * (z n).re - 1) *
    ‖mellinSchurInnovation (fun i : Fin n => z i.val) (fun i => b i.val) (z n) (b n)‖ ^ 2 /
    mellinCenteredProduct (fun i : Fin n => z i.val) (z n)

theorem mellinPrefixCapacity_zero (z b : ℕ → ℂ) : mellinPrefixCapacity z b 0 = 0 := by
  simp [mellinPrefixCapacity, mellinInverseCapacity]

theorem mellinPrefixInnovation_nonneg (z b : ℕ → ℂ)
    (hz : ∀ n, (1 / 2 : ℝ) < (z n).re) (n : ℕ) :
    0 ≤ mellinPrefixInnovation z b n := by
  exact div_nonneg (mul_nonneg (by linarith [hz n]) (sq_nonneg _))
    (mellinCenteredProduct_nonneg _ _)

theorem mellinPrefixCapacity_succ (z b : ℕ → ℂ)
    (hz : ∀ n, (1 / 2 : ℝ) < (z n).re) (hinj : Function.Injective z) (n : ℕ) :
    mellinPrefixCapacity z b (n + 1) =
      mellinPrefixCapacity z b n + mellinPrefixInnovation z b n := by
  let s : Fin (n + 1) → ℂ := fun i => z i.val
  let c : Fin (n + 1) → ℂ := fun i => b i.val
  let t : Fin n → ℂ := fun i => z i.val
  let d : Fin n → ℂ := fun i => b i.val
  have hs : ∀ i, (1 / 2 : ℝ) < (s i).re := fun i => hz i.val
  have hi : Function.Injective s := fun i j h => Fin.ext (hinj h)
  have hdet := (mellinCauchyGram_det_ne_zero_iff_injective s hs).mpr hi
  have he : s ∘ finSuccEquivLast.symm = mellinAppend t (z n) := by
    funext i
    cases i <;> simp [s, t, mellinAppend, finSuccEquivLast_symm_some,
      finSuccEquivLast_symm_none]
  have hb : c ∘ finSuccEquivLast.symm = mellinAppend d (b n) := by
    funext i
    cases i <;> simp [c, d, mellinAppend, finSuccEquivLast_symm_some,
      finSuccEquivLast_symm_none]
  have hr := mellinInverseCapacity_reindex finSuccEquivLast.symm s c hdet
  rw [he, hb] at hr
  change mellinInverseCapacity s c = _
  rw [← hr, mellinInverseCapacity_append_product t d (z n) (b n)
    (fun i => hz i.val) (hz n) (fun i j h => Fin.ext (hinj h))
    (fun i h => (Nat.ne_of_lt i.isLt) (hinj h))]
  rfl

/-- Every signed arithmetic source has an exact finite innovation decomposition. -/
theorem mellinPrefixInnovation_sum (z b : ℕ → ℂ)
    (hz : ∀ n, (1 / 2 : ℝ) < (z n).re) (hinj : Function.Injective z) (N : ℕ) :
    (∑ n ∈ Finset.range N, mellinPrefixInnovation z b n) = mellinPrefixCapacity z b N := by
  induction N with
  | zero => simp [mellinPrefixCapacity_zero]
  | succ N ih =>
    rw [Finset.sum_range_succ, ih, mellinPrefixCapacity_succ z b hz hinj]

/-- Finite reordering changes individual innovations but preserves their total exactly. -/
theorem mellinPrefixInnovation_sum_reorder (z b w c : ℕ → ℂ)
    (hz : ∀ n, (1 / 2 : ℝ) < (z n).re) (hw : ∀ n, (1 / 2 : ℝ) < (w n).re)
    (hzi : Function.Injective z) (hwi : Function.Injective w)
    (N : ℕ) (e : Fin N ≃ Fin N)
    (he : ∀ i : Fin N, w i.val = z (e i).val)
    (hc : ∀ i : Fin N, c i.val = b (e i).val) :
    (∑ n ∈ Finset.range N, mellinPrefixInnovation w c n) =
      ∑ n ∈ Finset.range N, mellinPrefixInnovation z b n := by
  rw [mellinPrefixInnovation_sum w c hw hwi, mellinPrefixInnovation_sum z b hz hzi]
  have hdet := (mellinCauchyGram_det_ne_zero_iff_injective
    (fun i : Fin N => z i.val) (fun i => hz i.val)).mpr
      (fun i j h => Fin.ext (hzi h))
  have h := mellinInverseCapacity_reindex e (fun i : Fin N => z i.val)
    (fun i => b i.val) hdet
  have he' : (fun i : Fin N => w i.val) = (fun i : Fin N => z i.val) ∘ e := funext he
  have hc' : (fun i : Fin N => c i.val) = (fun i : Fin N => b i.val) ∘ e := funext hc
  simpa only [mellinPrefixCapacity, he', hc'] using h

/-- The full physical norm is the sum of all finite innovations and the complete remainder. -/
theorem mellinPrefixInnovation_physical_completion (f : ThresholdHilbert) (z : ℕ → ℂ)
    (hz : ∀ n, (1 / 2 : ℝ) < (z n).re) (hinj : Function.Injective z) (N : ℕ) :
    ‖f‖ ^ 2 = (∑ n ∈ Finset.range N,
      mellinPrefixInnovation z (fun j => paretoMellin f (z j)) n) +
        mellinProjectionRemainder f (fun i : Fin N => z i.val) := by
  rw [mellinPrefixInnovation_sum z _ hz hinj]
  exact finiteMellinKernel_inverse_completion f (fun i : Fin N => z i.val)
    (fun i => hz i.val) ((mellinCauchyGram_det_ne_zero_iff_injective
      (fun i : Fin N => z i.val) (fun i => hz i.val)).mpr
        (fun i j h => Fin.ext (hinj h)))

end RiemannResearch.RH.Pareto

namespace RiemannResearch.RH.QRamanujanMellinCertificates
open Pareto ZetaTwoHilbert ZetaTwoProbability ZetaTwoParetoTransfer QParetoMetric QMellinTransfer

theorem qMellinPrefixInnovation_completion (f : QHilbert) (z : ℕ → ℂ)
    (hz : ∀ n, (1 / 2 : ℝ) < (z n).re) (hinj : Function.Injective z) (N : ℕ) :
    zetaTwo * ‖f‖ ^ 2 = (∑ n ∈ Finset.range N,
      mellinPrefixInnovation z (fun j => qMellin f (z j)) n) +
        mellinProjectionRemainder (toPareto f) (fun i : Fin N => z i.val) + metricCorrection f := by
  rw [norm_identity, mellinPrefixInnovation_physical_completion (toPareto f) z hz hinj N]
  rfl

end RiemannResearch.RH.QRamanujanMellinCertificates
