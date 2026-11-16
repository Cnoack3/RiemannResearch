import RiemannResearch.RH.WeilDampedPrimeOperator
import RiemannResearch.RH.WeilPrimeCutoffFactorization
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Exact arithmetic kernel of the damped prime operator

Source: user-provided prime-side factorization continuation, Priority 2.
The actual operator is identified entrywise and on every finite coordinate
form with the existing von Mangoldt prime kernel. The correlation is
constructed from the L² bump; its support bound is proved.
The complete signed two-sided prime sector is retained.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace RiemannResearch.RH.WeilDampedSynthesis
open RiemannResearch.Analysis.SquareSummableSynthesis
open WeilDampedWeights WeilPrimeCutoff
set_option maxHeartbeats 800000

@[simp] theorem shift_zero (f : L2) : shift 0 f = f := by
  apply Lp.ext
  simpa only [sub_zero] using shift_coe 0 f

theorem shift_adjoint (a : ℝ) :
    (shift a).toContinuousLinearMap.adjoint = (shift (-a)).toContinuousLinearMap := by
  apply ContinuousLinearMap.ext
  intro f
  apply ext_inner_left ℂ
  intro g
  rw [ContinuousLinearMap.adjoint_inner_right]
  change inner ℂ (shift a g) f = inner ℂ g (shift (-a) f)
  have hf : shift a (shift (-a) f) = f := by
    rw [shift_add, add_neg_cancel, shift_zero]
  calc
    _ = inner ℂ (shift a g) (shift a (shift (-a) f)) := by rw [hf]
    _ = _ := (shift a).inner_map_map _ _

theorem compression_adjoint {σ : ℝ} (hσ : 1 / 2 < σ) (φ : L2) (a : ℝ) :
    (compression hσ φ a).adjoint = compression hσ φ (-a) := by
  simp only [compression, ContinuousLinearMap.adjoint_comp,
    ContinuousLinearMap.adjoint_adjoint, shift_adjoint, neg_neg,
    ContinuousLinearMap.comp_assoc]

def correlation (φ : L2) (t : ℝ) : ℂ := inner ℂ φ (shift (-t) φ)

theorem inner_shifts (φ : L2) (a b : ℝ) :
    inner ℂ (shift a φ) (shift b φ) = inner ℂ φ (shift (b - a) φ) := by
  have he : shift a (shift (b - a) φ) = shift b φ := by
    rw [shift_add]
    congr 1
    ring
  rw [← he]
  exact (shift a).inner_map_map _ _

theorem correlation_support {r : ℝ} (φ : L2)
    (hφ : ∀ᵐ x : ℝ, r < |x| → φ x = 0) :
    ∀ t, 2 * r < |t| → correlation φ t = 0 := by
  intro t ht
  rcases lt_abs.mp ht with hp | hn
  · simpa only [correlation, shift_zero, zero_sub, neg_neg] using
      shift_inner_zero (a := 0) (b := -t) φ hφ (by linarith)
  · have h := shift_inner_zero (a := -t) (b := 0) φ hφ (by linarith)
    rw [shift_zero] at h
    unfold correlation
    rw [← inner_conj_symm, h]
    simp

theorem compression_entry {σ : ℝ} (hσ : 1 / 2 < σ) (φ : L2)
    (a : ℝ) (k m : ℕ) :
    inner ℂ (lp.single 2 k 1) (compression hσ φ a (lp.single 2 m 1)) =
      ((amplitude σ k : ℂ) * (amplitude σ m : ℂ)) *
        correlation φ (a - (Real.log m - Real.log k)) := by
  rw [compression, ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.adjoint_inner_right, J_single, J_single]
  unfold column
  rw [map_smul, inner_smul_left, inner_smul_right]
  change (starRingEnd ℂ) (amplitude σ k : ℂ) *
    ((amplitude σ m : ℂ) *
      inner ℂ (shift (Real.log k) φ) (shift (-a) (shift (Real.log m) φ))) = _
  rw [shift_add, inner_shifts]
  have he : -a + Real.log m - Real.log k = -(a - (Real.log m - Real.log k)) := by ring
  rw [he]
  simp only [correlation, Complex.conj_ofReal]
  ring

theorem primeTerm_entry {σ : ℝ} (hσ : 1 / 2 < σ) (φ : L2) (n k m : ℕ) :
    inner ℂ (lp.single 2 k 1) (primeTerm hσ φ n (lp.single 2 m 1)) =
      -((amplitude σ k : ℂ) * (amplitude σ m : ℂ)) *
        kernelTerm (correlation φ) (Real.log m - Real.log k) n := by
  rw [primeTerm, smul_apply, add_apply,
    inner_smul_right, inner_add_right, compression_adjoint,
    compression_entry, compression_entry]
  unfold kernelTerm
  ring

theorem primeOperator_entry {σ r : ℝ} (hσ : 1 < σ) (φ : L2)
    (hφ : ∀ᵐ x : ℝ, r < |x| → φ x = 0) (k m : ℕ) :
    inner ℂ (lp.single 2 k 1)
      (primeOperator (by linarith : 1 / 2 < σ) φ (lp.single 2 m 1)) =
      ((amplitude σ k : ℂ) * (amplitude σ m : ℂ)) *
        primeKernel (correlation φ) (Real.log m - Real.log k) := by
  let x : Coeff ℕ := lp.single 2 m 1
  let ev : (Coeff ℕ →L[ℂ] Coeff ℕ) →L[ℂ] Coeff ℕ :=
    ({ toFun := fun T => T x
       map_add' := by intros; rfl
       map_smul' := by intros; rfl } :
      (Coeff ℕ →L[ℂ] Coeff ℕ) →ₗ[ℂ] Coeff ℕ).mkContinuous ‖x‖ (by
        intro T
        change ‖T x‖ ≤ ‖x‖ * ‖T‖
        simpa only [mul_comm] using T.le_opNorm x)
  let e : (Coeff ℕ →L[ℂ] Coeff ℕ) →L[ℂ] ℂ :=
    (innerSL ℂ (lp.single 2 k 1 : Coeff ℕ)).comp ev
  have hp := e.hasSum (primeOperator_hasSum hσ φ hφ)
  have he : (fun n => e (primeTerm (by linarith : 1 / 2 < σ) φ n)) =
      (fun n => -((amplitude σ k : ℂ) * (amplitude σ m : ℂ)) *
        kernelTerm (correlation φ) (Real.log m - Real.log k) n) := by
    funext n
    exact primeTerm_entry _ φ n k m
  rw [he] at hp
  have hc := kernelTerm_summable (correlation_support φ hφ)
    (le_refl |Real.log m - Real.log k|)
  have ht := hc.hasSum.mul_left (-((amplitude σ k : ℂ) * (amplitude σ m : ℂ)))
  have hh := hp.unique ht
  change inner ℂ (lp.single 2 k 1)
    (primeOperator (by linarith : 1 / 2 < σ) φ (lp.single 2 m 1)) =
      -((amplitude σ k : ℂ) * (amplitude σ m : ℂ)) *
        (∑' n, kernelTerm (correlation φ) (Real.log m - Real.log k) n) at hh
  simpa only [primeKernel, neg_mul, mul_neg] using hh


theorem primeTerm_adjoint {σ : ℝ} (hσ : 1 / 2 < σ) (φ : L2) (n : ℕ) :
    (primeTerm hσ φ n).adjoint = primeTerm hσ φ n := by
  simp only [primeTerm, map_smulₛₗ, map_add,
    ContinuousLinearMap.adjoint_adjoint, map_neg, Complex.conj_ofReal]
  rw [add_comm]

theorem primeOperator_adjoint {σ r : ℝ} (hσ : 1 < σ) (φ : L2)
    (hφ : ∀ᵐ x : ℝ, r < |x| → φ x = 0) :
    (primeOperator (by linarith : 1 / 2 < σ) φ).adjoint =
      primeOperator (by linarith : 1 / 2 < σ) φ := by
  have hs := primeOperator_hasSum hσ φ hφ
  have ha := hs.map ContinuousLinearMap.adjoint ContinuousLinearMap.adjoint.continuous
  simp only [Function.comp_def, primeTerm_adjoint] at ha
  exact ha.unique hs

def finiteVector (s : Finset ℕ) (c : ℕ → ℂ) : Coeff ℕ :=
  ∑ m ∈ s, c m • lp.single 2 m 1

theorem primeOperator_finite_form {σ r : ℝ} (hσ : 1 < σ) (φ : L2)
    (hφ : ∀ᵐ x : ℝ, r < |x| → φ x = 0)
    (s t : Finset ℕ) (c d : ℕ → ℂ) :
    inner ℂ (finiteVector s c)
      (primeOperator (by linarith : 1 / 2 < σ) φ (finiteVector t d)) =
      ∑ k ∈ s, ∑ m ∈ t, (starRingEnd ℂ) (c k) * d m *
        ((amplitude σ k : ℂ) * (amplitude σ m : ℂ)) *
          primeKernel (correlation φ) (Real.log m - Real.log k) := by
  simp only [finiteVector, map_sum, map_smul, sum_inner, inner_sum,
    inner_smul_left, inner_smul_right, primeOperator_entry hσ φ hφ]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k hk
  apply Finset.sum_congr rfl
  intro m hm
  ring

end RiemannResearch.RH.WeilDampedSynthesis
