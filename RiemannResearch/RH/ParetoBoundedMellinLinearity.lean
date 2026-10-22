import RiemannResearch.RH.ParetoMellinHolomorphic
import Mathlib.Tactic.LinearCombination

/-!
# Linearity of bounded Pareto Mellin integrals in the positive half-plane

Source: the bounded-sequence Mellin argument used in the user-requested
Mellin DPP construction, September 20, 2026. These ordinary convergent
integrals include the critical line and do not use an RH hypothesis.
-/

noncomputable section
open MeasureTheory Set
open scoped BigOperators

namespace RiemannResearch.RH.Pareto

theorem paretoMellin_step_integrable_of_bounded (f : ThresholdHilbert) {C : ℝ}
    (hC : ∀ k, |hilbertSequence f k| ≤ C) (s : ℂ) (hs : 0 < s.re) :
    IntegrableOn (fun x : ℝ => (hilbertSequence f ⌊x⌋₊ : ℂ) *
      (x : ℂ) ^ (-s - 1)) (Ioi 1) := by
  have hi : IntegrableOn (fun x : ℝ => x ^ (-s.re - 1)) (Ioi 1) :=
    integrableOn_Ioi_rpow_of_lt (by linarith) (by norm_num)
  have hm : Measurable (fun x : ℝ => (hilbertSequence f ⌊x⌋₊ : ℂ) *
      (x : ℂ) ^ (-s - 1)) :=
    (Complex.measurable_ofReal.comp
      ((measurable_of_countable (hilbertSequence f)).comp Nat.measurable_floor)).mul
      (Complex.continuous_ofReal.measurable.pow_const _)
  apply (hi.const_mul C).mono' hm.aestronglyMeasurable
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
  have hx0 : 0 < x := zero_lt_one.trans hx
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    Complex.norm_cpow_eq_rpow_re_of_pos hx0]
  simp only [Complex.sub_re, Complex.neg_re, Complex.one_re]
  exact mul_le_mul_of_nonneg_right (hC _) (Real.rpow_nonneg hx0.le _)

theorem paretoMellin_add_of_bounded (f g : ThresholdHilbert) {Cf Cg : ℝ}
    (hf : ∀ k, |hilbertSequence f k| ≤ Cf)
    (hg : ∀ k, |hilbertSequence g k| ≤ Cg) (s : ℂ) (hs : 0 < s.re) :
    paretoMellin (f + g) s = paretoMellin f s + paretoMellin g s := by
  simp only [paretoMellin_eq_step_integral]
  have he : (fun x : ℝ => (hilbertSequence (f + g) ⌊x⌋₊ : ℂ) *
      (x : ℂ) ^ (-s - 1)) = fun x : ℝ =>
        (hilbertSequence f ⌊x⌋₊ : ℂ) * (x : ℂ) ^ (-s - 1) +
        (hilbertSequence g ⌊x⌋₊ : ℂ) * (x : ℂ) ^ (-s - 1) := by
    funext x
    have h := congrFun (hilbertSequenceLinear.map_add f g) ⌊x⌋₊
    change hilbertSequence (f + g) _ = hilbertSequence f _ + hilbertSequence g _ at h
    rw [h, Complex.ofReal_add, add_mul]
  rw [he]
  exact integral_add (paretoMellin_step_integrable_of_bounded f hf s hs)
    (paretoMellin_step_integrable_of_bounded g hg s hs)

theorem paretoMellin_fintype_sum_of_bounded {ι : Type*} [Fintype ι]
    (v : ι → ThresholdHilbert) (hv : ∀ i, ∃ C : ℝ, ∀ k, |hilbertSequence (v i) k| ≤ C)
    (s : ℂ) (hs : 0 < s.re) :
    paretoMellin (∑ i, v i) s = ∑ i, paretoMellin (v i) s := by
  classical
  simp only [paretoMellin_eq_step_integral]
  have he : (fun x : ℝ => (hilbertSequence (∑ i, v i) ⌊x⌋₊ : ℂ) *
      (x : ℂ) ^ (-s - 1)) = fun x : ℝ =>
      ∑ i, (hilbertSequence (v i) ⌊x⌋₊ : ℂ) * (x : ℂ) ^ (-s - 1) := by
    funext x
    have h := congrFun (map_sum hilbertSequenceLinear v Finset.univ) ⌊x⌋₊
    change hilbertSequence (∑ i, v i) _ = (∑ i, hilbertSequence (v i)) _ at h
    rw [h]
    simp only [Finset.sum_apply, Complex.ofReal_sum, Finset.sum_mul]
  rw [he]
  exact integral_finsetSum _ fun i _ => by
    obtain ⟨C, hC⟩ := hv i
    exact paretoMellin_step_integrable_of_bounded (v i) hC s hs

end RiemannResearch.RH.Pareto
