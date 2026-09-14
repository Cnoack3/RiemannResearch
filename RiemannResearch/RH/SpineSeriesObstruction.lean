import RiemannResearch.RH.ThresholdHilbertDilation
import RiemannResearch.RH.DilationWaveletAlgebra
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.InfiniteSum.NatInt

/-!
# The forced spine coefficients cannot define an ordinary convergent series

Source: RH_Minimal_Seeds_Canonical_Basis_and_Arithmetic_Charge_20260914.md,
Section 4, equation (4.6). This proves the genuine norm obstruction for the
actual weighted Hilbert dilations, including every enumeration of a dictionary
whose spine terms have the prescribed values. It does not replace changing
finite coefficient arrays by a series with fixed coefficients.
-/

namespace RiemannResearch.Analysis
open Filter

/-- An injective natural sequence eventually leaves every finite initial segment. -/
theorem injectiveNat_tendsto_atTop (j : ℕ → ℕ) (hj : Function.Injective j) :
    Tendsto j atTop atTop := by
  classical
  apply tendsto_atTop.2
  intro b
  let B := (Finset.range b).sup (Function.invFun j)
  apply eventually_atTop.2
  refine ⟨B+1, ?_⟩
  intro n hn
  by_contra h
  have he : j n ∈ Finset.range b := Finset.mem_range.mpr (by omega)
  have hb : Function.invFun j (j n) ≤ B := Finset.le_sup he
  have hi : Function.invFun j (j n) = n := Function.leftInverse_invFun hj n
  rw [hi] at hb
  omega

end RiemannResearch.Analysis

namespace RiemannResearch.RH.Pareto
open Filter
open scoped Topology BigOperators
noncomputable section

def sixSpineTerm (f : ThresholdHilbert) (k : ℕ) : ThresholdHilbert :=
  (1/3 : ℝ) • hilbertDilation (6^(k+1)) (pow_pos (by norm_num) _) f

theorem sixSpineTerm_norm_sq (f : ThresholdHilbert) (k : ℕ) :
    ‖sixSpineTerm f k‖^2 = (6 : ℝ)^(k+1) * ‖f‖^2 / 9 := by
  rw [sixSpineTerm, norm_smul, mul_pow, hilbertDilation_norm_sq]
  norm_num [Nat.cast_pow]
  ring

theorem sixSpineTerm_not_tendsto_zero (f : ThresholdHilbert) (hf : f ≠ 0) :
    ¬ Tendsto (sixSpineTerm f) atTop (𝓝 0) := by
  intro ht
  have hs : 0 < ‖f‖^2 := sq_pos_of_pos (norm_pos_iff.mpr hf)
  have hzero : Tendsto (fun k => ‖sixSpineTerm f k‖^2) atTop (𝓝 0) := by
    simpa using ht.norm.pow 2
  have hp : Tendsto (fun k : ℕ => (6 : ℝ)^(k+1)) atTop atTop :=
    (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1 : ℝ) < 6)).comp
      (tendsto_add_atTop_nat 1)
  have hlo := (tendsto_atTop.1 hp) (9 / ‖f‖^2 + 1)
  have hhi := (tendsto_order.1 hzero).2 1 (by norm_num)
  obtain ⟨k, hklo, hkhi⟩ := (hlo.and hhi).exists
  rw [sixSpineTerm_norm_sq] at hkhi
  have hcancel : (9 / ‖f‖^2) * ‖f‖^2 = 9 := div_mul_cancel₀ _ hs.ne'
  have hmul := mul_le_mul_of_nonneg_right hklo hs.le
  nlinarith

/-- The same obstruction for any countable dictionary, without constructing
or privileging an ordering of its index type. -/
theorem indexedSpineDictionary_not_tendsto_zero_in_any_order {ι : Type*}
    (v : ι → ThresholdHilbert) (spine : ℕ → ι) (hspine_inj : Function.Injective spine)
    (f : ThresholdHilbert) (hf : f ≠ 0)
    (hspine : ∀ k, v (spine k) = sixSpineTerm f k) (e : ℕ ≃ ι) :
    ¬ Tendsto (fun n => v (e n)) atTop (𝓝 0) := by
  intro h
  have hj : Function.Injective (fun k => e.symm (spine k)) :=
    e.symm.injective.comp hspine_inj
  have ht := h.comp (Analysis.injectiveNat_tendsto_atTop _ hj)
  apply sixSpineTerm_not_tendsto_zero f hf
  simpa only [Function.comp_def, Equiv.apply_symm_apply, hspine] using ht

theorem indexedSpineDictionary_no_series_in_any_order {ι : Type*}
    (v : ι → ThresholdHilbert) (spine : ℕ → ι) (hspine_inj : Function.Injective spine)
    (f : ThresholdHilbert) (hf : f ≠ 0)
    (hspine : ∀ k, v (spine k) = sixSpineTerm f k)
    (e : ℕ ≃ ι) (limit : ThresholdHilbert) :
    ¬ Tendsto (fun N => ∑ n ∈ Finset.range N, v (e n)) atTop (𝓝 limit) := by
  intro h
  have hz := (h.comp (tendsto_add_atTop_nat 1)).sub h
  apply indexedSpineDictionary_not_tendsto_zero_in_any_order
    v spine hspine_inj f hf hspine e
  simpa only [Function.comp_def, Finset.sum_range_succ, add_sub_cancel_left,
    sub_self] using hz

theorem dyadicResidue_nonzero : digitHilbert 2 1 (by norm_num) (by norm_num) ≠ 0 := by
  intro h
  have hc := congrArg (fun f : ThresholdHilbert => hilbertSequence f 1) h
  rw [hilbertSequence_digitHilbert] at hc
  have hz : hilbertSequence (0 : ThresholdHilbert) = 0 := hilbertSequenceLinear.map_zero
  rw [hz] at hc
  norm_num [digitSequence] at hc


end
end RiemannResearch.RH.Pareto
