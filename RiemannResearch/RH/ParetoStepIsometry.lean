import RiemannResearch.RH.ParetoDilation
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# The actual Pareto step embedding preserves square energy

The step function on the positive real half-line sends `f` to `f ⌊x⌋₊`.
The measure density `x⁻²` gives exactly the discrete Pareto masses. The
identity below includes the complete half-line and assumes only summability
of the weighted square energy. No boundedness or finite-support hypothesis
is used. This supplies the continuous realization needed before a future
Mellin analysis; no Mellin-transform theorem is asserted here.
-/

namespace RiemannResearch.RH.Pareto
open MeasureTheory Set
open scoped BigOperators
noncomputable section

/-- The actual step realization of a sequence. -/
def paretoStep (f : ℕ → ℝ) (x : ℝ) : ℝ := f ⌊x⌋₊

/-- Its square energy density for the Pareto measure `dx/x²`. -/
def paretoStepEnergy (f : ℕ → ℝ) (x : ℝ) : ℝ := paretoStep f x ^ 2 / x ^ 2

private def positiveStepCell (n : ℕ) : Set ℝ := Ico ((n : ℝ) + 1) ((n : ℝ) + 2)

private theorem positiveStepCell_floor (n : ℕ) {x : ℝ}
    (hx : x ∈ positiveStepCell n) : ⌊x⌋₊ = n + 1 := by
  apply Nat.floor_eq_on_Ico
  simpa only [positiveStepCell, Nat.cast_add, Nat.cast_one, add_assoc, one_add_one_eq_two]
    using hx

private theorem positiveStepCell_disjoint :
    Pairwise (Function.onFun Disjoint positiveStepCell) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  intro x hxi hxj
  have h := (positiveStepCell_floor i hxi).symm.trans (positiveStepCell_floor j hxj)
  exact hij (Nat.add_right_cancel h)

private theorem positiveStepCell_union : (⋃ n, positiveStepCell n) = Ici (1 : ℝ) := by
  ext x
  constructor
  · intro hx
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hx
    change (n : ℝ) + 1 ≤ x ∧ x < (n : ℝ) + 2 at hn
    have hn0 : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    exact le_trans (by linarith : (1 : ℝ) ≤ (n : ℝ) + 1) hn.1
  · intro hx
    have hx0 : 0 ≤ x := le_trans zero_le_one hx
    have hf : 1 ≤ ⌊x⌋₊ := (Nat.le_floor_iff hx0).2 (by simpa using hx)
    let n := ⌊x⌋₊ - 1
    have hn : n + 1 = ⌊x⌋₊ := Nat.sub_add_cancel hf
    apply Set.mem_iUnion.mpr
    refine ⟨n, ?_⟩
    have hlo := Nat.floor_le hx0
    have hhi := Nat.lt_floor_add_one x
    rw [← hn] at hlo hhi
    simpa only [positiveStepCell, Set.mem_Ico, Nat.cast_add, Nat.cast_one,
      add_assoc, one_add_one_eq_two] using And.intro hlo hhi

private theorem integral_inv_sq_positiveStepCell (n : ℕ) :
    (∫ x in positiveStepCell n, 1 / x ^ 2) = positiveWeight (n + 1) := by
  have hab : (n : ℝ) + 1 ≤ (n : ℝ) + 2 := by linarith
  have hz : (0 : ℝ) ∉ Set.uIcc ((n : ℝ) + 1) ((n : ℝ) + 2) := by
    rw [Set.uIcc_of_le hab]
    intro h
    have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith [h.1]
  have hp := integral_zpow (a := (n : ℝ) + 1) (b := (n : ℝ) + 2)
    (n := (-2 : ℤ)) (Or.inr ⟨by norm_num, hz⟩)
  have hfun : (fun x : ℝ => 1 / x ^ 2) = (fun x : ℝ => x ^ (-2 : ℤ)) := by
    funext x
    simp
  unfold positiveStepCell
  rw [integral_Ico_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab, hfun, hp]
  rw [positiveWeight_difference (n + 1) (by omega)]
  norm_num
  ring

private theorem paretoStepEnergy_integrable_cell (f : ℕ → ℝ) (n : ℕ) :
    IntegrableOn (paretoStepEnergy f) (positiveStepCell n) := by
  have hc : ContinuousOn (fun x : ℝ => f (n + 1) ^ 2 / x ^ 2)
      (Icc ((n : ℝ) + 1) ((n : ℝ) + 2)) := by
    apply continuousOn_const.div (continuousOn_id.pow 2)
    intro x hx
    apply pow_ne_zero
    change x ≠ 0
    have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
    exact ne_of_gt (by linarith [hx.1])
  have hi : IntegrableOn (fun x : ℝ => f (n + 1) ^ 2 / x ^ 2)
      (positiveStepCell n) := hc.integrableOn_Icc.mono_set Set.Ico_subset_Icc_self
  apply hi.congr
  filter_upwards [ae_restrict_mem (show MeasurableSet (positiveStepCell n) from measurableSet_Ico)]
    with x hx
  simp only [paretoStepEnergy, paretoStep, positiveStepCell_floor n hx]

private theorem paretoStepEnergy_integral_cell (f : ℕ → ℝ) (n : ℕ) :
    (∫ x in positiveStepCell n, paretoStepEnergy f x) =
      positiveWeight (n + 1) * f (n + 1) ^ 2 := by
  calc
    _ = ∫ x in positiveStepCell n, f (n + 1) ^ 2 * (1 / x ^ 2) := by
      apply setIntegral_congr_fun measurableSet_Ico
      intro x hx
      simp only [paretoStepEnergy, paretoStep, positiveStepCell_floor n hx]
      ring
    _ = _ := by
      rw [integral_const_mul, integral_inv_sq_positiveStepCell]
      ring

theorem paretoStepEnergy_nonneg (f : ℕ → ℝ) (x : ℝ) : 0 ≤ paretoStepEnergy f x :=
  div_nonneg (sq_nonneg _) (sq_nonneg _)

private theorem paretoStepEnergy_integrable_Ici (f : ℕ → ℝ)
    (hf : Summable (fun k => positiveWeight k * f k ^ 2)) :
    IntegrableOn (paretoStepEnergy f) (Ici 1) := by
  rw [← positiveStepCell_union]
  apply integrableOn_iUnion_of_summable_integral_norm (paretoStepEnergy_integrable_cell f)
  have hs : Summable (fun n => positiveWeight (n + 1) * f (n + 1) ^ 2) :=
    hf.comp_injective (fun _ _ h => Nat.add_right_cancel h)
  convert hs using 1
  funext n
  simp_rw [Real.norm_eq_abs, abs_of_nonneg (paretoStepEnergy_nonneg f _)]
  exact paretoStepEnergy_integral_cell f n

/-- Weighted square summability gives actual integrability on the full half-line. -/
theorem paretoStepEnergy_integrable (f : ℕ → ℝ)
    (hf : Summable (fun k => positiveWeight k * f k ^ 2)) :
    IntegrableOn (fun x : ℝ => f ⌊x⌋₊ ^ 2 / x ^ 2) (Ioi 1) :=
  (paretoStepEnergy_integrable_Ici f hf).mono_set Set.Ioi_subset_Ici_self

/-- The exact infinite step-embedding identity for every finite-energy sequence. -/
theorem paretoStep_energy_identity (f : ℕ → ℝ)
    (hf : Summable (fun k => positiveWeight k * f k ^ 2)) :
    (∫ x : ℝ in Ioi 1, f ⌊x⌋₊ ^ 2 / x ^ 2) =
      ∑' k, positiveWeight k * f k ^ 2 := by
  change (∫ x in Ioi 1, paretoStepEnergy f x) = _
  rw [← integral_Ici_eq_integral_Ioi, ← positiveStepCell_union]
  rw [integral_iUnion (s := positiveStepCell)
    (fun _ => measurableSet_Ico) positiveStepCell_disjoint
    (by simpa only [positiveStepCell_union] using paretoStepEnergy_integrable_Ici f hf)]
  simp_rw [paretoStepEnergy_integral_cell]
  rw [hf.tsum_eq_zero_add]
  simp [positiveWeight]

end
end RiemannResearch.RH.Pareto
