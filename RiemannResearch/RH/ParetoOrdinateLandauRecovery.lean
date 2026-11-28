import RiemannResearch.RH.ParetoOrdinatePairError
import RiemannResearch.RH.ParetoHilbertPhysical
import RiemannResearch.RH.ParetoWeights
import RiemannResearch.Analysis.ActualZeroSelbergDensity
import RiemannResearch.Analysis.ActualZeroCountAsymptotics
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Selberg slope two and the complete Pareto error of the Landau traces

The height-dependent cutoff is on the positive integer coordinates of the
comparison vector. Both the Landau and ordinate traces retain all actual
positive-height zero occurrences. The fourth logarithmic Pareto moment
bounds the full sum of the squared coordinate errors. The omitted Pareto
mass beyond integer K is exactly 1/(K+1).
-/

noncomputable section
open Set Filter Zeta23
open scoped Topology BigOperators
namespace RiemannResearch.RH.Pareto.OrdinateCosine
open CoefficientStabilization RiemannResearch.Analysis.ActualZeroOrdinate

/-- The centered Landau trace on the first K physical integers. -/
def landauHead (T : ℝ) (K : ℕ) : ThresholdHilbert :=
  sequenceHilbert
    (fun k : ℕ => if k ≤ K then (landauSum T (Real.log k) / (Ncount 0 T : ℂ)).re else 0)
    (by
      apply summable_of_ne_finset_zero (s := Finset.range (K + 1))
      intro k hk
      have h : ¬ k ≤ K := by simpa only [Finset.mem_range, Nat.lt_succ_iff] using hk
      simp [h])

theorem landauHead_physical (T : ℝ) (K i : ℕ) :
    hilbertGibbsPhysical (landauHead T K) i =
      if i < K then (landauSum T (Real.log ((i+1 : ℕ) : ℝ)) / (Ncount 0 T : ℂ)).re else 0 := by
  change (Real.sqrt (paretoWeight i) * (if i+1 ≤ K then _ else _)) /
    Real.sqrt (paretoWeight i) = _
  by_cases hi : i < K
  · have hk := Nat.succ_le_of_lt hi
    simp only [if_pos hi, if_pos hk]
    field_simp [(Real.sqrt_pos.mpr (paretoWeight_pos i)).ne']
  · have hk : ¬ i + 1 ≤ K := by omega
    simp [hi, hk]

private def fourthLogPrimitive (x : ℝ) : ℝ :=
  ((Real.log x)^4 + 4*(Real.log x)^3 + 12*(Real.log x)^2 + 24*Real.log x + 24) / x

private theorem fourthLogPrimitive_deriv {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt fourthLogPrimitive (-((Real.log x)^4) / x^2) x := by
  have h := Real.hasDerivAt_log hx
  have hp := ((((h.pow 4).add ((h.pow 3).const_mul 4)).add ((h.pow 2).const_mul 12)).add
    (h.const_mul 24)).add_const 24
  convert hp.div (hasDerivAt_id x) hx using 1 <;>
    first | rfl | (dsimp [fourthLogPrimitive]; field_simp [hx]; ring)

private theorem fourthLog_cell_le (i : ℕ) :
    paretoWeight i * (Real.log ((i : ℝ) + 1))^4 ≤
      fourthLogPrimitive ((i : ℝ)+1) - fourthLogPrimitive (((i : ℝ)+1)+1) := by
  let a : ℝ := (i : ℝ) + 1
  have ha : 1 ≤ a := by
    dsimp [a]
    linarith [Nat.cast_nonneg (α := ℝ) i]
  let g (x : ℝ) := fourthLogPrimitive x - (Real.log a)^4 / x
  have hd (x : ℝ) (hx : a ≤ x) : HasDerivAt g
      (((Real.log a)^4 - (Real.log x)^4) / x^2) x := by
    have hx' : x ≠ 0 := by linarith
    have h := (fourthLogPrimitive_deriv hx').sub
      ((hasDerivAt_const x ((Real.log a)^4)).div (hasDerivAt_id x) hx')
    convert h using 1 <;> first | rfl | (dsimp [g]; field_simp [hx']; ring)
  have hg : AntitoneOn g (Ici a) := by
    apply antitoneOn_of_deriv_nonpos (convex_Ici a)
    · intro x hx
      exact (hd x hx).continuousAt.continuousWithinAt
    · intro x hx
      exact (hd x (interior_subset hx)).differentiableAt.differentiableWithinAt
    · intro x hx
      have hx' : a ≤ x := interior_subset hx
      rw [(hd x hx').deriv]
      apply div_nonpos_of_nonpos_of_nonneg _ (sq_nonneg _)
      exact sub_nonpos.mpr (pow_le_pow_left₀ (Real.log_nonneg ha)
        (Real.log_le_log (zero_lt_one.trans_le ha) hx') 4)
  have hstep := hg (le_refl a) (show a ≤ a+1 by linarith) (show a ≤ a+1 by linarith)
  change fourthLogPrimitive (a+1) - (Real.log a)^4 / (a+1) ≤
    fourthLogPrimitive a - (Real.log a)^4 / a at hstep
  have hw : paretoWeight i = 1/a - 1/(a+1) := by
    rw [paretoWeight_eq_inv_sub]
    dsimp [a]
    ring
  change paretoWeight i * (Real.log a)^4 ≤ fourthLogPrimitive a - fourthLogPrimitive (a+1)
  rw [hw]
  calc
    _ = (Real.log a)^4/a - (Real.log a)^4/(a+1) := by ring
    _ ≤ _ := by linarith only [hstep]

/-- The finite sums of the fourth logarithmic moment are bounded by 4!. -/
theorem pareto_fourth_log_head_le (K : ℕ) :
    (∑ i ∈ Finset.range K, paretoWeight i * (Real.log ((i+1 : ℕ) : ℝ))^4) ≤ 24 := by
  have hs (k : ℕ) : (∑ i ∈ Finset.range k, paretoWeight i * (Real.log ((i : ℝ)+1))^4) ≤
      fourthLogPrimitive 1 - fourthLogPrimitive ((k : ℝ)+1) := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [Finset.sum_range_succ, Nat.cast_succ]
      linarith only [ih, fourthLog_cell_le k]
  have hp : 0 ≤ fourthLogPrimitive ((K : ℝ)+1) := by
    have hL : 0 ≤ Real.log ((K : ℝ)+1) := Real.log_nonneg (by linarith [Nat.cast_nonneg (α:=ℝ) K])
    unfold fourthLogPrimitive
    positivity
  have he : fourthLogPrimitive 1 = 24 := by norm_num [fourthLogPrimitive]
  have hh := hs K
  rw [he] at hh
  simpa only [Nat.cast_add, Nat.cast_one] using (hh.trans (sub_le_self _ hp))

/-- A global squared-norm comparison under the pointwise slope-two density
hypothesis at height T, valid for every integer head through that height. -/
theorem landauHead_distance_sq_le_of_selberg_two {T C : ℝ} (hT : 1 < T)
    (hN : 0 < Ncount 0 T) (hC : 0 ≤ C) (hD : SelbergDensityBound T C 2)
    (K : ℕ) (hK : (K : ℝ) ≤ T) :
    ‖recovery T 0 - landauHead T K‖ ^ 2 ≤
      24 * ((T / (Ncount 0 T : ℝ)) * (2 * C / (3 * Real.log T)))^2 + 1 / ((K : ℝ)+1) := by
  let a := (T / (Ncount 0 T : ℝ)) * (2 * C / (3 * Real.log T))
  let v := recovery T 0 - landauHead T K
  let g (i : ℕ) := paretoWeight i * (hilbertGibbsPhysical v i)^2
  have hs : Summable g := hilbertGibbsPhysical_square_summable v
  have hdiff (i : ℕ) : hilbertGibbsPhysical v i =
      hilbertGibbsPhysical (recovery T 0) i - hilbertGibbsPhysical (landauHead T K) i := by
    change (recovery T 0 i - landauHead T K i) / Real.sqrt (paretoWeight i) = _ - _
    exact sub_div _ _ _
  have hcoord (i : ℕ) (hi : i < K) : g i ≤ a^2 * (paretoWeight i *
      (Real.log ((i+1 : ℕ) : ℝ))^4) := by
    have hsite : ((i+1 : ℕ) : ℝ) ≤ T := (show ((i+1 : ℕ) : ℝ) ≤ (K : ℝ) by
      exact_mod_cast Nat.succ_le_of_lt hi).trans hK
    have hb : |hilbertGibbsPhysical v i| ≤ a * (Real.log ((i+1 : ℕ) : ℝ))^2 := by
      rw [hdiff, landauHead_physical, if_pos hi]
      exact (first_recovery_landau_error_of_selberg_two hT hN hC hD i hsite).trans_eq
        (by dsimp [a]; ring)
    have hsq := pow_le_pow_left₀ (abs_nonneg _) hb 2
    rw [sq_abs] at hsq
    exact (mul_le_mul_of_nonneg_left hsq (paretoWeight_pos i).le).trans_eq (by ring)
  have hh : (∑ i ∈ Finset.range K, g i) ≤ 24 * a^2 := by
    calc
      _ ≤ ∑ i ∈ Finset.range K, a^2 * (paretoWeight i * (Real.log ((i+1 : ℕ) : ℝ))^4) :=
        Finset.sum_le_sum (fun i hi => hcoord i (Finset.mem_range.mp hi))
      _ ≤ _ := by
        rw [← Finset.mul_sum, mul_comm 24]
        exact mul_le_mul_of_nonneg_left (pareto_fourth_log_head_le K) (sq_nonneg a)
  have ht (n : ℕ) : g (n+K) ≤ paretoWeight (n+K) := by
    have hb := first_recovery_physical_abs_le_one T (n+K)
    have hsq := pow_le_pow_left₀ (abs_nonneg _) hb 2
    rw [sq_abs, one_pow] at hsq
    have hn : ¬ n+K < K := by omega
    dsimp [g]
    rw [hdiff, landauHead_physical, if_neg hn, sub_zero]
    exact mul_le_of_le_one_right (paretoWeight_pos _).le hsq
  have hw := paretoWeight_hasSum.summable.sum_add_tsum_nat_add K
  rw [paretoWeight_tsum, paretoWeight_partial_sum] at hw
  have htail := ((summable_nat_add_iff K).mpr hs).tsum_le_tsum ht
    ((summable_nat_add_iff K).mpr paretoWeight_hasSum.summable)
  have he : ‖v‖^2 = ∑' i, g i := by
    rw [hilbert_norm_sq]
    exact tsum_congr (fun i => (hilbertGibbsPhysical_square v i).symm)
  change ‖v‖^2 ≤ 24*a^2 + _
  rw [he, ← hs.sum_add_tsum_nat_add K]
  linarith only [hh, htail, hw]

/-- On the head floor T the centered Landau traces have the same squared legal
projection error limit. The uniform slope-two bound is an explicit premise. -/
theorem landauHead_squaredError_tendsto_of_selberg_two (hD : UniformSelbergDensity 2) :
    Tendsto (fun T : ℝ => ‖closedSpaceᗮ.starProjection (landauHead T ⌊T⌋₊)‖^2)
      atTop (𝓝 ((1 - IntegerDPP.limitingKernel 0 0)/2)) := by
  obtain ⟨C,T₀,hC,ht₀,hD⟩ := hD
  have hl := (tendsto_inv_atTop_zero.comp Real.tendsto_log_atTop).const_mul (2*C/3)
  have ha : Tendsto (fun T : ℝ => (T / (Ncount 0 T : ℝ)) * (2*C / (3*Real.log T)))
      atTop (𝓝 0) := by
    have h := tendsto_height_div_count.mul hl
    simp only [mul_zero] at h
    apply h.congr
    intro T
    dsimp
    ring
  have hi : Tendsto (fun T : ℝ => T⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
  have hu := ((ha.pow 2).const_mul 24).add hi
  have hsq : Tendsto (fun T : ℝ => ‖recovery T 0 - landauHead T ⌊T⌋₊‖^2) atTop (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall (fun _ => sq_nonneg _)) _ (by simpa using hu)
    filter_upwards [eventually_ge_atTop T₀, eventually_count_pos] with T hT hN
    have ht := ht₀.trans_le hT
    have hp := landauHead_distance_sq_le_of_selberg_two ht hN hC (hD T hT) ⌊T⌋₊
      (Nat.floor_le (zero_lt_one.trans ht).le)
    apply hp.trans
    apply add_le_add le_rfl
    change 1 / ((⌊T⌋₊ : ℝ) + 1) ≤ T⁻¹
    simpa only [one_div] using
      one_div_le_one_div_of_le (zero_lt_one.trans ht) (Nat.lt_floor_add_one T).le
  have hn : Tendsto (fun T : ℝ => ‖recovery T 0 - landauHead T ⌊T⌋₊‖) atTop (𝓝 0) := by
    simpa only [Function.comp_def, Real.sqrt_sq_eq_abs, abs_norm, Real.sqrt_zero] using
      Real.continuous_sqrt.continuousAt.tendsto.comp hsq
  have hv := first_recovery_tendsto.sub (tendsto_zero_iff_norm_tendsto_zero.mpr hn)
  have hv' : Tendsto (fun T : ℝ => landauHead T ⌊T⌋₊) atTop (𝓝 (paretoPointHilbert 0)) := by
    simpa only [sub_sub_cancel, sub_zero] using hv
  have h := (closedSpaceᗮ.starProjection.continuous.continuousAt.tendsto.comp hv').norm.pow 2
  simpa only [Function.comp_def, first_site_residual_sq] using h

/-- Under slope two and the actual-ordinate sine second moment, the centered
Landau error and the contribution from pairs outside each fixed unfolded
window agree in the limit. -/
theorem landauHead_squaredError_sub_far_tendsto (hD : UniformSelbergDensity 2)
    (hS : RiemannResearch.Analysis.MontgomeryPositiveGap.SineWindowMoment)
    {q : ℝ} (hq : 0 < q) :
    Tendsto (fun T : ℝ => ‖closedSpaceᗮ.starProjection (landauHead T ⌊T⌋₊)‖ ^ 2 - farError T q)
      atTop (𝓝 0) := by
  simpa only [sub_self] using
    (landauHead_squaredError_tendsto_of_selberg_two hD).sub (farError_tendsto_of_sine hS hq)

/--
info: 'RiemannResearch.RH.Pareto.OrdinateCosine.rh_iff_farError_tendsto_zero_of_sine' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms rh_iff_farError_tendsto_zero_of_sine

/--
info: 'RiemannResearch.RH.Pareto.OrdinateCosine.landauHead_squaredError_sub_far_tendsto' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms landauHead_squaredError_sub_far_tendsto

end RiemannResearch.RH.Pareto.OrdinateCosine
