import RiemannResearch.RH.ParetoWeightedApproximationRH
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# Exact cells for every Mellin weight

Source: RH_Research_Agenda_2026-09-24(1).md, Priority 2.
This module proves the complete infinite physical-cell formula for every u ≥ 1.
The cells are strictly positive for u > 0. No zero-free region or approximation
hypothesis is used in these identities. The endpoint convergence theorem only
concerns u ≥ 2; approximation for fixed 1 < u < 2 remains open.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped Topology BigOperators
namespace RiemannResearch.RH.Pareto
open WeightedMellin

/-- Physical cell [n+1,n+2), with its exact Mellin weight. -/
def weightedCellWeight (u : ℝ) (n : ℕ) : ℝ :=
  (((n : ℝ) + 1) ^ (-u) - ((n : ℝ) + 2) ^ (-u)) / u

theorem weightedCellWeight_pos {u : ℝ} (hu : 0 < u) (n : ℕ) :
    0 < weightedCellWeight u n := by
  apply div_pos _ hu
  exact sub_pos.mpr (Real.rpow_lt_rpow_of_neg (by positivity)
    (by linarith) (neg_neg_of_pos hu))

private def weightedStepCell (n : ℕ) : Set ℝ := Ico ((n : ℝ) + 1) ((n : ℝ) + 2)

private theorem weightedStepCell_floor (n : ℕ) {x : ℝ}
    (hx : x ∈ weightedStepCell n) : ⌊x⌋₊ = n + 1 := by
  apply Nat.floor_eq_on_Ico
  simpa only [weightedStepCell, Nat.cast_add, Nat.cast_one, add_assoc,
    one_add_one_eq_two] using hx

private theorem weightedStepCell_disjoint :
    Pairwise (Function.onFun Disjoint weightedStepCell) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  intro x hxi hxj
  exact hij (Nat.add_right_cancel
    ((weightedStepCell_floor i hxi).symm.trans (weightedStepCell_floor j hxj)))

private theorem weightedStepCell_union : (⋃ n, weightedStepCell n) = Ici (1 : ℝ) := by
  ext x
  constructor
  · intro hx
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hx
    change (n : ℝ) + 1 ≤ x ∧ x < (n : ℝ) + 2 at hn
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
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
    simpa only [weightedStepCell, Set.mem_Ico, Nat.cast_add, Nat.cast_one,
      add_assoc, one_add_one_eq_two] using And.intro hlo hhi

private theorem integral_weightedStepCell {u : ℝ} (hu : 0 < u) (n : ℕ) :
    (∫ x in weightedStepCell n, x ^ (-u - 1)) = weightedCellWeight u n := by
  have hab : (n : ℝ) + 1 ≤ (n : ℝ) + 2 := by linarith
  have hz : (0 : ℝ) ∉ Set.uIcc ((n : ℝ) + 1) ((n : ℝ) + 2) := by
    rw [Set.uIcc_of_le hab]
    intro h
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith [h.1]
  have hp := integral_rpow (a := (n : ℝ) + 1) (b := (n : ℝ) + 2)
    (r := -u - 1) (Or.inr ⟨by linarith, hz⟩)
  unfold weightedStepCell
  rw [integral_Ico_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab, hp]
  rw [show -u - 1 + 1 = -u by ring]
  unfold weightedCellWeight
  ring

/-- The cell weight is the actual integral, with no tail cutoff. -/
theorem weightedCellWeight_eq_integral {u : ℝ} (hu : 0 < u) (n : ℕ) :
    weightedCellWeight u n =
      ∫ x in Ico ((n : ℝ) + 1) ((n : ℝ) + 2), x ^ (-u - 1) :=
  (integral_weightedStepCell hu n).symm

@[simp] theorem weightedCellWeight_one (n : ℕ) :
    weightedCellWeight 1 n = paretoWeight n := by
  unfold weightedCellWeight paretoWeight
  norm_num [Real.rpow_neg_one]
  field_simp
  ring

/-- Heavier weights are dominated cellwise by the original Pareto weight. -/
theorem weightedCellWeight_le_pareto {u : ℝ} (hu : 1 ≤ u) (n : ℕ) :
    weightedCellWeight u n ≤ paretoWeight n := by
  rw [← weightedCellWeight_one n, weightedCellWeight_eq_integral (by linarith : 0 < u),
    weightedCellWeight_eq_integral (by norm_num : (0 : ℝ) < 1)]
  have hsub : Ico ((n : ℝ) + 1) ((n : ℝ) + 2) ⊆ Ioi (1 / 2 : ℝ) := by
    intro x hx
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    change 1 / 2 < x
    linarith [hx.1]
  apply integral_mono_ae
    ((integrableOn_Ioi_rpow_of_lt (by linarith : -u - 1 < -1)
      (by norm_num : (0 : ℝ) < 1 / 2)).mono_set hsub)
    ((integrableOn_Ioi_rpow_of_lt (by norm_num : -(1 : ℝ) - 1 < -1)
      (by norm_num : (0 : ℝ) < 1 / 2)).mono_set hsub)
  filter_upwards [ae_restrict_mem measurableSet_Ico] with x hx
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  exact Real.rpow_le_rpow_of_exponent_le (by linarith [hx.1]) (by linarith)

private theorem integral_weighted_density_cell (f : ThresholdHilbert)
    {u : ℝ} (hu : 0 < u) (n : ℕ) :
    (∫ x in weightedStepCell n, ‖complexPhysicalStep f x‖ ^ 2 * x ^ (-u - 1)) =
      weightedCellWeight u n * hilbertSequence f (n + 1) ^ 2 := by
  calc
    _ = ∫ x in weightedStepCell n, hilbertSequence f (n + 1) ^ 2 * x ^ (-u - 1) := by
      apply setIntegral_congr_fun measurableSet_Ico
      intro x hx
      simp only [complexPhysicalStep, weightedStepCell_floor n hx,
        Complex.norm_real, Real.norm_eq_abs, sq_abs]
    _ = _ := by
      rw [integral_const_mul, integral_weightedStepCell hu]
      ring

/-- Exact complete energy at every weight, retaining all infinite physical cells. -/
theorem complexPhysicalStep_weighted_energy (f : ThresholdHilbert)
    {u : ℝ} (hu : 1 ≤ u) :
    energy (complexPhysicalStep f) u =
      ∑' n, weightedCellWeight u n * hilbertSequence f (n + 1) ^ 2 := by
  have hi := (finiteEnergy_mono (complexPhysicalStep_finiteEnergy f) hu).2
  have hi' : IntegrableOn
      (fun x : ℝ => ‖complexPhysicalStep f x‖ ^ 2 * x ^ (-u - 1))
      (⋃ n, weightedStepCell n) := by
    rw [weightedStepCell_union, integrableOn_Ici_iff_integrableOn_Ioi]
    exact hi
  unfold energy
  rw [← integral_Ici_eq_integral_Ioi, ← weightedStepCell_union,
    integral_iUnion (s := weightedStepCell) (fun _ => measurableSet_Ico)
      weightedStepCell_disjoint hi']
  simp_rw [integral_weighted_density_cell f (by linarith : 0 < u)]

/-- The critical weighted energy is the original full Pareto norm. -/
theorem complexPhysicalStep_critical_energy (f : ThresholdHilbert) :
    energy (complexPhysicalStep f) 1 = ‖f‖ ^ 2 := by
  calc
    _ = ∫ x in Ioi (1 : ℝ), hilbertSequence f ⌊x⌋₊ ^ 2 / x ^ 2 := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x hx
      have hx0 : 0 < x := lt_trans zero_lt_one hx
      have hp : x ^ (-(1 : ℝ) - 1) = 1 / x ^ 2 := by
        norm_num [Real.rpow_neg hx0.le]
      simp only [complexPhysicalStep, Complex.norm_real, Real.norm_eq_abs, sq_abs, hp]
      ring
    _ = _ := by
      rw [paretoStep_energy_identity _ (hilbertSequence_square_summable f),
        ← hilbert_norm_weighted_sq]

/-- The weighted norm of the actual target is exactly 1/u. -/
theorem complexPhysicalStep_one_energy {u : ℝ} (hu : 1 ≤ u) :
    energy (complexPhysicalStep hilbertOne) u = 1 / u := by
  calc
    _ = ∫ x in Ioi (1 : ℝ), x ^ (-u - 1) := by
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x hx
      change 1 < x at hx
      have hx0 : 0 ≤ x := le_trans zero_le_one hx.le
      have hf : 1 ≤ ⌊x⌋₊ := (Nat.le_floor_iff hx0).2 (by simpa only [Nat.cast_one] using hx.le)
      simp [complexPhysicalStep, hilbertOne_sequence, zeroAnchor, Nat.ne_of_gt hf]
    _ = _ := by
      rw [integral_Ioi_rpow_of_lt (by linarith : -u - 1 < -1)
        (by norm_num : (0 : ℝ) < 1), Real.one_rpow]
      rw [show -u - 1 + 1 = -u by ring, div_neg]
      ring

/-- Unconditional endpoint convergence persists at every heavier fixed weight. -/
theorem canonicalMobiusResidual_weighted_energy_tendsto_zero {u : ℝ} (hu : 2 ≤ u) :
    Tendsto (fun N => energy
      (complexPhysicalStep (hilbertOne - canonicalMobiusHilbert N)) u) atTop (𝓝 0) := by
  apply squeeze_zero (fun N => integral_nonneg_of_ae (by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with x hx
    change 1 < x at hx
    exact mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (by linarith [hx] : 0 ≤ x) _)))
    (fun N => energy_mono (complexPhysicalStep_endpoint_finiteEnergy _) hu)
  simpa only [complexPhysicalStep_endpoint_energy] using
    canonicalMobiusResidual_exactEndpointCellEnergy_tendsto_zero

end RiemannResearch.RH.Pareto
