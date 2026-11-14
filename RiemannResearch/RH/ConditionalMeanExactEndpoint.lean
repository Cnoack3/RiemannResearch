import RiemannResearch.RH.CRTMeanRepair
import RiemannResearch.RH.ConditionalMeanLowerGrowth
import RiemannResearch.RH.ConditionalMeanTailNonattainment
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Linarith

/-!
# Exact conditional-mean endpoints and zero period mean

Source: user-provided `RH_Random_Prime_Powers_CRT_Multi_Range_2026-09-19.tex`,
Theorem 12.2 and (1.8). The energy is the full conditional-mean square,
not the square error. The zero-mean infimum equality is unconditional.
The logarithmic witness criterion implies Mathlib RH by the existing
signed Mellin zero obstruction. No RH-to-density implication is assumed
or proved in this module.
-/
noncomputable section
open Filter
open scoped Topology
namespace RiemannResearch.RH.Pareto
open CRTBlock

/-- A positive period with zero arithmetic mean; no minimal-period choice is needed. -/
def HasZeroPeriodMean (F : ℕ → ℝ) : Prop :=
  ∃ Q : ℕ, 0 < Q ∧ (∀ n, F (n + Q) = F n) ∧ periodMean F Q = 0

/-- The manuscript's finite legal class `A_Y^0`. -/
def zeroMeanConditionalHeadClass (Y : ℕ) : Set (ℕ → ℝ) :=
  {F | F ∈ conditionalHeadClass Y ∧ HasZeroPeriodMean F}

/-- The genuine infimum, with nonemptiness and a lower bound proved below. -/
def zeroMeanConditionalHeadMinimum (Y : ℕ) : ℝ :=
  sInf (conditionalMeanSquare '' zeroMeanConditionalHeadClass Y)

theorem exists_zeroMean_conditionalHead_near (Y : ℕ) {F : ℕ → ℝ}
    (hF : F ∈ conditionalHeadClass Y) (ε : ℝ) (hε : 0 < ε) :
    ∃ G ∈ zeroMeanConditionalHeadClass Y,
      conditionalMeanSquare G < conditionalMeanSquare F + ε := by
  obtain ⟨Q, hQ, hp⟩ := legalSeedSpan_hasLegalReflectionPeriod
    (Set.Ici 1) (by intro a ha; exact ha) hF.1
  obtain ⟨G, hG, hmean, hE⟩ :=
    exists_zeroMean_head_near Y F hF Q hQ (hp Q dvd_rfl).1 ε hε
  exact ⟨G, ⟨hG, hmean⟩, hE⟩

theorem zeroMeanConditionalHeadClass_nonempty (Y : ℕ) :
    (zeroMeanConditionalHeadClass Y).Nonempty := by
  obtain ⟨F, hF⟩ := conditionalHeadClass_nonempty Y
  obtain ⟨G, hG, _⟩ := exists_zeroMean_conditionalHead_near Y hF 1 (by norm_num)
  exact ⟨G, hG⟩

theorem zeroMeanConditionalHeadEnergies_bddBelow (Y : ℕ) :
    BddBelow (conditionalMeanSquare '' zeroMeanConditionalHeadClass Y) := by
  refine ⟨0, ?_⟩
  rintro e ⟨F, hF, rfl⟩
  exact conditionalMeanSquare_nonneg F

theorem zeroMeanConditionalHeadMinimum_le (Y : ℕ) {F : ℕ → ℝ}
    (hF : F ∈ zeroMeanConditionalHeadClass Y) :
    zeroMeanConditionalHeadMinimum Y ≤ conditionalMeanSquare F :=
  csInf_le (zeroMeanConditionalHeadEnergies_bddBelow Y) ⟨F, hF, rfl⟩

/-- Zero period mean leaves every actual finite-head energy infimum unchanged. -/
theorem zeroMeanConditionalHeadMinimum_eq (Y : ℕ) :
    zeroMeanConditionalHeadMinimum Y = conditionalHeadMinimum Y := by
  apply le_antisymm
  · apply le_of_forall_pos_le_add
    intro ε hε
    obtain ⟨F, hF, hE⟩ := exists_head_energy_lt Y (ε / 2) (by positivity)
    obtain ⟨G, hG, hGE⟩ := exists_zeroMean_conditionalHead_near Y hF (ε / 2) (by positivity)
    have hmin := zeroMeanConditionalHeadMinimum_le Y hG
    linarith
  · apply le_csInf ((zeroMeanConditionalHeadClass_nonempty Y).image _)
    rintro e ⟨F, hF, rfl⟩
    exact conditionalHeadMinimum_le Y hF.1

/-- Statement (ii), with positive integer head lengths. -/
def ExactConditionalEndpoint : Prop :=
  ∀ Y : ℕ, 1 ≤ Y → conditionalHeadMinimum Y = (Y : ℝ) / ((Y : ℝ) + 2)

/-- Statement (iii). -/
def ZeroMeanExactConditionalEndpoint : Prop :=
  ∀ Y : ℕ, 1 ≤ Y → zeroMeanConditionalHeadMinimum Y = (Y : ℝ) / ((Y : ℝ) + 2)

theorem exactConditionalEndpoint_iff_zeroMean :
    ExactConditionalEndpoint ↔ ZeroMeanExactConditionalEndpoint := by
  simp only [ExactConditionalEndpoint, ZeroMeanExactConditionalEndpoint,
    zeroMeanConditionalHeadMinimum_eq]

/-- Equation (1.8), for one fixed cofinal family. -/
def ConditionalLogarithmicLimit (F : ℕ → ℕ → ℝ) (Y : ℕ → ℕ) : Prop :=
  Tendsto (fun j => Real.log (1 + conditionalMeanSquare (F j)) /
    Real.log (Y j : ℝ)) atTop (𝓝 0)

/-- Statement (iv); membership is in the algebraic span, hence witnesses are finite. -/
def LogarithmicConditionalHeads : Prop :=
  ∃ (Y : ℕ → ℕ) (F : ℕ → ℕ → ℝ),
    Tendsto Y atTop atTop ∧ (∀ j, 1 ≤ Y j) ∧
      (∀ j, F j ∈ conditionalHeadClass (Y j)) ∧ ConditionalLogarithmicLimit F Y

/-- The final, mean-neutral variant of statement (iv). -/
def ZeroMeanLogarithmicConditionalHeads : Prop :=
  ∃ (Y : ℕ → ℕ) (F : ℕ → ℕ → ℝ),
    Tendsto Y atTop atTop ∧ (∀ j, 1 ≤ Y j) ∧
      (∀ j, F j ∈ zeroMeanConditionalHeadClass (Y j)) ∧ ConditionalLogarithmicLimit F Y

theorem conditionalLogarithmicLimit_of_bounded_energy
    (F : ℕ → ℕ → ℝ) (Y : ℕ → ℕ) (hY : Tendsto Y atTop atTop)
    (C : ℝ) (hC : ∀ j, conditionalMeanSquare (F j) ≤ C) :
    ConditionalLogarithmicLimit F Y := by
  have hden := Real.tendsto_log_atTop.comp
    (tendsto_natCast_atTop_atTop.comp hY : Tendsto (fun j => (Y j : ℝ)) atTop atTop)
  have hupper : Tendsto (fun j => Real.log (1 + C) / Real.log (Y j : ℝ))
      atTop (𝓝 0) := tendsto_const_nhds.div_atTop hden
  apply squeeze_zero' ?_ ?_ hupper
  · filter_upwards [hY.eventually (eventually_ge_atTop 2)] with j hj
    exact div_nonneg (Real.log_nonneg (by linarith [conditionalMeanSquare_nonneg (F j)]))
      (Real.log_nonneg (by exact_mod_cast (show 1 ≤ Y j by omega)))
  · filter_upwards [hY.eventually (eventually_ge_atTop 2)] with j hj
    apply div_le_div_of_nonneg_right
      (Real.log_le_log (by linarith [conditionalMeanSquare_nonneg (F j)]) (by linarith [hC j]))
      (Real.log_nonneg (by exact_mod_cast (show 1 ≤ Y j by omega)))

/-- The mean-neutralization can be selected without changing the logarithmic limit. -/
theorem conditionalLogarithmicLimit_of_energy_lt_add_one
    (F G : ℕ → ℕ → ℝ) (Y : ℕ → ℕ) (hY : Tendsto Y atTop atTop)
    (hF : ConditionalLogarithmicLimit F Y)
    (hG : ∀ j, conditionalMeanSquare (G j) < conditionalMeanSquare (F j) + 1) :
    ConditionalLogarithmicLimit G Y := by
  have hden := Real.tendsto_log_atTop.comp
    (tendsto_natCast_atTop_atTop.comp hY : Tendsto (fun j => (Y j : ℝ)) atTop atTop)
  have hc : Tendsto (fun j => Real.log 2 / Real.log (Y j : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hden
  have ht : Tendsto (fun j => Real.log 2 / Real.log (Y j : ℝ) +
      Real.log (1 + conditionalMeanSquare (F j)) / Real.log (Y j : ℝ)) atTop (𝓝 0) := by
    simpa using hc.add hF
  apply squeeze_zero' ?_ ?_ ht
  · filter_upwards [hY.eventually (eventually_ge_atTop 2)] with j hj
    exact div_nonneg (Real.log_nonneg (by linarith [conditionalMeanSquare_nonneg (G j)]))
      (Real.log_nonneg (by exact_mod_cast (show 1 ≤ Y j by omega)))
  · filter_upwards [hY.eventually (eventually_ge_atTop 2)] with j hj
    rw [← add_div]
    apply div_le_div_of_nonneg_right _ (Real.log_nonneg
      (by exact_mod_cast (show 1 ≤ Y j by omega)))
    have hpos : 0 < 1 + conditionalMeanSquare (F j) := by
      linarith [conditionalMeanSquare_nonneg (F j)]
    rw [← Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (ne_of_gt hpos)]
    apply Real.log_le_log (by linarith [conditionalMeanSquare_nonneg (G j)])
    linarith [conditionalMeanSquare_nonneg (F j), hG j]

theorem logarithmicConditionalHeads_iff_zeroMean :
    LogarithmicConditionalHeads ↔ ZeroMeanLogarithmicConditionalHeads := by
  constructor
  · rintro ⟨Y, F, hY, hpos, hF, hlim⟩
    have hex (j : ℕ) := exists_zeroMean_conditionalHead_near (Y j) (hF j) 1 (by norm_num)
    choose G hG hE using hex
    exact ⟨Y, G, hY, hpos, hG,
      conditionalLogarithmicLimit_of_energy_lt_add_one F G Y hY hlim hE⟩
  · rintro ⟨Y, F, hY, hpos, hF, hlim⟩
    exact ⟨Y, F, hY, hpos, fun j => (hF j).1, hlim⟩

/-- A direct zero-obstruction implication, independent of strong Nyman--Beurling. -/
theorem riemannHypothesis_of_logarithmicConditionalHeads
    (h : LogarithmicConditionalHeads) : RiemannHypothesis := by
  obtain ⟨Y, F, hY, _, hF, hlim⟩ := h
  apply riemannHypothesis_of_cofinally_small_conditionalMean_heads
    (Set.Ici 1) (by intro a ha; exact ha) F Y
    (fun j => (hF j).1) (fun j => (hF j).2) hY
  intro ε hε
  exact (hlim.eventually (gt_mem_nhds hε)).frequently

/-- Endpoint infima produce a single cofinal family of finite, mean-neutral witnesses. -/
theorem zeroMeanLogarithmicConditionalHeads_of_exactEndpoint
    (h : ExactConditionalEndpoint) : ZeroMeanLogarithmicConditionalHeads := by
  have hex (j : ℕ) : ∃ G ∈ zeroMeanConditionalHeadClass (j + 2),
      conditionalMeanSquare G < 2 := by
    obtain ⟨F, hF, hE⟩ := exists_head_energy_lt (j + 2) (1 / 4) (by norm_num)
    obtain ⟨G, hG, hGE⟩ := exists_zeroMean_conditionalHead_near (j + 2) hF
      (1 / 4) (by norm_num)
    have hh := h (j + 2) (by omega)
    have hm : ((j + 2 : ℕ) : ℝ) / (((j + 2 : ℕ) : ℝ) + 2) ≤ 1 := by
      apply (div_le_iff₀ (by positivity)).2
      linarith
    refine ⟨G, hG, ?_⟩
    rw [hh] at hE
    linarith
  choose G hG hE using hex
  have hY : Tendsto (fun j : ℕ => j + 2) atTop atTop := Filter.tendsto_add_atTop_nat 2
  exact ⟨fun j => j + 2, G, hY, by intro j; dsimp; omega, hG,
    conditionalLogarithmicLimit_of_bounded_energy G _ hY 2 (fun j => (hE j).le)⟩

theorem riemannHypothesis_of_exactConditionalEndpoint
    (h : ExactConditionalEndpoint) : RiemannHypothesis :=
  riemannHypothesis_of_logarithmicConditionalHeads
    (logarithmicConditionalHeads_iff_zeroMean.mpr
      (zeroMeanLogarithmicConditionalHeads_of_exactEndpoint h))

#print axioms zeroMeanConditionalHeadMinimum_eq
#print axioms logarithmicConditionalHeads_iff_zeroMean
#print axioms riemannHypothesis_of_logarithmicConditionalHeads
end RiemannResearch.RH.Pareto
