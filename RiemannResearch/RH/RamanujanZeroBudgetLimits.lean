import RiemannResearch.RH.RamanujanZeroLogBudget
import RiemannResearch.RH.RamanujanZeroCountBounds
import RiemannResearch.RH.RamanujanMellinProduct
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Topology.Algebra.GroupWithZero
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Escape of positive zero charges and the complete unused Ramanujan budget

Source: deductions from the verified finite and infinite Ramanujan zero
certificates, requested in the fifth transfer program, 24 October 2026.
Charge summability forces finite positive-charge threshold sets and escape
from every fixed right-half-plane window. The full unused product and log
budgets converge even when the zero-prefix depth and actual packet stage
follow independent cofinal maps. Their zero limits characterize an explicit
unresolved equality; that equality is never asserted here. Every nonlinear
tail slack is retained in the exact logarithmic remainder.
-/

noncomputable section
open Filter MeasureTheory Set
open scoped BigOperators Topology

namespace RiemannResearch.RH.RamanujanZeroCertificates
open Pareto Pareto.CoefficientStabilization RamanujanCanonicalOptimizer
open RiemannResearch.Analysis.ContractiveLogBudget

theorem zero_charge_tendsto_zero (z : ℕ → ℂ)
    (hzre : ∀ i, (1 / 2 : ℝ) < (z i).re) (hinj : Function.Injective z)
    (hz1 : ∀ i, z i ≠ 1) (hzero : ∀ i, riemannZeta (z i) = 0) :
    Tendsto (fun i => zeroCharge (z i)) atTop (𝓝 0) :=
  (zero_charge_summable z hzre hinj hz1 hzero).tendsto_atTop_zero

/-- Every positive charge threshold contains only finitely many members of
an injective actual zero sequence. No finiteness of the whole sequence is claimed. -/
theorem zero_charge_threshold_finite (z : ℕ → ℂ)
    (hzre : ∀ i, (1 / 2 : ℝ) < (z i).re) (hinj : Function.Injective z)
    (hz1 : ∀ i, z i ≠ 1) (hzero : ∀ i, riemannZeta (z i) = 0)
    {η : ℝ} (hη : 0 < η) : Set.Finite {i : ℕ | η ≤ zeroCharge (z i)} := by
  have he := (zero_charge_tendsto_zero z hzre hinj hz1 hzero).eventually_lt_const hη
  obtain ⟨N, hN⟩ := eventually_atTop.1 he
  apply (Finset.range N).finite_toSet.subset
  intro i hi
  apply Finset.mem_range.mpr
  by_contra hn
  exact (not_lt_of_ge hi) (hN i (not_lt.mp hn))

theorem zero_window_finite (z : ℕ → ℂ)
    (hzre : ∀ i, (1 / 2 : ℝ) < (z i).re) (hinj : Function.Injective z)
    (hz1 : ∀ i, z i ≠ 1) (hzero : ∀ i, riemannZeta (z i) = 0)
    {δ R : ℝ} (hδ : 0 < δ) (hR : 0 < R) :
    Set.Finite {i : ℕ | 1 / 2 + δ ≤ (z i).re ∧ ‖z i‖ ^ 2 ≤ R} := by
  apply (zero_charge_threshold_finite z hzre hinj hz1 hzero
    (div_pos (by linarith : 0 < 2 * δ) hR)).subset
  intro i hi
  exact zeroCharge_lower_of_window (z i) hδ hR hi.1 hi.2

theorem zero_eventually_outside_window (z : ℕ → ℂ)
    (hzre : ∀ i, (1 / 2 : ℝ) < (z i).re) (hinj : Function.Injective z)
    (hz1 : ∀ i, z i ≠ 1) (hzero : ∀ i, riemannZeta (z i) = 0)
    {δ R : ℝ} (hδ : 0 < δ) (hR : 0 < R) :
    ∀ᶠ i in atTop, (z i).re < 1 / 2 + δ ∨ R < ‖z i‖ ^ 2 := by
  have he := (zero_charge_tendsto_zero z hzre hinj hz1 hzero).eventually_lt_const
    (div_pos (by linarith : 0 < 2 * δ) hR)
  filter_upwards [he] with i hi
  by_cases hre : 1 / 2 + δ ≤ (z i).re
  · right
    by_contra hn
    exact (not_lt_of_ge (zeroCharge_lower_of_window (z i) hδ hR hre
      (not_lt.mp hn))) hi
  · exact Or.inl (lt_of_not_ge hre)

/-- A sequence that stays a fixed distance right of the critical line must
escape every bounded norm window. This does not posit such a sequence. -/
theorem zero_norm_sq_tendsto_atTop_of_margin (z : ℕ → ℂ)
    (hzre : ∀ i, (1 / 2 : ℝ) < (z i).re) (hinj : Function.Injective z)
    (hz1 : ∀ i, z i ≠ 1) (hzero : ∀ i, riemannZeta (z i) = 0)
    {δ : ℝ} (hδ : 0 < δ) (hmargin : ∀ᶠ i in atTop, 1 / 2 + δ ≤ (z i).re) :
    Tendsto (fun i => ‖z i‖ ^ 2) atTop atTop := by
  apply tendsto_atTop.mpr
  intro B
  let R : ℝ := max B 0 + 1
  have hR : 0 < R := by dsimp [R]; linarith [le_max_right B 0]
  filter_upwards [zero_eventually_outside_window z hzre hinj hz1 hzero hδ hR,
    hmargin] with i hi hm
  rcases hi with hi | hi
  · exact (not_lt_of_ge hm hi).elim
  · dsimp [R] at hi
    linarith [le_max_left B 0]

/-- The unresolved additive gap between the full zero product and captured mass. -/
def zeroProductResidualGap (z : ℕ → ℂ) : ℝ :=
  mellinZeroProductLimit z - (1 - limitEnergy)

/-- The exact unresolved logarithmic budget, including no discarded slack. -/
def zeroLogResidualGap (z : ℕ → ℂ) : ℝ :=
  Real.log (mellinZeroProductLimit z / (1 - limitEnergy))

/-- The complete finite-prefix Mellin integral for the actual packet residual. -/
def zeroPrefixMellinRemainder (z : ℕ → ℂ) (N K : ℕ) : ℝ :=
  ∫ x in Ioi (1 : ℝ),
    ‖mellinWeightedStep (hilbertOne - packetCandidate K) x -
      starRingEnd ℂ (finiteMellinKernel (fun i : Fin N => z i.val)
        (mellinInverseCoefficients (fun i : Fin N => z i.val)
          (fun i => 1 / z i.val)) x)‖ ^ 2

theorem zeroPrefixMellinRemainder_nonneg (z : ℕ → ℂ) (N K : ℕ) :
    0 ≤ zeroPrefixMellinRemainder z N K :=
  integral_nonneg (fun _ => sq_nonneg _)

/-- Every finite unused product gap equals the full Mellin remainder exactly. -/
theorem zero_prefix_product_gap_eq_mellin_remainder (z : ℕ → ℂ)
    (hzre : ∀ i, (1 / 2 : ℝ) < (z i).re) (hinj : Function.Injective z)
    (hz1 : ∀ i, z i ≠ 1) (hzero : ∀ i, riemannZeta (z i) = 0) (N K : ℕ) :
    mellinZeroProduct (fun i : Fin N => z i.val) - packetMass K =
      zeroPrefixMellinRemainder z N K := by
  have hi : Function.Injective (fun i : Fin N => z i.val) := by
    intro i j hij
    exact Fin.ext (hinj hij)
  have he := packet_zeroProduct_energy_exact (fun i : Fin N => z i.val)
    (fun i => hzre i.val) hi (fun i => hz1 i.val) (fun i => hzero i.val) K
  change 1 - packetMass K = 1 - mellinZeroProduct (fun i : Fin N => z i.val) +
    zeroPrefixMellinRemainder z N K at he
  linarith

theorem zeroProductResidualGap_nonneg (z : ℕ → ℂ)
    (hzre : ∀ i, (1 / 2 : ℝ) < (z i).re) (hinj : Function.Injective z)
    (hz1 : ∀ i, z i ≠ 1) (hzero : ∀ i, riemannZeta (z i) = 0) :
    0 ≤ zeroProductResidualGap z := by
  unfold zeroProductResidualGap
  linarith [zeroProductLimit_limitEnergy_lower_bound z hzre hinj hz1 hzero]

theorem zeroLogResidualGap_nonneg (z : ℕ → ℂ)
    (hzre : ∀ i, (1 / 2 : ℝ) < (z i).re) (hinj : Function.Injective z)
    (hz1 : ∀ i, z i ≠ 1) (hzero : ∀ i, riemannZeta (z i) = 0) :
    0 ≤ zeroLogResidualGap z := by
  apply Real.log_nonneg
  apply (le_div_iff₀ packetLimitMass_pos).mpr
  have h := zeroProductLimit_limitEnergy_lower_bound z hzre hinj hz1 hzero
  linarith

theorem zeroLogResidualGap_eq_log_one_add (z : ℕ → ℂ) :
    zeroLogResidualGap z =
      Real.log (1 + zeroProductResidualGap z / (1 - limitEnergy)) := by
  unfold zeroLogResidualGap zeroProductResidualGap
  congr 1
  rw [sub_div, div_self packetLimitMass_pos.ne']
  ring

theorem zeroProductResidualGap_eq_zero_iff (z : ℕ → ℂ) :
    zeroProductResidualGap z = 0 ↔ mellinZeroProductLimit z = 1 - limitEnergy :=
  sub_eq_zero

theorem zeroLogResidualGap_eq_zero_iff (z : ℕ → ℂ)
    (hzre : ∀ i, (1 / 2 : ℝ) < (z i).re) (hinj : Function.Injective z)
    (hz1 : ∀ i, z i ≠ 1) (hzero : ∀ i, riemannZeta (z i) = 0) :
    zeroLogResidualGap z = 0 ↔ mellinZeroProductLimit z = 1 - limitEnergy := by
  unfold zeroLogResidualGap
  constructor
  · intro h
    have he := congrArg Real.exp h
    rw [Real.exp_log (div_pos (zeroProductLimit_pos z hzre hinj hz1 hzero)
      packetLimitMass_pos), Real.exp_zero] at he
    exact (div_eq_one_iff_eq packetLimitMass_pos.ne').mp he
  · intro h
    rw [h, div_self packetLimitMass_pos.ne', Real.log_one]

/-- The unused logarithmic budget consists of the full tail charge, every
nonlinear tail slack, and the unresolved residual gap. -/
theorem zero_prefix_log_gap_exact (z : ℕ → ℂ)
    (hzre : ∀ i, (1 / 2 : ℝ) < (z i).re) (hinj : Function.Injective z)
    (hz1 : ∀ i, z i ≠ 1) (hzero : ∀ i, riemannZeta (z i) = 0) (N : ℕ) :
    Real.log (mellinZeroProduct (fun i : Fin N => z i.val) / (1 - limitEnergy)) =
      (∑' i, zeroCharge (z (i + N))) +
      (∑' i, slack (zeroFactor (z (i + N)))) + zeroLogResidualGap z := by
  have hp : 0 < mellinZeroProduct (fun i : Fin N => z i.val) := by
    unfold mellinZeroProduct
    apply Finset.prod_pos
    intro i _
    have hz0 : z i.val ≠ 0 := by
      intro h
      have hh := hzre i.val
      simp [h] at hh
      linarith
    exact zeroFactor_pos (z i.val) hz0 (hz1 i.val)
  have hL := zeroProductLimit_pos z hzre hinj hz1 hzero
  have ht := zero_tail_log_budget z hzre hinj hz1 hzero N
  rw [Real.log_div hp.ne' hL.ne'] at ht
  unfold zeroLogResidualGap
  rw [Real.log_div hp.ne' packetLimitMass_pos.ne',
    Real.log_div hL.ne' packetLimitMass_pos.ne']
  linarith

theorem zero_complete_log_budget_exhaustion_iff (z : ℕ → ℂ)
    (hzre : ∀ i, (1 / 2 : ℝ) < (z i).re) (hinj : Function.Injective z)
    (hz1 : ∀ i, z i ≠ 1) (hzero : ∀ i, riemannZeta (z i) = 0) :
    (-Real.log (1 - limitEnergy) = (∑' i, zeroCharge (z i)) +
      ∑' i, slack (zeroFactor (z i))) ↔
        mellinZeroProductLimit z = 1 - limitEnergy := by
  have he := zero_limit_packet_log_budget z hzre hinj hz1 hzero
  change -Real.log (1 - limitEnergy) = _ + zeroLogResidualGap z at he
  rw [← zeroLogResidualGap_eq_zero_iff z hzre hinj hz1 hzero]
  constructor <;> intro h <;> linarith

variable {α : Type*} {l : Filter α}

/-- Product-gap convergence needs no nontrivial-filter hypothesis. -/
theorem zero_prefix_product_gap_tendsto (z : ℕ → ℂ)
    (hzre : ∀ i, (1 / 2 : ℝ) < (z i).re) (hinj : Function.Injective z)
    (N : α → ℕ) (hN : Tendsto N l atTop) :
    Tendsto (fun i => mellinZeroProduct (fun j : Fin (N i) => z j.val) -
      (1 - limitEnergy)) l (𝓝 (zeroProductResidualGap z)) :=
  ((mellinZeroProduct_prefix_tendsto z hzre hinj).comp hN).sub tendsto_const_nhds

theorem zero_prefix_log_gap_tendsto (z : ℕ → ℂ)
    (hzre : ∀ i, (1 / 2 : ℝ) < (z i).re) (hinj : Function.Injective z)
    (hz1 : ∀ i, z i ≠ 1) (hzero : ∀ i, riemannZeta (z i) = 0)
    (N : α → ℕ) (hN : Tendsto N l atTop) :
    Tendsto (fun i => Real.log
      (mellinZeroProduct (fun j : Fin (N i) => z j.val) / (1 - limitEnergy)))
      l (𝓝 (zeroLogResidualGap z)) := by
  have ht := ((mellinZeroProduct_prefix_tendsto z hzre hinj).comp hN).div
    tendsto_const_nhds packetLimitMass_pos.ne'
  have hp := div_pos (zeroProductLimit_pos z hzre hinj hz1 hzero) packetLimitMass_pos
  exact (Real.continuousAt_log hp.ne').tendsto.comp ht

/-- Independent cofinal zero-prefix and packet-stage maps retain the same
complete unused product gap. No relation between the two stage indices is needed. -/
theorem zero_coupled_product_gap_tendsto (z : ℕ → ℂ)
    (hzre : ∀ i, (1 / 2 : ℝ) < (z i).re) (hinj : Function.Injective z)
    (N K : α → ℕ) (hN : Tendsto N l atTop) (hK : Tendsto K l atTop) :
    Tendsto (fun i => mellinZeroProduct (fun j : Fin (N i) => z j.val) -
      packetMass (K i)) l (𝓝 (zeroProductResidualGap z)) :=
  ((mellinZeroProduct_prefix_tendsto z hzre hinj).comp hN).sub
    (packetMass_tendsto.comp hK)

theorem zero_coupled_log_gap_tendsto (z : ℕ → ℂ)
    (hzre : ∀ i, (1 / 2 : ℝ) < (z i).re) (hinj : Function.Injective z)
    (hz1 : ∀ i, z i ≠ 1) (hzero : ∀ i, riemannZeta (z i) = 0)
    (N K : α → ℕ) (hN : Tendsto N l atTop) (hK : Tendsto K l atTop) :
    Tendsto (fun i => Real.log
      (mellinZeroProduct (fun j : Fin (N i) => z j.val) / packetMass (K i)))
      l (𝓝 (zeroLogResidualGap z)) := by
  have ht := ((mellinZeroProduct_prefix_tendsto z hzre hinj).comp hN).div
    (packetMass_tendsto.comp hK) packetLimitMass_pos.ne'
  have hp := div_pos (zeroProductLimit_pos z hzre hinj hz1 hzero) packetLimitMass_pos
  exact (Real.continuousAt_log hp.ne').tendsto.comp ht

/-- Both finite stages may tend to infinity independently; the whole integral
remainder converges to the full, still unresolved product gap. -/
theorem zero_coupled_mellin_remainder_tendsto (z : ℕ → ℂ)
    (hzre : ∀ i, (1 / 2 : ℝ) < (z i).re) (hinj : Function.Injective z)
    (hz1 : ∀ i, z i ≠ 1) (hzero : ∀ i, riemannZeta (z i) = 0)
    (N K : α → ℕ) (hN : Tendsto N l atTop) (hK : Tendsto K l atTop) :
    Tendsto (fun i => zeroPrefixMellinRemainder z (N i) (K i))
      l (𝓝 (zeroProductResidualGap z)) := by
  simpa only [zero_prefix_product_gap_eq_mellin_remainder z hzre hinj hz1 hzero] using
    zero_coupled_product_gap_tendsto z hzre hinj N K hN hK

theorem zero_prefix_product_gap_zero_iff [NeBot l] (z : ℕ → ℂ)
    (hzre : ∀ i, (1 / 2 : ℝ) < (z i).re) (hinj : Function.Injective z)
    (N : α → ℕ) (hN : Tendsto N l atTop) :
    Tendsto (fun i => mellinZeroProduct (fun j : Fin (N i) => z j.val) -
      (1 - limitEnergy)) l (𝓝 0) ↔ mellinZeroProductLimit z = 1 - limitEnergy := by
  have ht := zero_prefix_product_gap_tendsto z hzre hinj N hN
  constructor
  · intro h
    exact (zeroProductResidualGap_eq_zero_iff z).mp (tendsto_nhds_unique ht h)
  · intro h
    simpa only [(zeroProductResidualGap_eq_zero_iff z).mpr h] using ht

theorem zero_prefix_log_gap_zero_iff [NeBot l] (z : ℕ → ℂ)
    (hzre : ∀ i, (1 / 2 : ℝ) < (z i).re) (hinj : Function.Injective z)
    (hz1 : ∀ i, z i ≠ 1) (hzero : ∀ i, riemannZeta (z i) = 0)
    (N : α → ℕ) (hN : Tendsto N l atTop) :
    Tendsto (fun i => Real.log
      (mellinZeroProduct (fun j : Fin (N i) => z j.val) / (1 - limitEnergy)))
      l (𝓝 0) ↔ mellinZeroProductLimit z = 1 - limitEnergy := by
  have ht := zero_prefix_log_gap_tendsto z hzre hinj hz1 hzero N hN
  constructor
  · intro h
    exact (zeroLogResidualGap_eq_zero_iff z hzre hinj hz1 hzero).mp
      (tendsto_nhds_unique ht h)
  · intro h
    simpa only [(zeroLogResidualGap_eq_zero_iff z hzre hinj hz1 hzero).mpr h] using ht

/-- Vanishing of the actual two-stage product gap is an exact exhaustion
criterion, not an unconditional identification of product and captured mass. -/
theorem zero_coupled_product_gap_zero_iff [NeBot l] (z : ℕ → ℂ)
    (hzre : ∀ i, (1 / 2 : ℝ) < (z i).re) (hinj : Function.Injective z)
    (N K : α → ℕ) (hN : Tendsto N l atTop) (hK : Tendsto K l atTop) :
    Tendsto (fun i => mellinZeroProduct (fun j : Fin (N i) => z j.val) -
      packetMass (K i)) l (𝓝 0) ↔ mellinZeroProductLimit z = 1 - limitEnergy := by
  have ht := zero_coupled_product_gap_tendsto z hzre hinj N K hN hK
  constructor
  · intro h
    exact (zeroProductResidualGap_eq_zero_iff z).mp (tendsto_nhds_unique ht h)
  · intro h
    simpa only [(zeroProductResidualGap_eq_zero_iff z).mpr h] using ht

theorem zero_coupled_log_gap_zero_iff [NeBot l] (z : ℕ → ℂ)
    (hzre : ∀ i, (1 / 2 : ℝ) < (z i).re) (hinj : Function.Injective z)
    (hz1 : ∀ i, z i ≠ 1) (hzero : ∀ i, riemannZeta (z i) = 0)
    (N K : α → ℕ) (hN : Tendsto N l atTop) (hK : Tendsto K l atTop) :
    Tendsto (fun i => Real.log
      (mellinZeroProduct (fun j : Fin (N i) => z j.val) / packetMass (K i)))
      l (𝓝 0) ↔ mellinZeroProductLimit z = 1 - limitEnergy := by
  have ht := zero_coupled_log_gap_tendsto z hzre hinj hz1 hzero N K hN hK
  constructor
  · intro h
    exact (zeroLogResidualGap_eq_zero_iff z hzre hinj hz1 hzero).mp
      (tendsto_nhds_unique ht h)
  · intro h
    simpa only [(zeroLogResidualGap_eq_zero_iff z hzre hinj hz1 hzero).mpr h] using ht

theorem zero_coupled_mellin_remainder_zero_iff [NeBot l] (z : ℕ → ℂ)
    (hzre : ∀ i, (1 / 2 : ℝ) < (z i).re) (hinj : Function.Injective z)
    (hz1 : ∀ i, z i ≠ 1) (hzero : ∀ i, riemannZeta (z i) = 0)
    (N K : α → ℕ) (hN : Tendsto N l atTop) (hK : Tendsto K l atTop) :
    Tendsto (fun i => zeroPrefixMellinRemainder z (N i) (K i)) l (𝓝 0) ↔
      mellinZeroProductLimit z = 1 - limitEnergy := by
  simpa only [zero_prefix_product_gap_eq_mellin_remainder z hzre hinj hz1 hzero] using
    zero_coupled_product_gap_zero_iff z hzre hinj N K hN hK

end RiemannResearch.RH.RamanujanZeroCertificates
