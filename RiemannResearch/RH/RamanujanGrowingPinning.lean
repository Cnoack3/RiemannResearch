import RiemannResearch.RH.RamanujanFinitePinning
import RiemannResearch.RH.RamanujanSaturationCriteria
import RiemannResearch.RH.RamanujanCoefficientLimits
import RiemannResearch.Analysis.FiniteHilbertGram
import RiemannResearch.Analysis.FiniteSamplingDiagonal
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Growing exact Moebius pinning with complete cost control

Source: user-requested fourth Ramanujan dual continuation, 23 October 2026.
The number and locations of pinned coordinates may vary without bound.
Their exact full Gram cost is retained: zero error is equivalent to both
canonical saturation and vanishing repair cost. A computable weighted
coefficient-defect budget is sufficient. Conversely, canonical saturation
permits any prescribed growing family to be pinned along a sufficiently
late increasing sequence of legal stages with arbitrary positive tolerances.
This diagonal has no asserted effective rate. The RH converse remains the
explicit Baez-Duarte provider obligation.
-/

noncomputable section
open Filter
open scoped Topology BigOperators
namespace RiemannResearch.RH.RamanujanGrowingPinning
open Pareto Pareto.CoefficientStabilization RamanujanCanonicalOptimizer
open RamanujanFinitePinning
open RiemannResearch.Analysis.FiniteHilbertGram
open RiemannResearch.Analysis.FiniteSamplingDiagonal

variable {κ : Type*} [Fintype κ]

def pinDefect (n : ℕ) (e : κ ↪ ℕ) (j : κ) : ℝ :=
  packetMultipleCoefficient n (e j + 2) + (ArithmeticFunction.moebius (e j + 2) : ℝ)

def pinningCost (n : ℕ) (e : κ ↪ ℕ) : ℝ :=
  ‖coordinateRepair e (hilbertOne - packetCandidate n)‖ ^ 2

def defectBudget (n : ℕ) (e : κ ↪ ℕ) : ℝ :=
  ∑ j, |pinDefect n e j| * ‖residueAtom (e j)‖

theorem repair_eq_signed_defects (n : ℕ) (e : κ ↪ ℕ) :
    coordinateRepair e (hilbertOne - packetCandidate n) =
      -Fintype.linearCombination ℝ (fun j => residueAtom (e j)) (pinDefect n e) := by
  rw [coordinateRepair_apply, Fintype.linearCombination_apply]
  have hc (j : κ) : coefficientCLM (e j + 2) (hilbertOne - packetCandidate n) =
      -pinDefect n e j := by
    change -(mobiusDifferenceCLM (e j + 2) (hilbertOne - packetCandidate n)) = _
    rw [← packetMultipleCoefficient_defect n (e j + 2) (by omega)]
    rfl
  simp only [hc, neg_smul, Finset.sum_neg_distrib]

/-- The exact cost is the entire signed residue Gram quadratic form. -/
theorem pinningCost_gram (n : ℕ) (e : κ ↪ ℕ) :
    pinningCost n e = ∑ i, pinDefect n e i *
      gram (fun j => residueAtom (e j)) (pinDefect n e) i := by
  rw [pinningCost, repair_eq_signed_defects, norm_neg, gram_quadratic]

theorem repair_norm_le_budget (n : ℕ) (e : κ ↪ ℕ) :
    ‖coordinateRepair e (hilbertOne - packetCandidate n)‖ ≤ defectBudget n e := by
  rw [repair_eq_signed_defects, norm_neg, Fintype.linearCombination_apply]
  calc
    _ ≤ ∑ j, ‖pinDefect n e j • residueAtom (e j)‖ := norm_sum_le _ _
    _ = defectBudget n e := by simp only [norm_smul, Real.norm_eq_abs, defectBudget]

theorem pinningCost_le_budget_sq (n : ℕ) (e : κ ↪ ℕ) :
    pinningCost n e ≤ defectBudget n e ^ 2 := by
  have h := repair_norm_le_budget n e
  have hb : 0 ≤ defectBudget n e := (norm_nonneg _).trans h
  exact (sq_le_sq₀ (norm_nonneg _) hb).mpr h

/-- Exact error identity before any estimate of a growing constraint set. -/
theorem pinned_error_with_cost (n : ℕ) (e : κ ↪ ℕ) (hn : ∀ j, e j < n) :
    ‖hilbertOne - pinnedCandidate n e‖ ^ 2 = 1 - packetMass n + pinningCost n e :=
  pinned_error_exact n e hn

section Moving
variable {α : Type*} {J : α → Type*} [∀ i, Fintype (J i)]
  {l : Filter α} [NeBot l]

/-- Growing and moving exact constraints require precisely one additional
vanishing quantity: their complete signed repair Gram cost. -/
theorem moving_error_iff (N : α → ℕ) (hN : Tendsto N l atTop)
    (e : ∀ i, J i ↪ ℕ) (hstage : ∀ᶠ i in l, ∀ j, e i j < N i) :
    Tendsto (fun i => ‖hilbertOne - pinnedCandidate (N i) (e i)‖ ^ 2) l (𝓝 0) ↔
      limitEnergy = 0 ∧ Tendsto (fun i => pinningCost (N i) (e i)) l (𝓝 0) := by
  have hb : Tendsto (fun i => 1 - packetMass (N i)) l (𝓝 limitEnergy) := by
    simpa only [Function.comp_def, packet_energy_eq_original] using energy_tendsto.comp hN
  have he : (fun i => ‖hilbertOne - pinnedCandidate (N i) (e i)‖ ^ 2) =ᶠ[l]
      (fun i => 1 - packetMass (N i) + pinningCost (N i) (e i)) := by
    filter_upwards [hstage] with i hi
    exact pinned_error_with_cost (N i) (e i) hi
  have hnonneg : ∀ i, 0 ≤ 1 - packetMass (N i) := by
    intro i
    rw [← packet_error]
    exact sq_nonneg _
  constructor
  · intro hp
    have hbaseupper : ∀ᶠ i in l, 1 - packetMass (N i) ≤
        ‖hilbertOne - pinnedCandidate (N i) (e i)‖ ^ 2 := by
      filter_upwards [he] with i hi
      rw [hi]
      exact le_add_of_nonneg_right (sq_nonneg _)
    have hcostupper : ∀ᶠ i in l, pinningCost (N i) (e i) ≤
        ‖hilbertOne - pinnedCandidate (N i) (e i)‖ ^ 2 := by
      filter_upwards [he] with i hi
      rw [hi]
      exact le_add_of_nonneg_left (hnonneg i)
    have hz := squeeze_zero' (Filter.Eventually.of_forall hnonneg) hbaseupper hp
    refine ⟨tendsto_nhds_unique hb hz, ?_⟩
    exact squeeze_zero' (Filter.Eventually.of_forall (fun _ => sq_nonneg _)) hcostupper hp
  · rintro ⟨hz, hc⟩
    have ht : Tendsto (fun i => 1 - packetMass (N i) + pinningCost (N i) (e i)) l (𝓝 0) := by
      simpa only [hz, zero_add] using hb.add hc
    exact ht.congr' he.symm

/-- A concrete weighted coefficient-defect budget controls arbitrary growing pinning. -/
theorem moving_error_of_budget (N : α → ℕ) (hN : Tendsto N l atTop)
    (e : ∀ i, J i ↪ ℕ) (hstage : ∀ᶠ i in l, ∀ j, e i j < N i)
    (hzero : limitEnergy = 0)
    (hbudget : Tendsto (fun i => defectBudget (N i) (e i)) l (𝓝 0)) :
    Tendsto (fun i => ‖hilbertOne - pinnedCandidate (N i) (e i)‖ ^ 2) l (𝓝 0) := by
  apply (moving_error_iff N hN e hstage).mpr
  refine ⟨hzero, ?_⟩
  have hs : Tendsto (fun i => defectBudget (N i) (e i) ^ 2) l (𝓝 0) := by
    simpa using hbudget.pow 2
  exact squeeze_zero' (Filter.Eventually.of_forall (fun _ => sq_nonneg _))
    (Filter.Eventually.of_forall (fun i => pinningCost_le_budget_sq (N i) (e i))) hs

theorem moving_error_rh_iff
    (hBaezDuarte : RiemannHypothesis → BaezDuarte.NaturalApproximation)
    (N : α → ℕ) (hN : Tendsto N l atTop)
    (e : ∀ i, J i ↪ ℕ) (hstage : ∀ᶠ i in l, ∀ j, e i j < N i) :
    Tendsto (fun i => ‖hilbertOne - pinnedCandidate (N i) (e i)‖ ^ 2) l (𝓝 0) ↔
      RiemannHypothesis ∧ Tendsto (fun i => pinningCost (N i) (e i)) l (𝓝 0) := by
  rw [moving_error_iff N hN e hstage]
  have hRH : limitEnergy = 0 ↔ RiemannHypothesis :=
    (packet_cofinal_mass_iff N hN).symm.trans
      (packet_cofinal_rh_equivalences hBaezDuarte N hN).1
  rw [hRH]

end Moving

section Diagonal
variable {J : ℕ → Type*} [∀ k, Fintype (J k)]

/-- Every prescribed growing family can be pinned with arbitrary positive
stagewise error tolerances by choosing sufficiently late increasing stages. -/
theorem exists_growing_pinning_diagonal (e : ∀ k, J k ↪ ℕ) (ε : ℕ → ℝ)
    (hε : ∀ k, 0 < ε k) (hzero : limitEnergy = 0) :
    ∃ N : ℕ → ℕ, StrictMono N ∧ (∀ k, k ≤ N k) ∧
      ∀ k, (∀ j, e k j < N k) ∧
        ‖hilbertOne - pinnedCandidate (N k) (e k)‖ ^ 2 ≤ ε k := by
  apply exists_strictMono_diagonal_of_eventually
    (fun k n => (∀ j, e k j < n) ∧ ‖hilbertOne - pinnedCandidate n (e k)‖ ^ 2 ≤ ε k)
  intro k
  have ht := (pinned_cofinal_error_iff id tendsto_id (e k)).mpr hzero
  have hsmall : ∀ᶠ n in atTop, ‖hilbertOne - pinnedCandidate n (e k)‖ ^ 2 ≤ ε k :=
    ((tendsto_order.1 ht).2 (ε k) (hε k)).mono (fun _ h => le_of_lt h)
  exact (eventually_contains id tendsto_id (e k)).and hsmall

/-- This exact growing-coordinate approximation criterion is equivalent to
canonical saturation, without assuming a uniform estimate as the head grows. -/
theorem growing_pinning_diagonal_iff (e : ∀ k, J k ↪ ℕ) (ε : ℕ → ℝ)
    (hε : ∀ k, 0 < ε k) (hεzero : Tendsto ε atTop (𝓝 0)) :
    (∃ N : ℕ → ℕ, StrictMono N ∧ (∀ k, k ≤ N k) ∧
      ∀ k, (∀ j, e k j < N k) ∧
        ‖hilbertOne - pinnedCandidate (N k) (e k)‖ ^ 2 ≤ ε k) ↔ limitEnergy = 0 := by
  constructor
  · rintro ⟨N, hmono, _, hbound⟩
    have hp : Tendsto (fun k => ‖hilbertOne - pinnedCandidate (N k) (e k)‖ ^ 2)
        atTop (𝓝 0) := by
      exact squeeze_zero' (Filter.Eventually.of_forall (fun _ => sq_nonneg _))
        (Filter.Eventually.of_forall (fun k => (hbound k).2)) hεzero
    exact ((moving_error_iff N hmono.tendsto_atTop e
      (Filter.Eventually.of_forall (fun k => (hbound k).1))).mp hp).1
  · exact exists_growing_pinning_diagonal e ε hε

theorem growing_pinning_diagonal_rh_iff
    (hBaezDuarte : RiemannHypothesis → BaezDuarte.NaturalApproximation)
    (e : ∀ k, J k ↪ ℕ) (ε : ℕ → ℝ)
    (hε : ∀ k, 0 < ε k) (hεzero : Tendsto ε atTop (𝓝 0)) :
    (∃ N : ℕ → ℕ, StrictMono N ∧ (∀ k, k ≤ N k) ∧
      ∀ k, (∀ j, e k j < N k) ∧
        ‖hilbertOne - pinnedCandidate (N k) (e k)‖ ^ 2 ≤ ε k) ↔ RiemannHypothesis := by
  exact (growing_pinning_diagonal_iff e ε hε hεzero).trans
    ((packet_cofinal_mass_iff id tendsto_id).symm.trans
      (packet_cofinal_rh_equivalences hBaezDuarte id tendsto_id).1)

end Diagonal
end RiemannResearch.RH.RamanujanGrowingPinning
