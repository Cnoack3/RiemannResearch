import RiemannResearch.RH.RamanujanSaturationCriteria
import RiemannResearch.RH.RamanujanFiniteSpanBridge
import RiemannResearch.RH.MobiusCoefficientStabilization
import RiemannResearch.RH.MobiusHilbertCoordinates
import RiemannResearch.Analysis.FiniteBiorthogonalPinning
import RiemannResearch.Analysis.FiniteHilbertGramProjection
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Tactic.Linarith
import Lean.Elab.Tactic.Omega

/-!
# Finite exact Moebius pinning preserves Ramanujan approximation

Source: user-requested continuation of the duality structure, 23 October 2026.
Any fixed finite selection of original legal coefficients can be set exactly
to their negative-Moebius targets. The repair is a concrete continuous finite
sum of legal residue atoms. Its exact energy and uniform norm bound show that
this stronger approximation requirement is equivalent to the original one,
also along arbitrary cofinal maps. The RH reverse implication still carries
the explicit Baez-Duarte provider obligation.
-/

noncomputable section
open Filter
open scoped Topology BigOperators
namespace RiemannResearch.RH.RamanujanFinitePinning
open Pareto Pareto.CoefficientStabilization RamanujanCanonicalOptimizer
open RiemannResearch.Analysis.FiniteHilbertGram
open RiemannResearch.Analysis.FiniteBiorthogonalPinning

variable {κ : Type*} [Fintype κ]

def coordinateRepair (e : κ ↪ ℕ) : ThresholdHilbert →L[ℝ] ThresholdHilbert :=
  repair (fun j => residueAtom (e j)) (fun j => coefficientCLM (e j + 2))

theorem coordinateRepair_apply (e : κ ↪ ℕ) (x : ThresholdHilbert) :
    coordinateRepair e x = ∑ j, coefficientCLM (e j + 2) x • residueAtom (e j) :=
  repair_apply _ _ x

theorem selected_biorthogonal [DecidableEq κ] (e : κ ↪ ℕ) (i j : κ) :
    coefficientCLM (e i + 2) (residueAtom (e j)) = if i = j then 1 else 0 := by
  classical
  rw [coefficientCLM_biorthogonal]
  simp only [e.injective.eq_iff]

/-- A genuine finite coordinate projection, independent of the stage. -/
theorem coordinateRepair_idempotent (e : κ ↪ ℕ) (x : ThresholdHilbert) :
    coordinateRepair e (coordinateRepair e x) = coordinateRepair e x := by
  classical
  exact repair_idempotent _ _ (selected_biorthogonal e) x

def pinnedCandidate (n : ℕ) (e : κ ↪ ℕ) : ThresholdHilbert :=
  packetCandidate n + coordinateRepair e (hilbertOne - packetCandidate n)

/-- The selected original legal coefficients are exactly their desired limits
at every stage; no limiting interchange is needed. -/
theorem pinned_coordinate (n : ℕ) (e : κ ↪ ℕ) (j : κ) :
    coefficientCLM (e j + 2) (pinnedCandidate n e) =
      -(ArithmeticFunction.moebius (e j + 2) : ℝ) := by
  classical
  have h := pinTo_coordinate (fun j => residueAtom (e j))
    (fun j => coefficientCLM (e j + 2)) (selected_biorthogonal e)
    hilbertOne (packetCandidate n) j
  change coefficientCLM (e j + 2) (pinnedCandidate n e) =
    coefficientCLM (e j + 2) hilbertOne at h
  rw [h]
  change -(mobiusDifferenceCLM (e j + 2) hilbertOne) =
    -(ArithmeticFunction.moebius (e j + 2) : ℝ)
  rw [mobius_coordinate_one (e j + 2) (by omega)]

theorem residueAtom_mem_packetSpan (n i : ℕ) (hi : i < n) :
    residueAtom i ∈ synthesisSpan
      (fun j : Fin n => ramanujanPacketHilbert (j.val + 2)) := by
  change residueAtom i ∈ Submodule.span ℝ
    (Set.range (fun j : Fin n => ramanujanPacketHilbert (j.val + 2)))
  rw [finitePacket_span_eq]
  exact Submodule.subset_span ⟨⟨i, hi⟩, rfl⟩

theorem packet_residual_orthogonal_atom (n i : ℕ) (hi : i < n) :
    inner ℝ (hilbertOne - packetCandidate n) (residueAtom i) = 0 := by
  have hg := residueAtom_mem_packetSpan n i hi
  rw [synthesisSpan, ← Fintype.range_linearCombination] at hg
  obtain ⟨a, ha⟩ := hg
  rw [← ha]
  exact residual_orthogonal (finitePacket_independent n) hilbertOne a

/-- The pinned vector is still a legal synthesis in the same Ramanujan stage. -/
theorem pinned_packet_expansion (n : ℕ) (e : κ ↪ ℕ) (hn : ∀ j, e j < n) :
    ∃ a : Fin n → ℝ, Fintype.linearCombination ℝ
      (fun i : Fin n => ramanujanPacketHilbert (i.val + 2)) a = pinnedCandidate n e := by
  have hm : pinnedCandidate n e ∈ synthesisSpan
      (fun i : Fin n => ramanujanPacketHilbert (i.val + 2)) := by
    unfold pinnedCandidate
    apply Submodule.add_mem
    · exact synthesis_mem _ (packetCoefficients n)
    · rw [coordinateRepair_apply]
      apply Submodule.sum_mem
      intro j _
      exact Submodule.smul_mem _ _ (residueAtom_mem_packetSpan n (e j) (hn j))
  rwa [synthesisSpan, ← Fintype.range_linearCombination] at hm

/-- Full energy equality, including the complete signed finite repair norm. -/
theorem pinned_error_exact (n : ℕ) (e : κ ↪ ℕ) (hn : ∀ j, e j < n) :
    ‖hilbertOne - pinnedCandidate n e‖ ^ 2 = 1 - packetMass n +
      ‖coordinateRepair e (hilbertOne - packetCandidate n)‖ ^ 2 := by
  have h := pinTo_error_exact (fun j => residueAtom (e j))
    (fun j => coefficientCLM (e j + 2)) hilbertOne (packetCandidate n)
    (fun j => packet_residual_orthogonal_atom n (e j) (hn j))
  change ‖hilbertOne - pinnedCandidate n e‖ ^ 2 =
    ‖hilbertOne - packetCandidate n‖ ^ 2 +
      ‖coordinateRepair e (hilbertOne - packetCandidate n)‖ ^ 2 at h
  rwa [packet_error] at h

theorem pinned_error_bounds (n : ℕ) (e : κ ↪ ℕ) (hn : ∀ j, e j < n) :
    1 - packetMass n ≤ ‖hilbertOne - pinnedCandidate n e‖ ^ 2 ∧
    ‖hilbertOne - pinnedCandidate n e‖ ^ 2 ≤
      (1 + ‖coordinateRepair e‖ ^ 2) * (1 - packetMass n) := by
  constructor
  · rw [pinned_error_exact n e hn]
    exact le_add_of_nonneg_right (sq_nonneg _)
  · have h := pinTo_error_le (fun j => residueAtom (e j))
      (fun j => coefficientCLM (e j + 2)) hilbertOne (packetCandidate n)
      (fun j => packet_residual_orthogonal_atom n (e j) (hn j))
    change ‖hilbertOne - pinnedCandidate n e‖ ^ 2 ≤
      (1 + ‖coordinateRepair e‖ ^ 2) * ‖hilbertOne - packetCandidate n‖ ^ 2 at h
    rwa [packet_error] at h

theorem eventually_contains {α : Type*} {l : Filter α} (N : α → ℕ)
    (hN : Tendsto N l atTop) (e : κ ↪ ℕ) :
    ∀ᶠ i in l, ∀ j, e j < N i := by
  classical
  filter_upwards [hN.eventually (eventually_ge_atTop (Finset.univ.sup (fun j => e j) + 1))]
    with i hi
  intro j
  have hj : e j ≤ Finset.univ.sup (fun j => e j) := Finset.le_sup (Finset.mem_univ j)
  omega

/-- A fixed finite exact Moebius constraint costs only a bounded factor,
and hence preserves every cofinal zero-error criterion. -/
theorem pinned_cofinal_error_iff {α : Type*} {l : Filter α} [NeBot l]
    (N : α → ℕ) (hN : Tendsto N l atTop) (e : κ ↪ ℕ) :
    Tendsto (fun i => ‖hilbertOne - pinnedCandidate (N i) e‖ ^ 2) l (𝓝 0) ↔
      limitEnergy = 0 := by
  have hb : Tendsto (fun i => 1 - packetMass (N i)) l (𝓝 limitEnergy) := by
    simpa only [Function.comp_def, packet_energy_eq_original] using energy_tendsto.comp hN
  have hn := eventually_contains N hN e
  constructor
  · intro hp
    have hz : Tendsto (fun i => 1 - packetMass (N i)) l (𝓝 0) := by
      have hnonneg : ∀ᶠ i in l, 0 ≤ 1 - packetMass (N i) :=
        Filter.Eventually.of_forall (fun i => by
          rw [← packet_error]
          exact sq_nonneg _)
      have hupper : ∀ᶠ i in l, 1 - packetMass (N i) ≤
          ‖hilbertOne - pinnedCandidate (N i) e‖ ^ 2 := by
        filter_upwards [hn] with i hi
        exact (pinned_error_bounds (N i) e hi).1
      exact squeeze_zero' hnonneg hupper hp
    exact tendsto_nhds_unique hb hz
  · intro he
    have hz : Tendsto (fun i => (1 + ‖coordinateRepair e‖ ^ 2) *
        (1 - packetMass (N i))) l (𝓝 0) := by
      simpa only [he, mul_zero] using hb.const_mul (1 + ‖coordinateRepair e‖ ^ 2)
    apply squeeze_zero' (Filter.Eventually.of_forall (fun _ => sq_nonneg _)) ?_ hz
    filter_upwards [hn] with i hi
    exact (pinned_error_bounds (N i) e hi).2

theorem pinned_cofinal_coefficients_iff {α : Type*} {l : Filter α} [NeBot l]
    (N : α → ℕ) (hN : Tendsto N l atTop) (e : κ ↪ ℕ) :
    Tendsto (fun i => ‖hilbertOne - pinnedCandidate (N i) e‖ ^ 2) l (𝓝 0) ↔
      ∀ m : ℕ, 1 < m → Tendsto (fun i => packetMultipleCoefficient (N i) m) l
        (𝓝 (-(ArithmeticFunction.moebius m : ℝ))) :=
  (pinned_cofinal_error_iff N hN e).trans (packet_cofinal_coefficients_iff N hN).symm

/-- Exact finite pinning implies RH without using the converse analytic provider. -/
theorem riemannHypothesis_of_pinned_cofinal_error
    {α : Type*} {l : Filter α} [NeBot l]
    (N : α → ℕ) (hN : Tendsto N l atTop) (e : κ ↪ ℕ)
    (h : Tendsto (fun i => ‖hilbertOne - pinnedCandidate (N i) e‖ ^ 2) l (𝓝 0)) :
    RiemannHypothesis := by
  have hz := (pinned_cofinal_error_iff N hN e).mp h
  apply packet_riemannHypothesis_of_saturation
  exact (packet_cofinal_mass_iff id tendsto_id).mpr hz

theorem pinned_cofinal_rh_iff
    (hBaezDuarte : RiemannHypothesis → BaezDuarte.NaturalApproximation)
    {α : Type*} {l : Filter α} [NeBot l]
    (N : α → ℕ) (hN : Tendsto N l atTop) (e : κ ↪ ℕ) :
    Tendsto (fun i => ‖hilbertOne - pinnedCandidate (N i) e‖ ^ 2) l (𝓝 0) ↔
      RiemannHypothesis := by
  exact (pinned_cofinal_error_iff N hN e).trans
    ((packet_cofinal_mass_iff N hN).symm.trans
      (packet_cofinal_rh_equivalences hBaezDuarte N hN).1)

end RiemannResearch.RH.RamanujanFinitePinning
