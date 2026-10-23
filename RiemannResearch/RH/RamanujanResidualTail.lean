import RiemannResearch.RH.RamanujanTailRegularity
import RiemannResearch.RH.ResidualTailPNT
import RiemannResearch.RH.ExactHeadResidualTail
import RiemannResearch.RH.RamanujanCanonicalOptimizer
import RiemannResearch.Analysis.FiniteHilbertGramProjection
import Mathlib.Tactic.Linarith
import Lean.Elab.Tactic.Omega

/-!
# Complete packet residual tails and exact-head obstructions

Source: user-requested second Ramanujan transfer program, 23 October 2026.
The project's proved quantitative PNT supplies the canonical sublinear
exact-head approximation input. The new cofinal criterion works along any
map tending to infinity from a nontrivial filter. All physical tails and all
Gram displacements are retained. No bounded-tail premise is asserted.
-/

noncomputable section
open Filter
open scoped Topology BigOperators
namespace RiemannResearch.RH.RamanujanCanonicalOptimizer
open Pareto Pareto.CoefficientStabilization RamanujanTransfer
open RiemannResearch.Analysis.FiniteHilbertGram

def packetTailEnergy (N : ℕ) : ℝ := ‖hilbertTailShift packetLimitResidual N‖ ^ 2

theorem packetTailEnergy_eq (N : ℕ) : packetTailEnergy N = residualTailEnergy N := by
  simp only [packetTailEnergy, packetLimitResidual_eq, residualTailEnergy]

theorem packetTailEnergy_physical (N : ℕ) :
    packetTailEnergy N = ∑' n : ℕ, positiveWeight (n + N + 1) *
      hilbertSequence packetLimitResidual (n + N + 1) ^ 2 := by
  simpa only [packetTailEnergy_eq, packetLimitResidual_eq] using
    residualTailEnergy_eq_weighted N

theorem packetTailEnergy_tendsto_zero :
    Tendsto packetTailEnergy atTop (𝓝 0) := by
  change Tendsto (fun N => packetTailEnergy N) _ _
  simp_rw [packetTailEnergy_eq]
  exact residualTailEnergy_tendsto_zero

/-- A nonzero packet residual forces divergence of the normalized complete tail. -/
theorem packet_normalized_tail_tendsto (hne : packetLimitResidual ≠ 0) :
    Tendsto (fun N : ℕ => (N : ℝ) * packetTailEnergy N) atTop atTop := by
  have he : limitEnergy ≠ 0 := by
    intro he
    exact hne (packetLimitResidual_zero_iff_energy_zero.mpr he)
  have hp : 0 < limitEnergy := lt_of_le_of_ne (sq_nonneg _) (Ne.symm he)
  simpa only [packetTailEnergy_eq] using normalized_residual_tail_tendsto_atTop hp

theorem packet_tail_dichotomy :
    packetLimitResidual = 0 ∨
      Tendsto (fun N : ℕ => (N : ℝ) * packetTailEnergy N) atTop atTop := by
  by_cases hz : packetLimitResidual = 0
  · exact Or.inl hz
  · exact Or.inr (packet_normalized_tail_tendsto hz)

/-- Frequent boundedness is enough along every cofinal map and nontrivial filter. -/
theorem packet_cofinal_tail_bounded_iff {α : Type*} {l : Filter α} [NeBot l]
    (N : α → ℕ) (hN : Tendsto N l atTop) :
    (∃ C : ℝ, ∃ᶠ i in l, (N i : ℝ) * packetTailEnergy (N i) ≤ C) ↔
      packetLimitResidual = 0 := by
  constructor
  · rintro ⟨C, hC⟩
    by_contra hne
    have ht := (packet_normalized_tail_tendsto hne).comp hN
    have hg : ∀ᶠ i in l, C + 1 ≤ (N i : ℝ) * packetTailEnergy (N i) :=
      ht.eventually (eventually_ge_atTop (C + 1))
    obtain ⟨i, hi, hgi⟩ := (hC.and_eventually hg).exists
    linarith
  · intro hz
    refine ⟨0, (Eventually.of_forall ?_).frequently⟩
    intro i
    have ht : hilbertTailShift packetLimitResidual (N i) = 0 := by
      ext n
      simp [hilbertTailShift, hz]
    simp [packetTailEnergy, ht]

theorem packet_cofinal_tail_bounded_iff_mass {α : Type*} {l : Filter α} [NeBot l]
    (N : α → ℕ) (hN : Tendsto N l atTop) :
    (∃ C : ℝ, ∃ᶠ i in l, (N i : ℝ) * packetTailEnergy (N i) ≤ C) ↔
      Tendsto packetMass atTop (𝓝 1) :=
  (packet_cofinal_tail_bounded_iff N hN).trans
    (packetLimitResidual_zero_iff_energy_zero.trans
      (packet_cofinal_mass_iff id tendsto_id).symm)

/-- Every finite packet competitor is in the actual complete legal space. -/
theorem packetSynthesis_mem_closedSpace (L : ℕ) (a : Fin L → ℝ) :
    Fintype.linearCombination ℝ
      (fun i : Fin L => ramanujanPacketHilbert (i.val + 2)) a ∈ closedSpace := by
  have hf := synthesis_mem
    (fun i : Fin L => ramanujanPacketHilbert (i.val + 2)) a
  change Fintype.linearCombination ℝ
      (fun i : Fin L => ramanujanPacketHilbert (i.val + 2)) a ∈
    Submodule.span ℝ (Set.range
      (fun i : Fin L => ramanujanPacketHilbert (i.val + 2))) at hf
  have hs : Set.range (fun i : Fin L => ramanujanPacketHilbert (i.val + 2)) ⊆
      ramanujanPacketHilbert '' {q : ℕ | 1 < q} := by
    rintro _ ⟨i, rfl⟩
    exact ⟨i.val + 2, by change 1 < i.val + 2; omega, rfl⟩
  rw [← p_fullPacketClosedSpan_eq_closedSpace]
  exact Submodule.le_topologicalClosure _ ((Submodule.span_mono hs) hf)

/-- The exact-head obstruction contains the full canonical error AND Gram excess. -/
theorem packet_exact_head_product (N L : ℕ) (a : Fin L → ℝ)
    (hhead : ∀ k, 0 < k → k ≤ N →
      hilbertSequence (Fintype.linearCombination ℝ
        (fun i : Fin L => ramanujanPacketHilbert (i.val + 2)) a) k = 1) :
    limitEnergy ^ 2 ≤ packetTailEnergy N *
      (1 - packetMass L + ‖Fintype.linearCombination ℝ
        (fun i : Fin L => ramanujanPacketHilbert (i.val + 2))
        (a - packetCoefficients L)‖ ^ 2) := by
  have h := residual_tail_product_lower N (packetSynthesis_mem_closedSpace L a) hhead
  simpa only [packetTailEnergy_eq, packet_completion] using h

/-- Nonzero limiting energy forces every growing exact-head packet error to diverge. -/
theorem packet_exact_head_errors_tendsto (hpos : 0 < limitEnergy)
    (L : ℕ → ℕ) (a : (N : ℕ) → Fin (L N) → ℝ)
    (hhead : ∀ N k, 0 < k → k ≤ N →
      hilbertSequence (Fintype.linearCombination ℝ
        (fun i : Fin (L N) => ramanujanPacketHilbert (i.val + 2)) (a N)) k = 1) :
    Tendsto (fun N => 1 - packetMass (L N) + ‖Fintype.linearCombination ℝ
      (fun i : Fin (L N) => ramanujanPacketHilbert (i.val + 2))
      (a N - packetCoefficients (L N))‖ ^ 2) atTop atTop := by
  have hE : 0 < limitEnergy ^ 2 := sq_pos_of_pos hpos
  apply tendsto_atTop.mpr
  intro B
  let D : ℝ := max B 0 + 1
  have hD : 0 < D := by dsimp [D]; linarith [le_max_right B 0]
  have ht := packetTailEnergy_tendsto_zero.eventually_lt_const (div_pos hE hD)
  filter_upwards [ht] with N hN
  by_contra hn
  have hsmall : 1 - packetMass (L N) + ‖Fintype.linearCombination ℝ
      (fun i : Fin (L N) => ramanujanPacketHilbert (i.val + 2))
      (a N - packetCoefficients (L N))‖ ^ 2 ≤ D := by
    dsimp [D]
    linarith [lt_of_not_ge hn, le_max_left B 0]
  have hm := mul_le_mul_of_nonneg_left hsmall (sq_nonneg
    ‖hilbertTailShift packetLimitResidual N‖)
  have hh := packet_exact_head_product N (L N) (a N) (hhead N)
  have hstrict := (lt_div_iff₀ hD).mp hN
  change packetTailEnergy N * _ ≤ packetTailEnergy N * D at hm
  exact (not_lt_of_ge (hh.trans hm)) hstrict

theorem packet_cofinal_tail_bounded_iff_rh {α : Type*} {l : Filter α} [NeBot l]
    (hBaezDuarte : RiemannHypothesis → BaezDuarte.NaturalApproximation)
    (N : α → ℕ) (hN : Tendsto N l atTop) :
    (∃ C : ℝ, ∃ᶠ i in l, (N i : ℝ) * packetTailEnergy (N i) ≤ C) ↔
      RiemannHypothesis :=
  (packet_cofinal_tail_bounded_iff_mass N hN).trans
    (packet_cofinal_rh_equivalences hBaezDuarte id tendsto_id).1

end RiemannResearch.RH.RamanujanCanonicalOptimizer
