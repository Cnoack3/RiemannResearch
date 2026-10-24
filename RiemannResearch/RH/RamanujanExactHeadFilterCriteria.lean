import RiemannResearch.RH.RamanujanResidualTail
import RiemannResearch.RH.RamanujanSaturationCriteria
import Mathlib.Tactic.Linarith

/-!
# Arbitrary-filter exact-head Ramanujan tail criteria

Source: user-requested third Ramanujan transfer program, 23 October 2026.
These results strengthen the existing exact-head tail-product obstruction.
The main criterion needs only frequent simultaneous exact-head and small-product
trials; it assumes neither cofinality nor eventual exact-head interpolation.
Its converse retains the existence of frequent exact-head trials explicitly.
Every product contains the complete physical tail and the full Gram excess.
No small-product, bounded-error, or exact-head-family existence premise is proved.
-/

noncomputable section
open Filter
open scoped Topology BigOperators

namespace RiemannResearch.RH.RamanujanCanonicalOptimizer
open Pareto Pareto.CoefficientStabilization

def PacketExactHead (N L : ℕ) (a : Fin L → ℝ) : Prop :=
  ∀ k, 0 < k → k ≤ N → hilbertSequence
    (Fintype.linearCombination ℝ
      (fun j : Fin L => ramanujanPacketHilbert (j.val + 2)) a) k = 1

/-- The full trial error, retaining the displacement from the actual optimizer. -/
def packetTrialEnergy (L : ℕ) (a : Fin L → ℝ) : ℝ :=
  1 - packetMass L + ‖Fintype.linearCombination ℝ
    (fun j : Fin L => ramanujanPacketHilbert (j.val + 2))
    (a - packetCoefficients L)‖ ^ 2

theorem packetTrialEnergy_eq_error (L : ℕ) (a : Fin L → ℝ) :
    packetTrialEnergy L a = ‖hilbertOne - Fintype.linearCombination ℝ
      (fun j : Fin L => ramanujanPacketHilbert (j.val + 2)) a‖ ^ 2 :=
  (packet_completion L a).symm

theorem packetTrialEnergy_nonneg (L : ℕ) (a : Fin L → ℝ) :
    0 ≤ packetTrialEnergy L a := by
  rw [packetTrialEnergy_eq_error]
  exact sq_nonneg _

def packetTailProduct (N L : ℕ) (a : Fin L → ℝ) : ℝ :=
  packetTailEnergy N * packetTrialEnergy L a

theorem packetTailProduct_physical (N L : ℕ) (a : Fin L → ℝ) :
    packetTailProduct N L a =
      (∑' n : ℕ, positiveWeight (n + N + 1) *
        hilbertSequence packetLimitResidual (n + N + 1) ^ 2) *
      (1 - packetMass L + ‖Fintype.linearCombination ℝ
        (fun j : Fin L => ramanujanPacketHilbert (j.val + 2))
        (a - packetCoefficients L)‖ ^ 2) := by
  rw [packetTailProduct, packetTailEnergy_physical]
  rfl

theorem packetTailProduct_zero_of_residual_zero
    (hz : packetLimitResidual = 0) (N L : ℕ) (a : Fin L → ℝ) :
    packetTailProduct N L a = 0 := by
  have ht : hilbertTailShift packetLimitResidual N = 0 := by
    ext n
    simp [hilbertTailShift, hz]
  simp [packetTailProduct, packetTailEnergy, ht]

variable {α : Type*} {l : Filter α} [NeBot l]

omit [NeBot l] in
/-- No cofinality or eventual exact-head hypothesis is needed. The frequent
existence of exact-head trials is retained on the converse side. -/
theorem packet_frequent_exact_head_small_product_iff
    (N L : α → ℕ) (a : (i : α) → Fin (L i) → ℝ) :
    (∀ ε : ℝ, 0 < ε → ∃ᶠ i in l,
      PacketExactHead (N i) (L i) (a i) ∧
        packetTailProduct (N i) (L i) (a i) < ε) ↔
      packetLimitResidual = 0 ∧
        ∃ᶠ i in l, PacketExactHead (N i) (L i) (a i) := by
  constructor
  · intro h
    have hh : ∃ᶠ i in l, PacketExactHead (N i) (L i) (a i) :=
      (h 1 zero_lt_one).mono (fun _ hi => hi.1)
    refine ⟨?_, hh⟩
    by_contra hne
    have he : limitEnergy ≠ 0 := fun he =>
      hne (packetLimitResidual_zero_iff_energy_zero.mpr he)
    have hp : 0 < limitEnergy := lt_of_le_of_ne (sq_nonneg _) (Ne.symm he)
    obtain ⟨i, hhead, hsmall⟩ := (h (limitEnergy ^ 2) (sq_pos_of_pos hp)).exists
    have hb := packet_exact_head_product (N i) (L i) (a i) hhead
    exact (not_lt_of_ge hb) hsmall
  · rintro ⟨hz, hh⟩ ε hε
    exact hh.mono fun i hi => ⟨hi, by
      simpa only [packetTailProduct_zero_of_residual_zero hz] using hε⟩

omit [NeBot l] in
/-- The forward RH implication requires no converse analytic provider. -/
theorem riemannHypothesis_of_frequent_exact_head_small_product
    (N L : α → ℕ) (a : (i : α) → Fin (L i) → ℝ)
    (hsmall : ∀ ε : ℝ, 0 < ε → ∃ᶠ i in l,
      PacketExactHead (N i) (L i) (a i) ∧
        packetTailProduct (N i) (L i) (a i) < ε) : RiemannHypothesis := by
  have hz := ((packet_frequent_exact_head_small_product_iff (l := l) N L a).mp hsmall).1
  apply packet_riemannHypothesis_of_saturation
  exact (packet_cofinal_mass_iff id tendsto_id).mpr
    (packetLimitResidual_zero_iff_energy_zero.mp hz)

theorem packet_small_product_iff_residual_zero
    (N L : α → ℕ) (a : (i : α) → Fin (L i) → ℝ)
    (hhead : ∀ᶠ i in l, PacketExactHead (N i) (L i) (a i)) :
    (∀ ε : ℝ, 0 < ε → ∃ᶠ i in l,
      packetTailProduct (N i) (L i) (a i) < ε) ↔ packetLimitResidual = 0 := by
  constructor
  · intro h
    apply ((packet_frequent_exact_head_small_product_iff (l := l) N L a).mp ?_).1
    intro ε hε
    exact ((h ε hε).and_eventually hhead).mono (fun _ hi => ⟨hi.2, hi.1⟩)
  · intro hz ε hε
    exact (Eventually.of_forall fun i => by
      simpa only [packetTailProduct_zero_of_residual_zero hz] using hε).frequently

theorem packet_tail_product_tendsto_zero_iff
    (N L : α → ℕ) (a : (i : α) → Fin (L i) → ℝ)
    (hhead : ∀ᶠ i in l, PacketExactHead (N i) (L i) (a i)) :
    Tendsto (fun i => packetTailProduct (N i) (L i) (a i)) l (𝓝 0) ↔
      packetLimitResidual = 0 := by
  constructor
  · intro h
    apply (packet_small_product_iff_residual_zero N L a hhead).mp
    intro ε hε
    exact (h.eventually_lt_const hε).frequently
  · intro hz
    simp_rw [packetTailProduct_zero_of_residual_zero hz]
    exact tendsto_const_nhds

/-- A moving arithmetic budget need only dominate the complete trial error
frequently; its tail product tends to zero. Neither map must be cofinal. -/
theorem packet_residual_zero_of_frequent_budget
    (N L : α → ℕ) (a : (i : α) → Fin (L i) → ℝ) (B : α → ℝ)
    (hhead : ∀ᶠ i in l, PacketExactHead (N i) (L i) (a i))
    (hbudget : Tendsto (fun i => packetTailEnergy (N i) * B i) l (𝓝 0))
    (hbound : ∃ᶠ i in l, packetTrialEnergy (L i) (a i) ≤ B i) :
    packetLimitResidual = 0 := by
  apply (packet_small_product_iff_residual_zero N L a hhead).mp
  intro ε hε
  have hsmall := hbudget.eventually_lt_const hε
  apply (hbound.and_eventually hsmall).mono
  intro i hi
  have hm := mul_le_mul_of_nonneg_left hi.1
    (sq_nonneg ‖hilbertTailShift packetLimitResidual (N i)‖)
  exact lt_of_le_of_lt hm hi.2

omit [NeBot l] in
/-- The exact-head divergence obstruction works on every cofinal filter and
needs exact interpolation only eventually. -/
theorem packet_cofinal_exact_head_error_tendsto
    (hne : packetLimitResidual ≠ 0)
    (N L : α → ℕ) (a : (i : α) → Fin (L i) → ℝ)
    (hN : Tendsto N l atTop)
    (hhead : ∀ᶠ i in l, PacketExactHead (N i) (L i) (a i)) :
    Tendsto (fun i => packetTrialEnergy (L i) (a i)) l atTop := by
  have he : limitEnergy ≠ 0 := fun he =>
    hne (packetLimitResidual_zero_iff_energy_zero.mpr he)
  have hp : 0 < limitEnergy := lt_of_le_of_ne (sq_nonneg _) (Ne.symm he)
  have hE : 0 < limitEnergy ^ 2 := sq_pos_of_pos hp
  apply tendsto_atTop.mpr
  intro B
  let D : ℝ := max B 0 + 1
  have hD : 0 < D := by dsimp [D]; linarith [le_max_right B 0]
  have ht := (packetTailEnergy_tendsto_zero.comp hN).eventually_lt_const
    (div_pos hE hD)
  filter_upwards [ht, hhead] with i hi hhi
  by_contra hn
  have hsmall : packetTrialEnergy (L i) (a i) ≤ D := by
    dsimp [D]
    linarith [lt_of_not_ge hn, le_max_left B 0]
  have hm := mul_le_mul_of_nonneg_left hsmall
    (sq_nonneg ‖hilbertTailShift packetLimitResidual (N i)‖)
  have hh := packet_exact_head_product (N i) (L i) (a i) hhi
  have hstrict := (lt_div_iff₀ hD).mp hi
  change packetTailEnergy (N i) * packetTrialEnergy (L i) (a i) ≤
    packetTailEnergy (N i) * D at hm
  exact (not_lt_of_ge (hh.trans hm)) hstrict

omit [NeBot l] in
/-- Arbitrary trials may still diverge when the residual vanishes, so this
frequent bounded-error test is an implication, not a false equivalence. -/
theorem packet_residual_zero_of_frequent_bounded_error
    (N L : α → ℕ) (a : (i : α) → Fin (L i) → ℝ)
    (hN : Tendsto N l atTop)
    (hhead : ∀ᶠ i in l, PacketExactHead (N i) (L i) (a i))
    (hbound : ∃ C : ℝ, ∃ᶠ i in l, packetTrialEnergy (L i) (a i) ≤ C) :
    packetLimitResidual = 0 := by
  by_contra hne
  obtain ⟨C, hC⟩ := hbound
  have ht := packet_cofinal_exact_head_error_tendsto hne N L a hN hhead
  have hg := ht.eventually (eventually_ge_atTop (C + 1))
  obtain ⟨i, hi, hgi⟩ := (hC.and_eventually hg).exists
  linarith

theorem packet_tail_product_tendsto_iff_mass
    (N L : α → ℕ) (a : (i : α) → Fin (L i) → ℝ)
    (hhead : ∀ᶠ i in l, PacketExactHead (N i) (L i) (a i)) :
    Tendsto (fun i => packetTailProduct (N i) (L i) (a i)) l (𝓝 0) ↔
      Tendsto packetMass atTop (𝓝 1) :=
  (packet_tail_product_tendsto_zero_iff N L a hhead).trans
    (packetLimitResidual_zero_iff_energy_zero.trans
      (packet_cofinal_mass_iff id tendsto_id).symm)

theorem packet_tail_product_tendsto_iff_rh
    (hBaezDuarte : RiemannHypothesis → BaezDuarte.NaturalApproximation)
    (N L : α → ℕ) (a : (i : α) → Fin (L i) → ℝ)
    (hhead : ∀ᶠ i in l, PacketExactHead (N i) (L i) (a i)) :
    Tendsto (fun i => packetTailProduct (N i) (L i) (a i)) l (𝓝 0) ↔
      RiemannHypothesis :=
  (packet_tail_product_tendsto_iff_mass N L a hhead).trans
    (packet_cofinal_rh_equivalences hBaezDuarte id tendsto_id).1

end RiemannResearch.RH.RamanujanCanonicalOptimizer
