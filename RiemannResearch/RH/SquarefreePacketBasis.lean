/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.ArithmeticPacketCore
import RiemannResearch.RH.MeanOneRepair
import RiemannResearch.RH.ParetoArithmeticRepair
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Exact finite squarefree residue and packet basis transfer

Source: user-directed continuation of `PhysicalMeanOneAdvance20261008.md`.
The two transforms are actual finite divisor/Möbius inversion. Their equalities
hold in the physical sequence, hence in the complete Pareto norm. The ordinary
mean is transferred as a literal common-period mean; no approximation or RH
hypothesis is used in these finite identities.
-/

noncomputable section
open scoped BigOperators
open Matrix
namespace RiemannResearch.RH.Pareto.SquarefreePacketBasis
open PhysicalPacketCore MeanOneRepair BaezDuarte
open RiemannResearch.Probability.ConditionalIID (cesaro)

/-- Incidence transform from normalized residues to unnormalized packets. -/
def packetCoefficients (L : ℕ) (s : Finset ℕ) (a : ℕ → ℝ)
    (q : divisorPackets L) : ℝ :=
  ∑ d ∈ s, if q.val ∣ d then a d / (d : ℝ) else 0

private theorem period_packet_filter (L d : ℕ) (hL : 0 < L) (hd : 0 < d)
    (hdL : d ∣ L) :
    (divisorPackets L).filter (fun q => q ∣ d) =
      d.divisors.filter (fun q => 1 < q) := by
  classical
  ext q
  constructor
  · intro hq
    obtain ⟨hqL, hqd⟩ := Finset.mem_filter.mp hq
    obtain ⟨_, hq1⟩ := Finset.mem_filter.mp hqL
    exact Finset.mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨hqd, ne_of_gt hd⟩, hq1⟩
  · intro hq
    obtain ⟨hqd, hq1⟩ := Finset.mem_filter.mp hq
    have hdiv : q ∣ d := Nat.dvd_of_mem_divisors hqd
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_filter.mpr
        ⟨Nat.mem_divisors.mpr ⟨dvd_trans hdiv hdL, ne_of_gt hL⟩, hq1⟩, hdiv⟩

theorem period_packet_divisor_sum (L d k : ℕ) (hL : 0 < L) (hd : 0 < d)
    (hdL : d ∣ L) :
    (∑ q : divisorPackets L, if q.val ∣ d then ramanujanPacket q.val k else 0) =
      residue d k := by
  classical
  rw [Finset.sum_coe_sort (divisorPackets L)
    (fun q => if q ∣ d then ramanujanPacket q k else 0),
    ← Finset.sum_filter, period_packet_filter L d hL hd hdL]
  exact ramanujanPacket_divisor_sum_gt_one d k hd

/-- Every finite normalized-residue sum on divisors of a positive period
is the literal synthesis of the full packet dictionary for that period. -/
theorem residueSum_sequence_eq_synthesis (L : ℕ) (s : Finset ℕ) (a : ℕ → ℝ)
    (hL : 0 < L) (hs : ∀ d ∈ s, 0 < d) (hdiv : ∀ d ∈ s, d ∣ L) :
    hilbertSequence (finiteResidueSum s a) =
      synthesis (divisorPackets L) (packetCoefficients L s a) := by
  classical
  funext k
  rw [finiteResidueSum_sequence s a hs k]
  unfold synthesis FiniteSchur.combination packetCoefficients
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d hd
  calc
    a d * (((k % d : ℕ) : ℝ) / (d : ℝ)) =
        (a d / (d : ℝ)) * residue d k := by unfold residue; ring
    _ = (a d / (d : ℝ)) *
        ∑ q : divisorPackets L, if q.val ∣ d then ramanujanPacket q.val k else 0 := by
      rw [period_packet_divisor_sum L d k hL (hs d hd) (hdiv d hd)]
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro q hq
      split_ifs <;> ring

/-- Complete physical error agrees with the complete Hilbert squared norm,
including the zero-anchor convention. -/
theorem hilbert_target_error (f : ThresholdHilbert) :
    paretoError (hilbertSequence f) = ‖hilbertOne - f‖ ^ 2 := by
  rw [hilbert_norm_weighted_sq]
  unfold paretoError paretoInner
  apply tsum_congr
  intro k
  by_cases hk : k = 0
  · subst k
    simp [positiveWeight]
  · have hsub := congrFun (hilbertSequenceLinear.map_sub hilbertOne f) k
    change hilbertSequence (hilbertOne - f) k =
      hilbertSequence hilbertOne k - hilbertSequence f k at hsub
    rw [hsub, hilbertOne_sequence]
    simp only [zeroAnchor, hk, if_false]
    ring

theorem residueSum_error_eq_synthesis (L : ℕ) (s : Finset ℕ) (a : ℕ → ℝ)
    (hL : 0 < L) (hs : ∀ d ∈ s, 0 < d) (hdiv : ∀ d ∈ s, d ∣ L) :
    paretoError (synthesis (divisorPackets L) (packetCoefficients L s a)) =
      ‖hilbertOne - finiteResidueSum s a‖ ^ 2 := by
  rw [← residueSum_sequence_eq_synthesis L s a hL hs hdiv]
  exact hilbert_target_error _

private theorem cesaro_eq_fin_mean (f : ℕ → ℝ) (L : ℕ)
    (hf0 : f 0 = 0) (hfL : f L = 0) :
    cesaro f L = (∑ r : Fin L, f r.val) / (L : ℝ) := by
  classical
  unfold cesaro
  rw [Fin.sum_univ_eq_sum_range]
  congr 1
  have hleft : (∑ n ∈ Finset.Icc 1 L, f n) = ∑ n ∈ Finset.Icc 0 L, f n := by
    apply Finset.sum_subset
    · intro n hn
      simp only [Finset.mem_Icc] at hn ⊢
      omega
    · intro n hn hnot
      have hn0 : n = 0 := by
        simp only [Finset.mem_Icc] at hn hnot
        omega
      simpa only [hn0] using hf0
  have hright : (∑ n ∈ Finset.range L, f n) = ∑ n ∈ Finset.Icc 0 L, f n := by
    apply Finset.sum_subset
    · intro n hn
      simp only [Finset.mem_range, Finset.mem_Icc] at hn ⊢
      omega
    · intro n hn hnot
      have hnL : n = L := by
        simp only [Finset.mem_Icc, Finset.mem_range] at hn hnot
        omega
      simpa only [hnL] using hfL
  exact hleft.trans hright.symm

private theorem synthesis_zero (L : ℕ) (c : divisorPackets L → ℝ) :
    synthesis (divisorPackets L) c 0 = 0 := by
  simp [synthesis, FiniteSchur.combination, ramanujanPacket, residue]

/-- The coefficient transform preserves the actual ordinary mean. -/
theorem packetCoefficients_totient (L : ℕ) (s : Finset ℕ) (a : ℕ → ℝ)
    (hL : 0 < L) (hs : ∀ d ∈ s, 0 < d) (hdiv : ∀ d ∈ s, d ∣ L) :
    ramanujanTotientVector (divisorPackets L) ⬝ᵥ packetCoefficients L s a =
      2 * packetOrdinaryMean s a := by
  have hm := packetOrdinaryMean_eq_cesaro s a hs L hL hdiv
  rw [residueSum_sequence_eq_synthesis L s a hL hs hdiv,
    cesaro_eq_fin_mean _ L (synthesis_zero L _)
      (synthesis_zero_at_common_multiple _ _ L (divisorPackets_period L)),
    synthesis_period_mean L (divisorPackets L)
      (packetCoefficients L s a) hL (divisorPackets_legal L)
      (divisorPackets_period L)] at hm
  linarith

/-- The signed inverse transform into normalized residue coefficients.
The support is all divisors of `L`; the harmless index one gives a zero atom. -/
def residueCoefficients (L : ℕ) (c : divisorPackets L → ℝ) (d : ℕ) : ℝ :=
  (d : ℝ) * ∑ q : divisorPackets L,
    if d ∣ q.val then c q * (ArithmeticFunction.moebius (q.val / d) : ℝ) else 0

private theorem period_divisor_filter (L q : ℕ) (hL : 0 < L) (hq : 0 < q)
    (hqL : q ∣ L) : L.divisors.filter (fun d => d ∣ q) = q.divisors := by
  classical
  ext d
  constructor
  · intro hd
    obtain ⟨_, hdq⟩ := Finset.mem_filter.mp hd
    exact Nat.mem_divisors.mpr ⟨hdq, ne_of_gt hq⟩
  · intro hd
    have hdq := Nat.dvd_of_mem_divisors hd
    exact Finset.mem_filter.mpr
      ⟨Nat.mem_divisors.mpr ⟨dvd_trans hdq hqL, ne_of_gt hL⟩, hdq⟩

/-- The complete signed Möbius inverse realizes every finite packet synthesis
as a normalized-residue Hilbert vector with the same physical sequence. -/
theorem synthesis_eq_residueSum_sequence (L : ℕ) (c : divisorPackets L → ℝ)
    (hL : 0 < L) :
    synthesis (divisorPackets L) c =
      hilbertSequence (finiteResidueSum L.divisors (residueCoefficients L c)) := by
  classical
  have hs : ∀ d ∈ L.divisors, 0 < d := fun _ hd => Nat.pos_of_mem_divisors hd
  funext k
  rw [finiteResidueSum_sequence L.divisors (residueCoefficients L c) hs k]
  have hterm (d : ℕ) (hd : d ∈ L.divisors) :
      residueCoefficients L c d * (((k % d : ℕ) : ℝ) / (d : ℝ)) =
        ∑ q : divisorPackets L,
          if d ∣ q.val then c q * (ArithmeticFunction.moebius (q.val / d) : ℝ) *
            residue d k else 0 := by
    have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt (hs d hd))
    unfold residueCoefficients
    rw [Finset.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro q hq
    unfold residue
    split_ifs <;> field_simp [hd0] <;> ring
  have he :
      (∑ d ∈ L.divisors, residueCoefficients L c d *
        (((k % d : ℕ) : ℝ) / (d : ℝ))) =
      ∑ d ∈ L.divisors, ∑ q : divisorPackets L,
        if d ∣ q.val then c q * (ArithmeticFunction.moebius (q.val / d) : ℝ) *
          residue d k else 0 := Finset.sum_congr rfl hterm
  rw [he, Finset.sum_comm]
  unfold synthesis FiniteSchur.combination
  apply Finset.sum_congr rfl
  intro q hq
  rw [← Finset.sum_filter,
    period_divisor_filter L q.val hL
      (by have h := divisorPackets_legal L q.val q.property; omega)
      (divisorPackets_period L q.val q.property)]
  unfold ramanujanPacket
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d hd
  ring

theorem synthesis_error_eq_residueSum (L : ℕ) (c : divisorPackets L → ℝ)
    (hL : 0 < L) :
    paretoError (synthesis (divisorPackets L) c) =
      ‖hilbertOne - finiteResidueSum L.divisors (residueCoefficients L c)‖ ^ 2 := by
  rw [synthesis_eq_residueSum_sequence L c hL]
  exact hilbert_target_error _

theorem residueCoefficients_mean (L : ℕ) (c : divisorPackets L → ℝ)
    (hL : 0 < L) :
    packetOrdinaryMean L.divisors (residueCoefficients L c) =
      (ramanujanTotientVector (divisorPackets L) ⬝ᵥ c) / 2 := by
  rw [← packetOrdinaryMean_eq_cesaro L.divisors (residueCoefficients L c)
    (fun _ hd => Nat.pos_of_mem_divisors hd) L hL
    (fun _ hd => Nat.dvd_of_mem_divisors hd),
    ← synthesis_eq_residueSum_sequence L c hL,
    cesaro_eq_fin_mean _ L (synthesis_zero L c)
      (synthesis_zero_at_common_multiple _ _ L (divisorPackets_period L)),
    synthesis_period_mean L (divisorPackets L) c hL
      (divisorPackets_legal L) (divisorPackets_period L)]

/-- Squarefree periods give genuinely squarefree normalized-residue support. -/
theorem period_divisors_squarefree (L : ℕ) (hsq : Squarefree L) :
    ∀ d ∈ L.divisors, Squarefree d := by
  intro d hd
  exact Squarefree.squarefree_of_dvd (Nat.dvd_of_mem_divisors hd) hsq

end RiemannResearch.RH.Pareto.SquarefreePacketBasis
