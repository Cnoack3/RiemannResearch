/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.Analysis.FullSupportPerturbation
import RiemannResearch.RH.QRamanujanPackets
import RiemannResearch.RH.ParetoPrimePackets
import RiemannResearch.RH.ParetoPacketGreenGram
import RiemannResearch.RH.ZetaTwoCRTSquarefreeConverse
import Mathlib.Data.Nat.Prime.Infinite
import Mathlib.Data.Nat.Squarefree
import Mathlib.Tactic.Abel
import Mathlib.Tactic.Choose
import Mathlib.Tactic.NormNum
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Filling finite squarefree Ramanujan support while preserving exact heads
Source: the user's full-support construction request, 30 October 2026.
A fresh prime gives B_q + B_(pq) = p B_q(floor(n/p)), hence an exact
zero-head direction. Perturbations can have arbitrarily small complete Q norm.
No arithmetic energy-growth estimate or RH conclusion is assumed here.
-/

namespace RiemannResearch.RH.QRamanujanFullSupport
open ZetaTwoHilbert ZetaTwoProbability QRamanujanPackets
open RiemannResearch.Analysis.FullSupportPerturbation
open scoped BigOperators
noncomputable section

theorem packet_mem_squarefree (q : ℕ) (hsf : Squarefree q) :
    qRamanujanPacket q ∈ qSquarefreeCRTSpan := by
  unfold qRamanujanPacket
  apply Submodule.sum_mem
  intro d hd
  apply Submodule.smul_mem
  by_cases hd1 : d = 1
  · rw [hd1, qResidue_one]
    exact Submodule.zero_mem _
  · exact Submodule.subset_span
      ⟨⟨d, by have := Nat.pos_of_mem_divisors hd; omega,
        hsf.squarefree_of_dvd (Nat.dvd_of_mem_divisors hd)⟩, rfl⟩

theorem fresh_packet_sequence (p q n : ℕ) (hp : p.Prime) (hq : 1 < q)
    (hpq : ¬p ∣ q) :
    qSequence (qRamanujanPacket q + qRamanujanPacket (p * q)) n =
      (p : ℝ) * Pareto.ramanujanPacket q (n / p) := by
  change qSequenceLinear (_ + _) n = _
  simp only [map_add, Pi.add_apply]
  change qSequence (qRamanujanPacket q) n + qSequence (qRamanujanPacket (p * q)) n = _
  rw [qSequence_qRamanujanPacket, qSequence_qRamanujanPacket]
  rw [Pareto.ramanujanPacket_mul_prime_of_not_dvd p q n hp hq hpq]
  unfold Pareto.dilation
  ring

def direction (s : Finset ℕ) (p : ℕ) : QHilbert :=
  ∑ q ∈ s, (qRamanujanPacket q + qRamanujanPacket (p * q))

def perturb (s : Finset ℕ) (b : ℕ → ℝ) (p : ℕ) (t : ℝ) : QHilbert :=
  (∑ q ∈ s, (b q + t) • qRamanujanPacket q) +
    ∑ q ∈ s, t • qRamanujanPacket (p * q)

theorem perturb_eq (s : Finset ℕ) (b : ℕ → ℝ) (p : ℕ) (t : ℝ) :
    perturb s b p t = (∑ q ∈ s, b q • qRamanujanPacket q) + t • direction s p := by
  simp only [perturb, direction, add_smul, Finset.sum_add_distrib,
    Finset.smul_sum, smul_add]
  abel

theorem direction_head (s : Finset ℕ) (p n : ℕ) (hp : p.Prime)
    (hs : ∀ q ∈ s, 1 < q ∧ q < p) (hn : n < p) :
    qSequence (direction s p) n = 0 := by
  change qSequenceLinear (∑ q ∈ s, _) n = 0
  rw [map_sum]
  simp only [Finset.sum_apply]
  change (∑ q ∈ s, qSequence (qRamanujanPacket q + qRamanujanPacket (p * q)) n) = 0
  apply Finset.sum_eq_zero
  intro q hq
  rw [fresh_packet_sequence p q n hp (hs q hq).1
    (Nat.not_dvd_of_pos_of_lt (by have := (hs q hq).1; omega) (hs q hq).2), Nat.div_eq_of_lt hn]
  simp [Pareto.ramanujanPacket, Pareto.residue]

theorem perturb_head (s : Finset ℕ) (b : ℕ → ℝ) (p n : ℕ) (t : ℝ)
    (hp : p.Prime) (hs : ∀ q ∈ s, 1 < q ∧ q < p) (hn : n < p) :
    qSequence (perturb s b p t) n =
      qSequence (∑ q ∈ s, b q • qRamanujanPacket q) n := by
  rw [perturb_eq]
  change qSequenceLinear (_ + _ • _) n = _
  simp only [map_add, map_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  change _ + t * qSequence (direction s p) n = _
  rw [direction_head s p n hp hs hn, mul_zero, add_zero]
  rfl

theorem perturb_legal (s : Finset ℕ) (b : ℕ → ℝ) (p : ℕ) (t : ℝ)
    (hp : p.Prime) (hs : ∀ q ∈ s, 1 < q ∧ q < p ∧ Squarefree q) :
    perturb s b p t ∈ qSquarefreeCRTSpan := by
  apply Submodule.add_mem
  · apply Submodule.sum_mem
    intro q hq
    exact Submodule.smul_mem _ _ (packet_mem_squarefree q (hs q hq).2.2)
  · apply Submodule.sum_mem
    intro q hq
    apply Submodule.smul_mem
    apply packet_mem_squarefree
    exact Nat.squarefree_mul_iff.mpr
      ⟨hp.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt
        (by have := (hs q hq).1; omega) (hs q hq).2.1), hp.squarefree, (hs q hq).2.2⟩

theorem exists_full_support_perturbation (s : Finset ℕ) (b : ℕ → ℝ) (H : ℕ)
    (hs : ∀ q ∈ s, 1 < q ∧ Squarefree q) (ε : ℝ) (hε : 0 < ε) :
    ∃ p : ℕ, p.Prime ∧ H < p ∧ (∀ q ∈ s, q < p) ∧
      ∃ t : ℝ, 0 < t ∧ (∀ q ∈ s, b q + t ≠ 0) ∧
        perturb s b p t ∈ qSquarefreeCRTSpan ∧
        ‖perturb s b p t - ∑ q ∈ s, b q • qRamanujanPacket q‖ < ε ∧
        ∀ n, n ≤ H → qSequence (perturb s b p t) n =
          qSequence (∑ q ∈ s, b q • qRamanujanPacket q) n := by
  obtain ⟨p, hpb, hp⟩ := Nat.exists_infinite_primes (H + s.sup id + 1)
  have hqp : ∀ q ∈ s, q < p := by
    intro q hq
    have hqle : q ≤ s.sup id := Finset.le_sup (f := id) hq
    omega
  have hs' : ∀ q ∈ s, 1 < q ∧ q < p ∧ Squarefree q :=
    fun q hq => ⟨(hs q hq).1, hqp q hq, (hs q hq).2⟩
  obtain ⟨t, ht, hnorm, hcoeff⟩ := exists_small_step s b (fun _ => 1)
    (by intro q hq; norm_num) (direction s p) ε hε
  refine ⟨p, hp, by omega, hqp, t, ht, ?_, perturb_legal s b p t hp hs', ?_, ?_⟩
  · simpa only [mul_one] using hcoeff
  · simpa only [perturb_eq, add_sub_cancel_left] using hnorm
  · intro n hn
    exact perturb_head s b p n t hp (fun q hq => ⟨(hs q hq).1, hqp q hq⟩) (by omega)
end
end RiemannResearch.RH.QRamanujanFullSupport

namespace RiemannResearch.RH.QRamanujanFullSupport
open ZetaTwoHilbert ZetaTwoProbability QRamanujanPackets
abbrev SquarefreeIndex := {q : ℕ // 2 ≤ q ∧ Squarefree q}
theorem squarefree_span_eq_packets :
    qSquarefreeCRTSpan = Submodule.span ℝ
      (Set.range (fun q : SquarefreeIndex => qRamanujanPacket q.val)) := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro f ⟨d, rfl⟩
    dsimp only
    rw [qResidue_eq_divisor_packets d.val (by have := d.property.1; omega)]
    apply Submodule.smul_mem
    apply Submodule.sum_mem
    intro q hq
    by_cases hq1 : q = 1
    · rw [hq1, qRamanujanPacket_one]
      exact Submodule.zero_mem _
    · exact Submodule.subset_span
        ⟨⟨q, by have := Nat.pos_of_mem_divisors hq; omega,
          d.property.2.squarefree_of_dvd (Nat.dvd_of_mem_divisors hq)⟩, rfl⟩
  · apply Submodule.span_le.mpr
    rintro f ⟨q, rfl⟩
    exact packet_mem_squarefree q.val q.property.2

theorem finite_packet_representation (f : QHilbert) (hf : f ∈ qSquarefreeCRTSpan) :
    ∃ s : Finset ℕ, ∃ b : ℕ → ℝ,
      (∀ q ∈ s, 1 < q ∧ Squarefree q) ∧
      f = ∑ q ∈ s, b q • qRamanujanPacket q := by
  classical
  rw [squarefree_span_eq_packets] at hf
  obtain ⟨c, hc⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp hf
  let s : Finset ℕ := c.support.image Subtype.val
  let b : ℕ → ℝ := fun q => if h : 2 ≤ q ∧ Squarefree q then c ⟨q, h⟩ else 0
  refine ⟨s, b, ?_, ?_⟩
  · intro q hq
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hq
    exact ⟨by have := i.property.1; omega, i.property.2⟩
  · rw [← hc]
    change (∑ i ∈ c.support, c i • qRamanujanPacket i.val) =
      ∑ q ∈ c.support.image Subtype.val, b q • qRamanujanPacket q
    rw [Finset.sum_image (fun _ _ _ _ h => Subtype.ext h)]
    apply Finset.sum_congr rfl
    intro i hi
    simp only [b, dif_pos i.property]

theorem enlarged_packet_representation (f : QHilbert) (hf : f ∈ qSquarefreeCRTSpan)
    (u : Finset ℕ) (hu : ∀ q ∈ u, 1 < q ∧ Squarefree q) :
    ∃ s : Finset ℕ, ∃ b : ℕ → ℝ, u ⊆ s ∧
      (∀ q ∈ s, 1 < q ∧ Squarefree q) ∧
      f = ∑ q ∈ s, b q • qRamanujanPacket q := by
  classical
  obtain ⟨v, b, hv, hf⟩ := finite_packet_representation f hf
  let c : ℕ → ℝ := fun q => if q ∈ v then b q else 0
  refine ⟨v ∪ u, c, Finset.subset_union_right, ?_, ?_⟩
  · intro q hq
    rcases Finset.mem_union.mp hq with hq | hq
    · exact hv q hq
    · exact hu q hq
  · rw [hf]
    calc
      _ = ∑ q ∈ v, c q • qRamanujanPacket q := by
        apply Finset.sum_congr rfl
        intro q hq
        simp [c, hq]
      _ = _ := Finset.sum_subset Finset.subset_union_left
        (by intro q hq hnot; simp [c, hnot])

theorem fresh_support_disjoint (s : Finset ℕ) (p : ℕ)
    (hs : ∀ q ∈ s, 1 < q ∧ q < p) :
    Disjoint s (s.image (fun q => p * q)) := by
  apply Finset.disjoint_left.mpr
  intro q hq hnew
  obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hnew
  have hl := (hs (p * r) hq).2
  have hrpos : 0 < r := by have := (hs r hr).1; omega
  have hge : p ≤ p * r := Nat.le_mul_of_pos_right p hrpos
  omega

theorem perturb_flatten (s : Finset ℕ) (b : ℕ → ℝ) (p : ℕ) (t : ℝ)
    (hp : 0 < p) (hs : ∀ q ∈ s, 1 < q ∧ q < p) :
    perturb s b p t =
      ∑ q ∈ s ∪ s.image (fun q => p * q),
        (if q ∈ s then b q + t else t) • qRamanujanPacket q := by
  classical
  rw [Finset.sum_union (fresh_support_disjoint s p hs)]
  unfold perturb
  congr 1
  · apply Finset.sum_congr rfl
    intro q hq
    rw [if_pos hq]
  · rw [Finset.sum_image (fun _ _ _ _ h => Nat.eq_of_mul_eq_mul_left hp h)]
    apply Finset.sum_congr rfl
    intro q hq
    have hnot : p * q ∉ s := by
      intro hmem
      exact Finset.disjoint_left.mp (fresh_support_disjoint s p hs)
        hmem (Finset.mem_image.mpr ⟨q, hq, rfl⟩)
    rw [if_neg hnot]
end RiemannResearch.RH.QRamanujanFullSupport
namespace RiemannResearch.RH.QRamanujanFullSupport
open ZetaTwoHilbert ZetaTwoProbability QRamanujanPackets
open scoped BigOperators
theorem dense_full_support (f : QHilbert) (hf : f ∈ qSquarefreeCRTSpan)
    (H : ℕ) (u : Finset ℕ) (hu : ∀ q ∈ u, 1 < q ∧ Squarefree q)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ s : Finset ℕ, ∃ a : ℕ → ℝ, u ⊆ s ∧
      (∀ q ∈ s, 1 < q ∧ Squarefree q ∧ a q ≠ 0) ∧
      ‖(∑ q ∈ s, a q • qRamanujanPacket q) - f‖ < ε ∧
      ∀ n, n ≤ H → qSequence (∑ q ∈ s, a q • qRamanujanPacket q) n = qSequence f n := by
  classical
  obtain ⟨v, b, huv, hv, hf⟩ := enlarged_packet_representation f hf u hu
  obtain ⟨p, hp, hHp, hvp, t, ht, hcoeff, hlegal, hclose, hhead⟩ :=
    exists_full_support_perturbation v b H hv ε hε
  let s := v ∪ v.image (fun q => p * q)
  let a : ℕ → ℝ := fun q => if q ∈ v then b q + t else t
  have hv' : ∀ q ∈ v, 1 < q ∧ q < p := fun q hq => ⟨(hv q hq).1, hvp q hq⟩
  have hflat : perturb v b p t = ∑ q ∈ s, a q • qRamanujanPacket q :=
    perturb_flatten v b p t hp.pos hv'
  refine ⟨s, a, huv.trans Finset.subset_union_left, ?_, ?_, ?_⟩
  · intro q hq
    rcases Finset.mem_union.mp hq with hq | hq
    · exact ⟨(hv q hq).1, (hv q hq).2, by simpa only [a, if_pos hq] using hcoeff q hq⟩
    · obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hq
      have hrpos : 0 < r := by have := (hv r hr).1; omega
      have hcop := hp.coprime_iff_not_dvd.mpr
        (Nat.not_dvd_of_pos_of_lt hrpos (hvp r hr))
      have hnot : p * r ∉ v := by
        intro hmem
        exact Finset.disjoint_left.mp (fresh_support_disjoint v p hv')
          hmem (Finset.mem_image.mpr ⟨r, hr, rfl⟩)
      refine ⟨?_, Nat.squarefree_mul_iff.mpr ⟨hcop, hp.squarefree, (hv r hr).2⟩, ?_⟩
      · exact lt_of_lt_of_le hp.one_lt (Nat.le_mul_of_pos_right p hrpos)
      · simpa only [a, if_neg hnot] using ne_of_gt ht
  · rw [← hflat, hf]
    exact hclose
  · intro n hn
    rw [← hflat, hf]
    exact hhead n hn

/-- Every squarefree q is present with nonzero coefficient at every stage j >= q. -/
theorem full_support_sequence
    (F : ℕ → QHilbert) (hf : ∀ j, F j ∈ qSquarefreeCRTSpan)
    (H : ℕ → ℕ) (ε : ℕ → ℝ) (hε : ∀ j, 0 < ε j) :
    ∃ S : ℕ → Finset ℕ, ∃ a : ℕ → ℕ → ℝ,
      (∀ j q, q ∈ S j → 1 < q ∧ Squarefree q ∧ a j q ≠ 0) ∧
      (∀ j, ‖(∑ q ∈ S j, a j q • qRamanujanPacket q) - F j‖ < ε j) ∧
      (∀ j n, n ≤ H j →
        qSequence (∑ q ∈ S j, a j q • qRamanujanPacket q) n = qSequence (F j) n) ∧
      ∀ q, 2 ≤ q → Squarefree q → ∀ j, q ≤ j → q ∈ S j := by
  classical
  let u : ℕ → Finset ℕ := fun j => (Finset.Icc 2 j).filter Squarefree
  have hu : ∀ j q, q ∈ u j → 1 < q ∧ Squarefree q := by
    intro j q hq
    obtain ⟨hq, hs⟩ := Finset.mem_filter.mp hq
    exact ⟨by have := (Finset.mem_Icc.mp hq).1; omega, hs⟩
  choose S a hcover hcoeff hclose hhead using
    fun j => dense_full_support (F j) (hf j) (H j) (u j) (hu j) (ε j) (hε j)
  refine ⟨S, a, hcoeff, hclose, hhead, ?_⟩
  intro q hq hsf j hqj
  exact hcover j (Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hq, hqj⟩, hsf⟩)
end RiemannResearch.RH.QRamanujanFullSupport

namespace RiemannResearch.RH.QRamanujanFullSupport
open ZetaTwoHilbert QRamanujanPackets
open scoped BigOperators
/-- The cumulative Ramanujan identity for the actual complete-Q packet. -/
theorem packet_prefix (q n : ℕ) (hq : 1 < q) :
    qSequence (qRamanujanPacket q) n =
      -∑ k ∈ Finset.Ico 1 (n + 1), Pareto.ramanujanSum q k := by
  rw [qSequence_qRamanujanPacket]
  exact Pareto.ramanujanPacket_prefix q n hq
end RiemannResearch.RH.QRamanujanFullSupport
