/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QResidueHeadSpace
import RiemannResearch.RH.ZetaTwoHilbertSpace
import RiemannResearch.RH.ZetaTwoProbability
import RiemannResearch.RH.SquarefreeRadicalDifference
import RiemannResearch.RH.NormalizedResidueExactHeadCharges
import RiemannResearch.RH.ParetoResidueDuality
import RiemannResearch.RH.ZetaTwoCRTSquarefreeConverse
import RiemannResearch.RH.ZetaTwoParetoTransfer
import RiemannResearch.RH.QRamanujanPackets
import Mathlib.Data.Nat.Prime.Infinite
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Exact legal interpolation of every radical-compatible finite head

Source: the user's symbolic squarefree CRT continuation, 28 October 2026.
Möbius inversion is reused from ParetoResidueDuality. The fresh-prime
normalization preserves every signed coefficient. These are finite
interpolation results, with no uniform norm bound or density assertion.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.QSquarefreeCompatibleHeads
open ZetaTwoHilbert ZetaTwoProbability ArithmeticCumulative QResidueHeadSpace
open Pareto UniqueFactorizationMonoid

/-- Radical-compatible jumps have no nonsquarefree Möbius charge. -/
theorem nonsquarefree_charge_zero (v : ℕ → ℝ) (H : ℕ)
    (hrad : ∀ n, 2 ≤ n → n ≤ H →
      v n - v (n - 1) = v (radical n) - v (radical n - 1)) :
    ∀ n, 2 ≤ n → n ≤ H → ¬Squarefree n → mobiusDifference n v = 0 := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn hnH hns
    have hn0 : n ≠ 0 := by omega
    have ha2 : 2 ≤ radical n := Nat.two_le_radical_iff.mpr hn
    have halt : radical n < n := by
      have hale : radical n ≤ n := Nat.radical_le_self_iff.mpr hn0
      have hne : radical n ≠ n := by
        intro he
        exact hns (he ▸ squarefree_radical)
      omega
    have hsub : (radical n).divisors ⊆ n.divisors.erase n := by
      intro d hd
      have hda := Nat.dvd_of_mem_divisors hd
      have hdle := Nat.le_of_dvd (by omega : 0 < radical n) hda
      exact Finset.mem_erase.mpr ⟨by omega,
        Nat.mem_divisors.mpr ⟨dvd_trans hda radical_dvd_self, hn0⟩⟩
    have heq : (∑ d ∈ (radical n).divisors, mobiusDifference d v) =
        ∑ d ∈ n.divisors.erase n, mobiusDifference d v := by
      apply Finset.sum_subset hsub
      intro d hd hdnot
      have hde := Finset.mem_erase.mp hd
      have hdvd := Nat.dvd_of_mem_divisors hde.2
      have hdpos := Nat.pos_of_mem_divisors hde.2
      have hdle := Nat.le_of_dvd (by omega : 0 < n) hdvd
      have hdsf : ¬Squarefree d := by
        intro hs
        apply hdnot
        exact Nat.mem_divisors.mpr
          ⟨(dvd_radical_iff hs.isRadical hn0).mpr hdvd, by omega⟩
      have hd2 : 2 ≤ d := by
        by_contra hnot
        have hd1 : d = 1 := by omega
        exact hdsf (hd1.symm ▸ squarefree_one)
      exact ih d (by omega) hd2 (by omega) hdsf
    have hsum := sum_mobiusDifference v n (by omega)
    have hradSum := sum_mobiusDifference v (radical n) (by omega)
    have hnmem : n ∈ n.divisors := Nat.mem_divisors.mpr ⟨dvd_refl _, hn0⟩
    rw [← Finset.insert_erase hnmem, Finset.sum_insert (by simp : n ∉ n.divisors.erase n)] at hsum
    have hid := hrad n hn hnH
    linarith

def headSlope (v : ℕ → ℝ) (H : ℕ) : ℝ :=
  v 1 + ∑ d ∈ Finset.Icc 2 H, mobiusDifference d v / (d : ℝ)

def headSupport (H p : ℕ) : Finset ℕ := insert p (Finset.Icc 2 H)

def headCoefficient (v : ℕ → ℝ) (H p d : ℕ) : ℝ :=
  if d = p then (p : ℝ) * headSlope v H else -mobiusDifference d v

def headInterpolant (v : ℕ → ℝ) (H p : ℕ) : QHilbert :=
  ∑ d ∈ headSupport H p, headCoefficient v H p d • qResidue d

theorem headInterpolant_sequence (v : ℕ → ℝ) (H p n : ℕ) :
    qSequence (headInterpolant v H p) n =
      ∑ d ∈ headSupport H p, headCoefficient v H p d * residueFraction d n :=
  synthesis_sequence _ _ _

theorem headInterpolant_one (v : ℕ → ℝ) (H p : ℕ) (hp : 1 < p) (hHp : H < p) :
    qSequence (headInterpolant v H p) 1 = v 1 := by
  have hpnot : p ∉ Finset.Icc 2 H := by simp only [Finset.mem_Icc]; omega
  have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast (show p ≠ 0 by omega)
  have he : (∑ d ∈ Finset.Icc 2 H,
      headCoefficient v H p d * residueFraction d 1) =
      -(∑ d ∈ Finset.Icc 2 H, mobiusDifference d v / (d : ℝ)) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro d hd
    have hd' := Finset.mem_Icc.mp hd
    simp only [headCoefficient, if_neg (show d ≠ p by omega), residueFraction,
      Nat.mod_eq_of_lt (show 1 < d by omega), Nat.cast_one]
    ring
  rw [headInterpolant_sequence, headSupport, Finset.sum_insert hpnot, he]
  simp only [headCoefficient, residueFraction,
    Nat.mod_eq_of_lt hp, Nat.cast_one]
  simp only [ite_true]
  unfold headSlope
  field_simp [hpR]
  simp

theorem headInterpolant_charge (v : ℕ → ℝ) (H p m : ℕ)
    (hHp : H < p) (hm : 1 < m) (hmH : m ≤ H) :
    mobiusDifference m (qSequence (headInterpolant v H p)) = mobiusDifference m v := by
  have he : qSequence (headInterpolant v H p) =
      fun n => ∑ d ∈ headSupport H p, headCoefficient v H p d * residueFraction d n := by
    funext n
    exact headInterpolant_sequence v H p n
  rw [he, residueFraction_sum_mobiusDifference _ _ _ hm]
  simp [headSupport, headCoefficient, show m ≠ p by omega,
    show 2 ≤ m by omega, hmH]

/-- Local jump-charge inversion retains the anchored value at zero. -/
theorem equal_head_of_equal_charges (F G : ℕ → ℝ) (H : ℕ)
    (hzero : F 0 = G 0)
    (hc : ∀ m, 0 < m → m ≤ H → mobiusDifference m F = mobiusDifference m G) :
    ∀ n, n ≤ H → F n = G n := by
  intro n
  induction n with
  | zero => intro _; exact hzero
  | succ n ih =>
    intro hnH
    have he : (∑ d ∈ (n + 1).divisors, mobiusDifference d F) =
        ∑ d ∈ (n + 1).divisors, mobiusDifference d G := by
      apply Finset.sum_congr rfl
      intro d hd
      exact hc d (Nat.pos_of_mem_divisors hd)
        ((Nat.le_of_dvd (by omega) (Nat.dvd_of_mem_divisors hd)).trans hnH)
    rw [sum_mobiusDifference F (n + 1) (by omega),
      sum_mobiusDifference G (n + 1) (by omega)] at he
    simp only [Nat.add_sub_cancel] at he
    have hprev := ih (by omega)
    linarith

theorem headInterpolant_exact_head (v : ℕ → ℝ) (H p : ℕ)
    (hv0 : v 0 = 0) (hp : 1 < p) (hHp : H < p) :
    ∀ n, n ≤ H → qSequence (headInterpolant v H p) n = v n := by
  apply equal_head_of_equal_charges
  · rw [qSequence_zero, hv0]
  · intro m hm hmH
    by_cases hm1 : m = 1
    · subst m
      have hc1 (w : ℕ → ℝ) : mobiusDifference 1 w = w 1 - w 0 := by
        simp [mobiusDifference]
      rw [hc1, hc1, headInterpolant_one v H p hp hHp, qSequence_zero, hv0]
    · exact headInterpolant_charge v H p m hHp (by omega) hmH

theorem headInterpolant_legal_of_charges (v : ℕ → ℝ) (H p : ℕ)
    (hp : p.Prime) (hHp : H < p)
    (hcharge : ∀ d, 2 ≤ d → d ≤ H → ¬Squarefree d → mobiusDifference d v = 0) :
    headInterpolant v H p ∈ qSquarefreeCRTSpan := by
  apply Submodule.sum_mem
  intro d hd
  rcases Finset.mem_insert.mp hd with hdp | hd
  · subst d
    exact Submodule.smul_mem _ _
      (Submodule.subset_span ⟨⟨p, hp.two_le, hp.squarefree⟩, rfl⟩)
  · have hd' := Finset.mem_Icc.mp hd
    by_cases hsf : Squarefree d
    · exact Submodule.smul_mem _ _
        (Submodule.subset_span ⟨⟨d, hd'.1, hsf⟩, rfl⟩)
    · simp only [headCoefficient, if_neg (show d ≠ p by omega),
        hcharge d hd'.1 hd'.2 hsf, neg_zero, zero_smul]
      exact Submodule.zero_mem _

/-- Positive finite interpolation in the actual legal squarefree Q span. -/
theorem headInterpolant_legal_exact (v : ℕ → ℝ) (H p : ℕ)
    (hv0 : v 0 = 0) (hp : p.Prime) (hHp : H < p)
    (hrad : ∀ n, 2 ≤ n → n ≤ H →
      v n - v (n - 1) = v (radical n) - v (radical n - 1)) :
    headInterpolant v H p ∈ qSquarefreeCRTSpan ∧
      ∀ n, n ≤ H → qSequence (headInterpolant v H p) n = v n :=
  ⟨headInterpolant_legal_of_charges v H p hp hHp (nonsquarefree_charge_zero v H hrad),
    headInterpolant_exact_head v H p hv0 hp.one_lt hHp⟩


/-- The same explicit finite interpolation is legal in Pareto and has the
identical physical head; no measure-dependent coefficient change is needed. -/
theorem headInterpolant_pareto_legal_exact (v : ℕ → ℝ) (H p : ℕ)
    (hv0 : v 0 = 0) (hp : p.Prime) (hHp : H < p)
    (hrad : ∀ n, 2 ≤ n → n ≤ H →
      v n - v (n - 1) = v (radical n) - v (radical n - 1)) :
    ZetaTwoParetoTransfer.toPareto (headInterpolant v H p) ∈ squarefreeCRTSpan ∧
      ∀ n, n ≤ H → hilbertSequence
        (ZetaTwoParetoTransfer.toPareto (headInterpolant v H p)) n = v n := by
  have h := headInterpolant_legal_exact v H p hv0 hp hHp hrad
  constructor
  · rw [← qSquarefreeCRTSpan_map]
    exact ⟨headInterpolant v H p, h.1, rfl⟩
  · intro n hn
    rw [ZetaTwoParetoTransfer.toPareto_sequence]
    exact h.2 n hn


/-- Every finite radical-compatible anchored head has an actual squarefree
legal interpolant. No bound on its complete energy is asserted. -/
theorem exists_legal_exact_head (v : ℕ → ℝ) (H : ℕ)
    (hv0 : v 0 = 0)
    (hrad : ∀ n, 2 ≤ n → n ≤ H →
      v n - v (n - 1) = v (radical n) - v (radical n - 1)) :
    ∃ F : QHilbert, F ∈ qSquarefreeCRTSpan ∧
      ∀ n, n ≤ H → qSequence F n = v n := by
  obtain ⟨p, hpH, hp⟩ := Nat.exists_infinite_primes (H + 1)
  exact ⟨headInterpolant v H p,
    headInterpolant_legal_exact v H p hv0 hp (by omega) hrad⟩

/-- The literal complete vector has an exact finite Ramanujan packet expansion;
this changes its coefficients, not its span or its physical energy. -/
theorem headInterpolant_ramanujan_expansion (v : ℕ → ℝ) (H p : ℕ) (hp : 0 < p) :
    headInterpolant v H p =
      ∑ d ∈ headSupport H p, (headCoefficient v H p d / (d : ℝ)) •
        (∑ q ∈ d.divisors, QRamanujanPackets.qRamanujanPacket q) := by
  unfold headInterpolant
  apply Finset.sum_congr rfl
  intro d hd
  have hdpos : 0 < d := by
    rcases Finset.mem_insert.mp hd with hdp | hdi
    · simpa only [hdp] using hp
    · have := (Finset.mem_Icc.mp hdi).1
      omega
  rw [QRamanujanPackets.qResidue_eq_divisor_packets d hdpos, smul_smul]
  congr 1
  ring

end RiemannResearch.RH.QSquarefreeCompatibleHeads
