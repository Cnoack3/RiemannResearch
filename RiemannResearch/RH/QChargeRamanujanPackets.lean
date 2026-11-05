/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.RH.QDisplacementTranslationCarry
import RiemannResearch.RH.ParetoArithmeticRepair
import RiemannResearch.RH.ParetoPacketGreenGram

/-! # Exact finite Ramanujan rows of the physical Möbius charges

The same signed sums over multiples control each derivative frequency in a
fixed physical head. All sums below are finite. -/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.QChargeRamanujanPackets
open Pareto QDisplacementTranslationCarry

/-- Signed finite multiple sum at primitive conductor q. -/
def chargePacket (f : ℕ → ℝ) (H q : ℕ) : ℝ :=
  ∑ m ∈ Finset.Icc 1 H, if q ∣ m then mobiusDifference m f / (m : ℝ) else 0

private theorem residue_sum_head (H m k : ℕ) (hm : 1 ≤ m) (hmH : m ≤ H) :
    (∑ q ∈ Finset.Icc 2 H, if q ∣ m then ramanujanPacket q k else 0) = Pareto.residue m k := by
  classical
  rw [← Finset.sum_filter]
  have he : (Finset.Icc 2 H).filter (fun q => q ∣ m) =
      m.divisors.filter (fun q => 1 < q) := by
    ext q
    simp only [Finset.mem_filter, Finset.mem_Icc, Nat.mem_divisors]
    constructor
    · rintro ⟨⟨hq, _⟩, hdiv⟩
      exact ⟨⟨hdiv, by omega⟩, by omega⟩
    · rintro ⟨⟨hdiv, _⟩, hq⟩
      exact ⟨⟨by omega, (Nat.le_of_dvd hm hdiv).trans hmH⟩, hdiv⟩
  rw [he]
  exact ramanujanPacket_divisor_sum_gt_one m k hm

/-- Exact physical reconstruction of a finite head using its signed primitive
packets; q=1 supplies the separate scalar slope. -/
theorem finite_charge_antiderivative (f : ℕ → ℝ) (hf : f 0 = 0)
    (H n : ℕ) (hn : n ≤ H) :
    f n = (n : ℝ) * chargePacket f H 1 -
      ∑ q ∈ Finset.Icc 2 H, chargePacket f H q * ramanujanPacket q n := by
  classical
  rw [finite_floor_reconstruction f hf H n hn]
  unfold chargePacket
  simp only [one_dvd, if_true, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm (s := Finset.Icc 2 H), ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro m hm
  obtain ⟨hm1, hmH⟩ := Finset.mem_Icc.mp hm
  have hm0 : (m : ℝ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
  have he : (∑ q ∈ Finset.Icc 2 H,
        (if q ∣ m then mobiusDifference m f / (m : ℝ) else 0) * ramanujanPacket q n) =
      (mobiusDifference m f / (m : ℝ)) * Pareto.residue m n := by
    rw [← residue_sum_head H m n hm1 hmH, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun q _ => by by_cases h : q ∣ m <;> simp [h])
  rw [he]
  have hrem : (Pareto.residue m n : ℝ) + (m : ℝ) * ((n / m : ℕ) : ℝ) = n := by
    simpa only [Pareto.residue, Nat.cast_add, Nat.cast_mul] using
      congrArg (fun v : ℕ => (v : ℝ)) (Nat.mod_add_div n m)
  field_simp [hm0]
  linear_combination (norm := ring) (mobiusDifference m f) * hrem

/-- The exact Ramanujan row of the actual first difference on any fixed head,
including its slope and every signed sum over multiples. -/
theorem finite_charge_increment (f : ℕ → ℝ) (hf : f 0 = 0)
    (H n : ℕ) (hn : n ≤ H) (hn0 : 0 < n) :
    f n - f (n - 1) = chargePacket f H 1 +
      ∑ q ∈ Finset.Icc 2 H, chargePacket f H q * ramanujanSum q n := by
  have ha := finite_charge_antiderivative f hf H n hn
  have hb := finite_charge_antiderivative f hf H (n - 1) (by omega)
  have hnR : (n : ℝ) - ((n - 1 : ℕ) : ℝ) = 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ n), Nat.cast_one]
    ring
  have hs : (∑ q ∈ Finset.Icc 2 H, chargePacket f H q * ramanujanPacket q n) -
      (∑ q ∈ Finset.Icc 2 H, chargePacket f H q * ramanujanPacket q (n - 1)) =
        -(∑ q ∈ Finset.Icc 2 H, chargePacket f H q * ramanujanSum q n) := by
    rw [← Finset.sum_sub_distrib, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro q hq
    rw [← mul_sub, ramanujanPacket_increment q n (Finset.mem_Icc.mp hq).1 hn0, mul_neg]
  linear_combination ha - hb - hs + (chargePacket f H 1) * hnR

end RiemannResearch.RH.QChargeRamanujanPackets
