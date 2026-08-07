/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/
import Mathlib.LinearAlgebra.FreeModule.ModN

/-!
# Reducing fixed vectors to modulus two

For a torsion-free integral lattice on which a central element acts by
negation, vanishing of the fixed space modulo two forces vanishing modulo every
integer greater than one. At odd moduli, negation alone kills fixed vectors. At
an even modulus, a nonzero negation-fixed class canonically produces a nonzero
fixed class modulo two.
-/

namespace RiemannResearch.GroupTheory

/-- At an odd modulus, a class fixed by negation is zero. -/
theorem eq_zero_of_neg_fixed_mod_odd
    {L : Type*} [AddCommGroup L] {n : ℕ} (hn : Odd n) (a : L)
    (hneg : ModN.mkQ n (-a) = ModN.mkQ n a) :
    ModN.mkQ n a = 0 := by
  let x := ModN.mkQ n a
  have hnegx : -x = x := by
    simpa [x] using hneg
  have htwo : 2 • x = 0 := by
    rw [two_nsmul]
    nth_rewrite 1 [← hnegx]
    exact neg_add_cancel x
  have hnsmul : n • x = 0 := by
    change n • ModN.mkQ n a = 0
    rw [← map_nsmul]
    apply QuotientAddGroup.eq_zero_iff (n • a) |>.mpr
    refine ⟨a, ?_⟩
    simp
  rcases hn with ⟨k, rfl⟩
  calc
    x = (2 * k + 1) • x := by
      rw [add_nsmul, mul_nsmul, htwo]
      simp
    _ = 0 := hnsmul

/-- For a torsion-free lattice, a nonzero class at an even modulus that is
fixed by negation and by a family of integral endomorphisms produces a nonzero
class modulo two fixed by the same family. -/
theorem exists_nonzero_fixed_modTwo_of_neg_fixed_mod_even
    {L : Type*} [AddCommGroup L] [IsAddTorsionFree L]
    {ι : Type*} (T : ι → L →+ L) {m : ℕ} (hm : m ≠ 0) (a : L)
    (ha : ModN.mkQ (2 * m) a ≠ 0)
    (hneg : ModN.mkQ (2 * m) (-a) = ModN.mkQ (2 * m) a)
    (hfix : ∀ i, ModN.mkQ (2 * m) (T i a) = ModN.mkQ (2 * m) a) :
    ∃ b : L, ModN.mkQ 2 b ≠ 0 ∧
      ∀ i, ModN.mkQ 2 (T i b) = ModN.mkQ 2 b := by
  have hmem :
      a - (-a) ∈
        ((LinearMap.lsmul ℤ L) ((2 * m : ℕ) : ℤ)).range := by
    exact QuotientAddGroup.eq_iff_sub_mem.mp hneg.symm
  rcases hmem with ⟨b, hb⟩
  change ((2 * m : ℕ) : ℤ) • b = a - (-a) at hb
  have hba : (m : ℤ) • b = a := by
    apply zsmul_right_injective (by norm_num : (2 : ℤ) ≠ 0)
    simpa [Nat.cast_mul, mul_zsmul, sub_neg_eq_add, two_zsmul] using hb
  refine ⟨b, ?_, ?_⟩
  · intro hbzero
    have hbmem :
        b ∈ ((LinearMap.lsmul ℤ L) (2 : ℤ)).range := by
      exact QuotientAddGroup.eq_zero_iff b |>.mp hbzero
    rcases hbmem with ⟨c, hc⟩
    change (2 : ℤ) • c = b at hc
    apply ha
    apply QuotientAddGroup.eq_zero_iff a |>.mpr
    refine ⟨c, ?_⟩
    change ((2 * m : ℕ) : ℤ) • c = a
    calc
      ((2 * m : ℕ) : ℤ) • c = (m : ℤ) • ((2 : ℤ) • c) := by
        simp [Nat.cast_mul, mul_zsmul, mul_comm]
      _ = (m : ℤ) • b := by rw [hc]
      _ = a := hba
  · intro i
    apply QuotientAddGroup.eq_iff_sub_mem.mpr
    have himem :
        T i a - a ∈
          ((LinearMap.lsmul ℤ L) ((2 * m : ℕ) : ℤ)).range :=
      QuotientAddGroup.eq_iff_sub_mem.mp (hfix i)
    rcases himem with ⟨c, hc⟩
    change ((2 * m : ℕ) : ℤ) • c = T i a - a at hc
    refine ⟨c, ?_⟩
    change (2 : ℤ) • c = T i b - b
    apply zsmul_right_injective (n := (m : ℤ)) (by
      exact_mod_cast hm)
    calc
      (m : ℤ) • ((2 : ℤ) • c) =
          ((2 * m : ℕ) : ℤ) • c := by
        simp [Nat.cast_mul, mul_zsmul, mul_comm]
      _ = T i a - a := hc
      _ = T i ((m : ℤ) • b) - (m : ℤ) • b := by rw [hba]
      _ = (m : ℤ) • (T i b - b) := by
        rw [map_zsmul, zsmul_sub]

/-- If negation belongs to an integral action, vanishing of its mod-two fixed
space implies vanishing of every fixed space at modulus at least two. -/
theorem fixed_mod_eq_zero_of_negation_and_fixed_modTwo_eq_zero
    {L : Type*} [AddCommGroup L] [IsAddTorsionFree L]
    {ι : Type*} (T : ι → L →+ L)
    (hmodTwo : ∀ b : L,
      (∀ i, ModN.mkQ 2 (T i b) = ModN.mkQ 2 b) →
      ModN.mkQ 2 b = 0)
    {n : ℕ} (hn : 2 ≤ n) (a : L)
    (hneg : ModN.mkQ n (-a) = ModN.mkQ n a)
    (hfix : ∀ i, ModN.mkQ n (T i a) = ModN.mkQ n a) :
    ModN.mkQ n a = 0 := by
  by_contra ha
  rcases Nat.even_or_odd n with heven | hodd
  · rcases even_iff_two_dvd.mp heven with ⟨m, rfl⟩
    have hm_ne : m ≠ 0 := by omega
    obtain ⟨b, hb, hbfix⟩ :=
      exists_nonzero_fixed_modTwo_of_neg_fixed_mod_even T hm_ne a
        ha hneg hfix
    exact hb (hmodTwo b hbfix)
  · exact ha (eq_zero_of_neg_fixed_mod_odd hodd a hneg)

end RiemannResearch.GroupTheory
