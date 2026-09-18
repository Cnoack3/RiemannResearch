/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.CoupledCorrectionRHBridge
import Mathlib.Data.Nat.GCD.BigOperators
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Mixed coprime-block sources and genuine legal cumulative packets

The source product is expanded using pairwise coprimality. Cumulative summation
then gives a signed finite combination of the actual legal residue functions.
No weighted orthogonality or uniform energy estimate is inferred from CRT.
-/

namespace RiemannResearch.RH.CRTBlock
noncomputable section
open scoped BigOperators
open ArithmeticCumulative

/-- A finite coprime block; primes are a special case. -/
def blockSource (S : Finset ℕ) (n : ℕ) : ℝ :=
  ∏ p ∈ S, (1 - (p : ℝ) * divisorIndicator p n)

def blockPacket (S : Finset ℕ) (n : ℕ) : ℝ :=
  -∑ T ∈ S.powerset,
    (-1 : ℝ)^T.card * (∏ p ∈ T, (p : ℝ)) * residueFraction (∏ p ∈ T, p) n

theorem coprime_prod_dvd_iff (S : Finset ℕ) (n : ℕ)
    (hc : (S : Set ℕ).Pairwise Nat.Coprime) :
    (∏ p ∈ S, p) ∣ n ↔ ∀ p ∈ S, p ∣ n := by
  classical
  constructor
  · intro h p hp
    exact dvd_trans (Finset.dvd_prod_of_mem (fun p : ℕ => p) hp) h
  · intro h
    induction S using Finset.induction_on with
    | empty => simp
    | @insert p S hp ih =>
      rw [Finset.prod_insert hp]
      have hcS : (S : Set ℕ).Pairwise Nat.Coprime := by
        intro a ha b hb hab
        exact hc (by simp [ha]) (by simp [hb]) hab
      have hcp : Nat.Coprime p (∏ a ∈ S, a) := by
        apply Nat.coprime_prod_right_iff.mpr
        intro a ha
        exact hc (by simp) (by simp [ha]) (by intro he; subst a; exact hp ha)
      exact hcp.mul_dvd_of_dvd_of_dvd (h p (by simp))
        (ih hcS (fun a ha => h a (by simp [ha])))

theorem prod_divisorIndicator (S : Finset ℕ) (n : ℕ)
    (hc : (S : Set ℕ).Pairwise Nat.Coprime) :
    (∏ p ∈ S, divisorIndicator p n) = divisorIndicator (∏ p ∈ S, p) n := by
  classical
  by_cases h : ∀ p ∈ S, p ∣ n
  · rw [divisorIndicator, if_pos ((coprime_prod_dvd_iff S n hc).mpr h)]
    apply Finset.prod_eq_one
    intro p hp
    simp [divisorIndicator, h p hp]
  · have hprod : ¬ (∏ p ∈ S, p) ∣ n := by
      simpa [coprime_prod_dvd_iff S n hc] using h
    rw [divisorIndicator, if_neg hprod]
    push_neg at h
    obtain ⟨p, hp, hn⟩ := h
    apply Finset.prod_eq_zero hp
    simp [divisorIndicator, hn]

theorem blockSource_expansion (S : Finset ℕ) (n : ℕ)
    (hc : (S : Set ℕ).Pairwise Nat.Coprime) :
    blockSource S n = ∑ T ∈ S.powerset,
      (-1 : ℝ)^T.card * (∏ p ∈ T, (p : ℝ)) * divisorIndicator (∏ p ∈ T, p) n := by
  classical
  have he : blockSource S n =
      ∑ T ∈ S.powerset, ∏ p ∈ T, ((-1 : ℝ) * (p : ℝ) * divisorIndicator p n) := by
    rw [← Finset.prod_one_add]
    unfold blockSource
    apply Finset.prod_congr rfl
    intro p hp
    ring
  rw [he]
  apply Finset.sum_congr rfl
  intro T hT
  have hsub : T ⊆ S := Finset.mem_powerset.mp hT
  have hcT : (T : Set ℕ).Pairwise Nat.Coprime := by
    intro p hp q hq hpq
    exact hc (hsub hp) (hsub hq) hpq
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, Finset.prod_const,
    prod_divisorIndicator T n hcT]

theorem blockSource_balanced (S : Finset ℕ) (hS : S.Nonempty)
    (hpos : ∀ p ∈ S, 0 < p) (hc : (S : Set ℕ).Pairwise Nat.Coprime) (n : ℕ) :
    blockSource S n = ∑ T ∈ S.powerset,
      ((-1 : ℝ)^T.card * (∏ p ∈ T, (p : ℝ))) * balancedDivisor (∏ p ∈ T, p) n := by
  classical
  rw [blockSource_expansion S n hc]
  have hz : (∑ T ∈ S.powerset, (-1 : ℝ)^T.card) = 0 := by
    have hzZ : (∑ T ∈ S.powerset, (-1 : ℤ)^T.card) = 0 := by
      simpa [hS.ne_empty] using (Finset.sum_powerset_neg_one_pow_card (x := S))
    exact_mod_cast hzZ
  have he (T : Finset ℕ) (hT : T ∈ S.powerset) :
      ((-1 : ℝ)^T.card * (∏ p ∈ T, (p : ℝ))) * balancedDivisor (∏ p ∈ T, p) n =
      (-1 : ℝ)^T.card * (∏ p ∈ T, (p : ℝ)) * divisorIndicator (∏ p ∈ T, p) n -
        (-1 : ℝ)^T.card := by
    have hp : (∏ p ∈ T, (p : ℝ)) ≠ 0 := by
      apply Finset.prod_ne_zero_iff.mpr
      intro p hp
      exact ne_of_gt (by exact_mod_cast hpos p ((Finset.mem_powerset.mp hT) hp))
    unfold balancedDivisor
    push_cast
    field_simp
    <;> ring
  simp_rw [Finset.sum_congr rfl he]
  rw [Finset.sum_sub_distrib, hz, sub_zero]

theorem cumulative_blockSource (S : Finset ℕ) (hS : S.Nonempty)
    (hpos : ∀ p ∈ S, 0 < p) (hc : (S : Set ℕ).Pairwise Nat.Coprime) (n : ℕ) :
    cumulative (blockSource S) n = blockPacket S n := by
  classical
  have he : blockSource S = fun k => ∑ T ∈ S.powerset,
      ((-1 : ℝ)^T.card * (∏ p ∈ T, (p : ℝ))) * balancedDivisor (∏ p ∈ T, p) k := by
    funext k
    exact blockSource_balanced S hS hpos hc k
  rw [he]
  change (∑ k ∈ Finset.range n, ∑ T ∈ S.powerset,
      ((-1 : ℝ)^T.card * (∏ p ∈ T, (p : ℝ))) *
        balancedDivisor (∏ p ∈ T, p) (k + 1)) = _
  rw [Finset.sum_comm]
  unfold blockPacket
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro T hT
  rw [← Finset.mul_sum]
  change _ * cumulative (balancedDivisor (∏ p ∈ T, p)) n = _
  have hp : 0 < ∏ p ∈ T, p := Finset.prod_pos
    (fun p hp => hpos p ((Finset.mem_powerset.mp hT) hp))
  rw [cumulative_balancedDivisor _ _ hp]
  ring

theorem blockPacket_legal (S : Finset ℕ) (hpos : ∀ p ∈ S, 0 < p) :
    blockPacket S ∈ Pareto.legalSeedSpan allPositiveSeeds := by
  classical
  have hmem : (∑ T ∈ S.powerset,
      ((-1 : ℝ)^T.card * (∏ p ∈ T, (p : ℝ))) • residueFraction (∏ p ∈ T, p)) ∈
        Pareto.legalSeedSpan allPositiveSeeds := by
    apply Submodule.sum_mem
    intro T hT
    apply Submodule.smul_mem
    exact residueFraction_mem_legal _ (Finset.prod_pos
      (fun p hp => hpos p ((Finset.mem_powerset.mp hT) hp)))
  have he : blockPacket S = -(∑ T ∈ S.powerset,
      ((-1 : ℝ)^T.card * (∏ p ∈ T, (p : ℝ))) • residueFraction (∏ p ∈ T, p)) := by
    funext n
    simp [blockPacket, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [he]
  exact Submodule.neg_mem _ hmem

theorem blockPacket_head (S : Finset ℕ) (hS : S.Nonempty)
    (hc : (S : Set ℕ).Pairwise Nat.Coprime) (Y n : ℕ)
    (hlarge : ∀ p ∈ S, Y < p) (hn : n ≤ Y) : blockPacket S n = n := by
  have hp : ∀ p ∈ S, 0 < p := fun p h => lt_of_le_of_lt (Nat.zero_le Y) (hlarge p h)
  rw [← cumulative_blockSource S hS hp hc]
  unfold cumulative
  have he (k : ℕ) (hk : k ∈ Finset.range n) : blockSource S (k + 1) = 1 := by
    unfold blockSource
    apply Finset.prod_eq_one
    intro p hpm
    have hkn : k < n := Finset.mem_range.mp hk
    have hyp := hlarge p hpm
    have hlt : k + 1 < p := by omega
    have hnd : ¬ p ∣ k + 1 := Nat.not_dvd_of_pos_of_lt (Nat.succ_pos k) hlt
    simp [divisorIndicator, hnd]
  rw [Finset.sum_congr rfl he]
  simp

theorem coupled_block_head {ι : Type*} (s : Finset ι) (blocks : ι → Finset ℕ)
    (x : ι → ℝ) (F0 : ℕ → ℝ) (α : ℝ) (Y n : ℕ)
    (hsource : F0 n = 1 - α * n) (hn : n ≤ Y)
    (hS : ∀ i ∈ s, (blocks i).Nonempty)
    (hc : ∀ i ∈ s, (blocks i : Set ℕ).Pairwise Nat.Coprime)
    (hlarge : ∀ i ∈ s, ∀ p ∈ blocks i, Y < p)
    (hbalance : ∑ i ∈ s, x i = α) :
    F0 n + ∑ i ∈ s, x i * blockPacket (blocks i) n = 1 := by
  have he : (∑ i ∈ s, x i * blockPacket (blocks i) n) = α * n := by
    calc
      _ = ∑ i ∈ s, x i * (n : ℝ) := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [blockPacket_head _ (hS i hi) (hc i hi) Y n (hlarge i hi) hn]
      _ = _ := by rw [← Finset.sum_mul, hbalance]
  rw [he, hsource]
  ring

end
end RiemannResearch.RH.CRTBlock
