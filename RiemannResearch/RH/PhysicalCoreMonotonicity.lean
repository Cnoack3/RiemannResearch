/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.PhysicalPacketCore

/-!
# Actual nested packet-set monotonicity

Zero extension of an old coefficient vector preserves both its literal
physical synthesis and its actual ordinary-mean constraint. Thus enlargement
decreases the constrained error and increases the negative inverse-core charge.
This proves actual finite monotonicity without a supplied Schur inverse.
It does not prove saturation of the charge at -4*pi.

-/

noncomputable section
open Matrix
open scoped BigOperators
namespace RiemannResearch.RH.Pareto.PhysicalCoreMonotonicity
open PhysicalPacketCore

def extendCoefficientsNat (s : Finset ℕ) (c : s → ℝ) (n : ℕ) : ℝ :=
  if h : n ∈ s then c ⟨n, h⟩ else 0

def extendCoefficients (s t : Finset ℕ) (c : s → ℝ) (q : t) : ℝ :=
  extendCoefficientsNat s c q.val

theorem extendCoefficients_sum (s t : Finset ℕ) (c : s → ℝ)
    (f : ℕ → ℝ) (hst : s ⊆ t) :
    (∑ q : t, extendCoefficients s t c q * f q.val) =
      ∑ q : s, c q * f q.val := by
  classical
  have ht : (∑ q : t, extendCoefficients s t c q * f q.val) =
      ∑ q ∈ t, extendCoefficientsNat s c q * f q := by
    simpa only [extendCoefficients] using
      (Finset.sum_coe_sort t (fun q : ℕ => extendCoefficientsNat s c q * f q))
  have hs : (∑ q : s, c q * f q.val) =
      ∑ q ∈ s, extendCoefficientsNat s c q * f q := by
    calc
      _ = ∑ q : s, extendCoefficientsNat s c q.val * f q.val := by
        apply Finset.sum_congr rfl
        intro q hq
        simp only [extendCoefficientsNat, dif_pos q.property]
      _ = _ := by
        exact Finset.sum_coe_sort s (fun q : ℕ => extendCoefficientsNat s c q * f q)
  rw [ht, hs]
  symm
  apply Finset.sum_subset hst
  intro q hqt hqs
  simp only [extendCoefficientsNat, dif_neg hqs, zero_mul]

/-- Literal synthesis equality, including every physical tail site. -/
theorem synthesis_extendCoefficients (s t : Finset ℕ) (c : s → ℝ)
    (hst : s ⊆ t) :
    synthesis t (extendCoefficients s t c) = synthesis s c := by
  funext k
  unfold synthesis FiniteSchur.combination
  exact extendCoefficients_sum s t c (fun q => ramanujanPacket q k) hst

theorem totient_extendCoefficients (s t : Finset ℕ) (c : s → ℝ)
    (hst : s ⊆ t) :
    ramanujanTotientVector t ⬝ᵥ extendCoefficients s t c =
      ramanujanTotientVector s ⬝ᵥ c := by
  simp only [dotProduct, ramanujanTotientVector]
  simpa only [mul_comm] using
    extendCoefficients_sum s t c (fun q => (Nat.totient q : ℝ)) hst

theorem odd_prime_mono (s t : Finset ℕ) (hst : s ⊆ t)
    (hodd : ∃ p ∈ s, p.Prime ∧ 2 < p) :
    ∃ p ∈ t, p.Prime ∧ 2 < p := by
  obtain ⟨p, hps, hp, hpodd⟩ := hodd
  exact ⟨p, hst hps, hp, hpodd⟩

/-- Actual constrained error decreases on every nested legal packet set. -/
theorem constrained_error_antitone (s t : Finset ℕ) (hst : s ⊆ t)
    (hs : ∀ q ∈ s, 1 < q) (ht : ∀ q ∈ t, 1 < q)
    (hodd : ∃ p ∈ s, p.Prime ∧ 2 < p) :
    1 + 4 * Real.pi / inverseCharge t ≤ 1 + 4 * Real.pi / inverseCharge s := by
  have htodd := odd_prime_mono s t hst hodd
  have hmean : ramanujanTotientVector t ⬝ᵥ
      extendCoefficients s t (constrainedOptimizer s) = 2 := by
    rw [totient_extendCoefficients s t _ hst]
    exact constrainedOptimizer_totient s hs hodd
  have hmin := (constrainedOptimizer_unique_minimum t ht htodd
    (extendCoefficients s t (constrainedOptimizer s)) hmean).1
  rw [synthesis_extendCoefficients s t _ hst,
    constrainedOptimizer_error s hs hodd] at hmin
  exact hmin

theorem constrained_physical_error_antitone (s t : Finset ℕ) (hst : s ⊆ t)
    (hs : ∀ q ∈ s, 1 < q) (ht : ∀ q ∈ t, 1 < q)
    (hodd : ∃ p ∈ s, p.Prime ∧ 2 < p) :
    paretoError (synthesis t (constrainedOptimizer t)) ≤
      paretoError (synthesis s (constrainedOptimizer s)) := by
  rw [constrainedOptimizer_error t ht (odd_prime_mono s t hst hodd),
    constrainedOptimizer_error s hs hodd]
  exact constrained_error_antitone s t hst hs ht hodd

/-- Exact equality case: enlargement has no constrained gain precisely when
the zero-extended old vector is already the new unique optimizer. -/
theorem constrained_no_gain_iff (s t : Finset ℕ) (hst : s ⊆ t)
    (hs : ∀ q ∈ s, 1 < q) (ht : ∀ q ∈ t, 1 < q)
    (hodd : ∃ p ∈ s, p.Prime ∧ 2 < p) :
    (paretoError (synthesis s (constrainedOptimizer s)) =
      paretoError (synthesis t (constrainedOptimizer t))) ↔
        extendCoefficients s t (constrainedOptimizer s) = constrainedOptimizer t := by
  have htodd := odd_prime_mono s t hst hodd
  have hmean : ramanujanTotientVector t ⬝ᵥ
      extendCoefficients s t (constrainedOptimizer s) = 2 := by
    rw [totient_extendCoefficients s t _ hst]
    exact constrainedOptimizer_totient s hs hodd
  have hu := (constrainedOptimizer_unique_minimum t ht htodd
    (extendCoefficients s t (constrainedOptimizer s)) hmean).2
  rw [synthesis_extendCoefficients s t _ hst] at hu
  rw [constrainedOptimizer_error t ht htodd]
  exact hu

/-- The actual inverse-core charge increases under enlargement. All inverse,
mean, physical synthesis and optimizer premises are internally discharged. -/
theorem inverseCharge_mono (s t : Finset ℕ) (hst : s ⊆ t)
    (hs : ∀ q ∈ s, 1 < q) (ht : ∀ q ∈ t, 1 < q)
    (hodd : ∃ p ∈ s, p.Prime ∧ 2 < p) :
    inverseCharge s ≤ inverseCharge t := by
  have hsn := inverseCharge_neg s hs hodd
  have htn := inverseCharge_neg t ht (odd_prime_mono s t hst hodd)
  have he := constrained_error_antitone s t hst hs ht hodd
  have hfrac : 4 * Real.pi / (-inverseCharge s) ≤
      4 * Real.pi / (-inverseCharge t) := by
    simp only [div_neg]
    linarith only [he]
  have hmul := (div_le_div_iff₀ (neg_pos.mpr hsn) (neg_pos.mpr htn)).1 hfrac
  have hp : 0 < 4 * Real.pi := by positivity
  have hcancel := (mul_le_mul_iff_right₀ hp).mp hmul
  linarith only [hcancel]

/-- Nested nonzero conductor divisibility gives literal nested packet sets. -/
theorem divisorPackets_subset_of_dvd (L M : ℕ) (hLM : L ∣ M) (hM : M ≠ 0) :
    divisorPackets L ⊆ divisorPackets M := by
  intro q hq
  have hqlegal := (Finset.mem_filter.mp hq).2
  have hqL := (Nat.mem_divisors.mp (Finset.mem_filter.mp hq).1).1
  exact Finset.mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨dvd_trans hqL hLM, hM⟩, hqlegal⟩

theorem squarefree_inverseCharge_mono (L M : ℕ) (hLM : L ∣ M)
    (hL : 2 < L) (hM : 2 < M) (hsqL : Squarefree L) :
    inverseCharge (divisorPackets L) ≤ inverseCharge (divisorPackets M) := by
  exact inverseCharge_mono (divisorPackets L) (divisorPackets M)
    (divisorPackets_subset_of_dvd L M hLM (by omega))
    (divisorPackets_legal L) (divisorPackets_legal M) (divisorPackets_odd L hL hsqL)

end RiemannResearch.RH.Pareto.PhysicalCoreMonotonicity
