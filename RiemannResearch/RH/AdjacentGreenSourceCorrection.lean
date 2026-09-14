/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.AdjacentGreenSource

/-!
# Full-prefix error of the symmetric neighboring-mark replacement

Source: user-provided argument, 14 September 2026.  This module completes the
assembly of the local correction bound into the actual finite prefix Green
norm.  The first coordinate is retained and explicitly vanishes when `1` is
not selected.  No assertion about the remaining legal-span distance is made.
-/

open scoped BigOperators
open RiemannResearch.Analysis.AdjacentGreenPair

namespace RiemannResearch.RH.AdjacentGreenSource

noncomputable section

/-- The symmetric compulsory unit-jump profile on the same disjoint pairs. -/
def symmetricOddPairProfile (select : ℕ → Prop) [DecidablePred select]
    (r : ℕ) : ℝ :=
  if r % 2 = 0 then
    if select (r + 1) then -(1 / 2 : ℝ) else 0
  else
    if select r then (1 / 2 : ℝ) else 0

theorem symmetricOddPairProfile_one (select : ℕ → Prop) [DecidablePred select]
    (h1 : ¬ select 1) : symmetricOddPairProfile select 1 = 0 := by
  simp [symmetricOddPairProfile, h1]

theorem symmetricOddPairProfile_left (select : ℕ → Prop) [DecidablePred select]
    (k : ℕ) :
    symmetricOddPairProfile select (2 * k + 2) =
      if select (2 * k + 3) then -(1 / 2 : ℝ) else 0 := by
  have hp : (2 * k + 2) % 2 = 0 := by omega
  have hs : 2 * k + 2 + 1 = 2 * k + 3 := by omega
  simp only [symmetricOddPairProfile, hp, if_true, hs]

theorem symmetricOddPairProfile_right (select : ℕ → Prop) [DecidablePred select]
    (k : ℕ) :
    symmetricOddPairProfile select (2 * k + 3) =
      if select (2 * k + 3) then (1 / 2 : ℝ) else 0 := by
  have hp : (2 * k + 3) % 2 ≠ 0 := by omega
  simp only [symmetricOddPairProfile, hp, if_false]

/-- Exact full-prefix norm of the optimal profile minus its symmetric replacement. -/
theorem oddPairProfile_symmetric_difference_energy
    (M : ℕ) (select : ℕ → Prop) [DecidablePred select] (h1 : ¬ select 1) :
    finitePrefixGreenEnergy M
      (fun r => oddPairProfile select r - symmetricOddPairProfile select r) =
        ∑ k ∈ Finset.range M,
          if select (2 * k + 3) then unitCorrection (((2 * k + 3 : ℕ) : ℝ)) else 0 := by
  rw [finitePrefixGreenEnergy_eq_pairs]
  have hfirst :
      (oddPairProfile select 1 - symmetricOddPairProfile select 1) ^ 2 / 2 = 0 := by
    rw [oddPairProfile_one select h1, symmetricOddPairProfile_one select h1]
    norm_num
  rw [hfirst, zero_add]
  apply Finset.sum_congr rfl
  intro k _
  rw [oddPairProfile_left, oddPairProfile_right,
    symmetricOddPairProfile_left, symmetricOddPairProfile_right]
  by_cases hk : select (2 * k + 3)
  · simp only [if_pos hk]
    have hn : (1 : ℝ) < (((2 * k + 3 : ℕ) : ℝ)) := by
      exact_mod_cast (show 1 < 2 * k + 3 by omega)
    simpa only [sub_neg_eq_add, one_pow, one_mul] using
      symmetric_profile_correction (((2 * k + 3 : ℕ) : ℝ)) 1 hn
  · simp [hk, pairEnergy]

/-- A cutoff beyond `X` gives a bound uniform in the conductor and selected set. -/
theorem oddPairProfile_symmetric_difference_le_cubic
    (M X : ℕ) (hX : 1 ≤ X) (select : ℕ → Prop) [DecidablePred select]
    (hcut : ∀ n, select n → X < n) :
    finitePrefixGreenEnergy M
      (fun r => oddPairProfile select r - symmetricOddPairProfile select r) ≤
        1 / (6 * (X : ℝ) ^ 3) := by
  have h1 : ¬ select 1 := by
    intro hs
    have := hcut 1 hs
    omega
  let S : Finset ℕ := (Finset.range M).filter fun k => select (2 * k + 3)
  let f : ℕ → ℕ := fun k => 2 * k + 3 - (X + 1)
  have hkcut (k : ℕ) (hk : k ∈ S) : X < 2 * k + 3 :=
    hcut (2 * k + 3) (Finset.mem_filter.mp hk).2
  have hindex (k : ℕ) (hk : k ∈ S) :
      (X : ℝ) + (f k : ℝ) + 1 = (((2 * k + 3 : ℕ) : ℝ)) := by
    have hx := hkcut k hk
    have hn : X + f k + 1 = 2 * k + 3 := by
      dsimp [f]
      omega
    exact_mod_cast hn
  have hf : ∀ k ∈ S, ∀ l ∈ S, f k = f l → k = l := by
    intro k hk l hl he
    have hxk := hkcut k hk
    have hxl := hkcut l hl
    dsimp [f] at he
    omega
  have hsub : S.image f ⊆ Finset.range (2 * M + 2) := by
    intro r hr
    rcases Finset.mem_image.mp hr with ⟨k, hk, rfl⟩
    have hkm : k < M := Finset.mem_range.mp (Finset.mem_filter.mp hk).1
    apply Finset.mem_range.mpr
    dsimp [f]
    omega
  have hreindex :
      (∑ r ∈ S.image f, unitCorrection ((X : ℝ) + (r : ℝ) + 1)) =
        ∑ k ∈ S, unitCorrection (((2 * k + 3 : ℕ) : ℝ)) := by
    rw [Finset.sum_image hf]
    apply Finset.sum_congr rfl
    intro k hk
    rw [hindex k hk]
  have hXreal : (1 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX
  have hbound := sum_subset_unitCorrection_le_cubic
    (X : ℝ) hXreal (2 * M + 2) (S.image f) hsub
  rw [hreindex] at hbound
  rw [oddPairProfile_symmetric_difference_energy M select h1]
  simpa only [S, Finset.sum_filter] using hbound

end

end RiemannResearch.RH.AdjacentGreenSource
