/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.Analysis.AdjacentGreenPair
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Tactic.NormNum

/-!
# The compulsory rough-source profile in the full finite Green energy

Source: user-provided argument, 14 September 2026.

For the even conductor `P = 2M + 2`, this module uses the actual full prefix
energy on coordinates `1,...,P-1`.  The selected pairs are `(n-1,n)` for odd
selected centers `n`, so their supports are automatically disjoint.  The
coordinate `1` is retained explicitly.  The resulting exact Pythagorean
identity is then applied to a cumulative rough source minus arbitrary gcd-atom
increments with coefficient zero on the coprime atom.

In particular, the source-specific identity below has no unproved orthogonality
or jump assumption: its jump is proved directly from the gcd-atom definition.
The theorem does not bound the distance of the repaired source to the legal
CRT span.  Actual legal support restrictions on the atom coefficient field
remain part of that separate approximation problem.
-/

open scoped BigOperators
open RiemannResearch.Analysis.AdjacentGreenPair

namespace RiemannResearch.RH.AdjacentGreenSource

noncomputable section

/-- Full Green energy at every physical coordinate `1,...,2M+1`. -/
def finitePrefixGreenEnergy (M : ℕ) (A : ℕ → ℝ) : ℝ :=
  ∑ r ∈ Finset.range (2 * M + 1),
    (A (r + 1)) ^ 2 / (((r + 1 : ℕ) : ℝ) * ((r + 2 : ℕ) : ℝ))

/-- The local minimum profile on disjoint adjacent odd-centered pairs. -/
def oddPairProfile (select : ℕ → Prop) [DecidablePred select] (r : ℕ) : ℝ :=
  if r % 2 = 0 then
    if select (r + 1) then localLeft ((r + 1 : ℕ) : ℝ) 1 else 0
  else
    if select r then localRight (r : ℝ) 1 else 0

def oddPairLocalFloor (M : ℕ) (select : ℕ → Prop) [DecidablePred select] : ℝ :=
  ∑ k ∈ Finset.range M,
    if select (2 * k + 3) then 1 / (2 * (((2 * k + 3 : ℕ) : ℝ)) ^ 2) else 0

theorem oddPairProfile_one (select : ℕ → Prop) [DecidablePred select]
    (h1 : ¬ select 1) : oddPairProfile select 1 = 0 := by
  simp [oddPairProfile, h1]

theorem oddPairProfile_left (select : ℕ → Prop) [DecidablePred select] (k : ℕ) :
    oddPairProfile select (2 * k + 2) =
      if select (2 * k + 3) then localLeft (((2 * k + 3 : ℕ) : ℝ)) 1 else 0 := by
  have hp : (2 * k + 2) % 2 = 0 := by omega
  have hs : 2 * k + 2 + 1 = 2 * k + 3 := by omega
  simp only [oddPairProfile, hp, if_true, hs]

theorem oddPairProfile_right (select : ℕ → Prop) [DecidablePred select] (k : ℕ) :
    oddPairProfile select (2 * k + 3) =
      if select (2 * k + 3) then localRight (((2 * k + 3 : ℕ) : ℝ)) 1 else 0 := by
  have hp : (2 * k + 3) % 2 ≠ 0 := by omega
  simp only [oddPairProfile, hp, if_false]

/-- Appending the next two physical coordinates gives one exact pair energy. -/
theorem finitePrefixGreenEnergy_succ (M : ℕ) (A : ℕ → ℝ) :
    finitePrefixGreenEnergy (M + 1) A = finitePrefixGreenEnergy M A +
      pairEnergy (((2 * M + 3 : ℕ) : ℝ)) (A (2 * M + 2)) (A (2 * M + 3)) := by
  have hs : 2 * (M + 1) + 1 = (2 * M + 1) + 1 + 1 := by omega
  unfold finitePrefixGreenEnergy
  rw [hs, Finset.sum_range_succ, Finset.sum_range_succ]
  norm_num [pairEnergy, Nat.cast_add, Nat.cast_mul, Nat.add_assoc]
  ring

/-- Exact reindexing of the full energy, with its unpaired first coordinate. -/
theorem finitePrefixGreenEnergy_eq_pairs (M : ℕ) (A : ℕ → ℝ) :
    finitePrefixGreenEnergy M A = (A 1) ^ 2 / 2 +
      ∑ k ∈ Finset.range M,
        pairEnergy (((2 * k + 3 : ℕ) : ℝ)) (A (2 * k + 2)) (A (2 * k + 3)) := by
  induction M with
  | zero => simp [finitePrefixGreenEnergy]
  | succ M ih =>
      rw [finitePrefixGreenEnergy_succ, ih, Finset.sum_range_succ]
      ring

/-- Global Pythagoras for any selected finite collection of compulsory jumps. -/
theorem finitePrefixGreenEnergy_odd_pair_split
    (M : ℕ) (select : ℕ → Prop) [DecidablePred select] (A : ℕ → ℝ)
    (h1 : ¬ select 1)
    (hjump : ∀ n, select n → A n - A (n - 1) = 1) :
    finitePrefixGreenEnergy M A = oddPairLocalFloor M select +
      finitePrefixGreenEnergy M (fun r => A r - oddPairProfile select r) := by
  have hpair (k : ℕ) :
      pairEnergy (((2 * k + 3 : ℕ) : ℝ)) (A (2 * k + 2)) (A (2 * k + 3)) =
        (if select (2 * k + 3) then
          1 / (2 * (((2 * k + 3 : ℕ) : ℝ)) ^ 2) else 0) +
          pairEnergy (((2 * k + 3 : ℕ) : ℝ))
            (A (2 * k + 2) - oddPairProfile select (2 * k + 2))
            (A (2 * k + 3) - oddPairProfile select (2 * k + 3)) := by
    rw [oddPairProfile_left, oddPairProfile_right]
    by_cases hk : select (2 * k + 3)
    · simp only [if_pos hk]
      have hn : (1 : ℝ) < (((2 * k + 3 : ℕ) : ℝ)) := by
        exact_mod_cast (show 1 < 2 * k + 3 by omega)
      have hj := hjump (2 * k + 3) hk
      have hp : 2 * k + 3 - 1 = 2 * k + 2 := by omega
      rw [hp] at hj
      simpa only [one_pow] using
        pairEnergy_pythagoras (((2 * k + 3 : ℕ) : ℝ))
          (A (2 * k + 2)) (A (2 * k + 3)) 1 hn hj
    · simp [hk]
  have hsum :
      (∑ k ∈ Finset.range M,
        pairEnergy (((2 * k + 3 : ℕ) : ℝ)) (A (2 * k + 2)) (A (2 * k + 3))) =
        oddPairLocalFloor M select +
          ∑ k ∈ Finset.range M,
            pairEnergy (((2 * k + 3 : ℕ) : ℝ))
              (A (2 * k + 2) - oddPairProfile select (2 * k + 2))
              (A (2 * k + 3) - oddPairProfile select (2 * k + 3)) := by
    unfold oddPairLocalFloor
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun k _ => hpair k
  rw [finitePrefixGreenEnergy_eq_pairs, finitePrefixGreenEnergy_eq_pairs, hsum]
  rw [oddPairProfile_one select h1]
  simp only [sub_zero]
  ring

/-- The concrete selector consists of rough interior indices, excluding `1`. -/
def roughProfile (M : ℕ) : ℕ → ℝ :=
  oddPairProfile (fun n => 1 < n ∧ n < 2 * M + 2 ∧ n.Coprime (2 * M + 2))

def roughLocalFloor (M : ℕ) : ℝ :=
  oddPairLocalFloor M (fun n => 1 < n ∧ n < 2 * M + 2 ∧ n.Coprime (2 * M + 2))

/-- The rough-source floor is an explicit positive arithmetic sum. -/
theorem roughLocalFloor_eq (M : ℕ) :
    roughLocalFloor M =
      ∑ k ∈ Finset.range M,
        if (2 * k + 3).Coprime (2 * M + 2) then
          1 / (2 * (((2 * k + 3 : ℕ) : ℝ)) ^ 2) else 0 := by
  unfold roughLocalFloor oddPairLocalFloor
  apply Finset.sum_congr rfl
  intro k hk
  have hlt := Finset.mem_range.mp hk
  have hn : 1 < 2 * k + 3 := by omega
  have hP : 2 * k + 3 < 2 * M + 2 := by omega
  simp only [hn, hP, true_and]

theorem finitePrefixGreenEnergy_rough_split (M : ℕ) (A : ℕ → ℝ)
    (hjump : ∀ n, 1 < n → n < 2 * M + 2 → n.Coprime (2 * M + 2) →
      A n - A (n - 1) = 1) :
    finitePrefixGreenEnergy M A = roughLocalFloor M +
      finitePrefixGreenEnergy M (fun r => A r - roughProfile M r) := by
  unfold roughLocalFloor roughProfile
  apply finitePrefixGreenEnergy_odd_pair_split
  · simp
  · intro n hn
    exact hjump n hn.1 hn.2.1 hn.2.2

/-- Prefix sum of increments at physical indices `1,...,r`. -/
def cumulative (a : ℕ → ℝ) (r : ℕ) : ℝ :=
  ∑ m ∈ Finset.range r, a (m + 1)

theorem cumulative_jump (a : ℕ → ℝ) (n : ℕ) (hn : 0 < n) :
    cumulative a n - cumulative a (n - 1) = a n := by
  cases n with
  | zero => omega
  | succ n => simp [cumulative, Finset.sum_range_succ]

/-- The actual rough source minus an arbitrary gcd-atom coefficient field. -/
def crtResidual (P : ℕ) (g : ℕ → ℝ) : ℕ → ℝ :=
  cumulative (fun n =>
    (if 1 < n ∧ n.Coprime P then (1 : ℝ) else 0) - g (n.gcd P))

/-- Coprime atom exclusion proves the compulsory source jump directly. -/
theorem crtResidual_rough_jump (P : ℕ) (g : ℕ → ℝ) (hg : g 1 = 0)
    (n : ℕ) (hn : 1 < n) (hc : n.Coprime P) :
    crtResidual P g n - crtResidual P g (n - 1) = 1 := by
  unfold crtResidual
  rw [cumulative_jump _ n (by omega)]
  simp [hn, hc, hg]

/-- An unconditional source-specific identity, for every coprime-zero atom field.
Further legal coefficient restrictions can be imposed without changing it. -/
theorem crtResidual_green_split (M : ℕ) (g : ℕ → ℝ) (hg : g 1 = 0) :
    finitePrefixGreenEnergy M (crtResidual (2 * M + 2) g) = roughLocalFloor M +
      finitePrefixGreenEnergy M
        (fun r => crtResidual (2 * M + 2) g r - roughProfile M r) := by
  apply finitePrefixGreenEnergy_rough_split
  intro n hn _ hc
  exact crtResidual_rough_jump (2 * M + 2) g hg n hn hc

end

end RiemannResearch.RH.AdjacentGreenSource
