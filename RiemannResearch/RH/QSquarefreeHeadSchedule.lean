/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.ZetaTwoHilbertSpace
import RiemannResearch.RH.QSquarefreeLatticePackets
import RiemannResearch.RH.QSquarefreeAffineHead
import RiemannResearch.NumberTheory.IsolatedPrimeReciprocalSum
import Mathlib.NumberTheory.Primorial
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Feasible squarefree primorial head schedules

Source: user-provided LCM telescoping question, 19 October 2026, for the
research objective. Bertrand's postulate supplies the prime in the upper
half interval. The elementary composite anchor 2p avoids adding a new prime
merely to obtain an anchor. This is a feasibility result, not an energy bound.
-/

noncomputable section
namespace RiemannResearch.RH.QSquarefreeHeadSchedule
open ZetaTwoHilbert QSquarefreeAffineHead QSquarefreeLatticePackets

/-- Every field is finite-stage feasibility data; there is no analytic budget. -/
structure Schedule where
  period : ℕ → ℕ
  anchor : ℕ → ℕ
  positive : ∀ i, 0 < period i
  squarefree : ∀ i, Squarefree (period i)
  nested : ∀ i, period i ∣ period (i + 1)
  anchor_mem : ∀ i, anchor i ∈ conductors (period i)
  anchor_gt : ∀ i, i + 1 < anchor i
  anchor_le : ∀ i, anchor i ≤ 2 * (i + 1)
  small : ∀ i d, 1 < d → d ≤ i + 1 → Squarefree d → d ∣ period i

theorem Schedule.anchor_mem_next (s : Schedule) (i : ℕ) :
    s.anchor i ∈ conductors (s.period (i + 1)) := by
  obtain ⟨hd, hg⟩ := Finset.mem_filter.mp (s.anchor_mem i)
  apply Finset.mem_filter.mpr
  exact ⟨Nat.mem_divisors.mpr
    ⟨dvd_trans (Nat.mem_divisors.mp hd).1 (s.nested i),
      ne_of_gt (s.positive (i + 1))⟩, hg⟩

/-- Radical of the LCM through H, with the startup prime 3 retained. -/
def period (H : ℕ) : ℕ := primorial (max 3 H)

theorem period_pos (H : ℕ) : 0 < period H := primorial_pos _

theorem period_squarefree (H : ℕ) : Squarefree (period H) := squarefree_primorial _

theorem period_nested {H J : ℕ} (h : H ≤ J) : period H ∣ period J :=
  primorial_dvd_primorial (max_le_max_left 3 h)

theorem small_dvd (H d : ℕ) (hd : Squarefree d) (h : d ≤ H) : d ∣ period H :=
  dvd_trans hd.dvd_primorial (primorial_dvd_primorial (h.trans (le_max_right 3 H)))

/-- For H >= 4, take an odd prime H/2 < p <= H and use r=2p.
The three startup cases are explicit. Every anchor divides the existing stage. -/
theorem exists_near_anchor (H : ℕ) (hH : 0 < H) :
    ∃ r : ℕ, r ∈ conductors (period H) ∧ H < r ∧ r ≤ 2 * H := by
  by_cases h4 : 4 ≤ H
  · obtain ⟨p, hp, hpH, hH2p⟩ :=
      RiemannResearch.NumberTheory.exists_prime_upper_half (by omega : 2 ≤ H)
    have hp2 : 2 < p := by omega
    have hnot : ¬p ∣ 2 := by
      intro h
      have := Nat.le_of_dvd (by decide : 0 < 2) h
      omega
    have hcop : Nat.Coprime 2 p := (hp.coprime_iff_not_dvd.mpr hnot).symm
    have h2 : 2 ∣ period H :=
      Nat.prime_two.dvd_primorial_iff.mpr (by omega)
    have hpd : p ∣ period H :=
      hp.dvd_primorial_iff.mpr (hpH.trans (le_max_right 3 H))
    refine ⟨2 * p, ?_, hH2p, Nat.mul_le_mul_left 2 hpH⟩
    exact Finset.mem_filter.mpr
      ⟨Nat.mem_divisors.mpr
        ⟨hcop.mul_dvd_of_dvd_of_dvd h2 hpd, ne_of_gt (period_pos H)⟩, by omega⟩
  · have hc : H = 1 ∨ H = 2 ∨ H = 3 := by omega
    rcases hc with rfl | rfl | rfl
    · exact ⟨2, by decide, by decide, by decide⟩
    · exact ⟨3, by decide, by decide, by decide⟩
    · exact ⟨6, by decide, by decide, by decide⟩

def anchor (i : ℕ) : ℕ :=
  (exists_near_anchor (i + 1) (Nat.succ_pos i)).choose

theorem anchor_spec (i : ℕ) :
    anchor i ∈ conductors (period (i + 1)) ∧
      i + 1 < anchor i ∧ anchor i ≤ 2 * (i + 1) :=
  (exists_near_anchor (i + 1) (Nat.succ_pos i)).choose_spec

def primorialSchedule : Schedule where
  period i := period (i + 1)
  anchor := anchor
  positive i := period_pos (i + 1)
  squarefree i := period_squarefree (i + 1)
  nested i := period_nested (by omega)
  anchor_mem i := (anchor_spec i).1
  anchor_gt i := (anchor_spec i).2.1
  anchor_le i := (anchor_spec i).2.2
  small i d _ hd hs := small_dvd (i + 1) d hs hd

/-- One must enlarge the period before imposing the first missing prime site. -/
theorem missing_prime_blocks_head (H L p : ℕ) (hL : 0 < L) (hp : Nat.Prime p)
    (hpH : p ≤ H) (hmissing : ¬p ∣ L) :
    ¬∃ f : QHilbert, f ∈ divisorStage L ∧
      ∀ n, 0 < n → n ≤ H → qSequence f n = 1 := by
  rintro ⟨f, hf, hh⟩
  apply hmissing
  apply exact_head_forces_conductor H L hL f hf hh p hp.one_lt hpH
  rw [ArithmeticFunction.moebius_apply_prime hp]
  norm_num

/-- Certified finite transition: period 6 must be enlarged before head 5. -/
theorem period_six_cannot_reach_head_five :
    ¬∃ f : QHilbert, f ∈ divisorStage 6 ∧
      ∀ n, 0 < n → n ≤ 5 → qSequence f n = 1 :=
  missing_prime_blocks_head 5 6 5 (by decide) (by decide) (by decide) (by decide)

end RiemannResearch.RH.QSquarefreeHeadSchedule
