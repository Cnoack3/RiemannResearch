/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.GroupTheory.IsPerfect

/-!
# Perfect cores from the derived series

A stable term of the derived series is the solvable residual: it is perfect,
its quotient is solvable, and it is contained in every normal subgroup with
solvable quotient.  For a finite group the derived series has a stable term by
the pigeonhole principle.

These lemmas formalize the group-theoretic part of a finite perfect-core
compression.  A separate finite certificate may identify which stable terms
occur in a concrete subgroup census.
-/

namespace RiemannResearch.GroupTheory

/-- Once the derived series stabilizes, every later term is the stable term. -/
theorem derivedSeries_tail_eq_of_stable
    {G : Type*} [Group G] {n : ℕ}
    (hstable : derivedSeries G (n + 1) = derivedSeries G n) :
    ∀ k : ℕ, derivedSeries G (n + k) = derivedSeries G n := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Nat.add_succ, derivedSeries_succ G (n + k), ih,
        ← derivedSeries_succ G n]
      exact hstable

/-- A stable derived-series term is a perfect group. -/
theorem stable_derivedSeries_isPerfect
    {G : Type*} [Group G] {n : ℕ}
    (hstable : derivedSeries G (n + 1) = derivedSeries G n) :
    Group.IsPerfect ↥(derivedSeries G n) := by
  apply Subgroup.isPerfect_iff.mpr
  rw [← derivedSeries_succ G n]
  exact hstable

/-- If a derived-series term lies in a normal subgroup, the corresponding
quotient is solvable. -/
theorem quotient_isSolvable_of_derivedSeries_le
    {G : Type*} [Group G] {N : Subgroup G} [N.Normal] {n : ℕ}
    (hN : derivedSeries G n ≤ N) :
    Group.IsSolvable (G ⧸ N) := by
  rw [Group.isSolvable_def]
  refine ⟨n, ?_⟩
  rw [← map_derivedSeries_eq (f := QuotientGroup.mk' N)
    (QuotientGroup.mk'_surjective N) n]
  apply le_antisymm
  · rintro y ⟨x, hx, rfl⟩
    apply (Subgroup.mem_bot).2
    simpa only [QuotientGroup.mk'_apply] using
      (QuotientGroup.eq_one_iff x).2 (hN hx)
  · exact bot_le

/-- Conversely, a solvable quotient kills some term of the derived series. -/
theorem derivedSeries_le_of_quotient_isSolvable
    {G : Type*} [Group G] (N : Subgroup G) [N.Normal]
    (hsolv : Group.IsSolvable (G ⧸ N)) :
    ∃ n, derivedSeries G n ≤ N := by
  rcases (Group.isSolvable_def (G ⧸ N)).mp hsolv with ⟨n, hn⟩
  refine ⟨n, ?_⟩
  intro x hx
  have hxmap :
      QuotientGroup.mk' N x ∈
        (derivedSeries G n).map (QuotientGroup.mk' N) :=
    ⟨x, hx, rfl⟩
  rw [map_derivedSeries_eq (f := QuotientGroup.mk' N)
    (QuotientGroup.mk'_surjective N) n, hn] at hxmap
  apply (QuotientGroup.eq_one_iff x).1
  simpa only [QuotientGroup.mk'_apply] using
    (Subgroup.mem_bot.mp hxmap)

/-- A stable derived-series term is contained in every normal subgroup whose
quotient is solvable. -/
theorem stable_derivedSeries_le_of_isSolvable_quotient
    {G : Type*} [Group G] {n : ℕ}
    (hstable : derivedSeries G (n + 1) = derivedSeries G n)
    {N : Subgroup G} [N.Normal]
    (hsolv : Group.IsSolvable (G ⧸ N)) :
    derivedSeries G n ≤ N := by
  rcases derivedSeries_le_of_quotient_isSolvable N hsolv with ⟨m, hm⟩
  rw [← derivedSeries_tail_eq_of_stable hstable m]
  exact (derivedSeries_antitone G (Nat.le_add_left m n)).trans hm

/-- If the type of subgroups is finite, the derived series has a stable term. -/
theorem exists_stable_derivedSeries_of_finite_subgroups
    {G : Type*} [Group G] [Finite (Subgroup G)] :
    ∃ n, derivedSeries G (n + 1) = derivedSeries G n := by
  obtain ⟨a, b, hab, hEq⟩ :=
    Finite.exists_ne_map_eq_of_infinite (derivedSeries G)
  rcases lt_or_gt_of_ne hab with hab | hba
  · refine ⟨a, le_antisymm
      (derivedSeries_antitone G (Nat.le_add_right a 1)) ?_⟩
    rw [hEq]
    exact derivedSeries_antitone G (Nat.add_one_le_of_lt hab)
  · refine ⟨b, le_antisymm
      (derivedSeries_antitone G (Nat.le_add_right b 1)) ?_⟩
    rw [← hEq]
    exact derivedSeries_antitone G (Nat.add_one_le_of_lt hba)

end RiemannResearch.GroupTheory
