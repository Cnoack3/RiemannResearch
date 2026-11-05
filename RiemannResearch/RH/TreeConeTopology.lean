/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import Mathlib.Data.Nat.Prime.Infinite
import Mathlib.Data.Nat.Squarefree
import Mathlib.Topology.Clopen
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Tactic.NormNum

/-! # Topology of increasing-prime prefix trees

The compact model records presence or absence of every prime. A prefix stops
being distinguishable from its children at primes tending to infinity. The
physical remainder probe cannot extend continuously to this compactum. -/

noncomputable section
open Filter
open scoped Topology
namespace RiemannResearch.RH.PrimeTreeTopology

/-- The discrete two-point space records absence or presence. -/
abbrev Bit := Fin 2

abbrev PrimeMask := Nat.Primes → Bit

theorem primeMask_compact : CompactSpace PrimeMask := inferInstance

/-- Prime support. Restricted to positive squarefree integers, these are the vertices. -/
def vertex (m : ℕ) : PrimeMask := fun p =>
  if p.val ∣ m then 1 else 0

/-- Specify a finite set of prime coordinates. -/
def cylinder (s : Finset Nat.Primes) (x : PrimeMask) : Set PrimeMask :=
  {y | ∀ p ∈ s, y p = x p}

theorem cylinder_isClopen (s : Finset Nat.Primes) (x : PrimeMask) :
    IsClopen (cylinder s x) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have h : cylinder ∅ x = Set.univ := by ext y; simp [cylinder]
    rw [h]
    exact isClopen_univ
  | @insert p s hp ih =>
    have h : cylinder (insert p s) x =
        (fun y : PrimeMask => y p) ⁻¹' ({x p} : Set Bit) ∩ cylinder s x := by
      ext y
      simp [cylinder]
    rw [h]
    have hpt : IsClopen ({x p} : Set Bit) := isClopen_discrete _
    exact (hpt.preimage (continuous_apply p)).inter ih

/-- Prime coordinates through the largest chosen prime, including skipped primes. -/
def coordinatesThrough (k : ℕ) : Finset Nat.Primes :=
  (Finset.range (k + 1)).biUnion fun i =>
    if h : Nat.Prime i then {⟨i, h⟩} else ∅

/-- Cone through a positive squarefree vertex in increasing prime order.
For the empty prefix, the supremum in naturals is zero. -/
def prefixCone (r : ℕ) : Set PrimeMask :=
  cylinder (coordinatesThrough (r.primeFactors.sup id)) (vertex r)

theorem prefixCone_isClopen (r : ℕ) : IsClopen (prefixCone r) :=
  cylinder_isClopen _ _

/-- Children formed with primes escaping to infinity converge to the parent. -/
theorem vertex_mul_prime_tendsto (r : ℕ) (q : ℕ → ℕ)
    (hp : ∀ k, Nat.Prime (q k)) (hq : Tendsto q atTop atTop) :
    Tendsto (fun k => vertex (r * q k)) atTop (𝓝 (vertex r)) := by
  apply tendsto_pi_nhds.mpr
  intro p
  apply tendsto_const_nhds.congr'
  filter_upwards [hq.eventually (eventually_gt_atTop p.val)] with k hk
  have hn : ¬p.val ∣ q k := by
    intro h
    exact (ne_of_lt hk) (((Nat.dvd_prime (hp k)).mp h).resolve_left p.property.ne_one)
  simp only [vertex, p.property.dvd_mul, hn, or_false]

/-- There is no continuous physical remainder test at n = 2 on the prime-mask
compactum agreeing at all positive squarefree vertices. -/
theorem no_continuous_mod_two :
    ¬ ∃ u : PrimeMask → ℕ, Continuous u ∧
      ∀ m : ℕ, Squarefree m → u (vertex m) = 2 % m := by
  rintro ⟨u, hu, hv⟩
  let q (j : ℕ) := Classical.choose (Nat.exists_infinite_primes (j + 3))
  have hs (j : ℕ) : j + 3 ≤ q j ∧ Nat.Prime (q j) :=
    Classical.choose_spec (Nat.exists_infinite_primes (j + 3))
  have hq : Tendsto q atTop atTop := by
    apply tendsto_atTop.2
    intro a
    filter_upwards [eventually_ge_atTop a] with j hj
    exact le_trans (by omega : a ≤ j + 3) (hs j).1
  have hroot : Tendsto (fun j => vertex (q j)) atTop (𝓝 (vertex 1)) := by
    simpa using vertex_mul_prime_tendsto 1 q (fun j => (hs j).2) hq
  have hlimit : Tendsto (fun j => u (vertex (q j))) atTop (𝓝 (u (vertex 1))) :=
    (hu.tendsto (vertex 1)).comp hroot
  have heq : (fun j => u (vertex (q j))) = (fun _ : ℕ => 2) := by
    funext j
    have hj := (hs j).1
    rw [hv _ (hs j).2.prime.squarefree, Nat.mod_eq_of_lt (by omega : 2 < q j)]
  rw [heq, hv 1 squarefree_one] at hlimit
  have hconst : Tendsto (fun _ : ℕ => 2) atTop (𝓝 (2 : ℕ)) := tendsto_const_nhds
  have hbad := tendsto_nhds_unique hlimit hconst
  norm_num at hbad

end RiemannResearch.RH.PrimeTreeTopology
