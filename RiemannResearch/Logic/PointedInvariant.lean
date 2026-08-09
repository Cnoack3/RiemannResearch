/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/
import RiemannResearch.GroupTheory.CoprimeRestriction
import RiemannResearch.Logic.PointedKernel

/-!
# Detection by pointed additive invariants

This module combines a pointed invariant with additive annihilator
calculations. If the invariant has trivial neutral fiber, then a finite
gcd-one family of degrees annihilating its value detects the distinguished
point.

The restriction--corestriction theorem below is the abstract form of the
user-provided Rost-descent reduction. It does not construct a Rost invariant,
its cohomological targets, or the trivial-kernel theorem needed for a concrete
algebraic group.
-/

namespace RiemannResearch.Logic

open RiemannResearch.GroupTheory

/-- A pointed invariant with trivial kernel detects the basepoint once a
gcd-one family of degrees annihilates its value. -/
theorem eq_basepoint_of_gcd_one_annihilated_invariant
    {X A ι : Type*} [AddCommGroup A]
    (x₀ : X) (invariant : X → A)
    (hkernel : HasTrivialKernel x₀ 0 invariant)
    (s : Finset ι) (degree : ι → ℕ)
    (hgcd : s.gcd (fun i => (degree i : ℤ)) = 1)
    {x : X} (hkill : ∀ i ∈ s, degree i • invariant x = 0) :
    x = x₀ := by
  apply (hkernel x).mp
  exact eq_zero_of_gcd_one_annihilators s degree hgcd hkill

/-- A pointed invariant detects the global basepoint from a finite gcd-one
family of local basepoints when it is natural for additive restriction maps
satisfying restriction--corestriction index formulas.

For a Rost-invariant application, `X` is the pointed nonabelian `H¹` set, `A`
and `B i` are the global and local degree-three cohomology groups, `restrict`
is scalar extension on torsor classes, and `invariant` and `localInvariant`
are the corresponding Rost invariants. The load-bearing `hkernel` hypothesis
is precisely triviality of the global Rost kernel. -/
theorem eq_basepoint_of_gcd_one_restriction_corestriction_invariant
    {X ι A : Type*} [AddCommGroup A]
    (B : ι → Type*) [∀ i, AddCommGroup (B i)]
    (Y : ι → Type*)
    (x₀ : X) (y₀ : ∀ i, Y i)
    (restrict : ∀ i, X → Y i)
    (hrestrict₀ : ∀ i, restrict i x₀ = y₀ i)
    (invariant : X → A)
    (localInvariant : ∀ i, Y i → B i)
    (hkernel : HasTrivialKernel x₀ 0 invariant)
    (s : Finset ι) (degree : ι → ℕ)
    (res : ∀ i, A →+ B i) (cor : ∀ i, B i →+ A)
    (hindex : ∀ i a, cor i (res i a) = degree i • a)
    (hnatural : ∀ i x,
      res i (invariant x) = localInvariant i (restrict i x))
    (hgcd : s.gcd (fun i => (degree i : ℤ)) = 1)
    {x : X} (hlocal : ∀ i ∈ s, restrict i x = y₀ i) :
    x = x₀ := by
  apply eq_basepoint_of_gcd_one_annihilated_invariant
    x₀ invariant hkernel s degree hgcd
  intro i hi
  rw [← hindex i (invariant x), hnatural i x, hlocal i hi,
    ← hrestrict₀ i, ← hnatural i x₀, hkernel.map_basepoint]
  simp

end RiemannResearch.Logic
