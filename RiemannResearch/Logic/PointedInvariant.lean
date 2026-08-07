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

end RiemannResearch.Logic
