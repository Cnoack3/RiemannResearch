/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/
import RiemannResearch.AlgebraicGeometry.PointFields

/-!
# Prime-power degree spectra and index one

Over a p-special field, every finite point-field degree is a power of p. For
such a degree spectrum, gcd one forces degree one to occur. This is the
arithmetic endpoint used after an index-one theorem in the manuscript's
p-special reduction.
-/

namespace RiemannResearch.AlgebraicGeometry

/-- A set consisting of powers of one prime and having set-gcd one contains
one. -/
theorem one_mem_of_setGcd_eq_one_of_prime_powers
    {s : Set ℕ} {p : ℕ} (hp : p.Prime)
    (hpow : ∀ n ∈ s, ∃ k : ℕ, n = p ^ k)
    (hgcd : Nat.setGcd s = 1) :
    1 ∈ s := by
  by_contra hnot
  have hpdiv : p ∣ Nat.setGcd s := by
    rw [Nat.dvd_setGcd_iff]
    intro n hn
    obtain ⟨k, rfl⟩ := hpow n hn
    have hk : k ≠ 0 := by
      intro hk
      subst k
      apply hnot
      simpa using hn
    exact dvd_pow_self p hk
  have hpone : p ∣ 1 := by
    simpa [hgcd] using hpdiv
  exact hp.ne_one (Nat.dvd_one.mp hpone)

/-- If every finite point-field degree is a power of one prime and the
point-field index is one, an actual degree-one finite point field exists. -/
theorem degree_one_pointField_exists_of_prime_power_degrees
    {Extension : Type*}
    (isFinite : Extension → Prop) (degree : Extension → ℕ)
    (hasPoint : Extension → Prop) {p : ℕ} (hp : p.Prime)
    (hpow : ∀ n ∈ finitePointDegrees isFinite degree hasPoint,
      ∃ k : ℕ, n = p ^ k)
    (hindex : pointFieldIndex isFinite degree hasPoint = 1) :
    ∃ L, isFinite L ∧ hasPoint L ∧ degree L = 1 := by
  have hone : 1 ∈ finitePointDegrees isFinite degree hasPoint :=
    one_mem_of_setGcd_eq_one_of_prime_powers hp hpow hindex
  rcases hone with ⟨L, hL, hdegree⟩
  exact ⟨L, hL.1, hL.2, hdegree⟩

end RiemannResearch.AlgebraicGeometry
