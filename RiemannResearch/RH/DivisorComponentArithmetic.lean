import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Tactic.Ring

/-!
Arithmetic closure of the divisors of `D` under legal seed edges in `D * r`,
provided the complementary factor `r` is coprime to those seeds.
-/

namespace RiemannResearch.RH

/-- Both endpoints of a legal dilation edge belong to the divisor component of
`D` together, when its seed is coprime to the complementary conductor. -/
theorem seedEdge_dvd_component_iff {D r a m : ℕ}
    (hm : 0 < m) (har : Nat.Coprime a r)
    (hedge : a * m ∣ D * r) : m ∣ D ↔ a * m ∣ D := by
  constructor
  · rintro ⟨t, rfl⟩
    rcases hedge with ⟨q, hq⟩
    have hmul : m * (t * r) = m * (a * q) := by
      calc
        m * (t * r) = (m * t) * r := by ring
        _ = (a * m) * q := hq
        _ = m * (a * q) := by ring
    have htr : t * r = a * q := Nat.eq_of_mul_eq_mul_left hm hmul
    have hat : a ∣ t := har.dvd_of_dvd_mul_right ⟨q, htr⟩
    rcases hat with ⟨u, hu⟩
    exact ⟨u, by rw [hu]; ring⟩
  · intro h
    exact dvd_trans (show m ∣ a * m from ⟨a, by ring⟩) h

/-- The actual seeds 2 and 3 satisfy component closure as soon as the
complementary conductor is coprime to 6. -/
theorem twoSeed_dvd_component_iff {D r a m : ℕ}
    (hm : 0 < m) (ha : a = 2 ∨ a = 3)
    (hr : Nat.Coprime 6 r) (hedge : a * m ∣ D * r) :
    m ∣ D ↔ a * m ∣ D := by
  have ha6 : a ∣ 6 := by rcases ha with rfl | rfl <;> decide
  exact seedEdge_dvd_component_iff hm (Nat.Coprime.of_dvd_left ha6 hr) hedge

end RiemannResearch.RH
