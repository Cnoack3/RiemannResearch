/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/
import Mathlib.Data.Finset.Insert
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.NormNum.GCD

/-!
# Arithmetic of the three triality-packet Sylow-seven indices

This module verifies the numerical entries used in the Sylow-seven reduction
for the `Sp₆(2)`, `2⁶ : A₈`, and `A₉` triality packets. It does not identify
the finite groups or prove that the corresponding fixed fields split an
`E₈`-torsor.
-/

namespace RiemannResearch.E8

/-- The `Sp₆(2)` packet has the displayed normalizer index and Sylow
congruence. -/
theorem sp6Packet_sylowIndex :
    34560 = 2^8 * 3^3 * 5 ∧ Nat.Coprime 34560 7 ∧ 34560 % 7 = 1 := by
  norm_num [Nat.Coprime]

/-- The `2⁶ : A₈` packet has the displayed normalizer index and Sylow
congruence. -/
theorem a8Packet_sylowIndex :
    61440 = 2^12 * 3 * 5 ∧ Nat.Coprime 61440 7 ∧ 61440 % 7 = 1 := by
  norm_num [Nat.Coprime]

/-- The `A₉` packet has the displayed normalizer index and Sylow
congruence. -/
theorem a9Packet_sylowIndex :
    4320 = 2^5 * 3^3 * 5 ∧ Nat.Coprime 4320 7 ∧ 4320 % 7 = 1 := by
  norm_num [Nat.Coprime]

/-- Every numerical index in the three-packet table is prime to seven and
congruent to one modulo seven. -/
theorem trialityPacket_sylowIndex_arithmetic :
    ∀ d ∈ ({34560, 61440, 4320} : Finset ℕ),
      Nat.Coprime d 7 ∧ d % 7 = 1 := by
  intro d hd
  simp only [Finset.mem_insert, Finset.mem_singleton] at hd
  rcases hd with rfl | rfl | rfl
  · norm_num [Nat.Coprime]
  · norm_num [Nat.Coprime]
  · norm_num [Nat.Coprime]

/-- The normalizer orders and indices multiply to the packet group orders
reported in the manuscript. -/
theorem trialityPacket_normalizer_index_products :
    42 * 34560 = 1451520 ∧
    21 * 61440 = 1290240 ∧
    42 * 4320 = 181440 := by
  norm_num

end RiemannResearch.E8
