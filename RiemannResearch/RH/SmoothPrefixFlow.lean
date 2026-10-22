import RiemannResearch.RH.FixedPrefixIncidence

/-!
# Homogeneous smooth-layer flux for the actual fixed two-channel prefixes

Source: user-provided argument, RH_CRT_Packet_Research_2026-09-09.md,
Section 9.1. The homogeneous-layer flux is computed from the actual
Möbius incidence equations, not assumed.
-/

namespace RiemannResearch.RH.Pareto

open scoped BigOperators
open SmoothRepairAntichain OneBoundaryRepair

noncomputable section

private def layerSum (f : ℕ → ℕ → ℝ) (r : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (r + 1), f i (r - i)

private def latticeDivergence (U V : ℕ → ℕ → ℝ) (i j : ℕ) : ℝ :=
  U i j + V i j - (if i = 0 then 0 else U (i - 1) j) -
    (if j = 0 then 0 else V i (j - 1))

private theorem layer_incoming_first (U : ℕ → ℕ → ℝ) (r : ℕ) :
    layerSum (fun i j => if i = 0 then 0 else U (i - 1) j) (r + 1) =
      layerSum U r := by
  unfold layerSum
  rw [Finset.sum_range_succ']
  simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte,
    Nat.add_sub_cancel, Nat.add_sub_add_right, add_zero]

private theorem layer_incoming_second (V : ℕ → ℕ → ℝ) (r : ℕ) :
    layerSum (fun i j => if j = 0 then 0 else V i (j - 1)) (r + 1) =
      layerSum V r := by
  unfold layerSum
  rw [Finset.sum_range_succ]
  simp only [Nat.sub_self, ↓reduceIte, add_zero]
  apply Finset.sum_congr rfl
  intro i hi
  have hir : i ≤ r := by have := Finset.mem_range.mp hi; omega
  have hn : r + 1 - i ≠ 0 := by omega
  have he : r + 1 - i - 1 = r - i := by omega
  simp [hn, he]

private theorem layer_divergence (U V : ℕ → ℕ → ℝ) (r : ℕ) :
    layerSum (latticeDivergence U V) (r + 1) =
      layerSum (fun i j => U i j + V i j) (r + 1) -
        layerSum (fun i j => U i j + V i j) r := by
  have hf := layer_incoming_first U r
  have hs := layer_incoming_second V r
  unfold layerSum latticeDivergence at *
  simp_rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
  rw [hf, hs]
  ring

private theorem coprime_not_dvd {a b : ℕ} (ha : 1 < a) (hc : Nat.Coprime a b) :
    ¬ a ∣ b := by
  intro hd
  have hg : a ∣ Nat.gcd a b := Nat.dvd_gcd (dvd_refl a) hd
  change Nat.gcd a b = 1 at hc
  rw [hc] at hg
  have := Nat.le_of_dvd (by omega : 0 < 1) hg
  omega

private theorem incoming_two_smooth (u : ℕ → ℝ) (i j : ℕ) :
    (if 2 ∣ 2 ^ i * 3 ^ j then u ((2 ^ i * 3 ^ j) / 2) else 0) =
      (if i = 0 then 0 else u (2 ^ (i - 1) * 3 ^ j)) := by
  cases i with
  | zero =>
    have hc : Nat.Coprime 2 (3 ^ j) := by
      simpa using (Nat.Coprime.pow 1 j (by decide : Nat.Coprime 2 3))
    simp [coprime_not_dvd (by omega : 1 < 2) hc]
  | succ i =>
    have he : 2 ^ (i + 1) * 3 ^ j = 2 * (2 ^ i * 3 ^ j) := by
      rw [pow_succ]
      ring
    simp [he]

private theorem incoming_three_smooth (v : ℕ → ℝ) (i j : ℕ) :
    (if 3 ∣ 2 ^ i * 3 ^ j then v ((2 ^ i * 3 ^ j) / 3) else 0) =
      (if j = 0 then 0 else v (2 ^ i * 3 ^ (j - 1))) := by
  cases j with
  | zero =>
    have hc : Nat.Coprime 3 (2 ^ i) := by
      simpa using (Nat.Coprime.pow 1 i (by decide : Nat.Coprime 3 2))
    simp [coprime_not_dvd (by omega : 1 < 3) hc]
  | succ j =>
    have he : 2 ^ i * 3 ^ (j + 1) = 3 * (2 ^ i * 3 ^ j) := by
      rw [pow_succ]
      ring
    simp [he]

/-- The full outgoing coefficient sum on the actual homogeneous smooth layer. -/
def smoothPrefixFlux (u v : ℕ → ℝ) (r : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (r + 1),
    (u (2 ^ i * 3 ^ (r - i)) + v (2 ^ i * 3 ^ (r - i)))

private def smoothMobiusLayer (r : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (r + 1),
    (ArithmeticFunction.moebius (2 ^ i * 3 ^ (r - i)) : ℝ) /
      ((2 ^ i * 3 ^ (r - i) : ℕ) : ℝ)

private theorem smoothMobiusLayer_zero (r : ℕ) (hr : 3 ≤ r) :
    smoothMobiusLayer r = 0 := by
  unfold smoothMobiusLayer
  apply Finset.sum_eq_zero
  intro i hi
  have hir : i ≤ r := by have := Finset.mem_range.mp hi; omega
  have hlarge : 6 < 2 ^ i * 3 ^ (r - i) := by
    have he := endpoint_lower r i hir
    have hpow : 2 ^ 3 ≤ 2 ^ r := Nat.pow_le_pow_right (by omega) hr
    change 2 ^ r ≤ 2 ^ i * 3 ^ (r - i) at he
    norm_num at hpow
    omega
  have hz := moebius_tail_zero_of_dvd_six_pow 6
    (2 ^ i * 3 ^ (r - i)) (i + (r - i)) (by omega)
    (seedPowers_dvd_six_pow i (r - i))
    (2 ^ i * 3 ^ (r - i))
    (Nat.mem_divisors.mpr ⟨dvd_refl _, by positivity⟩) hlarge
  rw [hz]
  simp

private theorem prefix_lattice_incidence (u v : ℕ → ℝ)
    (hhead : ∀ N k, 0 < k → k ≤ N → twoChannelPrefix N u v k = 1)
    (i j : ℕ) :
    latticeDivergence (fun i j => u (2 ^ i * 3 ^ j))
      (fun i j => v (2 ^ i * 3 ^ j)) i j =
      (ArithmeticFunction.moebius (2 ^ i * 3 ^ j) : ℝ) /
        ((2 ^ i * 3 ^ j : ℕ) : ℝ) := by
  have he := twoChannelPrefix_exact_head_incidence
    (2 ^ i * 3 ^ j) (2 ^ i * 3 ^ j) u v (by positivity) le_rfl
    (hhead (2 ^ i * 3 ^ j))
  rw [incoming_two_smooth, incoming_three_smooth] at he
  exact he

private theorem smoothPrefixFlux_succ_sub (u v : ℕ → ℝ)
    (hhead : ∀ N k, 0 < k → k ≤ N → twoChannelPrefix N u v k = 1)
    (r : ℕ) :
    smoothPrefixFlux u v (r + 1) - smoothPrefixFlux u v r =
      smoothMobiusLayer (r + 1) := by
  have hl := layer_divergence (fun i j => u (2 ^ i * 3 ^ j))
    (fun i j => v (2 ^ i * 3 ^ j)) r
  change layerSum (fun i j => u (2 ^ i * 3 ^ j) + v (2 ^ i * 3 ^ j)) (r + 1) -
    layerSum (fun i j => u (2 ^ i * 3 ^ j) + v (2 ^ i * 3 ^ j)) r = _
  rw [← hl]
  unfold layerSum smoothMobiusLayer
  apply Finset.sum_congr rfl
  intro i hi
  exact prefix_lattice_incidence u v hhead i (r + 1 - i)

/-- The homogeneous outgoing flux is exactly 1/3, uniformly in the layer size. -/
theorem smoothPrefixFlux_eq_third (u v : ℕ → ℝ)
    (hhead : ∀ N k, 0 < k → k ≤ N → twoChannelPrefix N u v k = 1)
    (r : ℕ) (hr : 2 ≤ r) : smoothPrefixFlux u v r = (1 : ℝ) / 3 := by
  have hzero : smoothPrefixFlux u v 0 = 1 := by
    have he := prefix_lattice_incidence u v hhead 0 0
    norm_num [smoothPrefixFlux, latticeDivergence] at *
    exact he
  have hone : smoothMobiusLayer 1 = -(5 : ℝ) / 6 := by
    have hm2 := ArithmeticFunction.moebius_apply_prime (by decide : Nat.Prime 2)
    have hm3 := ArithmeticFunction.moebius_apply_prime (by decide : Nat.Prime 3)
    norm_num [smoothMobiusLayer, Finset.sum_range_succ, hm2, hm3]
  have htwo : smoothMobiusLayer 2 = (1 : ℝ) / 6 := by
    have hm2 := ArithmeticFunction.moebius_apply_prime (by decide : Nat.Prime 2)
    have hm3 := ArithmeticFunction.moebius_apply_prime (by decide : Nat.Prime 3)
    have hm4 := ArithmeticFunction.moebius_apply_prime_pow (p := 2) (k := 2)
      (by decide) (by decide)
    have hm9 := ArithmeticFunction.moebius_apply_prime_pow (p := 3) (k := 2)
      (by decide) (by decide)
    have hm6 : ArithmeticFunction.moebius 6 = 1 := by
      have he := ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime
        (by decide : Nat.Coprime 2 3)
      norm_num [hm2, hm3] at he
      exact he
    norm_num at hm4 hm9
    norm_num [smoothMobiusLayer, Finset.sum_range_succ, hm4, hm9, hm6]
  have hbase : smoothPrefixFlux u v 2 = (1 : ℝ) / 3 := by
    have h1 := smoothPrefixFlux_succ_sub u v hhead 0
    have h2 := smoothPrefixFlux_succ_sub u v hhead 1
    change smoothPrefixFlux u v 1 - smoothPrefixFlux u v 0 = smoothMobiusLayer 1 at h1
    change smoothPrefixFlux u v 2 - smoothPrefixFlux u v 1 = smoothMobiusLayer 2 at h2
    rw [hzero, hone] at h1
    rw [htwo] at h2
    linarith
  obtain ⟨s, rfl⟩ := Nat.exists_eq_add_of_le hr
  clear hr
  induction s with
  | zero => simpa using hbase
  | succ s ih =>
    have he := smoothPrefixFlux_succ_sub u v hhead (2 + s)
    rw [smoothMobiusLayer_zero (2 + s + 1) (by omega), ih] at he
    simpa only [Nat.add_assoc] using (sub_eq_zero.mp he)

/-- The exact nonzero flux forces one large outgoing coefficient on every layer. -/
theorem exists_large_smooth_prefix_coefficient (u v : ℕ → ℝ)
    (hhead : ∀ N k, 0 < k → k ≤ N → twoChannelPrefix N u v k = 1)
    (r : ℕ) (hr : 2 ≤ r) :
    ∃ i ∈ Finset.range (r + 1),
      1 / (3 * ((r : ℝ) + 1)) ≤
        |u (2 ^ i * 3 ^ (r - i)) + v (2 ^ i * 3 ^ (r - i))| := by
  by_contra hnot
  have hlt : ∀ i ∈ Finset.range (r + 1),
      u (2 ^ i * 3 ^ (r - i)) + v (2 ^ i * 3 ^ (r - i)) <
        1 / (3 * ((r : ℝ) + 1)) := by
    intro i hi
    have hn : ¬ 1 / (3 * ((r : ℝ) + 1)) ≤
        |u (2 ^ i * 3 ^ (r - i)) + v (2 ^ i * 3 ^ (r - i))| := by
      intro hh
      exact hnot ⟨i, hi, hh⟩
    exact (le_abs_self _).trans_lt (lt_of_not_ge hn)
  have hs := Finset.sum_lt_sum (fun i hi => (hlt i hi).le)
    ⟨0, Finset.mem_range.mpr (by omega), hlt 0 (Finset.mem_range.mpr (by omega))⟩
  have hm : ((r : ℝ) + 1) * (1 / (3 * ((r : ℝ) + 1))) = (1 : ℝ) / 3 := by
    have hh : (r : ℝ) + 1 ≠ 0 := by positivity
    field_simp <;> ring
  change smoothPrefixFlux u v r <
    ∑ i ∈ Finset.range (r + 1), (1 / (3 * ((r : ℝ) + 1))) at hs
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul,
    Nat.cast_add, Nat.cast_one] at hs
  rw [smoothPrefixFlux_eq_third u v hhead r hr, hm] at hs
  exact (lt_irrefl _ hs)

end
end RiemannResearch.RH.Pareto
