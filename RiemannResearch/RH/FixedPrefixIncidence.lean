import RiemannResearch.RH.ExactHeadCharges
import RiemannResearch.RH.SmoothRepairAntichain

/-!
# Exact incidence and first-block cost of the fixed-prefix construction

Source: user-provided argument, RH_CRT_Packet_Research_2026-09-09.md,
Section 9.1, equations (42)--(43). This module identifies the actual
coefficient incidence and retains the exact first-block squared energy.
The global antichain-flow divergence is not asserted here.
-/

namespace RiemannResearch.RH.Pareto

open scoped BigOperators
open TwoSeedThreshold FiniteSeedComponentCharge

noncomputable section

private theorem mobiusDifference_add (n : ℕ) (F G : ℕ → ℝ) :
    mobiusDifference n (fun k => F k + G k) =
      mobiusDifference n F + mobiusDifference n G := by
  unfold mobiusDifference
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro d hd
  ring

/-- Prefix in one of the original generator channels. -/
def channelPrefix (a N : ℕ) (u : ℕ → ℝ) (k : ℕ) : ℝ :=
  ∑ m ∈ Finset.Icc 1 N, u m * certificateGenerator a m k

/-- Both original channels, with coefficients fixed as N varies. -/
def twoChannelPrefix (N : ℕ) (u v : ℕ → ℝ) (k : ℕ) : ℝ :=
  channelPrefix 2 N u k + channelPrefix 3 N v k

theorem channelPrefix_succ (a N : ℕ) (u : ℕ → ℝ) (k : ℕ) :
    channelPrefix a (N + 1) u k = channelPrefix a N u k +
      u (N + 1) * certificateGenerator a (N + 1) k := by
  have hs : Finset.Icc 1 (N + 1) = insert (N + 1) (Finset.Icc 1 N) := by
    ext m
    simp only [Finset.mem_Icc, Finset.mem_insert]
    omega
  simp [channelPrefix, hs, add_comm]

/-- Exact relation between a fixed-prefix increment and its two generator packets. -/
theorem twoChannelPrefix_succ_sub (N : ℕ) (u v : ℕ → ℝ) (k : ℕ) :
    twoChannelPrefix (N + 1) u v k - twoChannelPrefix N u v k =
      u (N + 1) * certificateGenerator 2 (N + 1) k +
        v (N + 1) * certificateGenerator 3 (N + 1) k := by
  simp only [twoChannelPrefix, channelPrefix_succ]
  ring

private theorem incoming_prefix_sum (a N n : ℕ) (u : ℕ → ℝ)
    (ha : 0 < a) (hn : 0 < n) (hnN : n ≤ N) :
    (∑ m ∈ Finset.Icc 1 N,
      u m * (if n = a * m then ((a * m : ℕ) : ℝ) else 0)) =
      (n : ℝ) * (if a ∣ n then u (n / a) else 0) := by
  by_cases hd : a ∣ n
  · have hquot : a * (n / a) = n := Nat.mul_div_cancel' hd
    have hapos : a ≤ n := Nat.le_of_dvd hn hd
    have hqpos : 0 < n / a := Nat.div_pos hapos ha
    have hqN : n / a ≤ N := (Nat.div_le_self n a).trans hnN
    rw [Finset.sum_eq_single (n / a)]
    · simp [hd, hquot, mul_comm]
    · intro m hm hne
      have hneq : n ≠ a * m := by
        intro heq
        have hprod : a * (n / a) = a * m := hquot.trans heq
        have he : n / a = m := Nat.eq_of_mul_eq_mul_left ha hprod
        exact hne he.symm
      simp [hneq]
    · intro hnot
      exact (hnot (Finset.mem_Icc.mpr ⟨hqpos, hqN⟩)).elim
  · have hz : (∑ m ∈ Finset.Icc 1 N,
        u m * (if n = a * m then ((a * m : ℕ) : ℝ) else 0)) = 0 := by
      apply Finset.sum_eq_zero
      intro m hm
      have hneq : n ≠ a * m := fun h => hd ⟨m, h⟩
      simp [hneq]
    rw [if_neg hd, mul_zero]
    exact hz

/-- Every incoming coefficient is retained, including its sign. -/
theorem channelPrefix_mobiusDifference (a N n : ℕ) (u : ℕ → ℝ)
    (ha : 0 < a) (hn : 0 < n) (hnN : n ≤ N) :
    mobiusDifference n (channelPrefix a N u) =
      (n : ℝ) * (u n - if a ∣ n then u (n / a) else 0) := by
  rw [show channelPrefix a N u =
    (fun k => ∑ m ∈ Finset.Icc 1 N, u m * certificateGenerator a m k) from rfl,
    mobiusDifference_sum]
  simp_rw [mobiusDifference_generator n a _ hn, mul_sub]
  rw [Finset.sum_sub_distrib, incoming_prefix_sum a N n u ha hn hnN]
  have ho : (∑ m ∈ Finset.Icc 1 N,
      u m * (if n = m then (m : ℝ) else 0)) = u n * (n : ℝ) := by
    rw [Finset.sum_eq_single n]
    · simp
    · intro m hm hne
      simp [Ne.symm hne]
    · intro hnot
      exact (hnot (Finset.mem_Icc.mpr ⟨hn, hnN⟩)).elim
  rw [ho]
  ring

/-- Equation (42) follows from exact interpolation in the two actual channels. -/
theorem twoChannelPrefix_exact_head_incidence (N n : ℕ) (u v : ℕ → ℝ)
    (hn : 0 < n) (hnN : n ≤ N)
    (hhead : ∀ k, 0 < k → k ≤ N → twoChannelPrefix N u v k = 1) :
    u n + v n - (if 2 ∣ n then u (n / 2) else 0) -
      (if 3 ∣ n then v (n / 3) else 0) =
        (ArithmeticFunction.moebius n : ℝ) / (n : ℝ) := by
  have hz : twoChannelPrefix N u v 0 = 0 := by
    simp [twoChannelPrefix, channelPrefix, certificateGenerator]
  have he := exact_head_mobiusDifference hz hhead hn hnN
  change mobiusDifference n
    (fun k => channelPrefix 2 N u k + channelPrefix 3 N v k) = _ at he
  rw [mobiusDifference_add,
    channelPrefix_mobiusDifference 2 N n u (by omega) hn hnN,
    channelPrefix_mobiusDifference 3 N n v (by omega) hn hnN] at he
  have hnR : (n : ℝ) ≠ 0 := by positivity
  apply (eq_div_iff hnR).mpr
  nlinarith

/-- Actual generator value on the entire first positive dilation block. -/
theorem certificateGenerator_first_block (a n k : ℕ)
    (ha : 2 ≤ a) (hn : 0 < n) (hlo : n ≤ k) (hhi : k < 2 * n) :
    certificateGenerator a n k = (n : ℝ) := by
  have hkan : k < a * n := lt_of_lt_of_le hhi (Nat.mul_le_mul_right n ha)
  have hmod : k % n = k - n := Nat.mod_eq_sub_mod hlo |>.trans
    (Nat.mod_eq_of_lt (by omega))
  simp only [certificateGenerator, Nat.mod_eq_of_lt hkan, hmod]
  rw [Nat.cast_sub hlo]
  ring

/-- The first-block cost is an equality, preceding all lower-bound arguments. -/
theorem twoChannel_first_block_energy (n : ℕ) (u v : ℝ) (hn : 0 < n) :
    (∑ k ∈ Finset.Ico n (2 * n), positiveWeight k *
      (u * certificateGenerator 2 n k + v * certificateGenerator 3 n k) ^ 2) =
        (n : ℝ) / 2 * (u + v) ^ 2 := by
  have hg : (∑ k ∈ Finset.Ico n (2 * n), positiveWeight k *
      (u * certificateGenerator 2 n k + v * certificateGenerator 3 n k) ^ 2) =
      (∑ k ∈ Finset.Ico n (2 * n), positiveWeight k) *
        ((n : ℝ) * (u + v)) ^ 2 := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro k hk
    rw [certificateGenerator_first_block 2 n k (by omega) hn
      (Finset.mem_Ico.mp hk).1 (Finset.mem_Ico.mp hk).2,
      certificateGenerator_first_block 3 n k (by omega) hn
      (Finset.mem_Ico.mp hk).1 (Finset.mem_Ico.mp hk).2]
    ring
  rw [hg, positiveWeight_interval n (2 * n) hn (by omega)]
  push_cast
  have hnR : (n : ℝ) ≠ 0 := by positivity
  field_simp
  ring

/-- The first-block identity applies to the actual fixed-prefix increments. -/
theorem twoChannelPrefix_increment_block_energy (N : ℕ) (u v : ℕ → ℝ) :
    (∑ k ∈ Finset.Ico (N + 1) (2 * (N + 1)), positiveWeight k *
      (twoChannelPrefix (N + 1) u v k - twoChannelPrefix N u v k) ^ 2) =
        ((N + 1 : ℕ) : ℝ) / 2 * (u (N + 1) + v (N + 1)) ^ 2 := by
  simp_rw [twoChannelPrefix_succ_sub]
  exact twoChannel_first_block_energy (N + 1) (u (N + 1)) (v (N + 1)) (by omega)

end
end RiemannResearch.RH.Pareto
