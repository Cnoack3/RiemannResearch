/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.Analysis.SmallColumnCovariance
import RiemannResearch.RH.AdjacentPacketNormBounds
import RiemannResearch.RH.ResonantDigitOverlap

/-!
# Uniform transfer from digit covariance to actual packet covariance

Source: the two-three resonance-cell continuation, 15 September 2026.
The complete signed cross-index covariance is transferred to the original
packets with an explicit constant independent of the common scale.
-/

namespace RiemannResearch.RH.Pareto.AdjacentPacket
noncomputable section
open AdjacentDigit

/-- Fixed one-digit energy controlling either seed. -/
def twoSeedEnergy : ℝ :=
  ‖digitHilbert 2 1 (by omega) (by omega)‖^2 +
  ‖digitHilbert 3 1 (by omega) (by omega)‖^2

/-- Common bounded packet-energy error from the binary and ternary estimates. -/
def twoSeedPacketError : ℝ := 2*twoSeedEnergy+249

/-- Linear packet-energy control for indices between k and 5k. -/
def twoSeedPacketLinear : ℝ := 10+twoSeedPacketError

/-- Fixed error in transfer of a full mixed covariance. -/
def twoSeedCovarianceError : ℝ := 2*twoSeedEnergy+twoSeedPacketLinear

theorem seed_energy_le (p : ℕ) (hp : 0 < p) (hs : p=2 ∨ p=3) :
    ‖digitHilbert p 1 hp (by omega)‖^2 ≤ twoSeedEnergy := by
  rcases hs with rfl | rfl <;> unfold twoSeedEnergy <;>
    nlinarith [sq_nonneg ‖digitHilbert 2 1 (by omega) (by omega)‖,
      sq_nonneg ‖digitHilbert 3 1 (by omega) (by omega)‖]

/-- Uniform small-column energy at the common scale k. -/
theorem shifted_digit_common_scale (p m k : ℕ) (hp : 0 < p)
    (hs : p=2 ∨ p=3) (hkm : k ≤ m) :
    (k:ℝ)*‖digitHilbert p (m+1) hp (by omega)‖^2 ≤ twoSeedEnergy := by
  have hkm' : (k:ℝ) ≤ ((m+1:ℕ):ℝ) := by
    exact_mod_cast (Nat.le_trans hkm (Nat.le_succ m))
  calc
    _ ≤ ((m+1:ℕ):ℝ)*‖digitHilbert p (m+1) hp (by omega)‖^2 :=
      mul_le_mul_of_nonneg_right hkm' (sq_nonneg _)
    _ = ‖digitHilbert p 1 hp (by omega)‖^2 := digit_energy_scaling p (m+1) hp (by omega)
    _ ≤ twoSeedEnergy := seed_energy_le p hp hs

/-- A uniform actual-packet bound sufficient for weighted Young transfer. -/
theorem packet_common_scale (p m k : ℕ) (hp : 0 < p) (hm : 0 < m)
    (hs : p=2 ∨ p=3) (hk : 0 < k) (hmhi : m ≤ 5*k) :
    ‖packet p m hp hm‖^2 ≤ (k:ℝ)*twoSeedPacketLinear := by
  have hm0 : (0:ℝ) < m := by exact_mod_cast hm
  have hm1 : (1:ℝ) ≤ m := by exact_mod_cast hm
  have hk1 : (1:ℝ) ≤ k := by exact_mod_cast hk
  have hm5 : (m:ℝ) ≤ 5*(k:ℝ) := by exact_mod_cast hmhi
  have hlog0 := Real.log_nonneg hm1
  have hlog : Real.log (m:ℝ) ≤ 5*(k:ℝ) := by
    have h := Real.log_le_sub_one_of_pos hm0
    linarith
  have hpacket : ‖packet p m hp hm‖^2 ≤
      2*Real.log (m:ℝ)+twoSeedPacketError := by
    rcases hs with rfl | rfl
    · have h := (abs_le.mp (binary_packet_log_bound m hm)).2
      unfold twoSeedPacketError twoSeedEnergy
      nlinarith [sq_nonneg ‖digitHilbert 3 1 (by omega) (by omega)‖]
    · have h := (abs_le.mp (ternary_packet_log_bound m hm)).2
      unfold twoSeedPacketError twoSeedEnergy
      nlinarith [sq_nonneg ‖digitHilbert 2 1 (by omega) (by omega)‖]
  have hC : 0 ≤ twoSeedPacketError := by unfold twoSeedPacketError twoSeedEnergy; positivity
  have hCk := mul_le_mul_of_nonneg_right hk1 hC
  unfold twoSeedPacketLinear
  nlinarith

/-- Every cross-index digit asymptotic transfers to the genuine packet Gram entry.
The complete signed tail is already inside `crossCovariance`. -/
theorem packet_cross_covariance_transfer (p q m n k : ℕ)
    (hp : 0 < p) (hq : 0 < q) (hm : 0 < m) (hn : 0 < n)
    (hps : p=2 ∨ p=3) (hqs : q=2 ∨ q=3) (hk : 0 < k)
    (hkm : k ≤ m) (hkn : k ≤ n) (hmhi : m ≤ 5*k) (hnhi : n ≤ 5*k) :
    |inner ℝ (packet p m hp hm) (packet q n hq hn) -
      (m:ℝ)*(n:ℝ)*crossCovariance p q m n| ≤ twoSeedCovarianceError := by
  let A := packet p m hp hm
  let A' := packet q n hq hn
  let B := digitHilbert p (m+1) hp (by omega)
  let B' := digitHilbert q (n+1) hq (by omega)
  have hu : B-A = (m:ℝ) •
      (digitHilbert p m hp hm-digitHilbert p (m+1) hp (by omega)) := by
    dsimp [A, B]
    rw [packet_eq_digit_correction]
    abel
  have hu' : B'-A' = (n:ℝ) •
      (digitHilbert q n hq hn-digitHilbert q (n+1) hq (by omega)) := by
    dsimp [A', B']
    rw [packet_eq_digit_correction]
    abel
  have he : inner ℝ (B-A) (B'-A') = (m:ℝ)*(n:ℝ)*crossCovariance p q m n := by
    rw [hu, hu', real_inner_smul_left, real_inner_smul_right,
      ← crossCovariance_eq_inner p q m n hp hq hm hn]
    ring
  change |inner ℝ A A'-(m:ℝ)*(n:ℝ)*crossCovariance p q m n| ≤ _
  rw [← he]
  exact RiemannResearch.Analysis.SmallColumnCovariance.covariance_error A A' B B'
    (by exact_mod_cast hk : (1:ℝ) ≤ (k:ℝ))
    (shifted_digit_common_scale p m k hp hps hkm)
    (shifted_digit_common_scale q n k hq hqs hkn)
    (packet_common_scale p m k hp hm hps hk hmhi)
    (packet_common_scale q n k hq hn hqs hk hnhi)

end
end RiemannResearch.RH.Pareto.AdjacentPacket
