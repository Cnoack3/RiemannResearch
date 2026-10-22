/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.Analysis.FiniteHarmonicBounds
import RiemannResearch.RH.AdjacentPacketCovarianceTransfer

/-!
# Uniform diagonal and separated-offset packet covariance bounds

These estimates retain the full signed digit covariance before transferring to
actual Hilbert packets. Separation removes the finite head exactly; only the
complete tail is bounded in absolute value.
-/

namespace RiemannResearch.RH.Pareto.AdjacentPacket
noncomputable section
open AdjacentDigit RiemannResearch.Analysis

/-- Binary and ternary diagonal entries at any index between k and 5k have
    the correct common harmonic coefficient, with a scale-independent error. -/
theorem packet_diagonal_harmonic_bound (p m k : ℕ) (hp : 0 < p)
    (hs : p=2 ∨ p=3) (hk : 0 < k) (hkm : k ≤ m) (hmhi : m ≤ 5*k) :
    |‖packet p m hp (by omega)‖^2-((p:ℝ)-1)*(harmonic k:ℝ)| ≤
      twoSeedCovarianceError+2000 := by
  have hm : 0 < m := by omega
  have hgap := harmonic_bounded_ratio_gap k m 5 hkm hmhi
  norm_num only [Nat.cast_ofNat] at hgap
  rcases hs with rfl | rfl
  · have he := packet_harmonic_error 2 m (by omega) hm (a:=1) (E:=28)
      (by norm_num) (by norm_num) (by simpa using binary_covariance_harmonic_error m hm)
    simp only [one_mul] at he
    have ht := abs_add_le (‖packet 2 m (by omega) hm‖^2-(harmonic m:ℝ))
      ((harmonic m:ℝ)-(harmonic k:ℝ))
    simp only [sub_add_sub_cancel] at ht
    norm_num only [Nat.cast_ofNat, show (2:ℝ)-1=1 by norm_num, one_mul] at ⊢
    unfold twoSeedCovarianceError twoSeedPacketLinear twoSeedPacketError twoSeedEnergy
    nlinarith [sq_nonneg ‖digitHilbert 2 1 (by omega) (by omega)‖,
      sq_nonneg ‖digitHilbert 3 1 (by omega) (by omega)‖]
  · have he := packet_harmonic_error 3 m (by omega) hm (a:=2) (E:=81)
      (by norm_num) (by norm_num) (ternary_covariance_harmonic_error m hm)
    have hh : |2*(harmonic m:ℝ)-2*(harmonic k:ℝ)| ≤ 10 := by
      rw [← mul_sub, abs_mul, abs_of_pos (by norm_num : (0:ℝ)<2)]
      linarith
    have ht := abs_add_le (‖packet 3 m (by omega) hm‖^2-2*(harmonic m:ℝ))
      (2*(harmonic m:ℝ)-2*(harmonic k:ℝ))
    simp only [sub_add_sub_cancel] at ht
    norm_num only [Nat.cast_ofNat, show (3:ℝ)-1=2 by norm_num] at ⊢
    unfold twoSeedCovarianceError twoSeedPacketLinear twoSeedPacketError twoSeedEnergy
    nlinarith [sq_nonneg ‖digitHilbert 2 1 (by omega) (by omega)‖,
      sq_nonneg ‖digitHilbert 3 1 (by omega) (by omega)‖]

/-- A quadratic cutoff controls the entire scaled covariance of two distinct
    offsets at the same base scale. The estimate is uniform in either seed. -/
theorem same_scale_scaled_covariance_bound (p q a k r s : ℕ)
    (hp : 0 < p) (hq : 0 < q) (hps : p=2 ∨ p=3) (hqs : q=2 ∨ q=3)
    (ha : a=2 ∨ a=3) (hk : 24 ≤ k) (hr : r ≤ 2) (hs : s ≤ 2) (hrs : r ≠ s) :
    |((a*k+r:ℕ):ℝ)*((a*k+s:ℕ):ℝ)*crossCovariance p q (a*k+r) (a*k+s)| ≤ 1800 := by
  let K := k*k/4
  have hkpos : 0 < k := by omega
  have hkk : 8 ≤ k*k := by nlinarith
  have hKpos : 0 < K := by dsimp [K]; omega
  have hKlower : k*k ≤ 8*K := by dsimp [K]; omega
  have hKupper : 4*K ≤ k*k := by dsimp [K]; omega
  have hak : k ≤ a*k := by rcases ha with rfl | rfl <;> omega
  have hapos : 0 < a*k := by omega
  have hgeom : 4*K ≤ (a*k)*(a*k) :=
    hKupper.trans (Nat.mul_le_mul hak hak)
  have hcross := separated_offsets_covariance_bound p q (a*k) r s K
    hp hq hapos hr hs hrs hKpos hgeom
  have hmr : a*k+r ≤ 5*k := by rcases ha with rfl | rfl <;> omega
  have hms : a*k+s ≤ 5*k := by rcases ha with rfl | rfl <;> omega
  have hmr' : ((a*k+r:ℕ):ℝ) ≤ 5*(k:ℝ) := by exact_mod_cast hmr
  have hms' : ((a*k+s:ℕ):ℝ) ≤ 5*(k:ℝ) := by exact_mod_cast hms
  have hmn : ((a*k+r:ℕ):ℝ)*((a*k+s:ℕ):ℝ) ≤ 25*(k:ℝ)*(k:ℝ) := by
    have h := mul_le_mul hmr' hms' (by positivity : (0:ℝ)≤((a*k+s:ℕ):ℝ))
      (by positivity : (0:ℝ)≤5*(k:ℝ))
    nlinarith
  have hpq : (p:ℝ)*q ≤ 9 := by
    rcases hps with rfl | rfl <;> rcases hqs with rfl | rfl <;> norm_num
  have hKlower' : (k:ℝ)*(k:ℝ) ≤ 8*(K:ℝ) := by exact_mod_cast hKlower
  have hKpos' : (0:ℝ) < K := by exact_mod_cast hKpos
  have hmn0 : (0:ℝ) ≤ ((a*k+r:ℕ):ℝ)*((a*k+s:ℕ):ℝ) := by positivity
  calc
    _ = ((a*k+r:ℕ):ℝ)*((a*k+s:ℕ):ℝ)*
        |crossCovariance p q (a*k+r) (a*k+s)| := by
      rw [abs_mul, abs_of_nonneg hmn0]
    _ ≤ ((a*k+r:ℕ):ℝ)*((a*k+s:ℕ):ℝ)*((p:ℝ)*q/(K:ℝ)) :=
      mul_le_mul_of_nonneg_left hcross hmn0
    _ = (((a*k+r:ℕ):ℝ)*((a*k+s:ℕ):ℝ)*((p:ℝ)*q))/(K:ℝ) := by ring
    _ ≤ 1800 := by
      apply (div_le_iff₀ hKpos').mpr
      have h1 := mul_le_mul_of_nonneg_left hpq hmn0
      have h2 := mul_le_mul_of_nonneg_right hmn (by norm_num : (0:ℝ)≤9)
      nlinarith

/-- Distinct offsets at the same base scale remain uniformly bounded after
    returning to the actual original packets. -/
theorem same_scale_packet_covariance_bound (p q a k r s : ℕ)
    (hp : 0 < p) (hq : 0 < q) (hps : p=2 ∨ p=3) (hqs : q=2 ∨ q=3)
    (ha : a=2 ∨ a=3) (hk : 24 ≤ k) (hr : r ≤ 2) (hs : s ≤ 2) (hrs : r ≠ s) :
    |inner ℝ (packet p (a*k+r) hp (by rcases ha with rfl | rfl <;> omega))
      (packet q (a*k+s) hq (by rcases ha with rfl | rfl <;> omega))| ≤
      twoSeedCovarianceError+1800 := by
  have hkm : k ≤ a*k+r := by rcases ha with rfl | rfl <;> omega
  have hkn : k ≤ a*k+s := by rcases ha with rfl | rfl <;> omega
  have hmr : a*k+r ≤ 5*k := by rcases ha with rfl | rfl <;> omega
  have hms : a*k+s ≤ 5*k := by rcases ha with rfl | rfl <;> omega
  have ht := packet_cross_covariance_transfer p q (a*k+r) (a*k+s) k hp hq
    (by omega) (by omega) hps hqs (by omega) hkm hkn hmr hms
  have hc := same_scale_scaled_covariance_bound p q a k r s hp hq hps hqs ha hk hr hs hrs
  have he := abs_add_le
    (inner ℝ (packet p (a*k+r) hp (by omega)) (packet q (a*k+s) hq (by omega)) -
      ((a*k+r:ℕ):ℝ)*((a*k+s:ℕ):ℝ)*crossCovariance p q (a*k+r) (a*k+s))
    (((a*k+r:ℕ):ℝ)*((a*k+s:ℕ):ℝ)*crossCovariance p q (a*k+r) (a*k+s))
  simp only [sub_add_cancel] at he
  linarith

/-- The old mixed digit covariance has uniformly bounded scaled energy. -/
theorem old_mixed_scaled_covariance_bound (k : ℕ) (hk : 0 < k) :
    |(k:ℝ)*(k:ℝ)*crossCovariance 2 3 k k| ≤ 30 := by
  have he : crossCovariance 2 3 k k = covariance 2 3 k := rfl
  rw [he, abs_mul, abs_of_nonneg (by positivity : (0:ℝ)≤(k:ℝ)*(k:ℝ))]
  have h := mixed_scaled_covariance_bound k hk
  rw [abs_mul, abs_of_nonneg (by positivity : (0:ℝ)≤(k:ℝ)*((k:ℝ)+1))] at h
  have hm : (k:ℝ)*(k:ℝ) ≤ (k:ℝ)*((k:ℝ)+1) := by nlinarith [Nat.cast_nonneg (α:=ℝ) k]
  exact (mul_le_mul_of_nonneg_right hm (abs_nonneg _)).trans h

/-- The mixed entry of the two old actual packets has a fixed absolute bound. -/
theorem old_mixed_packet_covariance_bound (k : ℕ) (hk : 0 < k) :
    |inner ℝ (packet 2 k (by omega) hk) (packet 3 k (by omega) hk)| ≤
      twoSeedCovarianceError+30 := by
  have ht := packet_cross_covariance_transfer 2 3 k k k (by omega) (by omega)
    hk hk (Or.inl rfl) (Or.inr rfl) hk le_rfl le_rfl (by omega) (by omega)
  have hc := old_mixed_scaled_covariance_bound k hk
  have he := abs_add_le
    (inner ℝ (packet 2 k (by omega) hk) (packet 3 k (by omega) hk) -
      (k:ℝ)*(k:ℝ)*crossCovariance 2 3 k k)
    ((k:ℝ)*(k:ℝ)*crossCovariance 2 3 k k)
  simp only [sub_add_cancel] at he
  linarith

end
end RiemannResearch.RH.Pareto.AdjacentPacket
