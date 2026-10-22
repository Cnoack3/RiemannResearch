import RiemannResearch.RH.NearbyDilationAsymptotic
import RiemannResearch.RH.OptimizedResiduePackets

/-!
# Actual asymptotic energies of the optimized legal correction packets

Source: user-provided argument, RH_CRT_Packet_Research_2026-09-09.md,
Sections 3--6. These are limits of the complete infinite weighted Gram
entries, with boundedness and periodicity supplied by the concrete seeds.
They do not assert uniform boundedness of a global approximation recursion.
-/

namespace RiemannResearch.RH.Pareto
open scoped BigOperators
open Filter RiemannResearch.Analysis
noncomputable section

theorem optimizedResidueSeed_abs_le (k : ℕ) : |optimizedResidueSeed k| ≤ 1 := by
  rw [optimizedResidueSeed_mod_six k]
  have hk : k % 6 < 6 := Nat.mod_lt _ (by omega)
  interval_cases h : k % 6 <;> norm_num [h, optimizedResidueSeed, residue]

theorem complementaryResidueSeed_abs_le (k : ℕ) : |complementaryResidueSeed k| ≤ 2 := by
  have hr : |residue 2 k| ≤ 1 := by
    have hk : k % 2 < 2 := Nat.mod_lt _ (by omega)
    unfold residue
    rw [abs_of_nonneg (Nat.cast_nonneg _)]
    exact_mod_cast (show k % 2 ≤ 1 by omega)
  have h := abs_sub_le (residue 2 k) 0 (optimizedResidueSeed k)
  simp only [sub_zero, zero_sub, abs_neg] at h
  change |residue 2 k-optimizedResidueSeed k| ≤ 2
  linarith [optimizedResidueSeed_abs_le k]

theorem optimizedNearby_energy_div_log_tendsto :
    Tendsto (fun n : ℕ => paretoInner (nearbyDilationPacket optimizedResidueSeed n)
      (nearbyDilationPacket optimizedResidueSeed n) / Real.log n) atTop (nhds (1/2:ℝ)) := by
  have h := nearbyDilationGram_div_log_tendsto optimizedResidueSeed_abs_le
    optimizedResidueSeed_abs_le optimizedResidueSeed_zero optimizedResidueSeed_zero
    6 (by norm_num) optimizedResidueSeed_periodic optimizedResidueSeed_periodic
  have he : periodicMean (fun j => (optimizedResidueSeed (j+1)-optimizedResidueSeed j)*
      (optimizedResidueSeed (j+1)-optimizedResidueSeed j)) 6 = (1/2:ℝ) :=
    sixJumpInner_optimized
  simpa only [he] using h

theorem complementaryNearby_energy_div_log_tendsto :
    Tendsto (fun n : ℕ => paretoInner (nearbyDilationPacket complementaryResidueSeed n)
      (nearbyDilationPacket complementaryResidueSeed n) / Real.log n) atTop (nhds (1/2:ℝ)) := by
  have h := nearbyDilationGram_div_log_tendsto complementaryResidueSeed_abs_le
    complementaryResidueSeed_abs_le complementaryResidueSeed_zero complementaryResidueSeed_zero
    6 (by norm_num) complementaryResidueSeed_periodic complementaryResidueSeed_periodic
  have he : periodicMean (fun j => (complementaryResidueSeed (j+1)-complementaryResidueSeed j)*
      (complementaryResidueSeed (j+1)-complementaryResidueSeed j)) 6 = (1/2:ℝ) :=
    sixJumpInner_complementary
  simpa only [he] using h

theorem optimizedComplementaryNearby_gram_div_log_tendsto :
    Tendsto (fun n : ℕ => paretoInner (nearbyDilationPacket optimizedResidueSeed n)
      (nearbyDilationPacket complementaryResidueSeed n) / Real.log n) atTop (nhds (0:ℝ)) := by
  have h := nearbyDilationGram_div_log_tendsto optimizedResidueSeed_abs_le
    complementaryResidueSeed_abs_le optimizedResidueSeed_zero complementaryResidueSeed_zero
    6 (by norm_num) optimizedResidueSeed_periodic complementaryResidueSeed_periodic
  have he : periodicMean (fun j => (optimizedResidueSeed (j+1)-optimizedResidueSeed j)*
      (complementaryResidueSeed (j+1)-complementaryResidueSeed j)) 6 = (0:ℝ) :=
    sixJumpInner_optimized_complementary
  simpa only [he] using h

theorem nearbyCorrectionGram_scaled {φ ψ : ℕ → ℝ} {C D : ℝ}
    (hφ : ∀ k, |φ k| ≤ C) (hψ : ∀ k, |ψ k| ≤ D) (n : ℕ) (hn : 0 < n) :
    (n:ℝ)^2 * paretoInner (-(1/(n:ℝ)) • nearbyDilationPacket φ n)
      (-(1/(n:ℝ)) • nearbyDilationPacket ψ n) =
      paretoInner (nearbyDilationPacket φ n) (nearbyDilationPacket ψ n) := by
  have hn0 : (n:ℝ) ≠ 0 := by positivity
  have hs := nearbyDilationGram_summable hφ hψ n
  have he : (fun k => positiveWeight k *
      ((-(1/(n:ℝ)) • nearbyDilationPacket φ n) k *
        (-(1/(n:ℝ)) • nearbyDilationPacket ψ n) k)) =
      (fun k => (1/(n:ℝ)^2) * (positiveWeight k *
        (nearbyDilationPacket φ n k * nearbyDilationPacket ψ n k))) := by
    funext k
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  unfold paretoInner
  rw [he, hs.tsum_mul_left]
  field_simp

theorem optimizedCorrection_energy_scaled_tendsto :
    Tendsto (fun n : ℕ => (n:ℝ)^2 *
      paretoInner (optimizedCorrectionSequence n) (optimizedCorrectionSequence n) /
      Real.log n) atTop (nhds (1/2:ℝ)) := by
  apply optimizedNearby_energy_div_log_tendsto.congr'
  filter_upwards [eventually_gt_atTop (0:ℕ)] with n hn
  rw [optimizedCorrectionSequence,
    nearbyCorrectionGram_scaled optimizedResidueSeed_abs_le optimizedResidueSeed_abs_le n hn]

theorem complementaryCorrection_energy_scaled_tendsto :
    Tendsto (fun n : ℕ => (n:ℝ)^2 *
      paretoInner (complementaryCorrectionSequence n) (complementaryCorrectionSequence n) /
      Real.log n) atTop (nhds (1/2:ℝ)) := by
  apply complementaryNearby_energy_div_log_tendsto.congr'
  filter_upwards [eventually_gt_atTop (0:ℕ)] with n hn
  rw [complementaryCorrectionSequence,
    nearbyCorrectionGram_scaled complementaryResidueSeed_abs_le complementaryResidueSeed_abs_le n hn]

theorem optimizedComplementaryCorrection_gram_scaled_tendsto :
    Tendsto (fun n : ℕ => (n:ℝ)^2 *
      paretoInner (optimizedCorrectionSequence n) (complementaryCorrectionSequence n) /
      Real.log n) atTop (nhds (0:ℝ)) := by
  apply optimizedComplementaryNearby_gram_div_log_tendsto.congr'
  filter_upwards [eventually_gt_atTop (0:ℕ)] with n hn
  rw [optimizedCorrectionSequence, complementaryCorrectionSequence,
    nearbyCorrectionGram_scaled optimizedResidueSeed_abs_le complementaryResidueSeed_abs_le n hn]

end
end RiemannResearch.RH.Pareto
