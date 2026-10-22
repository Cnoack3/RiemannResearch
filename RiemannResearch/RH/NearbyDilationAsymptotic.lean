import RiemannResearch.RH.NearbyDilationGram
import RiemannResearch.Analysis.PeriodicHarmonicMean

/-!
# Logarithmic leading coefficient of fixed periodic nearby packets

Source: user-provided argument, RH_CRT_Packet_Research_2026-09-09.md,
Section 3. This theorem uses the complete exact Gram decomposition, its
uniform remainder bound, and the unconditional periodic harmonic mean.
The seeds are fixed; no uniformity in varying seeds is asserted.
-/

namespace RiemannResearch.RH.Pareto
open scoped BigOperators
open Filter RiemannResearch.Analysis
noncomputable section

theorem nearbyDilationGram_div_log_tendsto {φ ψ : ℕ → ℝ} {C D : ℝ}
    (hφ : ∀ k, |φ k| ≤ C) (hψ : ∀ k, |ψ k| ≤ D)
    (hφ0 : φ 0 = 0) (hψ0 : ψ 0 = 0)
    (p : ℕ) (hp : 0 < p)
    (hφp : ∀ k, φ (k+p) = φ k) (hψp : ∀ k, ψ (k+p) = ψ k) :
    Tendsto (fun n : ℕ =>
      paretoInner (nearbyDilationPacket φ n) (nearbyDilationPacket ψ n) / Real.log n)
      atTop (nhds (periodicMean (fun j => (φ (j+1)-φ j)*(ψ (j+1)-ψ j)) p)) := by
  let a := fun j => (φ (j+1)-φ j)*(ψ (j+1)-ψ j)
  have hC : 0 ≤ C := (abs_nonneg (φ 0)).trans (hφ 0)
  have ha (j : ℕ) : |a j| ≤ 4*C*D := by
    have hdφ : |φ (j+1)-φ j| ≤ 2*C := by
      have ht := abs_sub_le (φ (j+1)) 0 (φ j)
      simp only [sub_zero, zero_sub, abs_neg] at ht
      linarith [hφ (j+1), hφ j]
    have hdψ : |ψ (j+1)-ψ j| ≤ 2*D := by
      have ht := abs_sub_le (ψ (j+1)) 0 (ψ j)
      simp only [sub_zero, zero_sub, abs_neg] at ht
      linarith [hψ (j+1), hψ j]
    dsimp [a]
    rw [abs_mul]
    nlinarith [mul_le_mul hdφ hdψ (abs_nonneg _) (by positivity : 0 ≤ 2*C)]
  have hap (j : ℕ) : a (j+p) = a j := by
    dsimp [a]
    rw [show j+p+1 = (j+1)+p by omega, hφp, hψp, hφp, hψp]
  have hmain := periodic_harmonic_div_log_tendsto a p hp hap (4*C*D) ha
  have he := bounded_error_div_log_tendsto_zero
    (fun n => paretoInner (nearbyDilationPacket φ n) (nearbyDilationPacket ψ n) -
      nearbyDilationHarmonicMain φ ψ n)
    (15*C*D) (fun n hn => nearbyDilationGram_harmonic_error_bound hφ hψ hφ0 hψ0 n hn)
  have h := hmain.add he
  simp only [add_zero] at h
  apply h.congr'
  filter_upwards [] with n
  dsimp [nearbyDilationHarmonicMain, a]
  ring

end
end RiemannResearch.RH.Pareto
