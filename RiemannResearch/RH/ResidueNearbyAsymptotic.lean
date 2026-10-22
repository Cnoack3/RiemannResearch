import RiemannResearch.RH.NearbyDilationAsymptotic
import RiemannResearch.RH.ResidueJumpCovariance

/-!
# The gcd leading coefficient for every pair of residue seeds

Source: user-provided argument, RH_CRT_Packet_Research_2026-09-09.md,
Section 3. The coefficient is supplied by the exact finite-period covariance
identity and the full weighted nearby-packet limit.
-/

namespace RiemannResearch.RH.Pareto
open Filter RiemannResearch.Analysis
noncomputable section

theorem residueNearbyGram_div_log_tendsto (a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    Tendsto (fun n : ℕ => paretoInner (nearbyDilationPacket (residue a) n)
      (nearbyDilationPacket (residue b) n) / Real.log n)
      atTop (nhds ((Nat.gcd a b : ℝ)-1)) := by
  have hQ : 0 < a*b := Nat.mul_pos ha hb
  have haQ : a ∣ a*b := ⟨b, rfl⟩
  have hbQ : b ∣ a*b := ⟨a, Nat.mul_comm a b⟩
  have hbound (c : ℕ) (hc : 0 < c) (k : ℕ) : |residue c k| ≤ (c:ℝ) := by
    unfold residue
    rw [abs_of_nonneg (Nat.cast_nonneg _)]
    exact_mod_cast (Nat.le_of_lt (Nat.mod_lt k hc))
  have hper (c : ℕ) (hc : c ∣ a*b) (k : ℕ) : residue c (k+a*b) = residue c k := by
    simp [residue, Nat.add_mod, Nat.mod_eq_zero_of_dvd hc]
  have h := nearbyDilationGram_div_log_tendsto (hbound a ha) (hbound b hb)
    (by simp [residue]) (by simp [residue]) (a*b) hQ (hper a haQ) (hper b hbQ)
  have he : periodicMean (fun j => (residue a (j+1)-residue a j)*
      (residue b (j+1)-residue b j)) (a*b) = (Nat.gcd a b:ℝ)-1 :=
    residueJump_covariance_mean a b (a*b) hQ haQ hbQ
  simpa only [he] using h

end
end RiemannResearch.RH.Pareto
