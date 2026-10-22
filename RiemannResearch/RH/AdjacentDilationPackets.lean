/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.DilationWaveletAlgebra
import RiemannResearch.RH.ParetoResidueMellinContinuation

/-!
# Ordinary adjacent-dilation packets and their source correlations

Source: independently derived continuation of Christian Noack's arithmetic
research, 15 September 2026. The packet is a difference of actual legal
dilations. Its target mean vanishes identically. The exact Mellin factor
retains zeta and the dilation-frequency difference. The source-correlation
identity makes no arithmetic lower-bound assertion.
-/

namespace RiemannResearch.RH.Pareto.AdjacentPacket
noncomputable section

def generator (p m : ℕ) (hp : 0 < p) (hm : 0 < m) : ThresholdHilbert :=
  hilbertDilation m hm (digitHilbert p 1 hp (by omega))

def packet (p m : ℕ) (hp : 0 < p) (hm : 0 < m) : ThresholdHilbert :=
  generator p (m+1) hp (by omega) - generator p m hp hm

/-- Normalization agrees with the original m times digit generator. -/
theorem generator_eq_scaled_digit (p m : ℕ) (hp : 0 < p) (hm : 0 < m) :
    generator p m hp hm = (m:ℝ) • digitHilbert p m hp hm := by
  apply hilbertSequence_injective
  simp only [generator, hilbertDilation_sequence, hilbertSequence_smul,
    hilbertSequence_digitHilbert]
  funext n
  simp [dilation, digitSequence]

/-- Every adjacent packet is exactly orthogonal to the target constant. -/
theorem packet_mean_zero (p m : ℕ) (hp : 0 < p) (hm : 0 < m) :
    inner ℝ (packet p m hp hm) hilbertOne = 0 := by
  unfold packet generator
  rw [inner_sub_left, hilbert_inner_one, hilbert_inner_one,
    hilbertDilation_mean, hilbertDilation_mean]
  ring

/-- At the optimum, packet-source correlation comes entirely from the old fit. -/
theorem packet_source_correlation (P : Submodule ℝ ThresholdHilbert)
    [P.HasOrthogonalProjection] (p m : ℕ) (hp : 0 < p) (hm : 0 < m) :
    inner ℝ (hilbertOne - P.starProjection hilbertOne) (packet p m hp hm) =
      -inner ℝ (P.starProjection hilbertOne) (packet p m hp hm) := by
  have hz : inner ℝ hilbertOne (packet p m hp hm) = 0 := by
    calc
      _ = inner ℝ (packet p m hp hm) hilbertOne := real_inner_comm _ _
      _ = 0 := packet_mean_zero p m hp hm
  rw [inner_sub_left, hz, zero_sub]

/-- Exact adjacent-frequency Mellin factor on the continuity half-plane. -/
theorem packet_mellin (p m : ℕ) (hp : 0 < p) (hm : 0 < m)
    (s : ℂ) (hs : (1 / 2 : ℝ) < s.re) (hs1 : s ≠ 1) :
    paretoMellin (packet p m hp hm) s =
      riemannZeta s / s * (1 - (p:ℂ)^(1-s)) *
        (((m+1:ℕ):ℂ)^(1-s) - (m:ℂ)^(1-s)) := by
  unfold packet generator
  have hsub (f g : ThresholdHilbert) :
      paretoMellin (f-g) s = paretoMellin f s - paretoMellin g s :=
    (paretoMellinContinuous s hs).map_sub f g
  rw [hsub,
    paretoMellin_generator_zeta p (m+1) hp (by omega) s hs hs1,
    paretoMellin_generator_zeta p m hp hm s hs hs1]
  ring

end
end RiemannResearch.RH.Pareto.AdjacentPacket
