/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.AdjacentDilationPackets
import RiemannResearch.LinearAlgebra.TwoThreeResonanceCell
import Mathlib.Tactic.Abel

/-!
# Exact two-three packet relations and compatible residual sources

Source: independently derived continuation of Christian Noack's arithmetic
research, 15 September 2026. These identities concern the actual Pareto Hilbert
vectors. They identify the common cycle and the legal composite-seed charge;
no covariance asymptotic or positive source lower bound is assumed.
-/

namespace RiemannResearch.RH.Pareto.AdjacentPacket
noncomputable section

private theorem sequence_sub (f g : ThresholdHilbert) :
    hilbertSequence (f-g) = hilbertSequence f-hilbertSequence g :=
  hilbertSequenceLinear.map_sub f g

private theorem sequence_add (f g : ThresholdHilbert) :
    hilbertSequence (f+g) = hilbertSequence f+hilbertSequence g :=
  hilbertSequenceLinear.map_add f g

/-- Actual coordinates, with the integer-dilation normalization retained. -/
theorem generator_sequence_apply (p m : ℕ) (hp : 0 < p) (hm : 0 < m) (n : ℕ) :
    hilbertSequence (generator p m hp hm) n = residue (p*m) n-residue m n := by
  rw [generator_eq_scaled_digit, hilbertSequence_smul, hilbertSequence_digitHilbert]
  exact digitSequence_generator p m n

/-- The commuting dilation square holds in the genuine weighted Hilbert space. -/
theorem generator_cocycle (p q k : ℕ) (hp : 0 < p) (hq : 0 < q) (hk : 0 < k) :
    generator p (q*k) hp (Nat.mul_pos hq hk) -
      generator q (p*k) hq (Nat.mul_pos hp hk) =
    generator p k hp hk-generator q k hq hk := by
  apply hilbertSequence_injective
  funext n
  simp only [sequence_sub, Pi.sub_apply, generator_sequence_apply]
  rw [show p*(q*k) = q*(p*k) by ring]
  ring

/-- Composite seeds are already finite legal combinations of the original seeds. -/
theorem generator_product (p q k : ℕ) (hp : 0 < p) (hq : 0 < q) (hk : 0 < k) :
    generator (p*q) k (Nat.mul_pos hp hq) hk =
      generator p k hp hk + generator q (p*k) hq (Nat.mul_pos hp hk) := by
  apply hilbertSequence_injective
  funext n
  simp only [sequence_add, Pi.add_apply, generator_sequence_apply]
  rw [show (p*q)*k = q*(p*k) by ring]
  ring

/-- The five adjacent packets satisfy this exact relation before projection. -/
theorem two_three_packet_cycle (k : ℕ) (hk : 0 < k) :
    packet 2 (3*k) (by omega) (by omega) +
      packet 2 (3*k+1) (by omega) (by omega) +
      packet 2 (3*k+2) (by omega) (by omega) -
      (packet 3 (2*k) (by omega) (by omega) +
        packet 3 (2*k+1) (by omega) (by omega)) =
      packet 2 k (by omega) hk-packet 3 k (by omega) hk := by
  have h0 := generator_cocycle 2 3 k (by omega) (by omega) hk
  have h1 := generator_cocycle 2 3 (k+1) (by omega) (by omega) (by omega)
  have h := congrArg₂ (fun a b : ThresholdHilbert => a-b) h1 h0
  unfold packet
  simp only [show 3*(k+1) = 3*k+2+1 by omega,
    show 2*(k+1) = 2*k+1+1 by omega] at h
  convert h using 1 <;> abel

/-- The sum of the two new ternary packets supplies the legal six-seed charge. -/
theorem six_packet_decomposition (k : ℕ) (hk : 0 < k) :
    packet 6 k (by omega) hk = packet 2 k (by omega) hk +
      packet 3 (2*k) (by omega) (by omega) +
      packet 3 (2*k+1) (by omega) (by omega) := by
  have h0 := generator_product 2 3 k (by omega) (by omega) hk
  have h1 := generator_product 2 3 (k+1) (by omega) (by omega) (by omega)
  have h := congrArg₂ (fun a b : ThresholdHilbert => a-b) h1 h0
  norm_num only [show 2*(k+1) = 2*k+1+1 by omega] at h
  unfold packet
  convert h using 1
  abel

open RiemannResearch.LinearAlgebra.TwoThreeResonanceCell

/-- The five correlations are taken against the actual source vector. -/
def cellSource (r : ThresholdHilbert) (k : ℕ) (hk : 0 < k) : CellVector :=
  ⟨inner ℝ r (packet 2 (3*k) (by omega) (by omega)),
   inner ℝ r (packet 2 (3*k+1) (by omega) (by omega)),
   inner ℝ r (packet 2 (3*k+2) (by omega) (by omega)),
   inner ℝ r (packet 3 (2*k) (by omega) (by omega)),
   inner ℝ r (packet 3 (2*k+1) (by omega) (by omega))⟩

/-- Orthogonality to the old packets forces compatibility with the cycle. -/
theorem cellSource_compatible (r : ThresholdHilbert) (k : ℕ) (hk : 0 < k)
    (h2 : inner ℝ r (packet 2 k (by omega) hk) = 0)
    (h3 : inner ℝ r (packet 3 k (by omega) hk) = 0) :
    Compatible (cellSource r k hk) := by
  have h := congrArg (fun f : ThresholdHilbert => inner ℝ r f)
    (two_three_packet_cycle k hk)
  simp only [inner_sub_right, inner_add_right, h2, h3] at h
  unfold Compatible binarySum ternarySum cellSource
  dsimp
  linarith

/-- For the actual projection residual, membership of the two old packets suffices. -/
theorem projection_cellSource_compatible (P : Submodule ℝ ThresholdHilbert)
    [P.HasOrthogonalProjection] (k : ℕ) (hk : 0 < k)
    (h2 : packet 2 k (by omega) hk ∈ P)
    (h3 : packet 3 k (by omega) hk ∈ P) :
    Compatible (cellSource (hilbertOne-P.starProjection hilbertOne) k hk) :=
  cellSource_compatible _ k hk
    (Submodule.starProjection_inner_eq_zero _ _ h2)
    (Submodule.starProjection_inner_eq_zero _ _ h3)

/-- The common sum of the five correlations is a composite-seed correlation. -/
theorem cellSource_six_charge (r : ThresholdHilbert) (k : ℕ) (hk : 0 < k)
    (h2 : inner ℝ r (packet 2 k (by omega) hk) = 0) :
    ternarySum (cellSource r k hk) = inner ℝ r (packet 6 k (by omega) hk) := by
  rw [six_packet_decomposition, inner_add_right, inner_add_right, h2, zero_add]
  rfl

/-- An exact specialization of the finite dual bound to the actual packet source. -/
theorem cellSource_energy_bound (r : ThresholdHilbert) (k : ℕ) (hk : 0 < k)
    (h2 : inner ℝ r (packet 2 k (by omega) hk) = 0)
    (h3 : inner ℝ r (packet 3 k (by omega) hk) = 0) :
    (3:ℝ)/7 * sizeSq (cellSource r k hk) ≤ sourceEnergy (cellSource r k hk) :=
  sourceEnergy_ge _ (cellSource_compatible r k hk h2 h3)

end
end RiemannResearch.RH.Pareto.AdjacentPacket
