import RiemannResearch.RH.CanonicalMobiusPNT

/-!
Reciprocal-coordinate weighted endpoint for the
actual boundary-corrected finite Möbius approximants. This is a weaker norm
than the RH-critical Pareto norm, so it is not an unconditional RH proof.

Source: research continuation of the user's manuscript-backed exact-head family.
The endpoint strategy has antecedents in Gallardo-Gutiérrez and Seco,
`https://arxiv.org/abs/2206.02654`, Section 2.1. The proof here combines the
project's exact-head identities and formal PNT provider; it does not formalize
the Hardy-space Mellin identification. See `HardyEndpointCompactness20260924.md`.
-/

noncomputable section
open Filter
open scoped BigOperators Topology
namespace RiemannResearch.RH.Pareto

/-- The full Pareto energy with one additional inverse physical coordinate. -/
def inverseCoordinateEnergy (x : ThresholdHilbert) : ℝ :=
  ∑' n : ℕ, positiveWeight n * hilbertSequence x n ^ 2 / (n : ℝ)

theorem inverseCoordinateEnergy_nonneg (x : ThresholdHilbert) :
    0 ≤ inverseCoordinateEnergy x := by
  exact tsum_nonneg (fun n => div_nonneg
    (mul_nonneg (positiveWeight_nonneg n) (sq_nonneg _)) (Nat.cast_nonneg n))

/-- An exact-head condition buys one inverse power of its length. -/
theorem inverseCoordinateEnergy_le_of_zero_head
    (x : ThresholdHilbert) (N : ℕ) (hN : 0 < N)
    (hhead : ∀ n, n < N → hilbertSequence x n = 0) :
    inverseCoordinateEnergy x ≤ ‖x‖ ^ 2 / (N : ℝ) := by
  let e : ℕ → ℝ := fun n => positiveWeight n * hilbertSequence x n ^ 2
  have he : Summable e := hilbertSequence_square_summable x
  have he0 (n : ℕ) : 0 ≤ e n :=
    mul_nonneg (positiveWeight_nonneg n) (sq_nonneg _)
  have hNreal : (0 : ℝ) < N := by exact_mod_cast hN
  have hb : Summable (fun n => e n / (N : ℝ)) := he.div_const _
  have hle (n : ℕ) : e n / (n : ℝ) ≤ e n / (N : ℝ) := by
    by_cases hn : n < N
    · simp [e, hhead n hn]
    · apply div_le_div_of_nonneg_left (he0 n) hNreal
      exact_mod_cast (Nat.le_of_not_gt hn)
  have hs : Summable (fun n => e n / (n : ℝ)) :=
    Summable.of_nonneg_of_le
      (fun n => div_nonneg (he0 n) (Nat.cast_nonneg n)) hle hb
  calc
    inverseCoordinateEnergy x ≤ ∑' n, e n / (N : ℝ) :=
      hs.tsum_le_tsum hle hb
    _ = ‖x‖ ^ 2 / (N : ℝ) := by
      rw [tsum_div_const]
      rw [hilbert_norm_weighted_sq]

/-- The actual corrected Möbius residual still has sublinear Pareto energy. -/
theorem canonicalMobiusResidual_sublinear :
    Tendsto (fun N => ‖hilbertOne - canonicalMobiusHilbert N‖ ^ 2 / (N : ℝ))
      atTop (𝓝 0) := by
  have hb (N : ℕ) :
      ‖hilbertOne - canonicalMobiusHilbert N‖ ^ 2 ≤
        2 * ‖canonicalMobiusHilbert N‖ ^ 2 + 2 := by
    have ht := norm_sub_le hilbertOne (canonicalMobiusHilbert N)
    have hsq := mul_self_le_mul_self
      (norm_nonneg (hilbertOne - canonicalMobiusHilbert N)) ht
    nlinarith [sq_nonneg (‖hilbertOne‖ - ‖canonicalMobiusHilbert N‖),
      hilbertOne_norm_sq]
  have hup : Tendsto
      (fun N : ℕ => (2 * ‖canonicalMobiusHilbert N‖ ^ 2 + 2) / (N : ℝ))
      atTop (𝓝 0) := by
    have hh := (canonicalMobiusHilbert_sublinear.const_mul 2).add
      (tendsto_inv_atTop_nhds_zero_nat.const_mul (2 : ℝ))
    simpa only [add_div, mul_div_assoc, div_eq_mul_inv, add_mul, mul_assoc, mul_zero, zero_add] using hh
  exact squeeze_zero
    (fun N => div_nonneg (sq_nonneg _) (Nat.cast_nonneg N))
    (fun N => div_le_div_of_nonneg_right (hb N) (Nat.cast_nonneg N)) hup

/-- Unconditional convergence in the weaker, inverse-coordinate weighted norm.
The missing RH assertion is the corresponding limit without division by n. -/
theorem canonicalMobiusResidual_inverseCoordinateEnergy_tendsto_zero :
    Tendsto
      (fun N => inverseCoordinateEnergy (hilbertOne - canonicalMobiusHilbert N))
      atTop (𝓝 0) := by
  apply squeeze_zero'
    (Eventually.of_forall (fun N => inverseCoordinateEnergy_nonneg _))
    _ canonicalMobiusResidual_sublinear
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with N hN
  apply inverseCoordinateEnergy_le_of_zero_head _ N (by omega)
  intro n hn
  change hilbertSequenceLinear (hilbertOne - canonicalMobiusHilbert N) n = 0
  rw [map_sub]
  change hilbertSequence hilbertOne n -
    hilbertSequence (canonicalMobiusHilbert N) n = 0
  by_cases hn0 : n = 0
  · subst n
    simp [hilbertSequence]
  · rw [canonicalMobiusHilbert_exact N n (by omega) (by omega),
      hilbertOne_sequence]
    simp [zeroAnchor, hn0]

end RiemannResearch.RH.Pareto
