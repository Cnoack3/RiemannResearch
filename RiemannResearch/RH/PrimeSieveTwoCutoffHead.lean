import RiemannResearch.RH.PrimeSievePrimitiveEscape
import RiemannResearch.RH.ExactHeadMeanGap
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Actual two-cutoff interpolation by finite prime sieves

Source: user-directed continuation of
`Independent_Primes_Squarefree_Approximation_2026-10-07.md`, equations
(5.5)--(5.7), supporting the exact signed interpolation statements.

These statements specialize the finite interpolation identities to the actual
factorial-divisor sieve already defined in the repository. No Mertens product
asymptotic, RH assumption, or limiting norm approximation is used here.

-/

noncomputable section
open Filter
open scoped Topology

namespace RiemannResearch.RH.Pareto
open ArithmeticCumulative

/-- The signed two-cutoff combination of the actual finite residue sieves. -/
def twoCutoffSievePrimitive (Y W k : ℕ) : ℝ :=
  (sieveReciprocal Y.factorial * derivativeSievePrimitive W k -
    sieveReciprocal W.factorial * derivativeSievePrimitive Y k) /
      (sieveReciprocal Y.factorial - sieveReciprocal W.factorial)

@[simp] theorem twoCutoffSievePrimitive_zero (Y W : ℕ) :
    twoCutoffSievePrimitive Y W 0 = 0 := by
  simp [twoCutoffSievePrimitive]

/-- The actual sieve primitive equals its exact rough count minus its drift. -/
theorem derivativeSievePrimitive_rough_exact (Y k : ℕ) :
    derivativeSievePrimitive Y k =
      sieveRoughCount Y.factorial k - sieveReciprocal Y.factorial * (k : ℝ) := by
  rw [derivativeSievePrimitive,
    sieveResidue_exact _ _ _ (Nat.factorial_pos Y) (by decide)]
  simp only [Nat.cast_one, Nat.div_one, div_one]
  ring

/-- Both linear drifts cancel identically at every integer, including zero. -/
theorem twoCutoffSievePrimitive_rough_exact (Y W k : ℕ) :
    twoCutoffSievePrimitive Y W k =
      (sieveReciprocal Y.factorial * sieveRoughCount W.factorial k -
        sieveReciprocal W.factorial * sieveRoughCount Y.factorial k) /
          (sieveReciprocal Y.factorial - sieveReciprocal W.factorial) := by
  unfold twoCutoffSievePrimitive
  rw [derivativeSievePrimitive_rough_exact, derivativeSievePrimitive_rough_exact]
  congr 1
  ring

/-- Actual finite residue legality is preserved under the signed interpolation. -/
theorem twoCutoffSievePrimitive_mem_legal (Y W : ℕ) :
    twoCutoffSievePrimitive Y W ∈ legalSeedSpan allPositiveSeeds := by
  have he : twoCutoffSievePrimitive Y W =
      (sieveReciprocal Y.factorial /
        (sieveReciprocal Y.factorial - sieveReciprocal W.factorial)) •
          derivativeSievePrimitive W -
      (sieveReciprocal W.factorial /
        (sieveReciprocal Y.factorial - sieveReciprocal W.factorial)) •
          derivativeSievePrimitive Y := by
    funext k
    simp only [twoCutoffSievePrimitive, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [he]
  exact (legalSeedSpan allPositiveSeeds).sub_mem
    ((legalSeedSpan allPositiveSeeds).smul_mem _ (derivativeSievePrimitive_mem_legal W))
    ((legalSeedSpan allPositiveSeeds).smul_mem _ (derivativeSievePrimitive_mem_legal Y))

/-- Every positive coordinate in the smaller head is interpolated exactly. -/
theorem twoCutoffSievePrimitive_head (Y W k : ℕ)
    (hYW : Y ≤ W) (hk : 0 < k) (hkY : k ≤ Y)
    (hneq : sieveReciprocal Y.factorial ≠ sieveReciprocal W.factorial) :
    twoCutoffSievePrimitive Y W k = 1 := by
  rw [twoCutoffSievePrimitive_rough_exact,
    sieveRoughCount_factorial_head W k hk (hkY.trans hYW),
    sieveRoughCount_factorial_head Y k hk hkY]
  simp only [mul_one]
  exact div_self (sub_ne_zero.mpr hneq)

/-- Exact residual up to the larger cutoff. Its complete rough-count term is retained. -/
theorem twoCutoffSievePrimitive_intermediate_residual (Y W k : ℕ)
    (hk : 0 < k) (hkW : k ≤ W)
    (hneq : sieveReciprocal Y.factorial ≠ sieveReciprocal W.factorial) :
    1 - twoCutoffSievePrimitive Y W k =
      sieveReciprocal W.factorial * (sieveRoughCount Y.factorial k - 1) /
        (sieveReciprocal Y.factorial - sieveReciprocal W.factorial) := by
  rw [twoCutoffSievePrimitive_rough_exact,
    sieveRoughCount_factorial_head W k hk hkW]
  field_simp [sub_ne_zero.mpr hneq]; ring

/-- Pointwise head interpolation holds eventually for every admissible cutoff schedule. -/
theorem twoCutoffSievePrimitive_eventually_eq_one (W : ℕ → ℕ)
    (hW : ∀ Y, Y ≤ W Y)
    (hneq : ∀ Y, sieveReciprocal Y.factorial ≠ sieveReciprocal (W Y).factorial)
    (k : ℕ) (hk : 0 < k) :
    ∀ᶠ Y in atTop, twoCutoffSievePrimitive Y (W Y) k = 1 := by
  filter_upwards [eventually_ge_atTop k] with Y hkY
  exact twoCutoffSievePrimitive_head Y (W Y) k (hW Y) hk hkY (hneq Y)

/-- The same construction in the existing actual Pareto Hilbert space. -/
def twoCutoffSieveHilbert (Y W : ℕ) : ThresholdHilbert :=
  (sieveReciprocal Y.factorial /
    (sieveReciprocal Y.factorial - sieveReciprocal W.factorial)) •
      derivativeSieveHilbert W -
  (sieveReciprocal W.factorial /
    (sieveReciprocal Y.factorial - sieveReciprocal W.factorial)) •
      derivativeSieveHilbert Y

theorem twoCutoffSieveHilbert_sequence (Y W : ℕ) :
    hilbertSequence (twoCutoffSieveHilbert Y W) = twoCutoffSievePrimitive Y W := by
  rw [twoCutoffSieveHilbert, hilbertSequence_sub,
    hilbertSequence_smul, hilbertSequence_smul,
    derivativeSieveHilbert_sequence, derivativeSieveHilbert_sequence]
  funext k
  simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, twoCutoffSievePrimitive]
  ring

theorem twoCutoffSieveHilbert_head (Y W k : ℕ)
    (hYW : Y ≤ W) (hk : 0 < k) (hkY : k ≤ Y)
    (hneq : sieveReciprocal Y.factorial ≠ sieveReciprocal W.factorial) :
    hilbertSequence (twoCutoffSieveHilbert Y W) k = 1 := by
  rw [twoCutoffSieveHilbert_sequence]
  exact twoCutoffSievePrimitive_head Y W k hYW hk hkY hneq

/-- The complete inverse-square error of the actual two-cutoff sieve is
bounded below by its mean gap times the physical head length. -/
theorem twoCutoffSieveHilbert_normalized_error_lower
    (Z : ℝ) (hZ : 0 < Z) (Y W : ℕ) (hYW : Y ≤ W)
    (hneq : sieveReciprocal Y.factorial ≠ sieveReciprocal W.factorial) :
    (((Y : ℝ) + 1) / Z) * (1 - paretoMean (twoCutoffSievePrimitive Y W)) ^ 2 ≤
      ComparableWeights.weightedEnergy
        (ExactHeadMeanGap.normalizedInverseSquareWeight Z)
        (hilbertOne - twoCutoffSieveHilbert Y W) := by
  have h := ExactHeadMeanGap.normalizedError_ge_mean_gap Z hZ Y
    (twoCutoffSieveHilbert Y W)
    (fun k hk hkY => twoCutoffSieveHilbert_head Y W k hYW hk hkY hneq)
  rw [twoCutoffSieveHilbert_sequence] at h
  exact h

end RiemannResearch.RH.Pareto
