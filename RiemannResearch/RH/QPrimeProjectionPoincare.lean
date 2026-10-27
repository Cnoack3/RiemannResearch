/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.Analysis.CountableProjectionPoincare
import RiemannResearch.RH.QPrimeInvariantIntersection
import RiemannResearch.RH.QPrimeResamplingCommutation

/-!
# Actual countable prime-projection Poincare inequality

The arithmetic averaging projections commute and their full common fixed
space is exactly the constants. Consequently their complete defect energy
dominates variance with constant one. No probability or arithmetic provider
is a hypothesis of the resulting actual-Q theorem.
Source: the user's countable prime-resampling agenda.
-/

noncomputable section
open scoped BigOperators ENNReal
namespace RiemannResearch.RH.QPrimeResampling
open ZetaTwoHilbert
open RiemannResearch.Analysis.CountableProjectionPoincare

/-- Nonprime indices are identity coordinates, allowing an ordinary natural
number enumeration without selecting an ordering of the primes. -/
def coordinateSpace (p : ℕ) : Submodule ℝ QHilbert :=
  if p.Prime then primeInvariant p else ⊤

instance coordinateSpace_hasOrthogonalProjection (p : ℕ) :
    (coordinateSpace p).HasOrthogonalProjection := by
  unfold coordinateSpace
  split_ifs <;> infer_instance

theorem coordinateSpace_projection (p : ℕ) (f : QHilbert) :
    (coordinateSpace p).starProjection f = if p.Prime then C p f else f := by
  by_cases hp : p.Prime
  · simp only [coordinateSpace, if_pos hp, C]
  · rw [if_neg hp]
    apply Submodule.starProjection_eq_self_iff.mpr
    simp [coordinateSpace, hp]

theorem coordinateSpace_commute (p q : ℕ) (f : QHilbert) :
    (coordinateSpace p).starProjection ((coordinateSpace q).starProjection f) =
      (coordinateSpace q).starProjection ((coordinateSpace p).starProjection f) := by
  by_cases hp : p.Prime <;> by_cases hq : q.Prime
  · simp only [coordinateSpace_projection, if_pos hp, if_pos hq]
    exact C_commute p q hp hq f
  · simp only [coordinateSpace_projection, if_pos hp, if_neg hq]
  · simp only [coordinateSpace_projection, if_neg hp, if_pos hq]
  · simp only [coordinateSpace_projection, if_neg hp, if_neg hq]

theorem iInf_coordinateSpace_eq_constantSpace :
    (⨅ p : ℕ, coordinateSpace p) = constantSpace := by
  ext f
  simp only [Submodule.mem_iInf]
  rw [← invariant_under_primes_iff_constant]
  constructor
  · intro hf p hp
    simpa only [coordinateSpace, if_pos hp] using hf p
  · intro hf p
    by_cases hp : p.Prime
    · simpa only [coordinateSpace, if_pos hp] using hf p hp
    · simp [coordinateSpace, hp]

instance coordinateSpace_iInf_hasOrthogonalProjection :
    (⨅ p : ℕ, coordinateSpace p).HasOrthogonalProjection := by
  rw [iInf_coordinateSpace_eq_constantSpace]
  infer_instance

def primeProjectionEnergy (f : QHilbert) : ℝ≥0∞ :=
  ∑' p : ℕ, if p.Prime then ENNReal.ofReal (‖f - C p f‖ ^ 2) else 0

/-- Gap one for the actual countable prime-resampling projections. The energy
may be infinite; no summability assumption or unproved estimate occurs. -/
theorem prime_projection_poincare (f : QHilbert) :
    ENNReal.ofReal (‖f‖ ^ 2 - (inner ℝ qOne f) ^ 2) ≤ primeProjectionEnergy f := by
  have h := projection_poincare coordinateSpace coordinateSpace_commute f
  have heproj : (⨅ p : ℕ, coordinateSpace p).starProjection =
      constantSpace.starProjection := by
    congr 1
    exact iInf_coordinateSpace_eq_constantSpace
  rw [heproj, constantSpace_projection,
    norm_smul, qOne_norm, mul_one, Real.norm_eq_abs, sq_abs] at h
  have he : (∑' p : ℕ, ENNReal.ofReal (‖f - (coordinateSpace p).starProjection f‖ ^ 2)) =
      primeProjectionEnergy f := by
    unfold primeProjectionEnergy
    apply tsum_congr
    intro p
    by_cases hp : p.Prime <;> simp [coordinateSpace_projection, hp]
  rwa [he] at h

end RiemannResearch.RH.QPrimeResampling
