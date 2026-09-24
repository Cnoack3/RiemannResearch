/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.RH.CenteredResiduePrefixes
import RiemannResearch.RH.NaturalMobiusVariation
import RiemannResearch.Analysis.BoundedPrimitiveAbel

/-!
# Exact raw Mobius energy from its centered primitive

Source: direct discrete product rule and finite Abel summation developed for
the user's directed RH attempt, September 24, 2026. The arithmetic inputs
are the existing centered residue primitive and exact raw Mobius jump.
The weighted interval equality retains both endpoints, the mean term,
the weight-difference term, and the complete signed jump correlation.
Only the diagonal of the primitive-times-divisor-jump product vanishes.
The separate reciprocal-mean term is retained and can contain diagonal
contributions. No upper bound for the growing energy or RH is assumed.
-/
noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.Pareto
open ArithmeticCumulative

def rawMobiusCenteredPrimitive (N k : ℕ) : ℝ :=
  ∑ d ∈ Finset.Icc 1 N, (ArithmeticFunction.moebius d : ℝ) * centeredResiduePrimitive d k

def rawMobiusPeriodMean (N : ℕ) : ℝ :=
  1 + ∑ d ∈ Finset.Icc 1 N, (ArithmeticFunction.moebius d : ℝ) *
    (((d : ℝ)-1)/(2*(d : ℝ)))

def rawMobiusPrimitiveJumpCross (N k : ℕ) : ℝ :=
  ∑ d ∈ Finset.Icc 1 N, ∑ e ∈ (Finset.Icc 1 N).erase d,
    (ArithmeticFunction.moebius d : ℝ) * (ArithmeticFunction.moebius e : ℝ) *
      centeredResiduePrimitive d k * divisorIndicator e k

theorem rawMobiusCenteredPrimitive_step (N k : ℕ) (hk : 0 < k) :
    rawMobiusCenteredPrimitive N (k+1) - rawMobiusCenteredPrimitive N k =
      hilbertSequence (hilbertOne-rawMobiusHilbert N) k - rawMobiusPeriodMean N := by
  rw [rawMobiusResidual_sequence N k hk]
  unfold rawMobiusCenteredPrimitive rawMobiusPeriodMean
  calc
    _ = ∑ d ∈ Finset.Icc 1 N, (ArithmeticFunction.moebius d : ℝ) *
        (centeredResiduePrimitive d (k+1)-centeredResiduePrimitive d k) := by
      simp only [mul_sub, Finset.sum_sub_distrib]
    _ = ∑ d ∈ Finset.Icc 1 N,
        ((ArithmeticFunction.moebius d : ℝ)*residueFraction d k -
          (ArithmeticFunction.moebius d : ℝ)*(((d : ℝ)-1)/(2*(d : ℝ)))) := by
      apply Finset.sum_congr rfl
      intro d hd
      rw [centeredResiduePrimitive_step d k (Finset.mem_Icc.mp hd).1]
      unfold residueFraction residue
      ring
    _ = _ := by rw [Finset.sum_sub_distrib]; ring

theorem centeredResiduePrimitive_mul_divisorIndicator (d k : ℕ) :
    centeredResiduePrimitive d k * divisorIndicator d k = 0 := by
  by_cases hd : d ∣ k
  · simp [centeredResiduePrimitive, residue, divisorIndicator,
      Nat.mod_eq_zero_of_dvd hd, hd]
  · simp [divisorIndicator, hd]

theorem rawMobiusPrimitiveJumpCross_eq_product (N k : ℕ) :
    rawMobiusPrimitiveJumpCross N k =
      rawMobiusCenteredPrimitive N k *
        (∑ e ∈ Finset.Icc 1 N, (ArithmeticFunction.moebius e : ℝ) * divisorIndicator e k) := by
  classical
  unfold rawMobiusPrimitiveJumpCross rawMobiusCenteredPrimitive
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro d hd
  rw [Finset.mul_sum]
  have hz : (ArithmeticFunction.moebius d : ℝ)*(ArithmeticFunction.moebius d : ℝ)*
      centeredResiduePrimitive d k*divisorIndicator d k = 0 := by
    calc
      _ = (ArithmeticFunction.moebius d : ℝ)^2 *
        (centeredResiduePrimitive d k*divisorIndicator d k) := by ring
      _ = 0 := by rw [centeredResiduePrimitive_mul_divisorIndicator]; ring
  have hs := Finset.sum_erase_add (Finset.Icc 1 N)
    (fun e => (ArithmeticFunction.moebius d : ℝ)*(ArithmeticFunction.moebius e : ℝ)*
      centeredResiduePrimitive d k*divisorIndicator e k) hd
  rw [hz, add_zero] at hs
  rw [hs]
  apply Finset.sum_congr rfl
  intro e he
  ring

theorem rawMobius_energy_primitive_point (N k : ℕ) (hk : 0 < k) :
    (hilbertSequence (hilbertOne-rawMobiusHilbert N) k)^2 =
      rawMobiusPeriodMean N * hilbertSequence (hilbertOne-rawMobiusHilbert N) k +
      (rawMobiusCenteredPrimitive N (k+1)*hilbertSequence (hilbertOne-rawMobiusHilbert N) (k+1) -
        rawMobiusCenteredPrimitive N k*hilbertSequence (hilbertOne-rawMobiusHilbert N) k) -
      mobiusReciprocalSum N*rawMobiusCenteredPrimitive N (k+1) +
      rawMobiusPrimitiveJumpCross N (k+1) := by
  have hp := congrArg (fun x : ℝ => x*hilbertSequence (hilbertOne-rawMobiusHilbert N) k)
    (rawMobiusCenteredPrimitive_step N k hk)
  have hj := congrArg (fun x : ℝ => rawMobiusCenteredPrimitive N (k+1)*x)
    (rawMobiusResidual_jump N k hk)
  rw [rawMobiusPrimitiveJumpCross_eq_product]
  nlinarith only [hp, hj]

theorem rawMobius_energy_primitive_interval (N K L : ℕ) (hK : 0 < K)
    (w : ℕ → ℝ) :
    (∑ i ∈ Finset.range L, w (K+i) *
      (hilbertSequence (hilbertOne-rawMobiusHilbert N) (K+i))^2) =
      rawMobiusPeriodMean N * (∑ i ∈ Finset.range L,
        w (K+i)*hilbertSequence (hilbertOne-rawMobiusHilbert N) (K+i)) +
      (w (K+L)*rawMobiusCenteredPrimitive N (K+L)*
        hilbertSequence (hilbertOne-rawMobiusHilbert N) (K+L) -
       w K*rawMobiusCenteredPrimitive N K*hilbertSequence (hilbertOne-rawMobiusHilbert N) K) +
      (∑ i ∈ Finset.range L, (w (K+i)-w (K+i+1))*
        rawMobiusCenteredPrimitive N (K+i+1)*
        hilbertSequence (hilbertOne-rawMobiusHilbert N) (K+i+1)) -
      mobiusReciprocalSum N * (∑ i ∈ Finset.range L, w (K+i)*rawMobiusCenteredPrimitive N (K+i+1)) +
      (∑ i ∈ Finset.range L, w (K+i)*rawMobiusPrimitiveJumpCross N (K+i+1)) := by
  let U : ℕ → ℝ := fun k => hilbertSequence (hilbertOne-rawMobiusHilbert N) k
  let P := rawMobiusCenteredPrimitive N
  have hab := RiemannResearch.Analysis.boundedPrimitive_abel_identity
    (fun i => P (K+i)*U (K+i)) (fun i => w (K+i)) L
  simp only [Nat.add_zero, ← Nat.add_assoc] at hab
  have he :
      (∑ i ∈ Finset.range L, w (K+i)*(U (K+i))^2) =
        rawMobiusPeriodMean N*(∑ i ∈ Finset.range L, w (K+i)*U (K+i)) +
        (∑ i ∈ Finset.range L, (P (K+i+1)*U (K+i+1)-P (K+i)*U (K+i))*w (K+i)) -
        mobiusReciprocalSum N*(∑ i ∈ Finset.range L, w (K+i)*P (K+i+1)) +
        (∑ i ∈ Finset.range L, w (K+i)*rawMobiusPrimitiveJumpCross N (K+i+1)) := by
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    have hp := rawMobius_energy_primitive_point N (K+i) (by omega)
    change (U (K+i))^2 = _ at hp
    rw [hp]
    dsimp [P, U]
    ring
  rw [hab] at he
  have hc :
      (∑ i ∈ Finset.range L, P (K+i+1)*U (K+i+1)*(w (K+i)-w (K+i+1))) =
      ∑ i ∈ Finset.range L, (w (K+i)-w (K+i+1))*P (K+i+1)*U (K+i+1) := by
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [hc] at he
  dsimp only [P, U] at he
  nlinarith only [he]

end RiemannResearch.RH.Pareto
