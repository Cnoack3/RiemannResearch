import RiemannResearch.RH.ParetoCovariance
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# General Pareto residue and packet means

Source: user-provided argument in
`RH_Candid_Assessment_Pareto_Green_CRT_2026-09-07.md`.
The proof evaluates the complete Pareto mean through an exact finite harmonic
identity. No truncated distribution replaces the original probability law.
-/

open scoped BigOperators Topology
open Filter
namespace RiemannResearch.RH.Pareto
noncomputable section

private theorem weighted_nat_partial_sum_succ (N : ℕ) :
    (∑ k ∈ Finset.range (N+1), positiveWeight k * (k : ℝ)) =
      (harmonic (N+1) : ℝ) - 1 := by
  induction N with
  | zero => norm_num [positiveWeight, harmonic]
  | succ N ih =>
    rw [Finset.sum_range_succ, ih, harmonic_succ (N+1)]
    push_cast
    unfold positiveWeight
    push_cast
    have h1 : (N : ℝ)+1 ≠ 0 := by positivity
    have h2 : (N : ℝ)+1+1 ≠ 0 := by positivity
    field_simp
    ring

private theorem weighted_nat_partial_sum (N : ℕ) (hN : 0 < N) :
    (∑ k ∈ Finset.range N, positiveWeight k * (k : ℝ)) =
      (harmonic N : ℝ) - 1 := by
  obtain ⟨M, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (ne_of_gt hN)
  exact weighted_nat_partial_sum_succ M

/-- An exact finite identity at a complete residue period, including both boundaries. -/
theorem residue_partial_sum_harmonic (n N : ℕ) (hn : 0 < n) (hN : 0 < N) :
    (∑ k ∈ Finset.range (n*N), positiveWeight k * residue n k) =
      (harmonic (n*N) : ℝ) - (harmonic N : ℝ) := by
  have hr (k : ℕ) : residue n k = (k : ℝ) - dilation n (fun j => (j : ℝ)) k := by
    have hk := Nat.mod_add_div k n
    have hk' : ((k % n : ℕ) : ℝ) + (n : ℝ) * ((k/n : ℕ) : ℝ) = k := by
      exact_mod_cast hk
    unfold residue dilation
    linarith
  simp_rw [hr, mul_sub]
  rw [Finset.sum_sub_distrib,
    dilation_partial_sum n N hn (fun j => (j : ℝ)) (by simp),
    weighted_nat_partial_sum (n*N) (Nat.mul_pos hn hN),
    weighted_nat_partial_sum N hN]
  ring

/-- Every positive conductor has exact complete Pareto residue mean `log n`. -/
theorem paretoMean_residue (n : ℕ) (hn : 0 < n) :
    paretoMean (residue n) = Real.log n := by
  have hn0 : (n : ℝ) ≠ 0 := by positivity
  have hmul : Tendsto (fun N : ℕ => n*N) atTop atTop :=
    tendsto_atTop_mono (fun N => Nat.le_mul_of_pos_left N hn) tendsto_id
  have hs := weighted_summable_of_bounded (fun k => residue_abs_le n k hn)
  have hp := hs.hasSum.tendsto_sum_nat.comp hmul
  have hlim := (Real.tendsto_harmonic_sub_log.comp hmul).sub
    Real.tendsto_harmonic_sub_log
  have hshift := hlim.add_const (Real.log (n : ℝ))
  have heq : (fun N : ℕ =>
      ((harmonic (n*N) : ℝ) - Real.log (n*N : ℕ)) -
        ((harmonic N : ℝ) - Real.log (N : ℝ)) + Real.log (n : ℝ)) =ᶠ[atTop]
      (fun N : ℕ => ∑ k ∈ Finset.range (n*N), positiveWeight k * residue n k) := by
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with N hN
    rw [residue_partial_sum_harmonic n N hn hN, Nat.cast_mul,
      Real.log_mul hn0 (by positivity : (N : ℝ) ≠ 0)]
    ring
  have htarget : Tendsto
      (fun N : ℕ => ∑ k ∈ Finset.range (n*N), positiveWeight k * residue n k)
      atTop (𝓝 (Real.log (n : ℝ))) := by
    simpa using hshift.congr' heq
  exact tendsto_nhds_unique hp htarget

/-- Every genuine arithmetic packet has exact complete Pareto mean `Λ(q)`.
All prime powers, including squares and higher powers, are retained. -/
theorem paretoMean_ramanujanPacket (q : ℕ) :
    paretoMean (ramanujanPacket q) = ArithmeticFunction.vonMangoldt q := by
  by_cases hq : q = 0
  · subst q
    simp [paretoMean, ramanujanPacket]
  have hs : ∀ d ∈ q.divisors, Summable (fun k =>
      positiveWeight k * ((ArithmeticFunction.moebius (q/d) : ℝ) * residue d k)) := by
    intro d hd
    apply weighted_summable_of_bounded
    exact bounded_const_mul (fun k => residue_abs_le d k (Nat.pos_of_mem_divisors hd)) _
  have he (d : ℕ) (hd : d ∈ q.divisors) :
      (∑' k, positiveWeight k *
        ((ArithmeticFunction.moebius (q/d) : ℝ) * residue d k)) =
      (ArithmeticFunction.moebius (q/d) : ℝ) * Real.log (d : ℝ) := by
    calc
      _ = (ArithmeticFunction.moebius (q/d) : ℝ) * paretoMean (residue d) := by
        unfold paretoMean
        simp_rw [mul_left_comm (positiveWeight _) (ArithmeticFunction.moebius (q/d) : ℝ)]
        exact tsum_mul_left
      _ = _ := by rw [paretoMean_residue d (Nat.pos_of_mem_divisors hd)]
  unfold paretoMean ramanujanPacket
  simp_rw [Finset.mul_sum]
  rw [Summable.tsum_finsetSum hs]
  rw [Finset.sum_congr rfl he]
  exact (mobius_inversion (fun d => ArithmeticFunction.vonMangoldt d)
    (fun d => Real.log (d : ℝ))).mp
      (by intro n hn; exact ArithmeticFunction.vonMangoldt_sum) q (Nat.pos_of_ne_zero hq)

/-- Conductors that are not prime powers carry zero signal under the actual Pareto law. -/
theorem paretoMean_ramanujanPacket_of_not_isPrimePow (q : ℕ) (hq : ¬ IsPrimePow q) :
    paretoMean (ramanujanPacket q) = 0 := by
  rw [paretoMean_ramanujanPacket, ArithmeticFunction.vonMangoldt_apply, if_neg hq]

/-- The signal of a prime-power conductor is the logarithm of its base prime. -/
theorem paretoMean_ramanujanPacket_of_isPrimePow (q : ℕ) (hq : IsPrimePow q) :
    paretoMean (ramanujanPacket q) = Real.log (q.minFac : ℝ) := by
  rw [paretoMean_ramanujanPacket, ArithmeticFunction.vonMangoldt_apply, if_pos hq]

end
end RiemannResearch.RH.Pareto
