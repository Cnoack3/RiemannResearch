/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.CotangentBridge
import RiemannResearch.RH.PhysicalPacketCore

/-!
# Arithmetic cotangent-difference realization of the actual packet core

The finite cotangent-difference matrix is defined without referring to the
Pareto Gram. Complete divisor expansions and Möbius inversion then prove its
rank-two Gram identity and equality with `PhysicalPacketCore.derivedCore`.
Contraction to the existing double-`cotangentV` formula is a separate step.
-/

noncomputable section
open Matrix
open scoped BigOperators
namespace RiemannResearch.RH.Pareto

private def divisorResidue (d : ℕ) (a : d.divisors) : ℕ → ℝ := residue a.val

private def divisorMoebius (d : ℕ) (a : d.divisors) : ℝ :=
  (ArithmeticFunction.moebius (d/a.val) : ℝ)

private theorem divisorResidue_bound (d : ℕ) (a : d.divisors) (k : ℕ) :
    |divisorResidue d a k| ≤ (a.val : ℝ) :=
  residue_abs_le a.val k (Nat.pos_of_mem_divisors a.property)

private theorem packet_eq_divisor_combination (d : ℕ) :
    ramanujanPacket d = FiniteSchur.combination (divisorResidue d) (divisorMoebius d) := by
  funext k
  unfold ramanujanPacket FiniteSchur.combination divisorResidue divisorMoebius
  exact (Finset.sum_coe_sort d.divisors (fun a : ℕ =>
    (ArithmeticFunction.moebius (d/a) : ℝ) * residue a k)).symm

theorem packet_inner_divisor_expansion (d e : ℕ) :
    paretoInner (ramanujanPacket d) (ramanujanPacket e) =
      ∑ a : d.divisors, ∑ b : e.divisors,
        (ArithmeticFunction.moebius (d/a.val) : ℝ) *
          (ArithmeticFunction.moebius (e/b.val) : ℝ) *
            paretoInner (residue a.val) (residue b.val) := by
  rw [packet_eq_divisor_combination d, packet_eq_divisor_combination e,
    FiniteSchur.inner_combination_left (divisorResidue_bound d)
      (FiniteSchur.combination_bounded (divisorResidue_bound e) (divisorMoebius e))]
  apply Finset.sum_congr rfl
  intro a _
  rw [FiniteSchur.inner_combination_right (divisorResidue_bound e)
    (divisorResidue_bound d a), Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  simp only [divisorResidue, divisorMoebius]
  ring

theorem packet_moebius_totient_source (d : ℕ) (hd : 1 < d) :
    (∑ a : d.divisors, (ArithmeticFunction.moebius (d/a.val) : ℝ) *
      ((a.val : ℝ)-1)) = (Nat.totient d : ℝ) := by
  rw [Finset.sum_coe_sort d.divisors (fun a : ℕ =>
    (ArithmeticFunction.moebius (d/a) : ℝ) * ((a : ℝ)-1))]
  have hconv := (mobius_inversion (fun n => (Nat.totient n : ℝ))
    (fun n => (n : ℝ))).mp
    (by intro n hn; exact_mod_cast Nat.sum_totient n) d (by omega)
  simp_rw [mul_sub, mul_one]
  rw [Finset.sum_sub_distrib, hconv, sum_moebius_div d hd]
  ring

theorem packet_moebius_log_source (d : ℕ) (hd : 0 < d) :
    (∑ a : d.divisors, (ArithmeticFunction.moebius (d/a.val) : ℝ) *
      Real.log (a.val : ℝ)) = ArithmeticFunction.vonMangoldt d := by
  rw [Finset.sum_coe_sort d.divisors (fun a : ℕ =>
    (ArithmeticFunction.moebius (d/a) : ℝ) * Real.log (a : ℝ))]
  exact (mobius_inversion (fun n => ArithmeticFunction.vonMangoldt n)
    (fun n => Real.log (n : ℝ))).mp
      (by intro n hn; exact ArithmeticFunction.vonMangoldt_sum) d hd

private theorem finite_rank_source_sum {ι κ : Type*} [Fintype ι] [Fintype κ]
    (u x y : ι → ℝ) (v z w : κ → ℝ) :
    (∑ i, ∑ j, u i * v j * (x i * w j + y i * z j) / 2) =
      ((∑ i, u i * x i) * (∑ j, v j * w j) +
        (∑ i, u i * y i) * (∑ j, v j * z j)) / 2 := by
  have hp (i : ι) (j : κ) :
      u i * v j * (x i * w j + y i * z j) / 2 =
        ((u i * x i) * (v j * w j) + (u i * y i) * (v j * z j)) / 2 := by ring
  have hfirst : (∑ i, ∑ j, (u i * x i) * (v j * w j)) =
      (∑ i, u i * x i) * (∑ j, v j * w j) := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    simp only [Finset.mul_sum]
  have hsecond : (∑ i, ∑ j, (u i * y i) * (v j * z j)) =
      (∑ i, u i * y i) * (∑ j, v j * z j) := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    simp only [Finset.mul_sum]
  simp_rw [hp]
  simp_rw [← Finset.sum_div, Finset.sum_add_distrib]
  rw [hfirst, hsecond]

/-- A finite arithmetic core, using common-period cotangent differences.
The complete signed divisor sum is retained. -/
def packetDifferenceCotangentCoreEntry (Q d e : ℕ) : ℝ :=
  ∑ a : d.divisors, ∑ b : e.divisors,
    (ArithmeticFunction.moebius (d/a.val) : ℝ) *
      (ArithmeticFunction.moebius (e/b.val) : ℝ) *
        residueDifferenceCotangentCore Q a.val b.val

/-- The actual full Pareto packet Gram has this explicit arithmetic core. -/
theorem packet_inner_eq_differenceCotangentCore (Q d e : ℕ) (hQ : 0 < Q)
    (hd : 1 < d) (he : 1 < e) (hdQ : d ∣ Q) (heQ : e ∣ Q) :
    paretoInner (ramanujanPacket d) (ramanujanPacket e) =
      Real.pi * packetDifferenceCotangentCoreEntry Q d e +
        (ArithmeticFunction.vonMangoldt d * (Nat.totient e : ℝ) +
          (Nat.totient d : ℝ) * ArithmeticFunction.vonMangoldt e) / 2 := by
  rw [packet_inner_divisor_expansion]
  have hpoint (a : d.divisors) (b : e.divisors) :=
    paretoInner_residue_eq_differenceCotangentCore Q a.val b.val hQ
      (Nat.pos_of_mem_divisors a.property) (Nat.pos_of_mem_divisors b.property)
      (dvd_trans (Nat.dvd_of_mem_divisors a.property) hdQ)
      (dvd_trans (Nat.dvd_of_mem_divisors b.property) heQ)
  simp_rw [hpoint, mul_add, Finset.sum_add_distrib]
  have hcore : (∑ a : d.divisors, ∑ b : e.divisors,
      (ArithmeticFunction.moebius (d/a.val) : ℝ) *
        (ArithmeticFunction.moebius (e/b.val) : ℝ) *
          (Real.pi * residueDifferenceCotangentCore Q a.val b.val)) =
      Real.pi * packetDifferenceCotangentCoreEntry Q d e := by
    unfold packetDifferenceCotangentCoreEntry
    simp_rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    ring
  rw [hcore]
  congr 1
  have hrank := finite_rank_source_sum
    (fun a : d.divisors => (ArithmeticFunction.moebius (d/a.val) : ℝ))
    (fun a => Real.log (a.val : ℝ)) (fun a => (a.val : ℝ)-1)
    (fun b : e.divisors => (ArithmeticFunction.moebius (e/b.val) : ℝ))
    (fun b => Real.log (b.val : ℝ)) (fun b => (b.val : ℝ)-1)
  rw [packet_moebius_log_source d (by omega), packet_moebius_log_source e (by omega),
    packet_moebius_totient_source d hd, packet_moebius_totient_source e he] at hrank
  convert hrank using 1
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring

def arithmeticPacketCore (Q : ℕ) (s : Finset ℕ) : Matrix s s ℝ :=
  fun i j => packetDifferenceCotangentCoreEntry Q i.val j.val

/-- Exact comparison with the independently derived physical core. -/
theorem arithmeticPacketCore_eq_derivedCore (Q : ℕ) (s : Finset ℕ) (hQ : 0 < Q)
    (hs : ∀ q ∈ s, 1 < q) (hsQ : ∀ q ∈ s, q ∣ Q) :
    arithmeticPacketCore Q s = PhysicalPacketCore.derivedCore s := by
  ext i j
  have h := packet_inner_eq_differenceCotangentCore Q i.val j.val hQ
    (hs i.val i.property) (hs j.val j.property)
    (hsQ i.val i.property) (hsQ j.val j.property)
  simp only [arithmeticPacketCore, PhysicalPacketCore.derivedCore,
    ramanujanGramMatrix, ramanujanVonMangoldtVector, ramanujanTotientVector]
  apply (eq_div_iff Real.pi_ne_zero).mpr
  linarith


/-- Ordinary reflection mean of the actual packet, independent of Pareto mean. -/
theorem packet_reflection_totient (Q d k : ℕ) (hd : 1 < d)
    (hdQ : d ∣ Q) (hk : k < Q) :
    ramanujanPacket d k + ramanujanPacket d (Q - 1 - k) = (Nat.totient d : ℝ) := by
  simp only [packet_eq_divisor_combination]
  unfold FiniteSchur.combination divisorResidue divisorMoebius
  rw [← Finset.sum_add_distrib]
  calc
    _ = ∑ a : d.divisors, (ArithmeticFunction.moebius (d / a.val) : ℝ) *
        ((a.val : ℝ) - 1) := by
      apply Finset.sum_congr rfl
      intro a ha
      have hp := Nat.pos_of_mem_divisors a.property
      have hr := residue_reflection_sum hp
        (dvd_trans (Nat.dvd_of_mem_divisors a.property) hdQ) hk
      rw [Nat.cast_sub (by omega)] at hr
      push_cast at hr
      nlinarith only [congrArg (fun x : ℝ =>
        (ArithmeticFunction.moebius (d / a.val) : ℝ) * x) hr]
    _ = _ := packet_moebius_totient_source d hd

/-- The totient coefficient constraint is exactly the ordinary period mean. -/
theorem synthesis_period_mean (Q : ℕ) (s : Finset ℕ) (c : s → ℝ)
    (hQ : 0 < Q) (hs : ∀ q ∈ s, 1 < q) (hsQ : ∀ q ∈ s, q ∣ Q) :
    (∑ r : Fin Q, PhysicalPacketCore.synthesis s c r.val) / (Q : ℝ) =
      (ramanujanTotientVector s ⬝ᵥ c) / 2 := by
  apply reflection_uniform_mean Q hQ (PhysicalPacketCore.synthesis s c)
    (ramanujanTotientVector s ⬝ᵥ c)
  intro k hk
  unfold PhysicalPacketCore.synthesis FiniteSchur.combination
  rw [← Finset.sum_add_distrib]
  unfold dotProduct ramanujanTotientVector
  apply Finset.sum_congr rfl
  intro q hq
  have hp := packet_reflection_totient Q q.val k (hs q.val q.property)
    (hsQ q.val q.property) hk
  nlinarith only [congrArg (fun x : ℝ => c q * x) hp]

end RiemannResearch.RH.Pareto
