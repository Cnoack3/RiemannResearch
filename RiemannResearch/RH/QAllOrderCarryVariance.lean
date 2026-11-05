/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.RH.QAllOrderCarryPackets
import RiemannResearch.RH.ParetoUniformJordanIdentification
import RiemannResearch.RH.ParetoArithmeticRepair

/-! # Complete-period variance of a centered primitive residue component

Apply the existing uniform Jordan variance formula to the single
Möbius-inverted atom. Every proper-divisor contribution vanishes. -/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.Pareto

/-- Product Haar variance of the primitive residue component, at every
conductor (including nonsquarefree ones). -/
theorem centeredResiduePacket_jordan_variance (D Q : ℕ) (hD : 1 < D) (hQ : 0 < Q)
    (hdQ : D ∣ Q) :
    (∑ n ∈ Finset.range Q, (centeredResiduePacket D n) ^ 2) / (Q : ℝ) =
      jordanTwo D / (12 * (D : ℝ) ^ 2) := by
  classical
  let c := fun d : ℕ => (ArithmeticFunction.moebius (D / d) : ℝ)
  let B := fun n : ℕ => ∑ d ∈ D.divisors,
    c d * (residue d n - ((d : ℝ) - 1) / 2)
  have hid (q : ℕ) : (∑ d ∈ D.divisors, c d * divisorIncidence d q) =
      if q = D then 1 else 0 := by
    apply (mobius_inversion (fun n => if q = n then (1 : ℝ) else 0)
      (fun n => divisorIncidence n q)).mp _ D (by omega)
    intro n hn
    simp [divisorIncidence, Nat.mem_divisors, hn.ne']
  have he := centeredResidue_uniform_variance_eq_jordan D.divisors c id Q hQ
    (fun _ hd => Nat.pos_of_mem_divisors hd)
    (fun _ hd => (Nat.dvd_of_mem_divisors hd).trans hdQ)
  change (∑ n ∈ Finset.range Q, (B n) ^ 2) / (Q : ℝ) =
    (∑ q ∈ Q.divisors.erase 1, jordanTwo q *
      (∑ d ∈ D.divisors, c d * divisorIncidence d q) ^ 2) / 12 at he
  simp_rw [hid] at he
  have hmem : D ∈ Q.divisors.erase 1 :=
    Finset.mem_erase.mpr ⟨by omega, Nat.mem_divisors.mpr ⟨hdQ, hQ.ne'⟩⟩
  have hdiag : (∑ q ∈ Q.divisors.erase 1,
      jordanTwo q * (if q = D then (1 : ℝ) else 0) ^ 2) = jordanTwo D := by
    rw [Finset.sum_eq_single D]
    · simp
    · exact fun q _ hq => by simp [hq]
    · exact fun h => (h hmem).elim
  rw [hdiag] at he
  have hpt (n : ℕ) : centeredResiduePacket D n = B n / (D : ℝ) :=
    centeredResiduePacket_divisors D n hD
  simp_rw [hpt, div_pow]
  rw [← Finset.sum_div]
  calc
    _ = ((∑ n ∈ Finset.range Q, B n ^ 2) / (Q : ℝ)) / (D : ℝ) ^ 2 := by ring
    _ = _ := by rw [he]; ring

end RiemannResearch.RH.Pareto
