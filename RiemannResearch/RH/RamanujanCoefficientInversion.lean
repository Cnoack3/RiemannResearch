import Mathlib.Tactic.Positivity
import RiemannResearch.RH.RamanujanCoefficientLimits
import RiemannResearch.RH.QRamanujanCanonicalOptimizer
import RiemannResearch.RH.RamanujanFiniteSpanBridge
import RiemannResearch.RH.MobiusCoefficientStabilization
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Two-sided finite legal coefficient inversion

Source: user-requested second Ramanujan duality program, 23 October 2026.
The divisor-sum inverse of the integrated packets gives the exact inverse
of the finite signed-multiple coordinate transform. This holds for every
coefficient vector, not only an optimizer, and therefore for both metrics.
Every sum is finite; no passage from coordinate limits to an infinite
multiple sum is made.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.RamanujanCoefficientInversion
open Pareto CoefficientStabilization RamanujanCanonicalOptimizer
open RiemannResearch.Analysis.FiniteHilbertGram

/-- Exact inverse arithmetic transform, indexed by packet conductor. -/
def residueToPacket (n : ℕ) (c : Fin n → ℝ) (i : Fin n) : ℝ :=
  ∑ j : Fin n, if i.val + 2 ∣ j.val + 2 then c j / ((j.val + 2 : ℕ) : ℝ) else 0

theorem residueToPacket_add (n : ℕ) (a b : Fin n → ℝ) :
    residueToPacket n (a+b) = residueToPacket n a + residueToPacket n b := by
  funext i
  simp only [residueToPacket, Pi.add_apply, add_div]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  split_ifs <;> simp

private theorem packet_divisor_sum_fin (n : ℕ) (j : Fin n) :
    (∑ d ∈ (j.val + 2).divisors.filter (fun d => 1 < d), ramanujanPacketHilbert d) =
      ∑ i : Fin n, if i.val + 2 ∣ j.val + 2 then
        ramanujanPacketHilbert (i.val + 2) else 0 := by
  classical
  rw [← Finset.sum_filter]
  symm
  apply Finset.sum_bij (fun i _ => i.val + 2)
  · intro i hi
    exact Finset.mem_filter.mpr ⟨Nat.mem_divisors.mpr
      ⟨(Finset.mem_filter.mp hi).2, by omega⟩, by omega⟩
  · intro i _ k _ hik
    apply Fin.ext
    omega
  · intro d hd
    have hd2 := (Finset.mem_filter.mp hd).2
    have hdiv := Nat.dvd_of_mem_divisors (Finset.mem_filter.mp hd).1
    have hdle := Nat.le_of_dvd (by omega : 0 < j.val + 2) hdiv
    refine ⟨⟨d - 2, by omega⟩, ?_, ?_⟩
    · apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      simpa only [show d - 2 + 2 = d by omega] using hdiv
    · simp only
      omega
  · intro i _
    rfl

theorem residueAtom_eq_packet_sum (n : ℕ) (j : Fin n) :
    residueAtom j.val =
      ∑ i : Fin n, if i.val + 2 ∣ j.val + 2 then
        (((j.val + 2 : ℕ) : ℝ)⁻¹) • ramanujanPacketHilbert (i.val + 2) else 0 := by
  have h := rawResidueAtom_eq_packet_divisor_sum (j.val + 2) (by omega)
  rw [Nat.add_sub_cancel, packet_divisor_sum_fin] at h
  have hi : ((j.val + 2 : ℕ) : ℝ) ≠ 0 := by positivity
  have hh := congrArg (fun f : ThresholdHilbert =>
    (((j.val + 2 : ℕ) : ℝ)⁻¹) • f) h
  simpa only [rawResidueAtom, smul_smul, inv_mul_cancel₀ hi, one_smul,
    Finset.smul_sum, smul_ite, smul_zero] using hh

/-- Exact equality of the two legal syntheses for arbitrary residue coefficients. -/
theorem residueToPacket_synthesis (n : ℕ) (c : Fin n → ℝ) :
    Fintype.linearCombination ℝ
      (fun i : Fin n => ramanujanPacketHilbert (i.val + 2))
      (residueToPacket n c) =
    Fintype.linearCombination ℝ (fun j : Fin n => residueAtom j.val) c := by
  classical
  simp only [Fintype.linearCombination_apply, residueToPacket, Finset.sum_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [residueAtom_eq_packet_sum n j, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro i _
  split_ifs <;> simp [div_eq_mul_inv, mul_smul]

/-- The original multiple transform is the exact forward coordinate map. -/
theorem packet_synthesis_eq_residue_transform (n : ℕ) (a : Fin n → ℝ) :
    Fintype.linearCombination ℝ
      (fun i : Fin n => ramanujanPacketHilbert (i.val + 2)) a =
    Fintype.linearCombination ℝ (fun i : Fin n => residueAtom i.val)
      (fun i => packetMultipleTransform n a (i.val + 2)) := by
  have hm := synthesis_mem (fun i : Fin n => ramanujanPacketHilbert (i.val + 2)) a
  change _ ∈ Submodule.span ℝ
    (Set.range (fun i : Fin n => ramanujanPacketHilbert (i.val + 2))) at hm
  rw [finitePacket_span_eq] at hm
  obtain ⟨b, hb⟩ := finiteSpace_expansion n _ hm
  have hc (i : Fin n) : packetMultipleTransform n a (i.val + 2) = b i := by
    rw [← coefficient_packet_synthesis n a (i.val + 2) (by omega), hb]
    exact coefficient_finite_sum n b i
  simpa only [Fintype.linearCombination_apply, hc] using hb

theorem packetMultipleTransform_residueToPacket (n : ℕ) (c : Fin n → ℝ) (i : Fin n) :
    packetMultipleTransform n (residueToPacket n c) (i.val + 2) = c i := by
  rw [← coefficient_packet_synthesis n (residueToPacket n c) (i.val + 2) (by omega),
    residueToPacket_synthesis]
  exact coefficient_finite_sum n c i

theorem residueToPacket_packetMultipleTransform (n : ℕ) (a : Fin n → ℝ) :
    residueToPacket n (fun i => packetMultipleTransform n a (i.val + 2)) = a := by
  have hs : Fintype.linearCombination ℝ
      (fun i : Fin n => ramanujanPacketHilbert (i.val + 2))
      (residueToPacket n (fun i => packetMultipleTransform n a (i.val + 2)) - a) = 0 := by
    rw [map_sub, residueToPacket_synthesis,
      ← packet_synthesis_eq_residue_transform, sub_self]
  have hz := Fintype.linearIndependent_iff.mp (finitePacket_independent n)
    (residueToPacket n (fun i => packetMultipleTransform n a (i.val + 2)) - a)
    (by simpa only [Fintype.linearCombination_apply] using hs)
  exact sub_eq_zero.mp (funext hz)

/-- A literal two-sided finite coordinate equivalence, independent of a metric. -/
def coefficientEquiv (n : ℕ) : (Fin n → ℝ) ≃ₗ[ℝ] (Fin n → ℝ) where
  toFun a := fun i => packetMultipleTransform n a (i.val + 2)
  invFun := residueToPacket n
  left_inv := residueToPacket_packetMultipleTransform n
  right_inv c := funext (packetMultipleTransform_residueToPacket n c)
  map_add' a b := by
    funext i
    change packetMultipleTransform n (a + b) (i.val + 2) =
      packetMultipleTransform n a (i.val + 2) + packetMultipleTransform n b (i.val + 2)
    rw [← coefficient_packet_synthesis n (a + b) (i.val + 2) (by omega),
      ← coefficient_packet_synthesis n a (i.val + 2) (by omega),
      ← coefficient_packet_synthesis n b (i.val + 2) (by omega), map_add, map_add]
  map_smul' r a := by
    funext i
    change packetMultipleTransform n (r • a) (i.val + 2) =
      r * packetMultipleTransform n a (i.val + 2)
    rw [← coefficient_packet_synthesis n (r • a) (i.val + 2) (by omega),
      ← coefficient_packet_synthesis n a (i.val + 2) (by omega), map_smul, map_smul]
    rfl

/-- The actual Pareto inverse-Gram packet coefficients are finite multiple sums
of the actual residue coefficients. -/
theorem canonical_packetCoefficient_formula (n : ℕ) (i : Fin n) :
    packetCoefficients n i =
      ∑ j : Fin n, if i.val + 2 ∣ j.val + 2 then
        coefficient n (j.val + 2) / ((j.val + 2 : ℕ) : ℝ) else 0 := by
  have hc (j : Fin n) :
      packetMultipleTransform n (packetCoefficients n) (j.val + 2) =
        coefficient n (j.val + 2) :=
    packetMultipleCoefficient_eq n (j.val + 2) (by omega)
  simpa only [residueToPacket, hc] using
    (congrFun (residueToPacket_packetMultipleTransform n (packetCoefficients n)) i).symm

/-- The same arithmetic inverse holds for the distinct actual Q optimizer. -/
theorem q_canonical_packetCoefficient_formula (n : ℕ) (i : Fin n) :
    QRamanujanCanonicalOptimizer.packetCoefficients n i =
      ∑ j : Fin n, if i.val + 2 ∣ j.val + 2 then
        QFullResidueProjection.coefficients n j / ((j.val + 2 : ℕ) : ℝ) else 0 := by
  have hc (j : Fin n) :
      packetMultipleTransform n (QRamanujanCanonicalOptimizer.packetCoefficients n)
        (j.val + 2) = QFullResidueProjection.coefficients n j := by
    change QRamanujanCanonicalOptimizer.packetCoordinate n (j.val + 2) = _
    exact (QRamanujanCanonicalOptimizer.residueCoefficients_eq_packetCoordinate n j).symm
  simpa only [residueToPacket, hc] using
    (congrFun (residueToPacket_packetMultipleTransform n
      (QRamanujanCanonicalOptimizer.packetCoefficients n)) i).symm

/-- Every finite reference vector gives an exact packet correction decomposition. -/
theorem canonical_packet_reference_decomposition (n : ℕ) (u : Fin n → ℝ) :
    packetCoefficients n = residueToPacket n u +
      residueToPacket n (fun i => coefficient n (i.val + 2) - u i) := by
  rw [← residueToPacket_add]
  have he : u + (fun i => coefficient n (i.val + 2) - u i) =
      (fun i => coefficient n (i.val + 2)) := by
    funext i
    simp only [Pi.add_apply]
    ring
  rw [he]
  funext i
  exact canonical_packetCoefficient_formula n i

end RiemannResearch.RH.RamanujanCoefficientInversion
