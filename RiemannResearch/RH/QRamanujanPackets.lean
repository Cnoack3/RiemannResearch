import RiemannResearch.RH.QCovarianceInverse
import RiemannResearch.RH.ZetaTwoHilbertSpace
import RiemannResearch.RH.ArithmeticCumulativeBasic
import RiemannResearch.RH.ParetoResidueDuality
import Mathlib.Data.Finset.Union
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Actual Q Hilbert vectors for integrated Ramanujan packets

Source: the user's October 13, 2026 Ramanujan/Von-Mangoldt discussion.
The arithmetic packet and its divisor inversion are the existing declarations
in `ParetoResidueDuality`. This module transports those exact identities to
the actual Q Hilbert space and rewrites every finite `qSynthesis` candidate
in finite integrated-Ramanujan coordinates. No convergence or uniform energy
estimate is assumed in these finite equalities.
-/

namespace RiemannResearch.RH.QRamanujanPackets
noncomputable section
open scoped BigOperators
open RiemannResearch.RH.ZetaTwoHilbert
open RiemannResearch.RH.ArithmeticCumulative
open RiemannResearch.RH.Pareto
open RiemannResearch.RH.QCovarianceInverse

private theorem qSequence_finset_sum {ι : Type*} (s : Finset ι)
    (f : ι → QHilbert) :
    qSequence (∑ i ∈ s, f i) = fun n => ∑ i ∈ s, qSequence (f i) n := by
  funext n
  change (qSequenceLinear (∑ i ∈ s, f i)) n = _
  rw [map_sum]
  simp only [Finset.sum_apply]
  rfl

private theorem qSequence_smul (a : ℝ) (f : QHilbert) :
    qSequence (a • f) = fun n => a * qSequence f n := by
  change qSequenceLinear (a • f) = a • qSequenceLinear f
  exact qSequenceLinear.map_smul a f

/-- A finite legal residue combination representing the actual integrated
Ramanujan packet in Q, including its entire infinite physical tail. -/
def qRamanujanPacket (q : ℕ) : QHilbert :=
  ∑ d ∈ q.divisors,
    ((ArithmeticFunction.moebius (q / d) : ℝ) * (d : ℝ)) • qResidue d

@[simp] theorem qSequence_qRamanujanPacket (q : ℕ) :
    qSequence (qRamanujanPacket q) = ramanujanPacket q := by
  rw [qRamanujanPacket, qSequence_finset_sum]
  funext n
  unfold ramanujanPacket
  apply Finset.sum_congr rfl
  intro d hd
  rw [qSequence_smul, qSequence_qResidue]
  have hdR : (d : ℝ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (Nat.pos_of_mem_divisors hd))
  unfold residueFraction residue
  field_simp [hdR]

@[simp] theorem qRamanujanPacket_zero : qRamanujanPacket 0 = 0 := by
  simp [qRamanujanPacket]

@[simp] theorem qRamanujanPacket_one : qRamanujanPacket 1 = 0 := by
  simp [qRamanujanPacket]

/-- Exact divisor inversion, now as equality of actual Q Hilbert vectors. -/
theorem qRamanujanPacket_divisor_sum (d : ℕ) (hd : 0 < d) :
    (∑ q ∈ d.divisors, qRamanujanPacket q) = (d : ℝ) • qResidue d := by
  apply qSequence_injective
  rw [qSequence_finset_sum, qSequence_smul, qSequence_qResidue]
  funext n
  simp only [qSequence_qRamanujanPacket]
  rw [ramanujanPacket_divisor_sum d n hd]
  have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hd)
  unfold residueFraction residue
  field_simp [hdR]

theorem qResidue_eq_divisor_packets (d : ℕ) (hd : 0 < d) :
    qResidue d = (1 / (d : ℝ)) •
      (∑ q ∈ d.divisors, qRamanujanPacket q) := by
  rw [qRamanujanPacket_divisor_sum d hd, smul_smul]
  have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hd)
  simp [hdR]

variable {ι : Type*} [Fintype ι]

/-- The actual residue synthesis is a finite packet synthesis without any
asymptotic interchange or change of the approximation target. -/
theorem qSynthesis_eq_nested_packets (d : ι → ℕ) (c : ι → ℝ)
    (hd : ∀ i, 0 < d i) :
    qSynthesis d c = ∑ i, ∑ q ∈ (d i).divisors,
      (c i / (d i : ℝ)) • qRamanujanPacket q := by
  unfold qSynthesis
  apply Finset.sum_congr rfl
  intro i hi
  rw [qResidue_eq_divisor_packets (d i) (hd i)]
  simp only [smul_smul, Finset.smul_sum, div_eq_mul_inv, one_mul]

/-- Every divisor conductor needed by a finite residue list. -/
def packetSupport (d : ι → ℕ) : Finset ℕ :=
  Finset.univ.biUnion (fun i => (d i).divisors)

/-- Exact conductor-coordinate transform; duplicated residue conductors are
permitted and their contributions are added. -/
def packetCoefficient (d : ι → ℕ) (c : ι → ℝ) (q : ℕ) : ℝ :=
  ∑ i, if q ∣ d i then c i / (d i : ℝ) else 0

private theorem packetSupport_filter (d : ι → ℕ) (hd : ∀ i, 0 < d i) (i : ι) :
    (packetSupport d).filter (fun q => q ∣ d i) = (d i).divisors := by
  classical
  ext q
  constructor
  · intro hq
    exact Nat.mem_divisors.mpr
      ⟨(Finset.mem_filter.mp hq).2, ne_of_gt (hd i)⟩
  · intro hq
    apply Finset.mem_filter.mpr
    refine ⟨?_, Nat.dvd_of_mem_divisors hq⟩
    exact Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, hq⟩

/-- Explicit flattened Ramanujan coefficients for every actual Q candidate. -/
theorem qSynthesis_eq_packets (d : ι → ℕ) (c : ι → ℝ)
    (hd : ∀ i, 0 < d i) :
    qSynthesis d c = ∑ q ∈ packetSupport d,
      packetCoefficient d c q • qRamanujanPacket q := by
  classical
  rw [qSynthesis_eq_nested_packets d c hd]
  calc
    (∑ i, ∑ q ∈ (d i).divisors,
        (c i / (d i : ℝ)) • qRamanujanPacket q) =
        ∑ i, ∑ q ∈ packetSupport d,
          (if q ∣ d i then c i / (d i : ℝ) else 0) • qRamanujanPacket q := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [← packetSupport_filter d hd i, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro q hq
      split_ifs <;> simp
    _ = ∑ q ∈ packetSupport d,
        packetCoefficient d c q • qRamanujanPacket q := by
      rw [Finset.sum_comm]
      simp only [packetCoefficient, Finset.sum_smul]

end
end RiemannResearch.RH.QRamanujanPackets
