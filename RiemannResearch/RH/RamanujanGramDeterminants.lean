import RiemannResearch.RH.ResidueClosureDensity
import RiemannResearch.RH.RamanujanSaturationCriteria
import RiemannResearch.RH.RamanujanFiniteSpanBridge
import RiemannResearch.RH.IntegerDPPGramDeterminant
import RiemannResearch.RH.IntegerDPPWindow
import RiemannResearch.RH.IntegerDPPExistence
import RiemannResearch.RH.IntegerDPPKernel
import RiemannResearch.RH.IntegerDPPHazards
import RiemannResearch.RH.IntegerDPPClosure
import RiemannResearch.RH.BaezDuarteNaturalApproximation
import RiemannResearch.RH.ParetoTailCapacity
import RiemannResearch.RH.MobiusCoefficientStabilization
import RiemannResearch.Analysis.FiniteHilbertGramProjection
import RiemannResearch.Analysis.FiniteHilbertGramMatrix
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Ramanujan first-site and finite-window determinant structure

Source: user-requested duality program, 23 October 2026, and the existing
arithmetic DPP construction. The finite packet and residue families have
exactly the same span. Their complete projection kernels, determinant
polynomials, and finite-window gap probabilities therefore agree.

The first-site target is marked by minus the Moebius function; the constant
target's von Mangoldt source is a different observation. Every Gram matrix
below is the actual complete Pareto Gram matrix. No inverse or determinant
nonvanishing hypothesis is imposed: finite packet independence supplies it.
-/

noncomputable section
open Filter
open scoped Topology BigOperators
namespace RiemannResearch.RH.Pareto
open CoefficientStabilization CoefficientStabilization.TailCapacity
open RiemannResearch.Analysis.FiniteHilbertGram
open RiemannResearch.Analysis.FiniteGramCapacity

/-- Packet inverse-Gram regression agrees with the actual finite projection
for every Hilbert target, not only the constant target. -/
theorem packetFit_eq_projection (n : ℕ) (x : ThresholdHilbert) :
    Fintype.linearCombination ℝ
      (fun i : Fin n => ramanujanPacketHilbert (i.val + 2))
      (inverseCoeff (finitePacket_independent n) x) =
    (finiteSpace n).starProjection x := by
  have hmem : Fintype.linearCombination ℝ
      (fun i : Fin n => ramanujanPacketHilbert (i.val + 2))
      (inverseCoeff (finitePacket_independent n) x) ∈ finiteSpace n := by
    have h := synthesis_mem
      (fun i : Fin n => ramanujanPacketHilbert (i.val + 2))
      (inverseCoeff (finitePacket_independent n) x)
    change Fintype.linearCombination ℝ
        (fun i : Fin n => ramanujanPacketHilbert (i.val + 2))
        (inverseCoeff (finitePacket_independent n) x) ∈
      Submodule.span ℝ
        (Set.range (fun i : Fin n => ramanujanPacketHilbert (i.val + 2))) at h
    rw [finitePacket_span_eq] at h
    exact h
  symm
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero hmem
  intro w hw
  have hp : w ∈ synthesisSpan
      (fun i : Fin n => ramanujanPacketHilbert (i.val + 2)) := by
    change w ∈ Submodule.span ℝ
      (Set.range (fun i : Fin n => ramanujanPacketHilbert (i.val + 2)))
    rw [finitePacket_span_eq]
    exact hw
  rw [synthesisSpan, ← Fintype.range_linearCombination] at hp
  obtain ⟨a, rfl⟩ := hp
  exact residual_orthogonal (finitePacket_independent n) x a

theorem finitePacketGram_det_pos (n : ℕ) : 0 < (finitePacketGram n).det :=
  gramMatrix_det_pos (finitePacket_independent n)

/-- Complete first-site determinant polynomial in packet coordinates. -/
def packetHeadDeterminant (n : ℕ) (z : ℝ) : ℝ :=
  (finitePacketGram n - (z / 2) •
    Matrix.vecMulVec (packetHeadSource n) (packetHeadSource n)).det /
      (finitePacketGram n).det

theorem packetHeadDeterminant_eq (n : ℕ) (z : ℝ) :
    packetHeadDeterminant n z = 1 - z * fullCapacity n / 2 := by
  have he : finitePacketGram n - (z / 2) •
      Matrix.vecMulVec (packetHeadSource n) (packetHeadSource n) =
      finitePacketGram n + (-(z / 2)) •
        Matrix.vecMulVec (packetHeadSource n) (packetHeadSource n) := by
    rw [neg_smul, sub_eq_add_neg]
  unfold packetHeadDeterminant
  rw [he]
  have h := gramMatrix_det_update (finitePacket_independent n)
    (packetHeadSource n) (-(z / 2))
  change (finitePacketGram n + _).det = (finitePacketGram n).det *
    (1 + (-(z / 2)) *
      capacity (finitePacket_independent n) (packetHeadSource n)) at h
  rw [h, ← fullCapacity_eq_packetCapacity]
  have hg := ne_of_gt (finitePacketGram_det_pos n)
  field_simp [hg]
  ring

/-- Equality holds for every real parameter, not only the vacancy endpoint. -/
theorem packetHeadDeterminant_eq_residue (n : ℕ) (z : ℝ) :
    packetHeadDeterminant n z = IntegerDPP.headDeterminant n z := by
  rw [packetHeadDeterminant_eq, IntegerDPP.headDeterminant_eq]

theorem packetHeadDeterminant_one (n : ℕ) :
    packetHeadDeterminant n 1 = IntegerDPP.vacancy n := by
  rw [packetHeadDeterminant_eq_residue, IntegerDPP.headDeterminant_one]

theorem packetHeadDeterminant_one_eq_gram_ratio (n : ℕ) :
    packetHeadDeterminant n 1 =
      (IntegerDPP.tailGram n).det / (IntegerDPP.fullGram n).det := by
  rw [packetHeadDeterminant_one, IntegerDPP.gram_det_ratio_eq_vacancy]

/-- Exact transfer of the first-site tail-capacity criterion. -/
theorem packetHeadDeterminant_zero_iff_capacity :
    Tendsto (fun n => packetHeadDeterminant n 1) atTop (𝓝 0) ↔
      Tendsto tailCapacity atTop atTop := by
  simp_rw [packetHeadDeterminant_one]
  exact IntegerDPP.vacancy_tendsto_zero_iff

theorem riemannHypothesis_of_packetHeadDeterminant_zero
    (h : Tendsto (fun n => packetHeadDeterminant n 1) atTop (𝓝 0)) :
    RiemannHypothesis :=
  riemannHypothesis_of_tailCapacity_tendsto
    (packetHeadDeterminant_zero_iff_capacity.mp h)

/-- The packet determinant criterion exactly detects approximation of the
constant target, without an external analytic provider. -/
theorem packetHeadDeterminant_zero_iff_one_mem :
    Tendsto (fun n => packetHeadDeterminant n 1) atTop (𝓝 0) ↔
      hilbertOne ∈ CoefficientStabilization.closedSpace := by
  simp_rw [packetHeadDeterminant_one]
  exact IntegerDPP.vacancy_tendsto_zero_iff_one_mem

/-- The first-site determinant also detects density of the full legal span. -/
theorem packetHeadDeterminant_zero_iff_density :
    Tendsto (fun n => packetHeadDeterminant n 1) atTop (𝓝 0) ↔
      CoefficientStabilization.closedSpace = ⊤ :=
  packetHeadDeterminant_zero_iff_one_mem.trans
    CoefficientStabilization.closedSpace_eq_top_iff_one_mem.symm

/-- The Moebius first-site determinant and von Mangoldt constant-target mass
are different finite quantities with the same limiting saturation criterion. -/
theorem packetHeadDeterminant_zero_iff_mass :
    Tendsto (fun n => packetHeadDeterminant n 1) atTop (𝓝 0) ↔
      Tendsto RiemannResearch.RH.RamanujanCanonicalOptimizer.packetMass
        atTop (𝓝 1) :=
  packetHeadDeterminant_zero_iff_one_mem.trans
    (CoefficientStabilization.limitEnergy_zero_iff_mem.symm.trans
      (RiemannResearch.RH.RamanujanCanonicalOptimizer.packet_cofinal_mass_iff
        id tendsto_id).symm)

/-- An unconditional equivalence with the precise natural approximation
property used in the analytic Baez-Duarte input. -/
theorem packetHeadDeterminant_zero_iff_naturalApproximation :
    Tendsto (fun n => packetHeadDeterminant n 1) atTop (𝓝 0) ↔
      BaezDuarte.NaturalApproximation :=
  packetHeadDeterminant_zero_iff_one_mem.trans
    BaezDuarte.naturalApproximation_iff_one_mem.symm

/-- The reverse RH implication explicitly retains the external analytic
provider. The forward implication requires no such hypothesis. -/
theorem packetHeadDeterminant_zero_iff_riemannHypothesis
    (hBaezDuarte : RiemannHypothesis → BaezDuarte.NaturalApproximation) :
    Tendsto (fun n => packetHeadDeterminant n 1) atTop (𝓝 0) ↔
      RiemannHypothesis := by
  constructor
  · exact riemannHypothesis_of_packetHeadDeterminant_zero
  · intro hRH
    exact packetHeadDeterminant_zero_iff_naturalApproximation.mpr (hBaezDuarte hRH)

theorem integerLaw_first_site_packet_determinant (n : ℕ) :
    (IntegerDPP.integerLaw n).real {x | x 0 = false} =
      packetHeadDeterminant n 1 := by
  rw [IntegerDPP.integerLaw_first_site_vacancy, packetHeadDeterminant_one]

/-- Full physical window observations of the integrated packet dictionary. -/
def packetWindowFeatures (N m : ℕ) (e : Fin m → ℕ) : Matrix (Fin m) (Fin N) ℝ :=
  observationMatrix (fun k : Fin N => ramanujanPacketHilbert (k.val + 2))
    (fun i => IntegerDPP.countingBasis (e i))

def packetWindowGram (N m : ℕ) (e : Fin m → ℕ) : Matrix (Fin N) (Fin N) ℝ :=
  (packetWindowFeatures N m e).transpose * packetWindowFeatures N m e

/-- The complete finite-window kernel in the actual packet inverse metric. -/
theorem integerKernel_packet_window_matrix (N m : ℕ) (e : Fin m → ℕ) :
    Matrix.of (fun i j => IntegerDPP.integerKernel N (e i) (e j)) =
      packetWindowFeatures N m e * (finitePacketGram N)⁻¹ *
        (packetWindowFeatures N m e).transpose := by
  have h := projection_kernel_matrix (finitePacket_independent N)
    (fun i : Fin m => IntegerDPP.countingBasis (e i))
  simp_rw [← synthesis_inverseCoeff_eq_projection (finitePacket_independent N),
    packetFit_eq_projection] at h
  exact h

/-- All real-parameter window determinants transfer, including repeated observations. -/
theorem packet_window_determinant_eq_gram_ratio
    (N m : ℕ) (e : Fin m → ℕ) (z : ℝ) :
    (1 - z • Matrix.of (fun i j => IntegerDPP.integerKernel N (e i) (e j))).det =
      (finitePacketGram N - z • packetWindowGram N m e).det /
        (finitePacketGram N).det := by
  have h := Matrix.det_sub_mul_div (finitePacketGram N)
    (isUnit_iff_ne_zero.mpr (ne_of_gt (finitePacketGram_det_pos N)))
    (z • (packetWindowFeatures N m e).transpose) (packetWindowFeatures N m e)
  rw [Matrix.smul_mul, Matrix.mul_smul] at h
  rw [integerKernel_packet_window_matrix]
  exact h.symm

/-- Equality of complete residue and packet determinant ratios in every window. -/
theorem packet_window_gram_ratio_eq_residue
    (N m : ℕ) (e : Fin m → ℕ) (z : ℝ) :
    (finitePacketGram N - z • packetWindowGram N m e).det /
        (finitePacketGram N).det =
      (IntegerDPP.fullGram N - z • IntegerDPP.windowGram N m e).det /
        (IntegerDPP.fullGram N).det := by
  rw [← packet_window_determinant_eq_gram_ratio,
    ← IntegerDPP.window_determinant_eq_gram_ratio]

/-- The actual probability law's finite-window gaps in packet coordinates. -/
theorem integerLaw_window_packet_determinant (N m : ℕ) (e : Fin m ↪ ℕ) :
    (IntegerDPP.integerLaw N).real {x | ∀ i, x (e i) = false} =
      (finitePacketGram N - packetWindowGram N m e).det /
        (finitePacketGram N).det := by
  rw [IntegerDPP.integerLaw_finite_gap]
  simpa only [one_smul] using packet_window_determinant_eq_gram_ratio N m e 1

end RiemannResearch.RH.Pareto
