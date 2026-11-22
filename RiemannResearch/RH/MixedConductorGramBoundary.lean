import RiemannResearch.RH.MixedConductorPolarizedParseval
import RiemannResearch.RH.RamanujanGramDeterminants
import RiemannResearch.RH.RamanujanUnitMean

/-!
# Centered finite packet Gram matrices and the ambient mean boundary

The Gram matrix uses the original Pareto norm on all packets with conductors
from two through the stage cutoff. Centering subtracts the outer product of the
von Mangoldt mean vector. Its inverse Gram quadratic form measures the response
to that vector.

Bagchi, *On Nyman, Beurling and Báez-Duarte's Hilbert space reformulation of the
Riemann hypothesis*, Proc. Indian Acad. Sci. (Math. Sci.) 116 (2006), 137–146,
p. 146, discusses the distance as a Gram determinant ratio. The rank-one
updates below use the matrix determinant lemma. They retain the centered
snake boundary in the actual mixed projection Gram matrix.
-/

noncomputable section
open Filter
open scoped Topology BigOperators Matrix

namespace RiemannResearch.RH.Pareto.PrimePowerSchur.PacketGramBoundary

open CoefficientStabilization RamanujanCanonicalOptimizer MixedConductorBasis

/-- The actual Pareto means of the packets in the finite dictionary. -/
def meanVector (n : ℕ) (i : Fin n) : ℝ := ArithmeticFunction.vonMangoldt (i.val + 2)

/-- Subtract a scalar multiple of the mean outer product from the full Gram matrix. -/
def meanPencil (n : ℕ) (t : ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  finitePacketGram n - t • Matrix.vecMulVec (meanVector n) (meanVector n)

/-- Every determinant on the rank-one pencil is affine in its parameter. -/
theorem det_meanPencil (n : ℕ) (t : ℝ) :
    (meanPencil n t).det = (finitePacketGram n).det * (1 - t * packetMass n) := by
  have he : meanPencil n t = finitePacketGram n +
      Matrix.vecMulVec ((-t) • meanVector n) (meanVector n) := by
    ext i j
    change _ - t * (_ * _) = _ + (-t * _) * _
    ring
  have hm : dotProduct (meanVector n) ((finitePacketGram n)⁻¹.mulVec (meanVector n)) =
      packetMass n := (packetMass_eq_inverseGram n).symm
  rw [he, Matrix.det_add_outer _ (isUnit_iff_ne_zero.mpr (finitePacketGram_det_pos n).ne'),
    Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul, hm]
  ring

/-- The centered matrix is nonsingular at every finite stage, including the empty stage. -/
theorem centered_det_pos (n : ℕ) : 0 < (meanPencil n 1).det := by
  rw [det_meanPencil, one_mul]
  exact mul_pos (finitePacketGram_det_pos n) (sub_pos.mpr (packetMass_bounds n).2)

/-- The centered inverse Gram form uses only the arithmetic matrix and logarithmic means. -/
def centeredInverseGramMass (n : ℕ) : ℝ :=
  dotProduct (meanVector n) ((meanPencil n 1)⁻¹.mulVec (meanVector n))

/-- Uncentering the positive definite matrix gives the exact reciprocal finite error. -/
theorem centeredInverseGramMass_eq (n : ℕ) :
    centeredInverseGramMass n = (1 - packetMass n)⁻¹ - 1 := by
  have hA : meanPencil n 1 + Matrix.vecMulVec (meanVector n) (meanVector n) =
      finitePacketGram n := by simp [meanPencil]
  have h := Matrix.det_add_outer (meanPencil n 1)
    (isUnit_iff_ne_zero.mpr (centered_det_pos n).ne') (meanVector n) (meanVector n)
  rw [hA] at h
  change (finitePacketGram n).det = (meanPencil n 1).det * (1 + centeredInverseGramMass n) at h
  rw [det_meanPencil, one_mul, mul_assoc] at h
  have hh : 1 = (1 - packetMass n) * (1 + centeredInverseGramMass n) :=
    mul_left_cancel₀ (finitePacketGram_det_pos n).ne' (by simpa only [mul_one] using h)
  have hp := (sub_pos.mpr (packetMass_bounds n).2).ne'
  field_simp [hp]
  linarith only [hh]

/-- Both the determinant quotient and its limit use the complete arithmetic Gram matrix. -/
theorem centered_det_ratio_tendsto :
    Tendsto (fun n => (meanPencil n 1).det / (finitePacketGram n).det) atTop (𝓝 limitEnergy) := by
  have h := (tendsto_const_nhds (x := (1 : ℝ))).sub packetMass_tendsto
  have he (n : ℕ) : (meanPencil n 1).det / (finitePacketGram n).det = 1 - packetMass n := by
    rw [det_meanPencil, one_mul]
    field_simp [(finitePacketGram_det_pos n).ne']
  simpa only [he, sub_sub_cancel] using h

/-- The inverse quadratic form increases as conductors are added. -/
theorem centeredInverseGramMass_monotone : Monotone centeredInverseGramMass := by
  intro n m hnm
  rw [centeredInverseGramMass_eq, centeredInverseGramMass_eq]
  apply sub_le_sub_right
  exact (inv_le_inv₀ (sub_pos.mpr (packetMass_bounds n).2) (sub_pos.mpr (packetMass_bounds m).2)).mpr
    (sub_le_sub_left (packetMass_monotone hnm) _)

private theorem energy_nonzero_of_boundary_ne {h : CenteredMeanSnake.boundary ≠ 0} :
    limitEnergy ≠ 0 := by
  intro he
  exact h (CenteredMeanSnake.boundary_eq_zero_iff_one_mem.mpr (limitEnergy_zero_iff_mem.mp he))

/-- In the nonzero boundary branch the inverse Gram quadratic forms have a finite endpoint. -/
theorem centeredInverseGramMass_tendsto_of_ne (hb : CenteredMeanSnake.boundary ≠ 0) :
    Tendsto centeredInverseGramMass atTop (𝓝 (‖CenteredMeanSnake.boundary‖ ^ 2)⁻¹) := by
  have ht : Tendsto (fun n => 1 - packetMass n) atTop (𝓝 limitEnergy) := by
    simpa only [sub_sub_cancel] using (tendsto_const_nhds (x := (1 : ℝ))).sub packetMass_tendsto
  have hn := energy_nonzero_of_boundary_ne (h := hb)
  have h := (ht.inv₀ hn).sub_const 1
  have he : limitEnergy⁻¹ - 1 = (‖CenteredMeanSnake.boundary‖ ^ 2)⁻¹ := by
    rw [CenteredMeanSnake.boundary_norm_sq_eq_energy, inv_div]
    field_simp [hn]
  simpa only [← centeredInverseGramMass_eq, he] using h

/-- A divergence criterion in finite arithmetic matrices for vanishing of the centered boundary. -/
theorem boundary_eq_zero_iff_centeredInverseGramMass_tendsto :
    CenteredMeanSnake.boundary = 0 ↔ Tendsto centeredInverseGramMass atTop atTop := by
  constructor
  · intro hb
    have hz := limitEnergy_zero_iff_mem.mpr (CenteredMeanSnake.boundary_eq_zero_iff_one_mem.mp hb)
    have he : Tendsto (fun n => 1 - packetMass n) atTop (𝓝 0) := by
      simpa only [hz, sub_zero, sub_self] using
        (tendsto_const_nhds (x := (1 : ℝ))).sub packetMass_tendsto
    apply tendsto_atTop.mpr
    intro b
    let R := max b 0 + 2
    have hR : 0 < R := by dsimp [R]; linarith only [le_max_right b 0]
    filter_upwards [(tendsto_order.mp he).2 (1 / R) (one_div_pos.mpr hR)] with n hn
    have hs := sub_pos.mpr (packetMass_bounds n).2
    have ha : R * (1 - packetMass n) < 1 := by
      simpa only [mul_comm] using (lt_div_iff₀ hR).mp hn
    have hi : R < (1 - packetMass n)⁻¹ := by
      rw [inv_eq_one_div]
      exact (lt_div_iff₀ hs).mpr ha
    rw [centeredInverseGramMass_eq]
    dsimp only [R] at hi
    linarith only [hi, le_max_left b 0]
  · intro ht
    by_contra hb
    let L := (‖CenteredMeanSnake.boundary‖ ^ 2)⁻¹
    have hfin := centeredInverseGramMass_tendsto_of_ne hb
    have hup := (tendsto_order.mp hfin).2 (L + 1) (by dsimp [L]; linarith)
    have hlo := tendsto_atTop.mp ht (L + 1)
    obtain ⟨n, hn, hm⟩ := (hup.and hlo).exists
    exact (not_lt_of_ge hm) hn

/-- Unbounded growth of the finite arithmetic inverse forms along the full filtration implies RH. -/
theorem riemannHypothesis_of_centeredInverseGramMass_tendsto
    (h : Tendsto centeredInverseGramMass atTop atTop) : RiemannHypothesis :=
  CenteredMeanSnake.riemannHypothesis_of_boundary_eq_zero
    (boundary_eq_zero_iff_centeredInverseGramMass_tendsto.mpr h)

end RiemannResearch.RH.Pareto.PrimePowerSchur.PacketGramBoundary
