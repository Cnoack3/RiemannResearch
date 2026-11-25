import RiemannResearch.RH.ParetoDampingAbsoluteSeed
import RiemannResearch.RH.DampedMobiusSquarefreeClosure
import RiemannResearch.RH.MellinModeOrthonormality
import RiemannResearch.RH.ParetoResidualBoundaryEnergy

/-! # Squarefree Pareto approximation under RH

An annihilator of the finite squarefree residue sums annihilates their
centered damped Mellin tests in absolute convergence. Analytic continuation
and the complete small-damping limit then kill its pairing against the
constant. The angular Fourier change of variables retains the factor 2π.

Bagchi states the discrete squarefree formulation in the remark following
the proof of Theorem 1. <https://arxiv.org/abs/math/0607733> -/

noncomputable section
open Complex MeasureTheory Set Filter
open scoped Topology ComplexConjugate
namespace RiemannResearch.RH.Pareto.ResidueMellin
open MellinFrequency (criticalPoint criticalPoint_re)

private def angularWitness (y : ThresholdHilbert) (t : ℝ) : ℂ :=
  conj (paretoMellinLogFourier y (t/(2*Real.pi)))

private theorem angularWitness_memLp (y : ThresholdHilbert) : MemLp (angularWitness y) 2 := by
  let F := paretoMellinLogFourier y
  have hs : StronglyMeasurable (angularWitness y) := by
    exact Complex.continuous_conj.comp_stronglyMeasurable
      ((Lp.stronglyMeasurable F).comp_measurable (by fun_prop))
  apply (memLp_two_iff_integrable_sq_norm hs.aestronglyMeasurable).mpr
  have hf := (memLp_two_iff_integrable_sq_norm (Lp.memLp F).1).mp (Lp.memLp F)
  apply (integrable_comp_mul_left_iff _ (by positivity : 2*Real.pi ≠ 0)).mp
  simpa only [angularWitness,norm_conj, mul_div_cancel_left₀ _ (by positivity : (2*Real.pi) ≠ 0)] using hf

private theorem angularWitness_pairing (y f : ThresholdHilbert) {C : ℝ}
    (hf : ∀ n, |hilbertSequence f n| ≤ C) :
    (∫ t, angularWitness y t * paretoMellin f (criticalPoint t)) = (2*Real.pi:ℝ) • (inner ℝ y f : ℂ) := by
  let k : ℝ := 2*Real.pi
  let g (t:ℝ) := angularWitness y t * paretoMellin f (criticalPoint t)
  have hk : 0 < k := by positivity
  have h := Measure.integral_comp_mul_left g k
  rw [abs_of_pos (inv_pos.mpr hk)] at h
  have he : (∫ x, g (k*x)) = inner ℂ (paretoMellinLogFourier y) (paretoMellinLogFourier f) := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [paretoMellinLogFourier_ae_eq_of_bounded f hf] with x hx
    rw [hx]
    dsimp [g,angularWitness]
    rw [show (k*x)/(2*Real.pi) = x by dsimp [k];field_simp]
    simp [k, mul_comm]
  rw [he,paretoMellinLogFourier_inner] at h
  change (∫ t, g t) = k • (inner ℝ y f : ℂ)
  rw [h,smul_smul,mul_inv_cancel₀ hk.ne',one_smul]

/-- Under RH the actual constant belongs to the closed span of the
squarefree residue atoms in the discrete Pareto Hilbert space. -/
theorem hilbertOne_mem_squarefreeClosure_of_riemannHypothesis (hRH : RiemannHypothesis) :
    hilbertOne ∈ squarefreeCRTSpan.topologicalClosure := by
  rw [← Submodule.orthogonal_orthogonal_eq_closure]
  apply (Submodule.mem_orthogonal _ _).mpr
  intro y hy
  have hfinite (d:ℝ) (N:ℕ) : (∫ t, angularWitness y t * paretoMellin
      (arithmeticFloorHilbertPartial (dampedMobiusWeight d) N) (criticalPoint t)) = 0 := by
    rw [angularWitness_pairing y _ (dampedMobius_partial_abs_le d N)]
    have h := (Submodule.mem_orthogonal' _ _).mp hy _ (dampedMobius_partial_mem_squarefreeSpan d N)
    simp [h]
  have hseed d (hd : d ∈ Ioo (1/2:ℝ) (3/4)) :=
    centeredTraceTest_seed_of_finite_annihilation hd.1 (angularWitness_memLp y) (hfinite d)
  have hz := target_pairing_zero_of_absolute_seed hRH (angularWitness_memLp y) hseed
  have h1 := angularWitness_pairing y hilbertOne RiemannResearch.RH.ParetoResidualBoundaryEnergy.hilbertOne_sequence_bound
  have hm (t:ℝ) : paretoMellin hilbertOne (criticalPoint t) = 1/criticalPoint t :=
    paretoMellin_one_of_pos _ (by rw [criticalPoint_re];norm_num)
  simp_rw [hm] at h1
  rw [hz] at h1
  have hscalar : ((2*Real.pi:ℝ):ℂ)*(inner ℝ y hilbertOne:ℂ) = 0 := by simpa [Complex.real_smul] using h1.symm
  exact_mod_cast (mul_eq_zero.mp hscalar).resolve_left (by exact_mod_cast (show (2*Real.pi:ℝ) ≠ 0 by positivity))

end RiemannResearch.RH.Pareto.ResidueMellin

namespace RiemannResearch.RH.Pareto.ResidueMellin

/--
info: 'RiemannResearch.RH.Pareto.ResidueMellin.hilbertOne_mem_squarefreeClosure_of_riemannHypothesis' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms hilbertOne_mem_squarefreeClosure_of_riemannHypothesis

end RiemannResearch.RH.Pareto.ResidueMellin
