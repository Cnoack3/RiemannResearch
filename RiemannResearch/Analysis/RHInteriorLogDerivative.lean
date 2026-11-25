import RiemannResearch.NumberTheory.PrimeNumberTheorem.Quantitative.ClassicalStrongPNT
import RiemannResearch.RH.RiemannHypothesisRightHalfStrip

/-! # Interior logarithmic derivatives on RH

The classical disk estimate measures the finite sum of nearby zeros.
Under RH that sum is empty in any strictly smaller disk centred
at real part three halves. The estimate is uniform in the height. -/

noncomputable section
open Complex Set Filter
open scoped Topology
namespace RiemannResearch.Analysis.RHInteriorLogDerivative
open RiemannResearch.NumberTheory.PrimeNumberTheorem.Quantitative.ClassicalRegion

private theorem right_zero_free (hRH : RiemannHypothesis) {s : ℂ} (hs : 1/2 < s.re) :
    riemannZeta s ≠ 0 := by
  rcases lt_or_ge s.re 1 with hr | hr
  · exact RiemannResearch.RH.riemannHypothesis_iff_right_half_strip_zero_free.mp hRH s hs hr
  · exact riemannZeta_ne_zero_of_one_le_re hr

/-- Uniform in the entire translated disk at heights of magnitude at least two. -/
theorem logDeriv_zeta_disk_of_riemannHypothesis (hRH : RiemannHypothesis)
    {d : ℝ} (hd : 0 < d) (hd' : d < 1) :
    ∃ C > 0, ∀ (t : ℝ), 2 ≤ |t| → ∀ z : ℂ, ‖z‖ ≤ d →
      ‖logDeriv riemannZeta (z+3/2+Complex.I*(t:ℂ))‖ ≤ C*Real.log |t| := by
  let r := (1+d)/2
  let p := (1+r)/2
  let R := (1+p)/2
  have hr : d < r := by dsimp [r]; linarith
  have hr1 : r < 1 := by dsimp [r]; linarith
  have hp : r < p := by dsimp [p]; linarith
  have hp1 : p < 1 := by dsimp [p]; linarith
  have hR : p < R := by dsimp [R]; linarith
  have hR1 : R < 1 := by dsimp [R]; linarith
  obtain ⟨c,hc,h⟩ := LogDerivZetaFinalBound hd hr hr1 hp hR hR1
  let B := 16*r^2/(r-d)^3+1/((R^2/p-p)*Real.log (R/p))
  refine ⟨|B*c|+1,by positivity,?_⟩
  intro t ht z hz
  let f := fun v : ℂ => riemannZeta (v+3/2+Complex.I*(t:ℂ))
  have hfinite : (SetOfZeros 1 f).Finite := ZetaShiftFiniteZeros ht rfl
  have hfree (v : ℂ) (hv : ‖v‖ < 1) : f v ≠ 0 := by
    apply right_zero_free hRH
    have hab := Complex.abs_re_le_norm v
    have hb := (abs_lt.mp (hab.trans_lt hv)).1
    simp only [Complex.add_re, Complex.div_ofNat_re, Complex.re_ofNat, Complex.mul_re,
      Complex.I_re, Complex.ofReal_re, Complex.I_im, Complex.ofReal_im, zero_mul,mul_zero,sub_zero,add_zero]
    linarith
  have hzero : (finiteSetOfZeros_mono hr1 hfinite).toFinset = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro v hv
    have hh := (Set.Finite.mem_toFinset _).mp hv
    exact hfree v (hh.1.trans_lt hr1) hh.2
  have hz' : z ∈ Metric.closedBall (0:ℂ) d \ SetOfZeros p f := by
    refine ⟨by simpa using hz,?_⟩
    intro hmem
    exact hfree z (hz.trans_lt hd') hmem.2
  have hx := h t ht hfinite z hz'
  rw [hzero, Finset.sum_empty, sub_zero] at hx
  have hid : deriv f z = deriv riemannZeta (z+3/2+Complex.I*(t:ℂ)) := by
    dsimp [f]
    simp only [add_assoc, deriv_comp_add_const]
  change ‖deriv f z / f z‖ ≤ B*(c*Real.log |t|) at hx
  rw [hid] at hx
  change ‖deriv riemannZeta (z+3/2+Complex.I*(t:ℂ)) /
    riemannZeta (z+3/2+Complex.I*(t:ℂ))‖ ≤ _
  have hlog : 0 ≤ Real.log |t| := Real.log_nonneg (by linarith)
  have hb : B*c ≤ |B*c|+1 := (le_abs_self _).trans (by linarith)
  exact hx.trans (by rw [← mul_assoc]; exact mul_le_mul_of_nonneg_right hb hlog)

/-- On every closed substrip separated from the critical line, RH gives a
logarithmic bound for the zeta logarithmic derivative at all high ordinates. -/
theorem logDeriv_zeta_interior_of_riemannHypothesis (hRH : RiemannHypothesis)
    {η : ℝ} (hη : 0 < η) (hη' : η ≤ 1/2) :
    ∃ C > 0, ∀ σ t : ℝ, 1/2+η ≤ σ → σ ≤ 3/2 → 2 ≤ |t| →
      ‖logDeriv riemannZeta ((σ:ℂ)+(t:ℂ)*Complex.I)‖ ≤ C*Real.log |t| := by
  obtain ⟨C,hC,h⟩ := logDeriv_zeta_disk_of_riemannHypothesis hRH
    (show 0 < 1-η by linarith) (show 1-η < 1 by linarith)
  refine ⟨C,hC,fun σ t hs hσ ht => ?_⟩
  have hn : ‖((σ-3/2:ℝ):ℂ)‖ ≤ 1-η := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonpos (by linarith)]; linarith
  have hlocal := h t ht _ hn
  rw [show ((σ-3/2:ℝ):ℂ)+3/2+Complex.I*(t:ℂ) = (σ:ℂ)+(t:ℂ)*Complex.I by push_cast;ring] at hlocal
  exact hlocal

end RiemannResearch.Analysis.RHInteriorLogDerivative

namespace RiemannResearch.Analysis.RHInteriorLogDerivative

/--
info: 'RiemannResearch.Analysis.RHInteriorLogDerivative.logDeriv_zeta_interior_of_riemannHypothesis' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms logDeriv_zeta_interior_of_riemannHypothesis

end RiemannResearch.Analysis.RHInteriorLogDerivative
