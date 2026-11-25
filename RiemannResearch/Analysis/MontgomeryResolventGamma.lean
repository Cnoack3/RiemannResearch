import RiemannResearch.Analysis.MontgomeryResolventWeilTest
import RiemannResearch.RH.WeilExplicitFormula.GammaFacts.StirlingVert
import RiemannResearch.RH.WeilExplicitFormula.GammaFacts

/-! # Real-line centering of the Weil gamma density at a Montgomery frequency

The weighted change in the real gamma density has a uniform absolute
integral. Its interaction with the oscillatory phase costs O(1) pointwise
in t and u, which suffices for fixed-frequency normalization by T log T.
-/

noncomputable section
open MeasureTheory Complex Set Filter
namespace RiemannResearch.Analysis.MontgomeryResolventGamma
open MontgomeryResolventWeilTest

theorem gamma_centering_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r : ℝ, |2*Real.pi*Zeta23.mu r - Real.log (|r|+2)| ≤ C := by
  let g := fun r : ℝ => |2*Real.pi*Zeta23.mu r - Real.log (|r|+2)|
  have hc : Continuous g := by
    have hm := Zeta23.mu_smooth.continuous
    have hl : Continuous (fun r : ℝ => Real.log (|r|+2)) := by
      apply Continuous.log (by fun_prop)
      intro r; positivity
    exact ((continuous_const.mul hm).sub hl).abs
  obtain ⟨a,ha,hmax⟩ := (isCompact_Icc (a := (-1:ℝ)) (b := 1)).exists_isMaxOn
    ⟨0, by simp⟩ hc.continuousOn
  obtain ⟨J,hJ⟩ := Zeta23.StirlingVert.mu_stirling
  let K := 2*Real.pi*|J| + Real.log 3 + |Real.log (2*Real.pi)|
  refine ⟨max (g a) K,(abs_nonneg _).trans (le_max_left _ _),fun r => ?_⟩
  by_cases hr : |r| ≤ 1
  · exact (hmax (abs_le.mp hr)).trans (le_max_left _ _)
  apply le_trans _ (le_max_right _ _)
  have h1 : 1 ≤ |r| := by linarith
  have hp : 0 < |r| := by linarith
  have hs := hJ r h1
  have hsq : 1 ≤ r^2 := by nlinarith only [sq_abs r, h1, sq_nonneg (|r|-1)]
  have hs' : |2*Real.pi*Zeta23.mu r - Real.log (|r|/(2*Real.pi))| ≤ 2*Real.pi*|J| := by
    have he : 2*Real.pi*Zeta23.mu r - Real.log (|r|/(2*Real.pi)) =
        (2*Real.pi)*(Zeta23.mu r - 1/(2*Real.pi)*Real.log (|r|/(2*Real.pi))) := by
      field_simp [Real.pi_ne_zero]
    rw [he,abs_mul,abs_of_pos (by positivity : 0 < 2*Real.pi)]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact hs.trans ((div_le_iff₀ (zero_lt_one.trans_le hsq)).mpr
      ((le_abs_self J).trans ((le_mul_of_one_le_right (abs_nonneg _) hsq))))
  have hlo : 0 ≤ Real.log (|r|+2) - Real.log |r| :=
    sub_nonneg.mpr (Real.log_le_log hp (by linarith))
  have hup : Real.log (|r|+2) - Real.log |r| ≤ Real.log 3 := by
    rw [← Real.log_div (by positivity) hp.ne']
    apply Real.log_le_log (by positivity)
    exact (div_le_iff₀ hp).mpr (by linarith)
  have hrew : 2*Real.pi*Zeta23.mu r - Real.log (|r|+2) =
      (2*Real.pi*Zeta23.mu r - Real.log (|r|/(2*Real.pi))) -
      (Real.log (|r|+2)-Real.log |r|) - Real.log (2*Real.pi) := by
    rw [Real.log_div hp.ne' (by positivity)]; ring
  rw [hrew]
  dsimp [K]
  have ha : |Real.log (|r|+2)-Real.log (|r|)| ≤ Real.log 3 := by rw [abs_of_nonneg hlo]; exact hup
  exact (abs_sub _ _).trans (add_le_add ((abs_sub _ _).trans (add_le_add hs' ha)) le_rfl)

private theorem log_distance_one_side (a b : ℝ) :
    Real.log (|a|+2) - Real.log (|b|+2) ≤ Real.log (2+|a-b|) := by
  rw [← Real.log_div (by positivity) (by positivity)]
  apply Real.log_le_log (by positivity)
  apply (div_le_iff₀ (by positivity)).mpr
  have h := abs_sub_abs_le_abs_sub a b
  nlinarith only [h,abs_nonneg b,abs_nonneg (a-b),mul_nonneg (abs_nonneg b) (abs_nonneg (a-b))]

theorem log_distance_envelope (a b : ℝ) :
    |Real.log (|a|+2)-Real.log (|b|+2)| ≤ Real.log (2+|a-b|) := by
  apply abs_le.mpr
  constructor
  · have h := log_distance_one_side b a
    rw [abs_sub_comm b a] at h
    linarith
  · exact log_distance_one_side a b

/-- The gamma variation in the literal Weil formula after centering at the
observation height. The rational kernel is written in real angular units. -/
def gammaVariation (u t : ℝ) : ℂ :=
  ∫ h : ℝ, Complex.exp (I*(u:ℂ)*(t+h)) * ((2/(1+h^2) : ℝ) : ℂ) *
    ((2*Real.pi*Zeta23.mu (t+h)-Real.log (|t|+2) : ℝ) : ℂ)

/-- Uniform in all angular frequencies and all heights. -/
theorem gammaVariation_uniform_bound :
    ∃ J : ℝ, 0 ≤ J ∧ ∀ u t : ℝ, ‖gammaVariation u t‖ ≤ J := by
  obtain ⟨C,hC,h⟩ := gamma_centering_bound
  let major := fun h : ℝ => 2*(C+5)*(1+‖h‖^2)^(-(3/2:ℝ)/2)
  have hm : Integrable major := (integrable_rpow_neg_one_add_norm_sq (E := ℝ) (μ := volume)
    (by rw [Module.finrank_self]; norm_num)).const_mul _
  refine ⟨∫ h : ℝ, major h, integral_nonneg (fun h => by dsimp [major]; positivity),fun u t => ?_⟩
  apply (norm_integral_le_integral_norm _).trans
  apply integral_mono_of_nonneg (Eventually.of_forall fun h => norm_nonneg _) hm
  filter_upwards [] with s
  have hq : 0 < (1+s^2 : ℝ) := by positivity
  have hc : |2*Real.pi*Zeta23.mu (t+s)-Real.log (|t|+2)| ≤ C+Real.log (2+|s|) := by
    have ha := abs_sub_le (2*Real.pi*Zeta23.mu (t+s)) (Real.log (|t+s|+2)) (Real.log (|t|+2))
    have hd := log_distance_envelope (t+s) t
    rw [add_sub_cancel_left] at hd
    exact ha.trans (add_le_add (h _) hd)
  have hlog := Zeta23.WeilEF.log_two_add_le (x := |s|) (abs_nonneg _)
  rw [sq_abs] at hlog
  have hp : 1 ≤ (1+s^2:ℝ)^(1/4:ℝ) := Real.one_le_rpow (by nlinarith [sq_nonneg s]) (by norm_num)
  have henv : |2*Real.pi*Zeta23.mu (t+s)-Real.log (|t|+2)| ≤ (C+5)*(1+s^2)^(1/4:ℝ) := by
    linarith only [hc,hlog,le_mul_of_one_le_right hC hp]
  have he : ‖Complex.exp (I*(u:ℂ)*(t+s))‖ = 1 := by rw [Complex.norm_exp]; simp
  simp only [norm_mul,he,one_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (by positivity : 0 < 2/(1+s^2))]
  apply (mul_le_mul_of_nonneg_left henv (by positivity)).trans_eq
  dsimp [major]
  simp only [Real.norm_eq_abs,sq_abs]
  rw [show -(3/2:ℝ)/2=1/4-1 by norm_num,Real.rpow_sub hq,Real.rpow_one]
  ring

end RiemannResearch.Analysis.MontgomeryResolventGamma

namespace RiemannResearch.Analysis.MontgomeryResolventGamma

/--
info: 'RiemannResearch.Analysis.MontgomeryResolventGamma.gammaVariation_uniform_bound' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms gammaVariation_uniform_bound

end RiemannResearch.Analysis.MontgomeryResolventGamma
