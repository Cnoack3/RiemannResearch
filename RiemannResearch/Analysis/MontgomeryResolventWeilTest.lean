import RiemannResearch.Analysis.ActualZeroGaussianLaplace
import RiemannResearch.Analysis.MontgomeryFiniteResolventSignal
import RiemannResearch.RH.WeilExplicitFormula

/-! # The shifted bilateral exponential in the actual Weil zero sum

The test has a cusp at the shifted center and exponential tails. Its actual
zero-side transform and reciprocal-square majorant are computed directly.
The compact smooth Weil identity requires an additional approximation step.
-/

noncomputable section
open Complex MeasureTheory Set
namespace RiemannResearch.Analysis.MontgomeryResolventWeilTest
open MontgomeryFiniteResolventSignal MontgomeryPoisson

/-- The modulation is centered at u, so the global phase is explicit. -/
def cutoffTest (u t v : ℝ) : ℂ :=
  (Real.exp (-|v-u|) : ℂ) * Complex.exp (-(t : ℂ)*I*(v-u))

theorem paperFT_cutoffTest (u t : ℝ) (ρ : ℂ) (hρ : |(ρ-1/2 : ℂ).re| < 1) :
    Zeta23.paperFT (cutoffTest u t) (Zeta23.gammaOf ρ) =
      Complex.exp ((u:ℂ)*(ρ-1/2))*rationalTerm (ρ-1/2) t := by
  let z := ρ-1/2
  have hgz : I*Zeta23.gammaOf ρ = z := by
    dsimp [z,Zeta23.gammaOf]; field_simp
  have hz : |(z-(t:ℂ)*I).re| < 1 := by simpa [z] using hρ
  unfold Zeta23.paperFT
  rw [← integral_add_right_eq_self (μ := volume)
    (fun v : ℝ => cutoffTest u t v * Complex.exp (I*Zeta23.gammaOf ρ*v)) u]
  have he (s : ℝ) : cutoffTest u t (s+u) * Complex.exp (I*Zeta23.gammaOf ρ*(s+u : ℝ)) =
      Complex.exp ((u:ℂ)*z) * feature 1 (z-(t:ℂ)*I) s := by
    rw [hgz]
    unfold cutoffTest feature
    rw [add_sub_cancel_right,one_mul,Complex.ofReal_exp,← Complex.exp_add,← Complex.exp_add,
      ← Complex.exp_add]
    congr 1
    push_cast
    ring
  simp_rw [he]
  rw [integral_const_mul,integral_feature 1 _ hz]
  simp [rationalTerm,z]

def fullZeroTerm (u t : ℝ) (ρ : Zeta23.zetaZeroConfig.carrier) : ℂ :=
  (Zeta23.zeroMult ρ : ℂ) * (Complex.exp ((u:ℂ)*((ρ:ℂ)-1/2))*rationalTerm ((ρ:ℂ)-1/2) t)

/-- Absolute convergence is unconditional for every fixed u and t. -/
theorem summable_norm_fullZeroTerm (u t : ℝ) : Summable (fun ρ => ‖fullZeroTerm u t ρ‖) := by
  let K := 32*Real.exp (|u|/2)*(1+t^2)
  apply (RiemannResearch.RH.WeilExplicitFormula.reciprocal_square_zero_sum_summable.mul_left K).of_norm_bounded
  intro ρ
  have hs := Zeta23.zetaZeroConfig.strip (ρ:ℂ) ρ.property
  have hz : |(((ρ:ℂ)-1/2):ℂ).re| ≤ 1/2 := by
    have he : (((ρ:ℂ)-1/2):ℂ).re = (ρ:ℂ).re-1/2 := by norm_num
    rw [he,abs_le]; constructor <;> linarith [hs.1,hs.2]
  have hg := Zeta23.WeilEF.abs_gammaOf_im_le hs
  have hh := norm_rationalTerm_le ((ρ:ℂ)-1/2) hz t
  have him : (((ρ:ℂ)-1/2):ℂ).im = (ρ:ℂ).im := by norm_num
  rw [him] at hh
  have hw : ‖Complex.exp ((u:ℂ)*((ρ:ℂ)-1/2))‖ ≤ Real.exp (|u|/2) := by
    rw [Complex.norm_exp,Complex.re_ofReal_mul]
    apply Real.exp_le_exp.mpr
    exact (le_abs_self _).trans ((abs_mul _ _).le.trans
      ((mul_le_mul_of_nonneg_left hz (abs_nonneg u)).trans_eq (by ring)))
  let γ := (ρ:ℂ).im
  let y := (Zeta23.gammaOf (ρ:ℂ)).im
  have hγ : 1+Complex.normSq (Zeta23.gammaOf (ρ:ℂ)) ≤ 4*(1+t^2)*(1+(γ-t)^2) := by
    rw [Complex.normSq_apply,Zeta23.WeilEF.gammaOf_re]
    have hy : y^2 ≤ (1/2:ℝ)^2 := (sq_abs y).symm.le.trans
      (pow_le_pow_left₀ (abs_nonneg _) hg 2)
    change 1 + (γ*γ + y*y) ≤ _
    nlinarith only [hy,sq_nonneg (γ-2*t),sq_nonneg ((γ-t)*t)]
  have hpos : 0 < 1+Complex.normSq (Zeta23.gammaOf (ρ:ℂ)) := by
    linarith [Complex.normSq_nonneg (Zeta23.gammaOf (ρ:ℂ))]
  have hratio : 8/(1+(γ-t)^2) ≤ 32*(1+t^2)/(1+Complex.normSq (Zeta23.gammaOf (ρ:ℂ))) := by
    apply (div_le_div_iff₀ (by positivity) hpos).mpr
    linarith only [hγ]
  rw [norm_norm,fullZeroTerm,norm_mul,Complex.norm_natCast,norm_mul]
  calc
    _ ≤ (Zeta23.zeroMult ρ : ℝ) * (Real.exp (|u|/2) *
        (32*(1+t^2)/(1+Complex.normSq (Zeta23.gammaOf (ρ:ℂ))))) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul hw (hh.trans hratio) (norm_nonneg _) (Real.exp_pos _).le) (Nat.cast_nonneg _)
    _ = _ := by dsimp only [K]; ring

/-- The heat-time multiplier of the modulated and translated normalized
Gaussian. Its integral gives the bilateral exponential resolvent. -/
def heatZeroTerm (u t v : ℝ) (ρ : Zeta23.zetaZeroConfig.carrier) : ℂ :=
  (2 * Complex.exp ((u:ℂ)*((ρ:ℂ)-1/2))) *
    GaussianLaplaceBridge.exponentialKernel (Zeta23.zeroMult ρ)
      (1-((ρ:ℂ)-1/2-(t:ℂ)*I)^2) v

private theorem heatDen_sector (t : ℝ) (ρ : Zeta23.zetaZeroConfig.carrier) :
    let D : ℂ := 1-((ρ:ℂ)-1/2-(t:ℂ)*I)^2
    0 < D.re ∧ ‖D‖ ≤ 2*D.re := by
  let z : ℂ := (ρ:ℂ)-1/2-(t:ℂ)*I
  let D := 1-z^2
  have hs := Zeta23.zetaZeroConfig.strip (ρ:ℂ) ρ.property
  have hz : |z.re| ≤ 1/2 := by
    have he : z.re = (ρ:ℂ).re-1/2 := by norm_num [z]
    rw [he,abs_le]; constructor <;> linarith [hs.1,hs.2]
  have hsqr : z.re^2 ≤ (1/2:ℝ)^2 :=
    (sq_abs _).symm.le.trans (pow_le_pow_left₀ (abs_nonneg _) hz 2)
  have hre : D.re = 1-z.re^2+z.im^2 := by simp [D,pow_two,Complex.mul_re]; ring
  have him : D.im = -2*z.re*z.im := by simp [D,pow_two,Complex.mul_im]; ring
  have hd : 0 < D.re := by rw [hre]; nlinarith [sq_nonneg z.im]
  refine ⟨hd,(Complex.norm_le_abs_re_add_abs_im D).trans ?_⟩
  rw [abs_of_pos hd,him,abs_mul,abs_mul,abs_neg,abs_two]
  have h₁ := mul_le_mul_of_nonneg_right hz (abs_nonneg z.im)
  have h₂ : |z.im| ≤ 3/4+z.im^2 := by nlinarith only [sq_nonneg (|z.im|-1/2),sq_abs z.im]
  rw [hre]
  nlinarith

theorem heatZeroTerm_integrable (u t : ℝ) (ρ : Zeta23.zetaZeroConfig.carrier) :
    IntegrableOn (fun v => heatZeroTerm u t v ρ) (Ioi (0:ℝ)) :=
  (GaussianLaplaceBridge.exponentialKernel_integrable _ _ (heatDen_sector t ρ).1).const_mul _

theorem integral_heatZeroTerm (u t : ℝ) (ρ : Zeta23.zetaZeroConfig.carrier) :
    (∫ v : ℝ in Ioi 0, heatZeroTerm u t v ρ) = fullZeroTerm u t ρ := by
  unfold heatZeroTerm fullZeroTerm rationalTerm
  rw [integral_const_mul,GaussianLaplaceBridge.exponentialKernel_integral _ _ (heatDen_sector t ρ).1]
  ring

private theorem integral_norm_heatZeroTerm_le (u t : ℝ) (ρ : Zeta23.zetaZeroConfig.carrier) :
    (∫ v : ℝ in Ioi 0, ‖heatZeroTerm u t v ρ‖) ≤ 2 * ‖fullZeroTerm u t ρ‖ := by
  let D : ℂ := 1-((ρ:ℂ)-1/2-(t:ℂ)*I)^2
  obtain ⟨hd,hD⟩ := heatDen_sector t ρ
  change 0 < D.re at hd
  change ‖D‖ ≤ 2*D.re at hD
  have hdn : 0 < ‖D‖ := hd.trans_le (Complex.re_le_norm _)
  let E := ‖Complex.exp ((u:ℂ)*((ρ:ℂ)-1/2))‖
  let M := (Zeta23.zeroMult ρ : ℝ)
  have hE : 0 ≤ E := norm_nonneg _
  have hM : 0 ≤ M := Nat.cast_nonneg _
  have hh : 1/D.re ≤ 2/‖D‖ := (div_le_div_iff₀ hd hdn).mpr (by simpa using hD)
  simp only [heatZeroTerm,norm_mul,integral_const_mul,
    GaussianLaplaceBridge.exponentialKernel_integral_norm _ _ (heatDen_sector t ρ).1,
    fullZeroTerm,rationalTerm,Complex.norm_natCast,norm_div,Complex.norm_ofNat]
  change 2 * E * (M/D.re) ≤ 2 * (M * (E * (2/‖D‖)))
  calc
    _ = (2*E*M)*(1/D.re) := by ring
    _ ≤ (2*E*M)*(2/‖D‖) := mul_le_mul_of_nonneg_left hh (by positivity)
    _ = _ := by ring

/-- Absolute Fubini for the actual zeta zeros and the heat-time mixture. -/
theorem integral_actual_zero_heat_mixture (u t : ℝ) :
    (∫ v : ℝ in Ioi 0, ∑' ρ : Zeta23.zetaZeroConfig.carrier, heatZeroTerm u t v ρ) =
      ∑' ρ : Zeta23.zetaZeroConfig.carrier, fullZeroTerm u t ρ := by
  have hs : Summable (fun ρ : Zeta23.zetaZeroConfig.carrier =>
      ∫ v : ℝ in Ioi 0, ‖heatZeroTerm u t v ρ‖) :=
    Summable.of_nonneg_of_le (fun _ => integral_nonneg fun _ => norm_nonneg _)
      (integral_norm_heatZeroTerm_le u t) ((summable_norm_fullZeroTerm u t).mul_left 2)
  letI : Countable Zeta23.zetaZeroConfig.carrier := ActualZeroGaussianLaplace.actualZero_countable
  have hi := integral_tsum_of_summable_integral_norm (heatZeroTerm_integrable u t) hs
  simp only [integral_heatZeroTerm] at hi
  exact hi.symm


end RiemannResearch.Analysis.MontgomeryResolventWeilTest
