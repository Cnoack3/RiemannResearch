import RiemannResearch.Analysis.GaussianPolynomialFourierGrowth
import RiemannResearch.Analysis.GaussianVerticalLaplace
import RiemannResearch.Analysis.MontgomeryResolventWeilTest
import RiemannResearch.Analysis.SmoothZeroRemoval
import RiemannResearch.Analysis.SuperexponentialTranslation
import RiemannResearch.RH.WeilNoncompactExplicitFormula

/-! # Admissibility of the actual heat Gaussian for Weil's formula -/

noncomputable section
open MeasureTheory Complex
namespace RiemannResearch.Analysis.MontgomeryResolventHeatFamily
open MontgomeryResolventWeilTest GaussianPolynomialFourier GaussianPolynomialFourierGrowth
open GaussianPolynomialStrip

/-- The translated, modulated heat kernel with the resolvent mixing weight. -/
def heatGaussian (u t v y : ℝ) : ℂ :=
  (2 / Real.sqrt (4*Real.pi*v) : ℂ) * Complex.exp
    (-((y:ℂ)-u)^2/(4*(v:ℂ)) - (t:ℂ)*I*((y:ℂ)-u) - v)

/-- Fourier transform of the translated and modulated Gaussian at every
complex spectral point. -/
theorem paperFT_heatGaussian (u t : ℝ) {v : ℝ} (hv : 0 < v) (ρ : ℂ) :
    Zeta23.paperFT (heatGaussian u t v) (Zeta23.gammaOf ρ) =
      2 * Complex.exp ((u:ℂ)*(ρ-1/2)) *
        Complex.exp ((-(1-(ρ-1/2-(t:ℂ)*I)^2))*(v:ℂ)) := by
  let z := (ρ:ℂ)-1/2
  let a : ℂ := -1/(4*(v:ℂ))
  let b : ℂ := z-(t:ℂ)*I
  let c : ℂ := (u:ℂ)*z-v
  let K : ℂ := 2 / Real.sqrt (4*Real.pi*v)
  have hv' : (v:ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hv.ne'
  have ha : a.re < 0 := by
    have he : a = ((-1/(4*v) : ℝ) : ℂ) := by dsimp [a]; push_cast; rfl
    rw [he,Complex.ofReal_re]; exact div_neg_of_neg_of_pos (by norm_num) (by positivity)
  have hgz : I*Zeta23.gammaOf (ρ:ℂ) = z := by dsimp [z,Zeta23.gammaOf]; field_simp
  unfold Zeta23.paperFT
  rw [← integral_add_right_eq_self (μ := volume)
    (fun y : ℝ => heatGaussian u t v y * Complex.exp (I*Zeta23.gammaOf (ρ:ℂ)*y)) u]
  have he (x : ℝ) :
      heatGaussian u t v (x+u) * Complex.exp (I*Zeta23.gammaOf (ρ:ℂ)*(x+u : ℝ)) =
        K * Complex.exp (a*(x:ℂ)^2+b*x+c) := by
    rw [hgz]
    unfold heatGaussian
    rw [mul_assoc,← Complex.exp_add]
    congr 1
    congr 1
    dsimp [a,b,c]
    push_cast
    ring
  simp_rw [he]
  rw [integral_const_mul,integral_cexp_quadratic ha b c]
  have hbase : (Real.pi : ℂ)/ -a = ((4*Real.pi*v : ℝ) : ℂ) := by
    dsimp [a]; push_cast; field_simp
  have hp : ((Real.pi : ℂ)/ -a) ^ (1/2 : ℂ) = (Real.sqrt (4*Real.pi*v) : ℂ) := by
    rw [hbase,show (1/2:ℂ) = ((1/2:ℝ):ℂ) by norm_num,
      ← Complex.ofReal_cpow (show 0 ≤ 4*Real.pi*v by positivity),← Real.sqrt_eq_rpow]
  rw [hp]
  have hsqrt : (Real.sqrt (4*Real.pi*v) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.mpr (by positivity)).ne'
  have hexp : c - b^2/(4*a) = (u:ℂ)*z + (-(1-b^2))*(v:ℂ) := by
    dsimp [c,a]; field_simp; ring
  rw [hexp,Complex.exp_add]
  dsimp [K,z,b]
  field_simp


/-- The heat multiplier on actual zeros, with analytic multiplicity. -/
theorem paperFT_heatGaussian_zero (u t : ℝ) {v : ℝ} (hv : 0 < v)
    (ρ : Zeta23.zetaZeroConfig.carrier) :
    (Zeta23.zeroMult ρ : ℂ) * Zeta23.paperFT (heatGaussian u t v) (Zeta23.gammaOf ρ) =
      heatZeroTerm u t v ρ := by
  rw [paperFT_heatGaussian _ _ hv]
  unfold heatZeroTerm GaussianLaplaceBridge.exponentialKernel
  ring

private theorem polynomial_gaussian_bound (d : ℕ) {v : ℝ} (hv : 0 < v) (a x : ℝ) :
    (1+|x|)^d * Real.exp (-x^2/(4*v)) ≤
      Real.exp (v*(a+d)^2)*Real.exp (-a*|x|) := by
  have hx := Real.add_one_le_exp |x|
  have hp : (1+|x|)^d ≤ Real.exp ((d:ℝ)*|x|) := by
    rw [Real.exp_nat_mul]
    exact pow_le_pow_left₀ (by positivity) (by linarith only [hx]) _
  apply (mul_le_mul_of_nonneg_right hp (Real.exp_pos _).le).trans
  rw [← Real.exp_add,← Real.exp_add,Real.exp_le_exp]
  have he : v*(a+d)^2 + (-a*|x|) - ((d:ℝ)*|x| + -x^2/(4*v)) =
      (|x|-2*v*(a+d))^2/(4*v) := by
    rw [← sq_abs x]
    field_simp; ring
  exact sub_nonneg.mp (he.symm ▸ div_nonneg (sq_nonneg _) (by positivity))

theorem gaussian_density_admissible {v : ℝ} (hv : 0 < v) :
    SmoothSuperexponentialDecay (density v) := by
  constructor
  · have hcast : ContDiff ℝ (↑(⊤ : ℕ∞)) (fun x : ℝ => (x:ℂ)) := Complex.ofRealCLM.contDiff
    unfold density
    fun_prop
  · intro j a ha
    let P := derivativePolynomial v j
    let G := Real.sqrt (4*Real.pi*v)
    let C := P.stripGrowthConstant 0 / G
    have hG : 0 < G := Real.sqrt_pos.mpr (by positivity)
    have hC : 0 ≤ C := div_nonneg (P.stripGrowthConstant_nonneg le_rfl) hG.le
    refine ⟨(C+1)*Real.exp (v*(a+P.natDegree)^2),by positivity,fun x => ?_⟩
    have hP : ‖P.eval (x:ℂ)‖ ≤ P.stripGrowthConstant 0*(1+|x|)^P.natDegree := by
      simpa using P.norm_eval_le_stripGrowthConstant (t := x) (y := 0) le_rfl (by simp)
    rw [iteratedDeriv_density_eq_polynomial hv, norm_mul,density_eq_real,
      Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (by positivity)]
    change ‖P.eval (x:ℂ)‖ * (Real.exp (-x^2/(4*v))/G) ≤ _
    calc
      _ ≤ (P.stripGrowthConstant 0*(1+|x|)^P.natDegree)*(Real.exp (-x^2/(4*v))/G) :=
        mul_le_mul_of_nonneg_right hP (by positivity)
      _ = C*((1+|x|)^P.natDegree*Real.exp (-x^2/(4*v))) := by dsimp [C]; ring
      _ ≤ C*(Real.exp (v*(a+P.natDegree)^2)*Real.exp (-a*|x|)) :=
        mul_le_mul_of_nonneg_left (polynomial_gaussian_bound _ hv _ _) hC
      _ ≤ (C+1)*(Real.exp (v*(a+P.natDegree)^2)*Real.exp (-a*|x|)) :=
        mul_le_mul_of_nonneg_right (by linarith : C ≤ C+1) (by positivity)
      _ = _ := by ring

theorem heatGaussian_eq_density (u t v : ℝ) : heatGaussian u t v = fun y : ℝ =>
    (2*Complex.exp (-(v:ℂ))) *
      (Complex.exp ((-(t:ℂ)*I)*((y-u:ℝ):ℂ))*density v (y-u)) := by
  funext y
  unfold heatGaussian density
  push_cast
  rw [show -((y:ℂ)-u)^2/(4*(v:ℂ))-(t:ℂ)*I*((y:ℂ)-u)-v =
    -(v:ℂ) + ((-(t:ℂ)*I)*((y:ℂ)-u) + (-((y:ℂ)-u)^2/(4*(v:ℂ)))) by ring,
    Complex.exp_add,Complex.exp_add]
  ring

theorem heatGaussian_admissible (u t : ℝ) {v : ℝ} (hv : 0 < v) :
    SmoothSuperexponentialDecay (heatGaussian u t v) := by
  have h := (((gaussian_density_admissible hv).exp_mul (-(t:ℂ)*I)).translate u).const_mul
    (2*Complex.exp (-(v:ℂ)))
  rw [heatGaussian_eq_density]
  exact h

/-- The explicit formula for the actual heat family, before integration
over scale. No contour assumption occurs in this specialization. -/
theorem heatGaussian_actual_Weil (u t : ℝ) {v : ℝ} (hv : 0 < v) :
    (∑' ρ : Zeta23.zetaZeroConfig.carrier, heatZeroTerm u t v ρ) =
      Zeta23.EF.literatureRHS (heatGaussian u t v) := by
  simp_rw [← paperFT_heatGaussian_zero u t hv]
  exact RiemannResearch.RH.SignedWeilCorrelation.actual_noncompact_literal_Weil_explicit_formula
    (heatGaussian_admissible u t hv)

end RiemannResearch.Analysis.MontgomeryResolventHeatFamily

namespace RiemannResearch.Analysis.MontgomeryResolventHeatFamily

/--
info: 'RiemannResearch.Analysis.MontgomeryResolventHeatFamily.paperFT_heatGaussian_zero' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms paperFT_heatGaussian_zero

end RiemannResearch.Analysis.MontgomeryResolventHeatFamily

namespace RiemannResearch.Analysis.MontgomeryResolventHeatFamily

/--
info: 'RiemannResearch.Analysis.MontgomeryResolventHeatFamily.heatGaussian_actual_Weil' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms heatGaussian_actual_Weil

end RiemannResearch.Analysis.MontgomeryResolventHeatFamily
