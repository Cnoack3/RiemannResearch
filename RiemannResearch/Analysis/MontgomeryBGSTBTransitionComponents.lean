import RiemannResearch.Analysis.MontgomeryRawSecondOrderTransition
import RiemannResearch.Analysis.MontgomeryPrimeCrossIntegral
import RiemannResearch.Analysis.MontgomeryLogMeanSquare
import RiemannResearch.Analysis.MontgomeryHorizontalTransfer
import RiemannResearch.Analysis.MontgomeryTransitionFrequency
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! # The narrow positive-cutoff BGSTB estimate from component bounds

BGSTB, corrected §3, (3.4), controls the third signal and the two height
cutoffs. Montgomery–Vaughan mean values and the prime number theorem yield
the separate prime second-moment estimate. The signed cross integral and
the logarithmic signal energy already have actual providers in the repository.
Sources: https://arxiv.org/html/2501.14545v3#S3.E4 and
https://doi.org/10.1112/jlms/s2-8.1.73 . -/

noncomputable section
open Filter Set MeasureTheory
open scoped Topology
namespace RiemannResearch.Analysis.MontgomeryHorizontalBessel
open MontgomeryHorizontalTransfer MontgomeryPrimeCrossIntegral ZeroOrdinate

def primeSignalEnergy (T x : ℝ) : ℝ :=
  ∫ t in (0:ℝ)..T, ‖∑' n : ℕ, (primeWeight x n : ℂ) * phase (Real.log n) t‖^2

def logSignalEnergy (T x : ℝ) : ℝ :=
  ∫ t in (0:ℝ)..T, (Real.log (t+2)/x)^2

/-- Positive-cutoff remainder after retaining the two main signal energies
and their exact signed cross integral. -/
def thirdSignalResidual (T x : ℝ) : ℝ :=
  2*Real.pi*(actualComplexPairSum T (Real.log x)).re -
    (logSignalEnergy T x + primeSignalEnergy T x + 2*(crossIntegral x T).re)

/-- BGSTB (3.4), M₃≪T/x²+x and the two Cauchy–Schwarz cross terms with A₃.
The A₁,A₂ cross term is still signed inside the left-hand side. -/
def PositiveCutoffThirdSignalSource : Prop :=
  ∃ D : ℝ, 0 ≤ D ∧ ∀ᶠ T : ℝ in atTop, ∀ x ∈ Icc (1:ℝ) T,
    let E := T/x^2+x
    |thirdSignalResidual T x| ≤ D*(Real.sqrt T+x+E+
      Real.sqrt ((logSignalEnergy T x+primeSignalEnergy T x)*E))

/-- Mean value of the actual infinite von Mangoldt Dirichlet polynomial.
A spacing-weighted version further sharpens x log(2x). -/
def PrimeSignalMeanSquareSource : Prop :=
  ∃ J : ℝ, 0 ≤ J ∧ ∀ᶠ T : ℝ in atTop, ∀ x ∈ Icc (2:ℝ) T,
    |primeSignalEnergy T x-T*Real.log x| ≤ J*(T+x*Real.log (2*x))

/-- A quadratic error in x suffices in the transition. It admits a direct
provider from the repository's checked Montgomery–Vaughan inequality. -/
def QuadraticPrimeSignalMeanSquareSource : Prop :=
  ∃ J : ℝ, 0 ≤ J ∧ ∀ᶠ T : ℝ in atTop, ∀ x ∈ Icc (2:ℝ) T,
    |primeSignalEnergy T x-T*Real.log x| ≤ J*(T+x^2)

theorem quadraticPrimeSignalMeanSquare_of_published (h : PrimeSignalMeanSquareSource) :
    QuadraticPrimeSignalMeanSquareSource := by
  obtain ⟨J,hJ,hp⟩ := h
  refine ⟨2*J,by positivity,?_⟩
  filter_upwards [hp,eventually_ge_atTop (0:ℝ)] with T ht hT
  intro x hx
  have hx0 : 0 < x := by linarith [hx.1]
  have hlog := Real.log_le_sub_one_of_pos (by positivity : 0 < 2*x)
  apply (ht x hx).trans
  have hlog' := mul_le_mul_of_nonneg_left hlog hx0.le
  calc
    _ ≤ J*(T+2*x^2) := mul_le_mul_of_nonneg_left (by nlinarith only [hlog',hx0.le]) hJ
    _ ≤ (2*J)*(T+x^2) := by nlinarith only [mul_nonneg hJ hT]

/-- Oscillation of the retained first-prime cross integral supplies a
uniform linear budget at all positive prime cutoffs. -/
theorem primeCross_linear_bound {T x : ℝ} (hT : 2 ≤ T) (hx : 0 < x) :
    |(crossIntegral x T).re| ≤ (4/Real.log 2 * ∑' n : ℕ, mangoldtThreeHalves n)*T := by
  have h := norm_crossIntegral_le hx (by linarith : 0 ≤ T)
  have hm : 0 ≤ ∑' n : ℕ, mangoldtThreeHalves n := tsum_nonneg fun n =>
    div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  have hlog := Real.log_le_sub_one_of_pos (by linarith : 0 < T+2)
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  calc
    _ ≤ ‖crossIntegral x T‖ := Complex.abs_re_le_norm _
    _ ≤ _ := h
    _ ≤ (4*T / Real.log 2) * ∑' n : ℕ, mangoldtThreeHalves n :=
      mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right (by linarith) hl2.le) hm
    _ = _ := by ring

/-- On x=e^(c/2)√log T the third-signal cross terms, the cutoff and
the prime mean-square residual are all O_A(T) before normalization. -/
theorem sharpTransitionSecondOrder_of_quadratic_components
    (hthird : PositiveCutoffThirdSignalSource) (hprime : QuadraticPrimeSignalMeanSquareSource) :
    SharpTransitionSecondOrder := by
  obtain ⟨D,hD,hd⟩ := hthird
  obtain ⟨J,hJ,hj⟩ := hprime
  intro A
  let B := Real.exp |A|+1
  let P := J*(1+2*B)
  let H := 4*B+1+P
  let X := 4/Real.log 2 * ∑' n : ℕ, mangoldtThreeHalves n
  let K := D*(2+2*B+Real.sqrt (H*(2*B))) + 3*B+P+2*X
  have hB : 0 < B := by dsimp [B]; positivity
  have hP : 0 ≤ P := by dsimp [P]; positivity
  have hH : 0 ≤ H := by dsimp [H]; positivity
  have hmn : 0 ≤ ∑' n : ℕ, mangoldtThreeHalves n := tsum_nonneg fun n =>
    div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  have hX : 0 ≤ X := by
    dsimp [X]
    exact mul_nonneg (by positivity) hmn
  refine ⟨K, by dsimp [K]; positivity, ?_⟩
  have hlog2 : Tendsto (fun T : ℝ => Real.log T^2 / T) atTop (𝓝 0) := by
    have h := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 2).comp Real.tendsto_log_atTop
    apply h.congr'
    filter_upwards [eventually_gt_atTop (0:ℝ)] with T hT
    simp only [Function.comp_def,Real.exp_neg,Real.exp_log hT,div_eq_mul_inv]
  filter_upwards [hd,hj,eventually_ge_atTop (2:ℝ), Real.tendsto_log_atTop.eventually_ge_atTop
    (max 1 B), (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).eventually_ge_atTop
      (2*Real.log 2+|A|), hlog2.eventually_le_const zero_lt_one] with T h3 h2 hT hLb hℓ hpow
  intro c hc
  let L := Real.log T
  let α := transitionFrequency c T
  let u := α*L
  let x := Real.exp u
  have hTpos : 0 < T := by linarith
  have hT1 : 1 < T := by linarith
  have hL : 0 < L := Real.log_pos hT1
  have hL1 : 1 ≤ L := (le_max_left 1 B).trans hLb
  have hBL : B ≤ L := (le_max_right 1 B).trans hLb
  have hLT2 : L^2 ≤ T := by simpa using (div_le_iff₀ hTpos).mp hpow
  have hLT : L ≤ T := by nlinarith only [hL1,hLT2, sq_nonneg (L-1)]
  have hLT' : L ≤ T/L := (le_div_iff₀ hL).2 (by simpa only [← sq] using hLT2)
  have hu : u = (Real.log L+c)/2 := div_mul_cancel₀ _ hL.ne'
  have hxp : 0 < x := Real.exp_pos _
  have hx2 : 2 ≤ x := by
    rw [show (2:ℝ)=Real.exp (Real.log 2) by rw [Real.exp_log (by norm_num)]]
    apply Real.exp_le_exp.mpr
    rw [hu]
    change 2*Real.log 2+|A| ≤ Real.log L at hℓ
    linarith only [hℓ, (abs_le.mp hc).1, le_abs_self A]
  have hxl : Real.log x = u := Real.log_exp _
  have hxx : x^2 = L*Real.exp c := by
    dsimp only [x]
    rw [pow_two, ← Real.exp_add, hu, show (Real.log L+c)/2+(Real.log L+c)/2 =
      Real.log L+c by ring, Real.exp_add,Real.exp_log hL]
  have hplus : Real.exp c ≤ B := (Real.exp_le_exp.mpr
    ((abs_le.mp hc).2.trans (le_abs_self A))).trans (by dsimp [B]; linarith)
  have hminus : Real.exp (-c) ≤ B := (Real.exp_le_exp.mpr
    (show -c ≤ |A| by linarith only [(abs_le.mp hc).1,le_abs_self A])).trans
    (by dsimp [B]; linarith)
  have hxSq : x^2 ≤ B*L := by rw [hxx,mul_comm B L]; exact mul_le_mul_of_nonneg_left hplus hL.le
  have hdiv : L/x^2 ≤ B := by
    rw [hxx,div_mul_eq_div_div,div_self hL.ne',one_div]
    simpa only [Real.exp_neg] using hminus
  have hxL : x ≤ B*L := (show x ≤ x^2 by
    nlinarith [mul_nonneg hxp.le (by linarith : 0 ≤ x-1)]).trans hxSq
  have hxT : x ≤ T := hxL.trans ((mul_le_mul_of_nonneg_right hBL hL.le).trans
    (by simpa only [← sq] using hLT2))
  have hxquad : x^2 ≤ 2*B*T := hxSq.trans ((mul_le_mul_of_nonneg_left hLT hB.le).trans
    (by nlinarith only [mul_nonneg hB.le hTpos.le]))
  have hxLogT : Real.log x ≤ L := Real.log_le_log hxp hxT
  have hM1₀ : 0 ≤ logSignalEnergy T x :=
    intervalIntegral.integral_nonneg hTpos.le fun t _ => sq_nonneg _
  have hM2₀ : 0 ≤ primeSignalEnergy T x :=
    intervalIntegral.integral_nonneg hTpos.le fun t _ => sq_nonneg _
  have herr₁ : |logSignalEnergy T x-T*L^2/x^2| ≤ (3*B)*T := by
    apply (MontgomeryLogMeanSquare.log_mean_square_error_le hT x).trans
    calc
      3*T*L/x^2 = (3*T)*(L/x^2) := by ring
      _ ≤ (3*T)*B := mul_le_mul_of_nonneg_left hdiv (by positivity)
      _ = _ := by ring
  have herr₂ : |primeSignalEnergy T x-T*Real.log x| ≤ P*T := by
    apply (h2 x ⟨hx2,hxT⟩).trans
    calc
      _ ≤ J*(T+2*B*T) := mul_le_mul_of_nonneg_left (add_le_add le_rfl hxquad) hJ
      _ = _ := by dsimp [P];ring
  have hmain₁ : T*L^2/x^2 ≤ B*T*L := by
    calc
      _ = (T*L)*(L/x^2) := by ring
      _ ≤ (T*L)*B := mul_le_mul_of_nonneg_left hdiv (by positivity)
      _ = _ := by ring
  have hMsum : logSignalEnergy T x+primeSignalEnergy T x ≤ H*T*L := by
    have hTL1 := le_mul_of_one_le_right hTpos.le hL1
    have hBp := mul_le_mul_of_nonneg_left hTL1 (show 0 ≤ 3*B by positivity)
    have hPp := mul_le_mul_of_nonneg_left hTL1 hP
    have hl := mul_le_mul_of_nonneg_left hxLogT hTpos.le
    dsimp [H]
    linarith only [(abs_le.mp herr₁).2,(abs_le.mp herr₂).2,hmain₁,hBp,hPp,hl]
  let E := T/x^2+x
  have hE₀ : 0 ≤ E := by dsimp [E]; positivity
  have hE : E ≤ (2*B)*T/L := by
    have h1 : T/x^2 ≤ B*(T/L) := by
      calc
        T/x^2 = (T/L)*(L/x^2) := by field_simp [hxp.ne',hL.ne']
        _ ≤ (T/L)*B := mul_le_mul_of_nonneg_left hdiv (by positivity)
        _ = _ := mul_comm _ _
    have h2' := hxL.trans (mul_le_mul_of_nonneg_left hLT' hB.le)
    exact (add_le_add h1 h2').trans_eq (by ring)
  have hE' : E ≤ (2*B)*T := hE.trans ((div_le_iff₀ hL).2
    (le_mul_of_one_le_right (by positivity) hL1))
  have hcross3 : Real.sqrt ((logSignalEnergy T x+primeSignalEnergy T x)*E) ≤
      Real.sqrt (H*(2*B))*T := by
    calc
      _ ≤ Real.sqrt (H*(2*B)*T^2) := Real.sqrt_le_sqrt ((mul_le_mul hMsum hE hE₀
        (by positivity)).trans_eq (by field_simp [hL.ne']))
      _ = _ := by rw [Real.sqrt_mul (show 0 ≤ H*(2*B) by positivity), Real.sqrt_sq hTpos.le]
  have hsqrtT : Real.sqrt T ≤ T := by
    nlinarith only [Real.sq_sqrt hTpos.le, Real.sqrt_nonneg T, hT, sq_nonneg (Real.sqrt T-1)]
  have hthird' : |thirdSignalResidual T x| ≤ D*(2+2*B+Real.sqrt (H*(2*B)))*T := by
    apply (h3 x ⟨by linarith,hxT⟩).trans
    calc
      _ ≤ D*(T+T+(2*B)*T+Real.sqrt (H*(2*B))*T) :=
        mul_le_mul_of_nonneg_left (add_le_add (add_le_add (add_le_add hsqrtT hxT) hE') hcross3) hD
      _ = _ := by ring
  have hmix : |2*(crossIntegral x T).re| ≤ (2*X)*T := by
    rw [abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2)]
    exact (mul_le_mul_of_nonneg_left (primeCross_linear_bound hT hxp) (by norm_num)).trans_eq
      (by ring)
  have htotal : |2*Real.pi*(actualComplexPairSum T (Real.log x)).re-
      T*(L^2/x^2+Real.log x)| ≤ K*T := by
    have hh := (abs_add_le (thirdSignalResidual T x) (logSignalEnergy T x-T*L^2/x^2)).trans
      (add_le_add hthird' herr₁)
    have hh' := (abs_add_le _ (primeSignalEnergy T x-T*Real.log x)).trans (add_le_add hh herr₂)
    have hh'' := (abs_add_le _ (2*(crossIntegral x T).re)).trans (add_le_add hh' hmix)
    calc
      _ = |thirdSignalResidual T x+(logSignalEnergy T x-T*L^2/x^2)+
          (primeSignalEnergy T x-T*Real.log x)+2*(crossIntegral x T).re| := by
        apply congrArg abs
        dsimp only [thirdSignalResidual]
        ring
      _ ≤ _ := hh''.trans_eq (by dsimp only [K]; ring)
  have hiden := sharpFormFactor_sub_main_eq_pair_remainder T α hT1
  change sharpFormFactor T α-(Real.exp (-2*u)*L+α) =
    ((actualComplexPairSum T (Real.log x)).re-T/(2*Real.pi)*(L^2/x^2+Real.log x))/
      (T*L/(2*Real.pi)) at hiden
  have hsp : Real.exp (-2*u)*L = Real.exp (-c) := transition_spike c T hT1
  rw [hsp] at hiden
  rw [hiden,show ((actualComplexPairSum T (Real.log x)).re-T/(2*Real.pi)*(L^2/x^2+Real.log x))/
    (T*L/(2*Real.pi)) = (2*Real.pi*(actualComplexPairSum T (Real.log x)).re-
      T*(L^2/x^2+Real.log x))/(T*L) by field_simp [Real.pi_ne_zero,hTpos.ne',hL.ne'],
    abs_div,abs_of_pos (mul_pos hTpos hL)]
  exact (div_le_div_of_nonneg_right htotal (by positivity)).trans_eq
    (show K*T/(T*L)=K/L by field_simp [hTpos.ne',hL.ne'])

/-- The published global prime mean-square estimate specializes to the
quadratic budget used by the narrow proof. -/
theorem sharpTransitionSecondOrder_of_component_bounds
    (hthird : PositiveCutoffThirdSignalSource) (hprime : PrimeSignalMeanSquareSource) :
    SharpTransitionSecondOrder :=
  sharpTransitionSecondOrder_of_quadratic_components hthird
    (quadraticPrimeSignalMeanSquare_of_published hprime)

end RiemannResearch.Analysis.MontgomeryHorizontalBessel
