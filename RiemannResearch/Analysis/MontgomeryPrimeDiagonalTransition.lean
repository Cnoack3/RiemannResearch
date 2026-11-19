import RiemannResearch.Analysis.MontgomeryInfiniteDirichletMeanSquare
import RiemannResearch.Analysis.MontgomeryCenteredTransition
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! # The actual prime diagonal in the narrow Montgomery transition

The ordinary infinite positive log-frequency mean square follows from the
repository's Montgomery–Vaughan inequality. The remaining input on the
prime side is the prime number theorem for a scalar von Mangoldt diagonal. -/

noncomputable section
open Filter Set MeasureTheory
open scoped Topology ArithmeticFunction
namespace RiemannResearch.Analysis.MontgomeryHorizontalBessel
open MontgomeryPrimeCrossIntegral MontgomeryHorizontalTransfer ZeroOrdinate

def primeDiagonal (x : ℝ) : ℝ := ∑' n : ℕ, (primeWeight x n)^2

/-- The quantitative prime number theorem for the weighted von Mangoldt
diagonal yields a bounded uniform difference from log x on x≥2. -/
def PrimeDiagonalBound : Prop := ∃ J : ℝ, 0 ≤ J ∧ ∀ x : ℝ, 2 ≤ x →
  |primeDiagonal x-Real.log x| ≤ J

/-- One further term of partial summation of Λ² gives a vanishing error. -/
def PrimeDiagonalAsymptotic : Prop := Tendsto (fun x : ℝ => primeDiagonal x-Real.log x) atTop (𝓝 0)

/-- Garunkštis–Paliulionytė, Lemmas 2.3–2.4 and the arithmetic estimate
immediately before (2.28). Their integer mean-value inequality and
prime-power spacing estimate apply to the untwisted coefficients. -/
def PrimePowerSpacingMeanSquareSource : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ T x : ℝ, 0 ≤ T → 2 ≤ x →
    |primeSignalEnergy T x-T*primeDiagonal x| ≤ C*x*Real.log (Real.log (4*x))

/-- The prime-power spacing error is stronger than x log(2x) throughout
the range x≥2 of the published prime-side component. -/
theorem primeSignalMeanSquare_of_primePowerSpacing
    (hspacing : PrimePowerSpacingMeanSquareSource) (hdiag : PrimeDiagonalBound) :
    PrimeSignalMeanSquareSource := by
  obtain ⟨C,hC,hs⟩ := hspacing
  obtain ⟨J,hJ,hd⟩ := hdiag
  let K := max C J
  have hK : 0 ≤ K := hC.trans (le_max_left _ _)
  refine ⟨K,hK,?_⟩
  filter_upwards [eventually_ge_atTop (0:ℝ)] with T hT
  intro x hx
  have hxp : 0 < x := by linarith [hx.1]
  have h4x : 1 < 4*x := by linarith [hx.1]
  have h2x : 1 ≤ 2*x := by linarith [hx.1]
  have hlog4x : Real.log (4*x) ≤ 2*x := by
    rw [Real.log_mul (by norm_num : (4:ℝ) ≠ 0) hxp.ne']
    linarith only [Real.log_le_sub_one_of_pos (by norm_num : (0:ℝ)<4),
      Real.log_le_sub_one_of_pos hxp,hx.1]
  have hcost : |primeSignalEnergy T x-T*primeDiagonal x| ≤ K*(x*Real.log (2*x)) := by
    apply (hs T x hT hx.1).trans
    have he := Real.log_le_log (Real.log_pos h4x) hlog4x
    calc
      _ ≤ C*x*Real.log (2*x) := mul_le_mul_of_nonneg_left he (mul_nonneg hC hxp.le)
      _ ≤ K*(x*Real.log (2*x)) := by
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_right (le_max_left _ _) (mul_nonneg hxp.le (Real.log_nonneg h2x))
  have hdiag' : |T*primeDiagonal x-T*Real.log x| ≤ K*T := by
    rw [← mul_sub,abs_mul,abs_of_nonneg hT,mul_comm K T]
    exact mul_le_mul_of_nonneg_left ((hd x hx.1).trans (le_max_right _ _)) hT
  exact (abs_sub_le _ _ _).trans ((add_le_add hcost hdiag').trans_eq (by ring))

private theorem mangoldtThreeHalves_nonneg (n : ℕ) : 0 ≤ mangoldtThreeHalves n :=
  div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _)

theorem n_mul_mangoldtThreeHalves_le_two_div_exp (n : ℕ) :
    (n : ℝ)*mangoldtThreeHalves n ≤ 2/Real.exp 1 := by
  rcases eq_or_ne n 0 with rfl | hn
  · norm_num [mangoldtThreeHalves] <;> positivity
  have hn0 : 0 < (n:ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hn
  have hs : 0 < Real.sqrt n := Real.sqrt_pos.mpr hn0
  have hp : (n : ℝ)^(3/2 : ℝ) = Real.sqrt n*n := by
    rw [show (3/2 : ℝ)=1/2+1 by norm_num,Real.rpow_add hn0,Real.rpow_one,← Real.sqrt_eq_rpow]
  have hlog : Real.log n = 2*Real.log (Real.sqrt n) := by
    have he := Real.log_pow (Real.sqrt n) 2
    rw [Real.sq_sqrt hn0.le] at he
    simpa using he
  calc
    _ = Λ n/Real.sqrt n := by rw [mangoldtThreeHalves,hp]; field_simp [hn0.ne',hs.ne'] <;> ring
    _ ≤ 2/Real.exp 1 := by
      apply (div_le_iff₀ hs).2
      apply ArithmeticFunction.vonMangoldt_le_log.trans
      have hE := Real.exp_pos 1
      have h := Real.log_le_sub_one_of_pos (div_pos hs hE)
      rw [Real.log_div hs.ne' hE.ne',Real.log_exp] at h
      rw [hlog]
      calc
        _ ≤ 2*(Real.sqrt n/Real.exp 1) := by linarith only [h]
        _ = _ := by ring

private theorem weighted_primeWeight_le {x : ℝ} (hx : 0 < x) (n : ℕ) :
    (n:ℝ)*(primeWeight x n)^2 ≤ ((2/Real.exp 1)*x^2)*mangoldtThreeHalves n := by
  have hm := mangoldtThreeHalves_nonneg n
  calc
    _ ≤ (n:ℝ)*(x*mangoldtThreeHalves n)^2 := mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (primeWeight_nonneg hx n) (primeWeight_le_mangoldtThreeHalves hx n) 2)
      (Nat.cast_nonneg n)
    _ = (x^2*mangoldtThreeHalves n)*((n:ℝ)*mangoldtThreeHalves n) := by ring
    _ ≤ (x^2*mangoldtThreeHalves n)*(2/Real.exp 1) := mul_le_mul_of_nonneg_left
      (n_mul_mangoldtThreeHalves_le_two_div_exp n) (mul_nonneg (sq_nonneg _) hm)
    _ = _ := by ring

private theorem square_primeWeight_le {x : ℝ} (hx : 0 < x) (n : ℕ) :
    (primeWeight x n)^2 ≤ ((2/Real.exp 1)*x^2)*mangoldtThreeHalves n := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp [primeWeight,mangoldtThreeHalves]
  have hp : (1 : ℝ) ≤ n := by exact_mod_cast Nat.pos_of_ne_zero hn
  exact (le_mul_of_one_le_left (sq_nonneg _) hp).trans (weighted_primeWeight_le hx n)

theorem primeDiagonal_le_quadratic {x : ℝ} (hx : 0 < x) :
    primeDiagonal x ≤ ((2/Real.exp 1)*x^2)*∑' n : ℕ, mangoldtThreeHalves n := by
  have hm := summable_mangoldtThreeHalves.mul_left ((2/Real.exp 1)*x^2)
  have hs := Summable.of_nonneg_of_le (fun n => sq_nonneg _) (square_primeWeight_le hx) hm
  exact (hs.tsum_le_tsum (square_primeWeight_le hx) hm).trans_eq tsum_mul_left

/-- The stronger prime-diagonal limit also gives the bounded estimate
at every real cutoff x≥2, including prime-power endpoints. -/
theorem primeDiagonalBound_of_asymptotic (h : PrimeDiagonalAsymptotic) : PrimeDiagonalBound := by
  obtain ⟨x₀,h0⟩ := eventually_atTop.1 ((Metric.tendsto_nhds.mp h) 1 zero_lt_one)
  let X := max 2 x₀
  let S := ∑' n : ℕ, mangoldtThreeHalves n
  have hX : 2 ≤ X := le_max_left _ _
  have hS : 0 ≤ S := tsum_nonneg mangoldtThreeHalves_nonneg
  have hlX : 0 ≤ Real.log X := Real.log_nonneg (by linarith)
  refine ⟨(2/Real.exp 1)*X^2*S+Real.log X+1,by positivity,?_⟩
  intro x hx
  by_cases hlarge : x₀ ≤ x
  · have he : |primeDiagonal x-Real.log x| < 1 := by
      simpa only [Real.dist_eq,sub_zero] using h0 x hlarge
    exact he.le.trans (by linarith [mul_nonneg (show 0 ≤ (2/Real.exp 1)*X^2 by positivity) hS])
  have hxX : x ≤ X := (le_of_lt (lt_of_not_ge hlarge)).trans (le_max_right 2 x₀)
  have hxp : 0 < x := by linarith
  have hlx : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
  have hd₀ : 0 ≤ primeDiagonal x := tsum_nonneg fun n => sq_nonneg _
  have hdX : primeDiagonal x ≤ (2/Real.exp 1)*X^2*S := (primeDiagonal_le_quadratic hxp).trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hxp.le hxX 2)
      (by positivity)) hS)
  apply abs_le.mpr
  constructor <;> linarith [Real.log_le_log hxp hxX]

set_option maxHeartbeats 600000 in
/-- The off-diagonal part of the actual infinite prime signal costs
O(x²) uniformly in T. This is o(T) at every bounded transition shift. -/
theorem primeMeanSquare_error_le_quadratic {x T : ℝ} (hx : 0 < x) (hT : 0 ≤ T) :
    |primeSignalEnergy T x-T*primeDiagonal x| ≤
      ((78/Real.exp 1)*∑' n : ℕ, mangoldtThreeHalves n)*x^2 := by
  let a := fun n : ℕ => (primeWeight x n : ℂ)
  have hn (n : ℕ) : ‖a n‖ = primeWeight x n := by
    simp [a,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (primeWeight_nonneg hx n)]
  have ha : Summable (fun n => ‖a n‖) := by
    apply Summable.of_nonneg_of_le (fun n => norm_nonneg _) _ (summable_mangoldtThreeHalves.mul_left x)
    intro n
    simpa only [hn] using primeWeight_le_mangoldtThreeHalves hx n
  have hw : Summable (fun n : ℕ => (n:ℝ)*‖a n‖^2) := by
    apply Summable.of_nonneg_of_le (fun n => by positivity) _
      (summable_mangoldtThreeHalves.mul_left ((2/Real.exp 1)*x^2))
    intro n
    simpa only [hn] using weighted_primeWeight_le hx n
  have h := DirichletMeanSquare.infinite_log_mean_square_le
    (fun n : ℕ => a (n+1)) ((summable_nat_add_iff 1).mpr ha)
    ((summable_nat_add_iff 1).mpr hw) hT
  have ha0 : a 0 = 0 := by simp [a,primeWeight]
  have hsum (t : ℝ) : (∑' n : ℕ, a (n+1)*phase (Real.log (n+1:ℕ)) t) =
      ∑' n : ℕ, a n*phase (Real.log n) t := by
    have hsum : Summable (fun n : ℕ => a n*phase (Real.log n) t) :=
      summable_norm_iff.mp (ha.congr fun n => by simp [norm_mul,phase_norm])
    simpa only [ha0,zero_mul,zero_add] using
      (hsum.tsum_eq_zero_add (f := fun n : ℕ => a n*phase (Real.log n) t)).symm
  have hdiag : Summable (fun n : ℕ => ‖a n‖^2) := by
    apply Summable.of_nonneg_of_le (fun n => sq_nonneg _) _ hw
    intro n
    rcases eq_or_ne n 0 with rfl | hn0
    · simp [ha0]
    · exact le_mul_of_one_le_left (sq_nonneg _) (by exact_mod_cast Nat.pos_of_ne_zero hn0)
  have hd : (∑' n : ℕ, ‖a (n+1)‖^2) = primeDiagonal x := by
    have he := hdiag.tsum_eq_zero_add
    simpa only [ha0,norm_zero,zero_pow (by norm_num : (2:ℕ) ≠ 0),zero_add,hn,primeDiagonal]
      using he.symm
  have hwm : (∑' n : ℕ, ((n+1:ℕ):ℝ)*‖a (n+1)‖^2) ≤
      ((2/Real.exp 1)*x^2)*∑' n : ℕ, mangoldtThreeHalves n := by
    have he := hw.tsum_eq_zero_add
    simp only [Nat.cast_zero,zero_mul,zero_add] at he
    rw [← he,← tsum_mul_left]
    apply hw.tsum_le_tsum _ (summable_mangoldtThreeHalves.mul_left ((2/Real.exp 1)*x^2))
    intro n
    simpa only [hn] using weighted_primeWeight_le hx n
  simp_rw [hsum,hd] at h
  exact h.trans ((mul_le_mul_of_nonneg_left hwm (by norm_num)).trans_eq (by ring))

/-- The uniform transition at second order requires only the prime diagonal
estimate and the positive-cutoff third signal on the analytic side. -/
theorem quadraticPrimeSignalMeanSquare_of_diagonal (hdiag : PrimeDiagonalBound) :
    QuadraticPrimeSignalMeanSquareSource := by
  obtain ⟨J,hJ,hj⟩ := hdiag
  let B := (78/Real.exp 1)*∑' n : ℕ, mangoldtThreeHalves n
  have hB : 0 ≤ B := mul_nonneg (by positivity) (tsum_nonneg mangoldtThreeHalves_nonneg)
  refine ⟨max J B,hJ.trans (le_max_left J B),?_⟩
  filter_upwards [eventually_ge_atTop (0:ℝ)] with T hT
  intro x hx
  have hxp : 0 < x := by linarith [hx.1]
  have h := primeMeanSquare_error_le_quadratic hxp hT
  have h' : |T*primeDiagonal x-T*Real.log x| ≤ T*J := by
    rw [← mul_sub,abs_mul,abs_of_nonneg hT]
    exact mul_le_mul_of_nonneg_left (hj x hx.1) hT
  apply (abs_sub_le _ _ _).trans
  apply (add_le_add h h').trans
  have hb := mul_le_mul_of_nonneg_right (le_max_right J B) (sq_nonneg x)
  have hh := mul_le_mul_of_nonneg_left (le_max_left J B) hT
  linarith only [hb,hh]

theorem sharpTransitionSecondOrder_of_diagonal
    (hcut : PositiveCutoffThirdSignalSource) (hdiag : PrimeDiagonalBound) :
    SharpTransitionSecondOrder := sharpTransitionSecondOrder_of_quadratic_components hcut
      (quadraticPrimeSignalMeanSquare_of_diagonal hdiag)

/-- The actual mean square has a uniform vanishing remainder after dividing
by T on the transition, assuming only the scalar prime-diagonal PNT. -/
theorem narrowPrimeMeanSquareRemainder_of_diagonal (hdiag : PrimeDiagonalAsymptotic) :
    NarrowPrimeMeanSquareRemainder := by
  intro A ε hε
  let η := ε/2
  have hη : 0 < η := by dsimp [η]; positivity
  obtain ⟨x₀,h0⟩ := eventually_atTop.1 ((Metric.tendsto_nhds.mp hdiag) η hη)
  let X := max 2 x₀
  let B := Real.exp |A|
  let S := (78/Real.exp 1)*∑' n : ℕ, mangoldtThreeHalves n
  have hX : 0 < X := by exact (by norm_num : (0:ℝ)<2).trans_le (le_max_left _ _)
  have hB : 0 < B := Real.exp_pos _
  have hS : 0 ≤ S := mul_nonneg (by positivity) (tsum_nonneg mangoldtThreeHalves_nonneg)
  have hLT : Tendsto (fun T : ℝ => Real.log T/T) atTop (𝓝 0) := by
    have he := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).comp Real.tendsto_log_atTop
    apply he.congr'
    filter_upwards [eventually_gt_atTop (0:ℝ)] with T hT
    simp only [Function.comp_def,pow_one,Real.exp_neg,Real.exp_log hT,div_eq_mul_inv]
  have hSB := (tendsto_const_nhds (x := S*B)).mul hLT
  simp only [mul_zero] at hSB
  filter_upwards [hSB.eventually_le_const hη,eventually_gt_atTop (1:ℝ),
    (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).eventually_ge_atTop
      (2*Real.log X+|A|)] with T hsmall hT hℓ
  intro c hc
  let L := Real.log T
  let α := transitionFrequency c T
  let u := α*L
  let x := Real.exp u
  have hTp : 0 < T := zero_lt_one.trans hT
  have hL : 0 < L := Real.log_pos hT
  have hxp : 0 < x := Real.exp_pos _
  have hu : u = (Real.log L+c)/2 := div_mul_cancel₀ _ hL.ne'
  have hxX : X ≤ x := by
    rw [← Real.exp_log hX]
    apply Real.exp_le_exp.mpr
    rw [hu]
    change 2*Real.log X+|A| ≤ Real.log L at hℓ
    linarith only [hℓ,(abs_le.mp hc).1,le_abs_self A]
  have hxSq : x^2 ≤ B*L := by
    dsimp only [x]
    rw [pow_two,← Real.exp_add,hu,show (Real.log L+c)/2+(Real.log L+c)/2=Real.log L+c by ring,
      Real.exp_add,Real.exp_log hL,mul_comm B L]
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ((abs_le.mp hc).2.trans (le_abs_self A))) hL.le
  have herr : |primeSignalEnergy T x-T*primeDiagonal x| ≤ η*T := by
    apply (primeMeanSquare_error_le_quadratic hxp hTp.le).trans
    apply (mul_le_mul_of_nonneg_left hxSq hS).trans
    change (S*B)*(L/T) ≤ η at hsmall
    calc
      S*(B*L) = ((S*B)*(L/T))*T := by field_simp [hTp.ne'] <;> ring
      _ ≤ η*T := mul_le_mul_of_nonneg_right hsmall hTp.le
  have hd : |primeDiagonal x-Real.log x| ≤ η := by
    simpa only [Real.dist_eq,sub_zero] using (h0 x ((le_max_right 2 x₀).trans hxX)).le
  have hd' : |T*primeDiagonal x-T*Real.log x| ≤ T*η := by
    rw [← mul_sub,abs_mul,abs_of_pos hTp]
    exact mul_le_mul_of_nonneg_left hd hTp.le
  exact (abs_sub_le _ _ _).trans ((add_le_add herr hd').trans_eq (by dsimp [η]; ring))

end RiemannResearch.Analysis.MontgomeryHorizontalBessel
