import RiemannResearch.Analysis.DirichletMeanSquare
import RiemannResearch.Analysis.MontgomeryPrimeCrossIntegral
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! # The opposite-frequency prime cross term

After conjugation, the prime signal and the reflected logarithmic derivative
from the centered explicit formula have frequencies of the same sign. Their
product has no zero frequency, even when the two prime powers coincide. -/

noncomputable section
open Set MeasureTheory
open scoped Topology
namespace RiemannResearch.Analysis.MontgomeryPrimeCrossIntegral
open ZeroOrdinate DirichletMeanSquare

/-- Absolutely summable Fourier series supported away from frequency zero have
a bounded integral, uniform in the height. -/
theorem norm_integral_frequency_series_le {ι : Type*} [Countable ι] (a : ι → ℂ)
    (ω : ι → ℝ) (ha : Summable fun i => ‖a i‖) {δ T : ℝ} (hδ : 0 < δ) (hT : 0 ≤ T)
    (hω : ∀ i, a i ≠ 0 → δ ≤ |ω i|) :
    ‖∫ t in (0:ℝ)..T, ∑' i, a i*phase (ω i) t‖ ≤ (2/δ)*∑' i, ‖a i‖ := by
  let term := fun i t => a i*phase (ω i) t
  have hint (i : ι) : IntegrableOn (term i) (Ioc 0 T) := by
    apply (intervalIntegrable_iff_integrableOn_Ioc_of_le hT).mp
    apply Continuous.intervalIntegrable
    dsimp [term,phase]
    fun_prop
  have hnorm (i : ι) : (∫ t in Ioc (0:ℝ) T, ‖term i t‖) =
      ‖a i‖*(∫ _t in Ioc (0:ℝ) T, (1:ℝ)) := by
    simp only [term,norm_mul,phase_norm,mul_one]
    rw [← integral_const_mul]
    simp
  have hsum : Summable (fun i => ∫ t in Ioc (0:ℝ) T, ‖term i t‖) := by
    simp only [hnorm]
    exact ha.mul_right _
  have hswap : (∫ t in Ioc (0:ℝ) T, ∑' i, term i t) =
      ∑' i, ∫ t in Ioc (0:ℝ) T, term i t :=
    (integral_tsum_of_summable_integral_norm hint hsum).symm
  have hi (i : ι) : (∫ t in Ioc (0:ℝ) T, term i t) = a i*finitePhaseKernel 0 T (ω i) := by
    rw [← integral_phase,intervalIntegral.integral_of_le hT]
    exact integral_const_mul _ _
  have hmajor (i : ι) : ‖a i*finitePhaseKernel 0 T (ω i)‖ ≤ (2/δ)*‖a i‖ := by
    by_cases hz : a i=0
    · simp [hz]
    · have hw := hω i hz
      rw [norm_mul,mul_comm (2/δ) _]
      apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
      exact (norm_finitePhaseKernel_le (abs_pos.mp (hδ.trans_le hw)) 0 T).trans
        (div_le_div_of_nonneg_left (by norm_num) hδ hw)
  have hm := ha.mul_left (2/δ)
  have hs := Summable.of_nonneg_of_le (fun i => norm_nonneg _) hmajor hm
  change ‖∫ t in (0:ℝ)..T, ∑' i, term i t‖ ≤ _
  rw [intervalIntegral.integral_of_le hT,hswap]
  simp_rw [hi]
  exact (norm_tsum_le_tsum_norm hs).trans ((hs.tsum_le_tsum hmajor hm).trans_eq tsum_mul_left)

/-- Two positive-frequency signals gain an absolute divisor from the sum of their
frequencies when multiplied without further conjugation. -/
theorem norm_integral_same_sign_product_le {ι κ : Type*} [Countable ι] [Countable κ]
    (a : ι → ℂ) (b : κ → ℂ) (ω : ι → ℝ) (v : κ → ℝ)
    (ha : Summable fun i => ‖a i‖) (hb : Summable fun j => ‖b j‖)
    {δ η T : ℝ} (hδη : 0 < δ+η) (hT : 0 ≤ T)
    (hw : ∀ i, a i ≠ 0 → δ ≤ ω i) (hv : ∀ j, b j ≠ 0 → η ≤ v j) :
    ‖∫ t in (0:ℝ)..T, (∑' i, a i*phase (ω i) t)*(∑' j, b j*phase (v j) t)‖ ≤
      (2/(δ+η))*(∑' i, ‖a i‖)*(∑' j, ‖b j‖) := by
  let ab := fun ij : ι × κ => a ij.1*b ij.2
  let Ω := fun ij : ι × κ => ω ij.1+v ij.2
  have hn : Summable (fun ij : ι × κ => ‖ab ij‖) := by
    exact ha.mul_norm hb
  have hsum (t : ℝ) :
      (∑' i, a i*phase (ω i) t)*(∑' j, b j*phase (v j) t) =
        ∑' ij : ι × κ, ab ij*phase (Ω ij) t := by
    have h₁ : Summable fun i => ‖a i*phase (ω i) t‖ := by simpa using ha
    have h₂ : Summable fun j => ‖b j*phase (v j) t‖ := by simpa using hb
    rw [tsum_mul_tsum_of_summable_norm h₁ h₂]
    apply tsum_congr
    intro ij
    dsimp only [ab,Ω]
    rw [phase_add]
    ring
  simp_rw [hsum]
  have hf (ij : ι × κ) (hnz : ab ij ≠ 0) : δ+η ≤ |Ω ij| := by
    have hno : a ij.1 ≠ 0 ∧ b ij.2 ≠ 0 := mul_ne_zero_iff.mp hnz
    exact (add_le_add (hw ij.1 hno.1) (hv ij.2 hno.2)).trans (le_abs_self _)
  apply (norm_integral_frequency_series_le ab Ω hn hδη hT hf).trans_eq
  have he := tsum_mul_tsum_of_summable_norm (f := fun i => ‖a i‖) (g := fun j => ‖b j‖)
    (by simpa using ha) (by simpa using hb)
  simp only [ab,norm_mul]
  rw [← he]
  ring

/-- Conjugating the two real-coefficient explicit-formula signals gives this
same-sign product. Its norm is independent of the choice of the common sign. -/
def reflectedPrimeCrossIntegral (x T : ℝ) : ℂ :=
  ∫ t in (0:ℝ)..T,
    (∑' n : ℕ, ((primeWeight x n / x : ℝ) : ℂ)*phase (Real.log n) t)*
    (∑' m : ℕ, (mangoldtThreeHalves m : ℂ)*phase (Real.log m) t)

/-- The actual crossed Dirichlet signals have a height-independent bound
because every surviving product frequency is at least log 4. -/
theorem norm_reflectedPrimeCrossIntegral_le {x T : ℝ} (hx : 0 < x) (hT : 0 ≤ T) :
    ‖reflectedPrimeCrossIntegral x T‖ ≤
      (2/Real.log 4)*(∑' n : ℕ, mangoldtThreeHalves n)^2 := by
  let a := fun n : ℕ => ((primeWeight x n/x:ℝ):ℂ)
  let b := fun n : ℕ => (mangoldtThreeHalves n : ℂ)
  have hq (n : ℕ) : 0 ≤ mangoldtThreeHalves n := div_nonneg ArithmeticFunction.vonMangoldt_nonneg
    (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  have hmajor (n : ℕ) : ‖a n‖ ≤ mangoldtThreeHalves n := by
    simp only [a,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (div_nonneg (primeWeight_nonneg hx n) hx.le)]
    exact (div_le_iff₀ hx).2 (by simpa only [mul_comm] using primeWeight_le_mangoldtThreeHalves hx n)
  have hn (n : ℕ) : ‖b n‖ = mangoldtThreeHalves n := by
    simp only [b,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (hq n)]
  have ha := Summable.of_nonneg_of_le (fun n => norm_nonneg _) hmajor summable_mangoldtThreeHalves
  have hb : Summable (fun n => ‖b n‖) := by simpa only [hn] using summable_mangoldtThreeHalves
  have hf {n : ℕ} (h : 2 ≤ n) : Real.log 2 ≤ Real.log n :=
    Real.log_le_log (by norm_num) (by exact_mod_cast h)
  have haω (n : ℕ) (h : a n ≠ 0) : Real.log 2 ≤ Real.log n := by
    by_cases h2 : 2 ≤ n
    · exact hf h2
    · have hz : n=0 ∨ n=1 := by omega
      rcases hz with rfl | rfl <;> simp [a,primeWeight] at h
  have hbω (n : ℕ) (h : b n ≠ 0) : Real.log 2 ≤ Real.log n := by
    by_cases h2 : 2 ≤ n
    · exact hf h2
    · have hz : n=0 ∨ n=1 := by omega
      rcases hz with rfl | rfl <;> simp [b,mangoldtThreeHalves] at h
  have hlog : Real.log 2 + Real.log 2 = Real.log 4 := by
    rw [← Real.log_mul (by norm_num : (2:ℝ) ≠ 0) (by norm_num : (2:ℝ) ≠ 0)]
    norm_num
  have hp : 0 < Real.log 2+Real.log 2 := by rw [hlog]; exact Real.log_pos (by norm_num)
  have h := norm_integral_same_sign_product_le a b (fun n : ℕ => Real.log n)
    (fun n : ℕ => Real.log n) ha hb hp hT haω hbω
  rw [hlog] at h
  simp only [hn] at h
  apply h.trans
  rw [pow_two,← mul_assoc]
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
    (ha.tsum_le_tsum hmajor summable_mangoldtThreeHalves) (by positivity)) (tsum_nonneg hq)

end RiemannResearch.Analysis.MontgomeryPrimeCrossIntegral
