/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.FiniteQuadraticCoshCorrection
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Exact asymptotic Frobenius coefficient for integer log frequencies

The normalized power sums for every real exponent p > −1 are evaluated
by upper and lower integral comparison. For |a| < 1/2 the limit of the
normalized Frobenius square of the horizontal cosine correction equals
6a⁴/((1−4a²)(1−a²)). The estimate applies uniformly to all smaller
displacements by quadratic scaling. It supplies a sharp bound for this
Frobenius calculation and an upper bound for the operator norm.
-/

noncomputable section
open Filter Set MeasureTheory Complex
open scoped BigOperators Topology
namespace RiemannResearch.Analysis.ActualZeroPhaseMoments
open HorizontalEuclideanMoments HorizontalPhaseBootstrap FiniteHyperbolicHarmonicCap ZeroOrdinate

private def integerPowerSum (d : ℕ) (p : ℝ) : ℝ :=
  ∑ i ∈ Finset.range d, (1 + (i : ℝ))^p

private theorem integerFrequencySum_eq_powerSum (d : ℕ) (p : ℝ) :
    finiteExponentialSum (integerLogFrequency d) p = integerPowerSum d p := by
  unfold integerPowerSum
  rw [Finset.sum_range]
  apply Finset.sum_congr rfl
  intro i _
  rw [Real.rpow_def_of_pos (show 0 < 1+(i.val:ℝ) by positivity)]
  simp only [integerLogFrequency,Nat.cast_add,Nat.cast_one,add_comm (1:ℝ),mul_comm]

private theorem integerPowerSum_integral_error (d : ℕ) {p : ℝ} (hp : -1 < p) :
    |integerPowerSum d p - (((1+(d:ℝ))^(p+1)-1)/(p+1))| ≤ 1+(1+(d:ℝ))^p := by
  let f := fun x : ℝ => x^p
  let I := (((1+(d:ℝ))^(p+1)-1)/(p+1))
  let S := integerPowerSum d p
  let U := ∑ i ∈ Finset.range d, f (1+((i+1:ℕ):ℝ))
  have hI : (∫ x in (1:ℝ)..1+(d:ℝ), f x) = I := by
    dsimp [f,I]
    rw [integral_rpow (Or.inl hp), Real.one_rpow]
  have hUS : U-S = (1+(d:ℝ))^p-1 := by
    have h := Finset.sum_range_sub (fun n : ℕ => (1+(n:ℝ))^p) d
    rw [Finset.sum_sub_distrib] at h
    simpa only [U,S,f,integerPowerSum,Nat.cast_zero,add_zero,Real.one_rpow] using h
  have hpos : 0 ≤ (1+(d:ℝ))^p := Real.rpow_nonneg (by positivity) _
  change |S-I| ≤ _
  rw [abs_le]
  by_cases hs : 0 ≤ p
  · have hm : MonotoneOn f (Icc (1:ℝ) (1+(d:ℝ))) := by
      intro x hx y _ hxy
      exact Real.rpow_le_rpow (zero_le_one.trans hx.1) hxy hs
    have h₁ : S ≤ I := hI ▸ hm.sum_le_integral
    have h₂ : I ≤ U := hI ▸ hm.integral_le_sum
    constructor <;> linarith only [h₁,h₂,hUS,hpos]
  · have hm : AntitoneOn f (Icc (1:ℝ) (1+(d:ℝ))) := by
      intro x hx y _ hxy
      exact Real.rpow_le_rpow_of_nonpos (zero_lt_one.trans_le hx.1) hxy (le_of_lt (lt_of_not_ge hs))
    have h₁ : U ≤ I := hI ▸ hm.sum_le_integral
    have h₂ : I ≤ S := hI ▸ hm.integral_le_sum
    constructor <;> linarith only [h₁,h₂,hUS,hpos]

/-- The two cases p ≥ 0 and −1 < p < 0 have one common normalized limit. -/
theorem integerFrequencySum_normalized_tendsto {p : ℝ} (hp : -1 < p) :
    Tendsto (fun d : ℕ => finiteExponentialSum (integerLogFrequency d) p / (1+(d:ℝ))^(p+1))
      atTop (𝓝 (1/(p+1))) := by
  have hq : 0 < p+1 := by linarith only [hp]
  have hx : Tendsto (fun d : ℕ => 1+(d:ℝ)) atTop atTop :=
    tendsto_atTop_add_const_left _ _ tendsto_natCast_atTop_atTop
  have hden := (tendsto_rpow_atTop hq).comp hx
  have hsmall := (hden.const_div_atTop (1+1/(p+1))).add (hx.const_div_atTop 1)
  simp only [Function.comp_apply,add_zero] at hsmall
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero (fun _ => norm_nonneg _) _ hsmall
  intro d
  let X := 1+(d:ℝ)
  let D := X^(p+1)
  let S := integerPowerSum d p
  have hX : 0 < X := by dsimp [X]; positivity
  have hD : 0 < D := Real.rpow_pos_of_pos hX _
  have hXpow : X^p/D=1/X := by
    dsimp [D]; rw [Real.rpow_add hX,Real.rpow_one]; field_simp [(Real.rpow_pos_of_pos hX p).ne']
  have h := integerPowerSum_integral_error d hp
  change |S-(D-1)/(p+1)| ≤ 1+X^p at h
  have heq : S/D-1/(p+1)=(S-(D-1)/(p+1)-1/(p+1))/D := by field_simp [hq.ne',hD.ne'] <;> ring
  rw [integerFrequencySum_eq_powerSum, Real.norm_eq_abs]
  change |S/D-1/(p+1)| ≤ (1+1/(p+1))/D + 1/X
  rw [heq,abs_div,abs_of_pos hD]
  apply (div_le_div_of_nonneg_right (abs_sub _ _) hD.le).trans
  rw [abs_of_nonneg (show 0≤1/(p+1) by positivity)]
  apply (div_le_div_of_nonneg_right (add_le_add_left h (1/(p+1))) hD.le).trans_eq
  rw [← hXpow]
  ring

theorem integerExponentialProduct_normalized_tendsto {p : ℝ} (hp : |p| < 1) :
    Tendsto (fun d : ℕ => finiteExponentialSum (integerLogFrequency d) p *
        finiteExponentialSum (integerLogFrequency d) (-p) / (1+(d:ℝ))^2)
      atTop (𝓝 (1/(1-p^2))) := by
  have h := (integerFrequencySum_normalized_tendsto (abs_lt.mp hp).1).mul
    (integerFrequencySum_normalized_tendsto (show -1 < -p by linarith only [(abs_lt.mp hp).2]))
  have hc : (1/(p+1))*(1/(-p+1))=1/(1-p^2) := by
    rw [div_mul_div_comm,one_mul,show (p+1)*(-p+1)=1-p^2 by ring]
  rw [hc] at h
  apply h.congr'
  filter_upwards with d
  have hX : 0 < 1+(d:ℝ) := by positivity
  rw [div_mul_div_comm,← Real.rpow_add hX,show p+1+(-p+1)=(2:ℝ) by ring, Real.rpow_ofNat]

/-- The endpoint constant is an equality for the Frobenius square. -/
theorem integerCoshFrobeniusSquare_normalized_tendsto {a : ℝ} (ha : |a| < 1/2) :
    Tendsto (fun d : ℕ => coshFrobeniusSquare (integerLogFrequency d) a / (1+(d:ℝ))^2) atTop
      (𝓝 (6*a^4/((1-4*a^2)*(1-a^2)))) := by
  have h2 : |2*a| < 1 := by rw [abs_mul,abs_of_pos (by norm_num : (0:ℝ)<2)]; linarith only [ha]
  have h1 := ha.trans (by norm_num : (1:ℝ)/2 < 1)
  have hx : Tendsto (fun d : ℕ => 1+(d:ℝ)) atTop atTop :=
    tendsto_atTop_add_const_left _ _ tendsto_natCast_atTop_atTop
  have hrat : Tendsto (fun d : ℕ => (d:ℝ)/(1+(d:ℝ))) atTop (𝓝 1) := by
    have h := (tendsto_const_nhds (x := (1:ℝ))).sub (hx.const_div_atTop 1)
    simp only [sub_zero] at h
    apply h.congr'
    filter_upwards with d
    field_simp
    ring
  have h := (((integerExponentialProduct_normalized_tendsto h2).sub
    ((integerExponentialProduct_normalized_tendsto h1).const_mul 4)).add ((hrat.pow 2).const_mul 3)).div_const 2
  have hn1 : 0 < 1-a^2 := sub_pos.mpr ((sq_lt_one_iff_abs_lt_one a).mpr h1)
  have hn2 : 0 < 1-(2*a)^2 := sub_pos.mpr ((sq_lt_one_iff_abs_lt_one (2*a)).mpr h2)
  have hc : (1/(1-(2*a)^2)-4*(1/(1-a^2))+3*1^2)/2 =
      6*a^4/((1-4*a^2)*(1-a^2)) := by
    have hn : 1-4*a^2≠0 := by rw [show 4*a^2=(2*a)^2 by ring]; exact hn2.ne'
    rw [show (2*a)^2=4*a^2 by ring]
    field_simp [hn1.ne',hn] <;> ring
  rw [hc] at h
  apply h.congr'
  filter_upwards with d
  have hf := coshFrobeniusSquare_eq (integerLogFrequency d) a
  change (_/(1+(d:ℝ))^2-4*(_/(1+(d:ℝ))^2)+3*((d:ℝ)/(1+(d:ℝ)))^2)/2 =
    coshFrobeniusSquare (integerLogFrequency d) a/(1+(d:ℝ))^2
  field_simp [show 1+(d:ℝ)≠0 by positivity]
  linarith only [hf]


private theorem coshFrobeniusSquare_nonneg {d : ℕ} (x : Fin d → ℝ) (a : ℝ) :
    0 ≤ coshFrobeniusSquare x a :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem copyCoshCorrection_norm_le_frobenius (d : ℕ) (ρ : ℂ) :
    ‖copyCoshCorrection d ρ‖ ≤ Real.sqrt (coshFrobeniusSquare (integerLogFrequency d) (ρ.re-1/2)) := by
  let A : Matrix (Fin d) (Fin d) ℂ := fun n m => phase (frequencyGap n m) ρ.im *
    ((Real.cosh ((ρ.re-1/2) * frequencyGap n m) : ℂ) - 1)
  apply euclideanCLM_norm_le_of_sq_sum A (Real.sqrt_nonneg _)
  rw [Real.sq_sqrt (coshFrobeniusSquare_nonneg _ _)]
  unfold coshFrobeniusSquare
  apply Finset.sum_le_sum
  intro n _
  apply Finset.sum_le_sum
  intro m _
  dsimp [A]
  rw [norm_mul,phase_norm,one_mul,← Complex.ofReal_one,← Complex.ofReal_sub,Complex.norm_real,
    Real.norm_eq_abs,abs_of_nonneg (sub_nonneg.mpr (Real.one_le_cosh _))]
  exact le_rfl

theorem copyCoshCorrection_norm_le_reference (d : ℕ) (ρ : ℂ) {η : ℝ}
    (hη : 0 < η) (hρ : |ρ.re-1/2| ≤ η) :
    ‖copyCoshCorrection d ρ‖ ≤ (|ρ.re-1/2|/η)^2 * Real.sqrt (coshFrobeniusSquare (integerLogFrequency d) η) := by
  let a := ρ.re-1/2
  let θ := |a|/η
  let x := integerLogFrequency d
  have hθ : 0 ≤ θ := div_nonneg (abs_nonneg _) hη.le
  have hθ1 : θ ≤ 1 := (div_le_one hη).mpr hρ
  have hf : coshFrobeniusSquare x a ≤ θ^4*coshFrobeniusSquare x η := by
    unfold coshFrobeniusSquare
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro n _
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro m _
    have h := cosh_sub_one_mul_le_quadratic (x := η*(x n-x m)) hθ hθ1
    have heq : θ*(η*(x n-x m))=|a| *(x n-x m) := by dsimp [θ]; field_simp [hη.ne']
    rw [heq] at h
    have h' : Real.cosh (a*(x n-x m))-1 ≤ θ^2*(Real.cosh (η*(x n-x m))-1) := by
      by_cases ha : 0 ≤ a
      · simpa only [abs_of_nonneg ha] using h
      · simpa only [abs_of_neg (lt_of_not_ge ha),neg_mul,Real.cosh_neg] using h
    exact (pow_le_pow_left₀ (sub_nonneg.mpr (Real.one_le_cosh _)) h' 2).trans_eq (by ring)
  apply (copyCoshCorrection_norm_le_frobenius d ρ).trans (Real.sqrt_le_sqrt hf |>.trans_eq ?_)
  rw [Real.sqrt_mul (show 0 ≤ θ^4 by positivity),show θ^4=(θ^2)^2 by ring,Real.sqrt_sq (sq_nonneg _)]

/-- Exact reference coefficient for the limiting Frobenius estimate. -/
def continuumQuadraticCoefficient (η : ℝ) := Real.sqrt (6/((1-4*η^2)*(1-η^2)))

theorem continuumQuadraticCoefficient_tendsto_zero :
    Tendsto continuumQuadraticCoefficient (𝓝 0) (𝓝 (Real.sqrt 6)) := by
  have h : ContinuousAt continuumQuadraticCoefficient 0 := by
    unfold continuumQuadraticCoefficient
    fun_prop (disch := norm_num)
  simpa only [continuumQuadraticCoefficient, zero_pow (by norm_num : (2:ℕ)≠0),mul_zero,
    sub_zero,one_mul,div_one] using h.tendsto

/-- A single threshold applies to every copy inside the chosen central
strip. The claimed coefficient is attached to the Frobenius estimate. -/
theorem eventually_copyCoshCorrection_le_reference {η : ℝ} (hη : 0 < η) (hη' : η < 1/2)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ d : ℕ in atTop, ∀ ρ : ℂ, |ρ.re-1/2| ≤ η →
      ‖copyCoshCorrection d ρ‖ ≤ (continuumQuadraticCoefficient η+ε)*(1+(d:ℝ))*(ρ.re-1/2)^2 := by
  let K := continuumQuadraticCoefficient η
  have ha : |η| < 1/2 := by rwa [abs_of_pos hη]
  have h := (Real.continuous_sqrt.tendsto _).comp (integerCoshFrobeniusSquare_normalized_tendsto ha)
  have heq : Real.sqrt (6*η^4/((1-4*η^2)*(1-η^2))) = η^2*K := by
    dsimp [K,continuumQuadraticCoefficient]
    rw [show 6*η^4/((1-4*η^2)*(1-η^2))=(η^2)^2*(6/((1-4*η^2)*(1-η^2))) by ring,
      Real.sqrt_mul (sq_nonneg _),Real.sqrt_sq (sq_nonneg _)]
  rw [heq] at h
  have hg : η^2*K < η^2*(K+ε) := by
    rw [mul_add]; exact lt_add_of_pos_right _ (mul_pos (sq_pos_of_pos hη) hε)
  filter_upwards [h.eventually (Iio_mem_nhds hg)] with d hd ρ hρ
  change Real.sqrt (coshFrobeniusSquare (integerLogFrequency d) η/(1+(d:ℝ))^2) < _ at hd
  have hx : 0 < 1+(d:ℝ) := by positivity
  rw [Real.sqrt_div (coshFrobeniusSquare_nonneg _ _),Real.sqrt_sq hx.le] at hd
  have hb := (div_lt_iff₀ hx).mp hd
  apply (copyCoshCorrection_norm_le_reference d ρ hη hρ).trans
  apply (mul_le_mul_of_nonneg_left hb.le (sq_nonneg _)).trans_eq
  rw [div_pow,sq_abs]
  dsimp [K]
  field_simp [hη.ne'] <;> ring

/-- Approaching the critical line at sufficiently large dimensions gives
every degree-linear quadratic Frobenius coefficient strictly above √6. -/
theorem exists_shrinking_copyCoshCorrection_coefficient {C : ℝ} (hC : Real.sqrt 6 < C) :
    ∃ η : ℝ, 0 < η ∧ η < 1/2 ∧ ∀ᶠ d : ℕ in atTop, ∀ ρ : ℂ, |ρ.re-1/2| ≤ η →
      ‖copyCoshCorrection d ρ‖ ≤ C*(1+(d:ℝ))*(ρ.re-1/2)^2 := by
  have hh : ∀ᶠ η : ℝ in 𝓝[>] 0, continuumQuadraticCoefficient η < C :=
    (continuumQuadraticCoefficient_tendsto_zero.mono_left nhdsWithin_le_nhds).eventually (Iio_mem_nhds hC)
  have hpos : ∀ᶠ η : ℝ in 𝓝[>] 0, 0 < η := self_mem_nhdsWithin
  have hsmall : ∀ᶠ η : ℝ in 𝓝[>] 0, η < 1/2 :=
    ((tendsto_id : Tendsto id (𝓝 (0:ℝ)) (𝓝 0)).mono_left nhdsWithin_le_nhds).eventually
      (Iio_mem_nhds (by norm_num : (0:ℝ) < 1/2))
  obtain ⟨η,hη,hη',hK⟩ := (hpos.and (hsmall.and hh)).exists
  refine ⟨η,hη,hη',?_⟩
  have hε : 0 < C-continuumQuadraticCoefficient η := sub_pos.mpr hK
  simpa only [add_sub_cancel] using eventually_copyCoshCorrection_le_reference hη hη' hε


end RiemannResearch.Analysis.ActualZeroPhaseMoments
