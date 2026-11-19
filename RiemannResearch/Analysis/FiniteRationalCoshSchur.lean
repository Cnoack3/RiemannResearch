/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.FiniteCoshFrobeniusAsymptotics
import RiemannResearch.Analysis.FiniteWeightedSchurBound

/-!
# Weighted Schur refinement of the true horizontal operator norm

A positive rational weight A x+B+C/x is a strict supersolution for the
continuum kernel cosh(η log(i/j))−1. The finite row averages converge to its
three explicit power integrals. The resulting bound holds simultaneously
for every smaller displacement and every sufficiently large dimension.
The rational witness is obtained by solving (Kη²I−M)(A,B,C)=(1,0,0),
where M is the three-dimensional continuum matrix in this Laurent basis.
The coefficients and the residual are verified below by exact arithmetic.
-/

noncomputable section
open Filter Set Complex Real
open scoped BigOperators Topology
namespace RiemannResearch.Analysis.ActualZeroPhaseMoments
open FiniteHyperbolicHarmonicCap HorizontalEuclideanMoments HorizontalPhaseBootstrap ZeroOrdinate

private def integerShiftExp (d : ℕ) (p : ℝ) (i : Fin d) :=
  Real.exp (p*(Real.log (1+(d:ℝ)) - integerLogFrequency d i))

private def shiftedMean (d : ℕ) (p : ℝ) := (∑ i : Fin d, integerShiftExp d p i)/(1+(d:ℝ))

private theorem shiftedMean_tendsto {p : ℝ} (hp : p < 1) :
    Tendsto (fun d : ℕ => shiftedMean d p) atTop (𝓝 (1/(1-p))) := by
  have h := integerFrequencySum_normalized_tendsto (p := -p) (by linarith only [hp])
  rw [show -p+1=1-p by ring] at h
  apply h.congr'
  filter_upwards with d
  have hx : 0 < 1+(d:ℝ) := by positivity
  have hxp := Real.rpow_pos_of_pos hx p
  have he (i : Fin d) : integerShiftExp d p i = (1+(d:ℝ))^p * Real.exp ((-p)*integerLogFrequency d i) := by
    unfold integerShiftExp
    rw [Real.rpow_def_of_pos hx,← Real.exp_add]
    congr 1; ring
  simp only [shiftedMean, he, ← Finset.mul_sum,finiteExponentialSum]
  rw [show 1-p=-p+1 by ring,Real.rpow_add hx,Real.rpow_neg hx.le,Real.rpow_one]
  field_simp [hxp.ne',hx.ne']

/-- Three moment relations with a strict x-sized residual and a globally
positive Laurent weight. -/
structure IntegerCoshSchurCertificate where
  η : ℝ
  K : ℝ
  A : ℝ
  B : ℝ
  C : ℝ
  eta_pos : 0 < η
  eta_lt_half : η < 1/2
  coefficient_nonneg : 0 ≤ K
  weight_pos : ∀ x : ℝ, 0 < x → 0 < A*x+B+C/x
  row_x : K*η^2*A - (A + B/(1+η) + C/(1+2*η))/2 = 1
  row_const : K*η^2*B + (A/(1-η) + B + C/(1+η)) = 0
  row_inv : K*η^2*C - (A/(1-2*η) + B/(1-η) + C)/2 = 0

namespace IntegerCoshSchurCertificate
variable (S : IntegerCoshSchurCertificate)

private def w (x : ℝ) := S.A*x+S.B+S.C/x
private def moment (d : ℕ) (p : ℝ) := S.A*shiftedMean d (p+S.η)+S.B*shiftedMean d p+S.C*shiftedMean d (p-S.η)
private def limit (p : ℝ) := S.A/(1-(p+S.η))+S.B/(1-p)+S.C/(1-(p-S.η))

private theorem moment_tendsto {p : ℝ} (hp : p+S.η < 1) :
    Tendsto (fun d : ℕ => S.moment d p) atTop (𝓝 (S.limit p)) := by
  have h := (((shiftedMean_tendsto hp).const_mul S.A).add
    ((shiftedMean_tendsto (p := p) (by linarith only [hp,S.eta_pos])).const_mul S.B)).add
    ((shiftedMean_tendsto (p := p-S.η) (by linarith only [hp,S.eta_pos])).const_mul S.C)
  simpa only [moment,limit,mul_one_div] using h

private theorem moment_eq (d : ℕ) (p : ℝ) :
    S.moment d p = (∑ j : Fin d, integerShiftExp d p j * S.w (integerShiftExp d S.η j))/(1+(d:ℝ)) := by
  have hX : 1+(d:ℝ)≠0 := by positivity
  unfold moment shiftedMean
  field_simp [hX]
  rw [Finset.mul_sum,Finset.mul_sum,Finset.mul_sum,← Finset.sum_add_distrib,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  unfold w integerShiftExp
  rw [add_mul,sub_mul,Real.exp_add,Real.exp_sub]
  ring

private theorem limit_residual (x : ℝ) (hx : 0 < x) :
    S.K*S.η^2*S.w x - (x/2*S.limit (-S.η) + (1/(2*x))*S.limit S.η - S.limit 0) = x := by
  have hm : S.limit (-S.η)=S.A+S.B/(1+S.η)+S.C/(1+2*S.η) := by
    dsimp [limit]; ring_nf
  have hp : S.limit S.η=S.A/(1-2*S.η)+S.B/(1-S.η)+S.C := by
    dsimp [limit]; ring_nf
  have hz : S.limit 0=S.A/(1-S.η)+S.B+S.C/(1+S.η) := by
    dsimp [limit]; ring_nf
  rw [hm,hp,hz]
  rw [show 1/(2*x)=(1/2)/x by field_simp [hx.ne'] <;> ring]
  calc
    _ = (S.K*S.η^2*S.A-(S.A+S.B/(1+S.η)+S.C/(1+2*S.η))/2)*x +
      (S.K*S.η^2*S.B+(S.A/(1-S.η)+S.B+S.C/(1+S.η))) +
      (S.K*S.η^2*S.C-(S.A/(1-2*S.η)+S.B/(1-S.η)+S.C)/2)/x := by dsimp [w]; ring
    _ = x := by rw [S.row_x,S.row_const,S.row_inv,one_mul,zero_div,add_zero,add_zero]

private theorem eventually_reference_row :
    ∀ᶠ d : ℕ in atTop, ∀ i : Fin d,
      ∑ j : Fin d, (Real.cosh (S.η*frequencyGap i j)-1)*S.w (integerShiftExp d S.η j) ≤
        (1+(d:ℝ))*(S.K*S.η^2)*S.w (integerShiftExp d S.η i) := by
  have hm := (S.moment_tendsto (p := -S.η) (by linarith only [S.eta_pos])).eventually
    (Iio_mem_nhds (show S.limit (-S.η)<S.limit (-S.η)+1/4 by linarith))
  have hp := (S.moment_tendsto (p := S.η) (by linarith only [S.eta_lt_half])).eventually
    (Iio_mem_nhds (show S.limit S.η<S.limit S.η+1/4 by linarith))
  have hz := (S.moment_tendsto (p := 0) (by linarith only [S.eta_lt_half])).eventually
    (Ioi_mem_nhds (show S.limit 0-1/4<S.limit 0 by linarith))
  filter_upwards [hm,hp,hz] with d hm hp hz i
  let X := 1+(d:ℝ)
  let x := integerShiftExp d S.η i
  have hX : 0 < X := by dsimp [X]; positivity
  have hx : 0 < x := Real.exp_pos _
  have hx1 : 1 ≤ x := by
    apply Real.one_le_exp_iff.mpr
    apply mul_nonneg S.eta_pos.le (sub_nonneg.mpr _)
    apply Real.log_le_log (by positivity : 0 < ((i.val+1:ℕ):ℝ))
    exact_mod_cast (show i.val+1 ≤ 1+d by omega)
  have he (j : Fin d) : (Real.cosh (S.η*frequencyGap i j)-1)*S.w (integerShiftExp d S.η j) =
      x/2*(integerShiftExp d (-S.η) j*S.w (integerShiftExp d S.η j))+
      (1/(2*x))*(integerShiftExp d S.η j*S.w (integerShiftExp d S.η j)) -
      integerShiftExp d 0 j*S.w (integerShiftExp d S.η j) := by
    have hf : frequencyGap i j = integerLogFrequency d i-integerLogFrequency d j := rfl
    have hr : Real.exp (S.η*frequencyGap i j) = integerShiftExp d S.η j / x := by
      dsimp [integerShiftExp,x]; rw [← Real.exp_sub,hf]; congr 1; ring
    have hr' : Real.exp (-(S.η*frequencyGap i j)) = x * integerShiftExp d (-S.η) j := by
      dsimp [integerShiftExp,x]; rw [← Real.exp_add,hf]; congr 1; ring
    rw [Real.cosh_eq,hr,hr']
    simp only [integerShiftExp,zero_mul,Real.exp_zero,one_mul]
    ring
  have hrow :
      (∑ j : Fin d, (Real.cosh (S.η*frequencyGap i j)-1)*S.w (integerShiftExp d S.η j)) =
        X*(x/2*S.moment d (-S.η)+(1/(2*x))*S.moment d S.η-S.moment d 0) := by
    simp_rw [he]
    rw [Finset.sum_sub_distrib,Finset.sum_add_distrib,← Finset.mul_sum,← Finset.mul_sum,
      S.moment_eq,S.moment_eq,S.moment_eq]
    dsimp [X]; field_simp [hX.ne',hx.ne'] <;> ring
  rw [hrow, mul_assoc]
  apply mul_le_mul_of_nonneg_left _ hX.le
  have hm' := mul_le_mul_of_nonneg_left hm.le (show 0 ≤ x/2 by positivity)
  have hp' := mul_le_mul_of_nonneg_left hp.le (show 0 ≤ 1/(2*x) by positivity)
  have hinv : 1/(2*x) ≤ 1/2 := (div_le_div_of_nonneg_left zero_le_one (by norm_num) (by linarith only [hx1]))
  have hres := S.limit_residual x hx
  change S.limit 0 - 1/4 < S.moment d 0 at hz
  change S.moment d (-S.η) < S.limit (-S.η)+1/4 at hm
  change S.moment d S.η < S.limit S.η+1/4 at hp
  linarith only [hres,hm',hp',hz,hx1,hinv]

theorem eventually_copyCoshCorrection (S : IntegerCoshSchurCertificate) :
    ∀ᶠ d : ℕ in atTop, ∀ ρ : ℂ, |ρ.re-1/2| ≤ S.η →
      ‖copyCoshCorrection d ρ‖ ≤ S.K*(1+(d:ℝ))*(ρ.re-1/2)^2 := by
  filter_upwards [S.eventually_reference_row] with d hr ρ hρ
  let a := ρ.re-1/2
  let θ := |a| / S.η
  let k := fun i j : Fin d => θ^2*(Real.cosh (S.η*frequencyGap i j)-1)
  let w := fun i : Fin d => S.w (integerShiftExp d S.η i)
  let G : Matrix (Fin d) (Fin d) ℂ := fun i j => phase (frequencyGap i j) ρ.im *
    ((Real.cosh (a * frequencyGap i j):ℂ)-1)
  have hθ : 0 ≤ θ := div_nonneg (abs_nonneg _) S.eta_pos.le
  have hθ1 : θ ≤ 1 := (div_le_one S.eta_pos).mpr hρ
  have hmajor (i j) : ‖G i j‖ ≤ k i j := by
    have h := cosh_sub_one_mul_le_quadratic (x := S.η*frequencyGap i j) hθ hθ1
    rw [show θ*(S.η*frequencyGap i j)=|a| *frequencyGap i j by dsimp [θ]; field_simp [S.eta_pos.ne']] at h
    dsimp [G,k]
    rw [norm_mul,phase_norm,one_mul,← Complex.ofReal_one,← Complex.ofReal_sub,Complex.norm_real,
      Real.norm_eq_abs,abs_of_nonneg (sub_nonneg.mpr (Real.one_le_cosh _))]
    by_cases ha : 0 ≤ a
    · simpa only [abs_of_nonneg ha] using h
    · simpa only [abs_of_neg (lt_of_not_ge ha),neg_mul,Real.cosh_neg] using h
  have hsym (i j) : k i j = k j i := by
    dsimp [k]
    rw [show frequencyGap j i = - frequencyGap i j by unfold frequencyGap; ring,mul_neg,Real.cosh_neg]
  have hnonneg (i j) : 0 ≤ k i j := mul_nonneg (sq_nonneg _) (sub_nonneg.mpr (Real.one_le_cosh _))
  have hM : 0 ≤ S.K*(1+(d:ℝ))*a^2 := mul_nonneg (mul_nonneg S.coefficient_nonneg (by positivity)) (sq_nonneg _)
  apply euclideanCLM_norm_le_weightedSchur G k w _ hM (fun i => S.weight_pos _ (Real.exp_pos _)) hnonneg hsym hmajor
  intro i
  dsimp [k,w]
  simp_rw [mul_assoc]
  rw [← Finset.mul_sum]
  apply (mul_le_mul_of_nonneg_left (hr i) (sq_nonneg θ)).trans_eq
  dsimp [θ]
  rw [div_pow,sq_abs]
  field_simp [S.eta_pos.ne'] <;> ring

end IntegerCoshSchurCertificate


/-- Exact rational coefficient for the true operator comparison. -/
def rationalSchurCoefficient : ℝ := 93969262079/50000000000

private def schurDen : ℝ := 1931878243568757612686166433246191221234301936532327444879080961
private def schurA : ℝ :=
  449903943996860606041129776898774684671812204216141643216676410046641062988795000000000000000000000000/schurDen
private def schurB : ℝ :=
  -899808009224506308977038773294954428689815519750000000000000000000000000000000000000000000000000000000/schurDen
private def schurC : ℝ :=
  449904065227665738795257946753377900272766379937500000000000000000000000000000000000000000000000000000/schurDen

/-- The row residual is exactly x. Positivity of the weight follows from the
negative discriminant of its quadratic numerator. -/
def rationalSchurCertificate : IntegerCoshSchurCertificate where
  η := 1/10000000
  K := rationalSchurCoefficient
  A := schurA
  B := schurB
  C := schurC
  eta_pos := by norm_num
  eta_lt_half := by norm_num
  coefficient_nonneg := by norm_num [rationalSchurCoefficient]
  weight_pos := by
    intro x hx
    have ha : 0 < schurA := by norm_num [schurA,schurDen]
    have hd : 0 < 4*schurA*schurC-schurB^2 := by norm_num [schurA,schurB,schurC,schurDen]
    have hp : 0 < schurA*x^2+schurB*x+schurC := by
      apply (mul_pos_iff_of_pos_left (show 0 < 4*schurA by positivity)).mp
      nlinarith only [sq_nonneg (2*schurA*x+schurB),hd]
    calc
      0 < (schurA*x^2+schurB*x+schurC)/x := div_pos hp hx
      _ = _ := by field_simp [hx.ne'] <;> ring
  row_x := by norm_num [rationalSchurCoefficient,schurA,schurB,schurC,schurDen]
  row_const := by norm_num [rationalSchurCoefficient,schurA,schurB,schurC,schurDen]
  row_inv := by norm_num [rationalSchurCoefficient,schurA,schurB,schurC,schurDen]

/-- Rayleigh quotient of the continuum quadratic kernel on the Laurent
test weight. The three quantities are its zeroth, first and second log
moments, obtained from the derivatives of its elementary rational integral. -/
def rationalSchurRayleighComparison : ℝ :=
  let η : ℝ := 1/10000000
  let m := schurA/(1-η)+schurB+schurC/(1+η)
  let m₁ := schurA/(1-η)^2+schurB+schurC/(1+η)^2
  let m₂ := 2*schurA/(1-η)^3+2*schurB+2*schurC/(1+η)^3
  let D := schurA^2/(1-2*η)+2*schurA*schurB/(1-η)+2*schurA*schurC+schurB^2+
    2*schurB*schurC/(1+η)+schurC^2/(1+2*η)
  (m*m₂-m₁^2)/D

theorem rationalSchurRayleighComparison_bracket :
    187938524157/100000000000 < rationalSchurRayleighComparison ∧
      rationalSchurRayleighComparison < rationalSchurCoefficient := by
  norm_num [rationalSchurRayleighComparison,rationalSchurCoefficient,schurA,schurB,schurC,schurDen]

theorem rationalSchurCoefficient_lt_frobenius : rationalSchurCoefficient < Real.sqrt 6 := by
  apply (Real.lt_sqrt (by norm_num [rationalSchurCoefficient])).mpr
  norm_num [rationalSchurCoefficient]

end RiemannResearch.Analysis.ActualZeroPhaseMoments
