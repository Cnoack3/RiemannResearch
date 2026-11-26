import RiemannResearch.Analysis.ActualZeroCountAsymptotics
import RiemannResearch.Analysis.ActualPrimeTorusFMZ
import RiemannResearch.Analysis.ActualZeroTriangularIntegral
import RiemannResearch.Analysis.ActualInghamCriticalTilt
import RiemannResearch.Analysis.ActualRationalHigherHorizontalEndpoint
import RiemannResearch.Analysis.RationalLandauMovingBand

/-!
# Horizontal moments in the Landau formula at the Ingham slope

For the actual zeros the Ingham curve gives a Gaussian gain beyond its
tangent of slope `4/3`. We use a comparison frequency one square-root
above that tangent to estimate the signed Taylor remainder. On the joint
numerator-frequency band of the rational Landau theorem the contraction
ratio is at most `3/10`. The retained horizontal moments keep their phases.

The Landau main term and its arithmetic domain follow
`RationalLandauMovingBand`. See Ford, Meng and Zaharescu, Lemma 1,
<https://doi.org/10.1112/blms.12001>, for the uniform Landau formula.
-/

noncomputable section
open Filter
open scoped BigOperators Topology

namespace RiemannResearch.Analysis.ActualZeroOrdinate

private theorem cosh_sub_one_le_mul_exp {x : ℝ} (hx : 0 ≤ x) :
    Real.cosh x - 1 ≤ x * Real.exp x := by
  have hneg : Real.exp (-x) ≤ Real.exp x := Real.exp_le_exp.mpr (by linarith)
  have hmul := mul_le_mul_of_nonneg_right (Real.add_one_le_exp (-x)) (Real.exp_pos x).le
  rw [← Real.exp_add, neg_add_cancel, Real.exp_zero] at hmul
  rw [Real.cosh_eq]
  nlinarith only [hneg, hmul]

private theorem badCosh_le_tilted_first (T v : ℝ) (hv : 0 ≤ v) :
    badWeightedSum T 0 (fun t => Real.cosh (v*t) - 1) ≤
      v * ∑ i : Copies T, copyDisplacement T i * Real.exp (v*copyDisplacement T i) := by
  rw [badWeightedSum_eq_realSum, realSum_eq_copies, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  let d := copyDisplacement T i
  have hd : 0 ≤ d := abs_nonneg _
  change (if 0 < d then Real.cosh (v*d)-1 else 0) ≤ v*(d*Real.exp (v*d))
  split_ifs
  · simpa only [mul_assoc] using cosh_sub_one_le_mul_exp (mul_nonneg hv hd)
  · positivity

/-- At the comparison frequency `v = (4/3)L + √L`, one constant works
for every Taylor order and every real frequency of absolute value at most
`v`. The proof retains the quadratic gain in the actual Ingham estimate. -/
theorem eventually_critical_landau_taylor_bound :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ T : ℝ in atTop, ∀ (u : ℝ) (J : ℕ),
      let L := Real.log T
      let v := (4/3)*L + Real.sqrt L
      |u| ≤ v → ‖horizontalTaylorError T u J / (T : ℂ)‖ ≤
        (|u|/v)^(2*(J+1)) * (K*L^4) := by
  obtain ⟨K,hK,hm⟩ := exists_critical_tilt_scaled_moments 1
  refine ⟨3*K,by positivity,?_⟩
  filter_upwards [hm,Real.tendsto_log_atTop.eventually_ge_atTop 1,
    eventually_gt_atTop (1:ℝ)] with T ht hL hT
  let L := Real.log T
  let v := (4/3)*L + Real.sqrt L
  have hL1 : 1 ≤ L := hL
  have hL0 : 0 < L := by linarith
  have hv : 0 < v := by dsimp [v]; positivity
  have hT0 := zero_lt_one.trans hT
  have hs := Real.sq_sqrt hL0.le
  have hsle : Real.sqrt L ≤ L := by nlinarith [Real.sqrt_nonneg L, sq_nonneg (Real.sqrt L-1)]
  have hvle : v ≤ 3*L := by dsimp [v]; linarith
  let S := (∑ i : Copies T, copyDisplacement T i * Real.exp (v*copyDisplacement T i))/T
  have hS : 0 ≤ S := by
    apply div_nonneg _ hT0.le
    exact Finset.sum_nonneg fun i _ => mul_nonneg (abs_nonneg _) (Real.exp_pos _).le
  have hmoment := ht 0 v hv.le (by dsimp [v,L]; simp)
  have hLS : L*S ≤ K*L^4 := by
    simpa only [Nat.zero_add, pow_one, Nat.factorial_one, Nat.cast_one, mul_one,
      Real.sq_sqrt hL0.le, S, L] using hmoment
  intro u J
  dsimp only
  intro hu
  have hbudget : badWeightedSum T 0 (fun t => Real.cosh (v*t)-1) / T ≤ 3*K*L^4 := by
    have h := div_le_div_of_nonneg_right (badCosh_le_tilted_first T v hv.le) hT0.le
    rw [mul_div_assoc] at h
    change _ ≤ v*S at h
    have hvs := mul_le_mul_of_nonneg_right hvle hS
    linarith only [h,hvs,hLS,show 3*L*S = 3*(L*S) by ring,show 3*K*L^4 = 3*(K*L^4) by ring]
  rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hT0]
  calc
    _ ≤ ((|u|/v)^(2*(J+1)) * badWeightedSum T 0 (fun t => Real.cosh (v*t)-1))/T :=
      div_le_div_of_nonneg_right (horizontalTaylorError_le_coshSum T u v J hv hu) hT0.le
    _ ≤ _ := by rw [mul_div_assoc]; exact mul_le_mul_of_nonneg_left hbudget (by positivity)

/-- Combine the joint rational Landau band with the `4/3` Ingham comparison.
The contour error has every fixed inverse-logarithmic order. The horizontal
error contracts geometrically as the number of retained signed terms grows. -/
theorem eventually_rational_landau_corrected_geometric (θ : ℝ) (hθ : θ < 1) (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in atTop, ∀ n m : ℕ, 1 ≤ m → m < n →
      let u := Real.log ((n : ℝ)/(m : ℝ))
      Real.log (n : ℝ) + 3*u/2 ≤ θ*Real.log T → ∀ J : ℕ,
      ‖higherCorrectedRationalRemainder T n m J‖ ≤ C/(Real.log T)^k +
        (3/10 : ℝ)^(2*(J+1)) * (C*(Real.log T)^4) := by
  obtain ⟨A,hA,ha⟩ := eventually_rational_landau_error_height_ratio_band θ hθ k
  obtain ⟨B,hB,hb⟩ := eventually_critical_landau_taylor_bound
  refine ⟨A+B,add_pos hA hB,?_⟩
  filter_upwards [ha,hb,eventually_gt_atTop (1:ℝ)] with T ha hb hT
  intro n m hm hmn u hband J
  have hm' : (1:ℝ) ≤ m := by exact_mod_cast hm
  have hm0 : (0:ℝ) < m := by linarith
  have hmn' : (m:ℝ) < n := by exact_mod_cast hmn
  have hu : 0 ≤ u := Real.log_nonneg ((one_le_div hm0).mpr hmn'.le)
  have hun : u ≤ Real.log (n:ℝ) := by
    dsimp [u]
    rw [Real.log_div (hm0.trans hmn').ne' hm0.ne']
    linarith only [Real.log_nonneg hm']
  let L := Real.log T
  let v := (4/3)*L + Real.sqrt L
  have hL : 0 < L := Real.log_pos hT
  have hv : 0 < v := by dsimp [v]; positivity
  have htθ := mul_le_mul_of_nonneg_right hθ.le hL.le
  have hsize : u ≤ (2/5)*L := by change _ ≤ θ*L at hband; linarith only [hun,hband,htθ]
  have hur : |u|/v ≤ 3/10 := by
    rw [abs_of_nonneg hu,div_le_iff₀ hv]
    dsimp [v]; linarith only [hsize, Real.sqrt_nonneg L]
  have huv : |u| ≤ v := (div_le_one hv).mp (hur.trans (by norm_num))
  have hpow := pow_le_pow_left₀ (div_nonneg (abs_nonneg _) hv.le) hur (2*(J+1))
  rw [higherCorrectedRationalRemainder_eq_taylor_landau T (zero_lt_one.trans hT).ne' hmn]
  have he := hb u J huv
  have hhor := he.trans (mul_le_mul hpow
    (show B*L^4 ≤ (A+B)*L^4 by gcongr; linarith) (by positivity) (by positivity))
  have har := (ha n m hm hmn hband).trans
    (div_le_div_of_nonneg_right (show A ≤ A+B by linarith) (pow_nonneg hL.le k))
  exact (norm_add_le _ _).trans (by linarith only [hhor, har])

/-- At the endpoint itself, an explicit number of signed even moments gives
any prescribed inverse-logarithmic accuracy after normalization by height. -/
theorem eventually_critical_landau_taylor_precision :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ T : ℝ in atTop, ∀ (k : ℕ) (u : ℝ) (J : ℕ),
      |u| ≤ (4/3)*Real.log T →
      ((k:ℝ)+4)*(1+(4/3)*Real.sqrt (Real.log T))*Real.log (Real.log T)
        ≤ 2*((J:ℝ)+1) →
      ‖horizontalTaylorError T u J / (T:ℂ)‖ ≤ K/(Real.log T)^k := by
  obtain ⟨K,hK,hb⟩ := eventually_critical_landau_taylor_bound
  refine ⟨K,hK,?_⟩
  filter_upwards [hb,Real.tendsto_log_atTop.eventually_ge_atTop 1] with T hb hL
  let L := Real.log T
  let s := Real.sqrt L
  let b := 1+(4/3)*s
  have hL0 : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hs : 0 < s := Real.sqrt_pos.2 hL0
  have hb0 : 0 < b := by dsimp [b]; positivity
  have hsq : s^2=L := Real.sq_sqrt hL0.le
  have hv : 0 < (4/3)*L+s := by positivity
  intro k u J hu hJ
  have hratio : |u| / ((4/3)*L+s) ≤ Real.exp (-1/b) := by
    calc
      _ ≤ ((4/3)*L) / ((4/3)*L+s) := div_le_div_of_nonneg_right hu hv.le
      _ = -1/b + 1 := by
        field_simp [hb0.ne',hv.ne']; dsimp [b]; nlinarith only [hsq]
      _ ≤ _ := Real.add_one_le_exp _
  let n := 2*(J+1)
  have hn : (n:ℝ)=2*((J:ℝ)+1) := by dsimp [n]; push_cast; ring
  have hexp : (n:ℝ)*(-1/b) ≤ -(((k+4 : ℕ):ℝ)*Real.log L) := by
    rw [← mul_div_assoc,div_le_iff₀ hb0]
    push_cast
    change ((k:ℝ)+4)*b*Real.log L ≤ 2*((J:ℝ)+1) at hJ
    rw [hn]
    linarith only [hJ]
  have hpow := pow_le_pow_left₀ (div_nonneg (abs_nonneg u) hv.le) hratio n
  rw [← Real.exp_nat_mul] at hpow
  have hdec : (|u| / ((4/3)*L+s))^n ≤ (L^(k+4))⁻¹ := by
    apply hpow.trans
    simpa only [Real.exp_neg,Real.exp_nat_mul,Real.exp_log hL0] using Real.exp_le_exp.mpr hexp
  have h := hb u J (hu.trans (le_add_of_nonneg_right hs.le))
  change _ ≤ (|u| / ((4/3)*L+s))^n * (K*L^4) at h
  apply h.trans
  calc
    _ ≤ (L^(k+4))⁻¹ * (K*L^4) := mul_le_mul_of_nonneg_right hdec (by positivity)
    _ = _ := by rw [pow_add]; field_simp [hL0.ne']; ring

/-- The squared modulus of the prime-orbit character sample is exactly the
unweighted all-pair cosine test, including equal ordinates and multiplicity. -/
theorem primeOrbit_character_gap_identity (P : Finset ℕ) (a : ℕ → ℤ) (T : ℝ) :
    Complex.normSq (ActualPrimeTorusFMZ.sampleFunctional P T
      (PrimeTorusHaar.character (fun p : P => a p))) =
    ∑ i : Copies T, ∑ j : Copies T,
      Real.cos ((copyOrdinate T i-copyOrdinate T j)*PrimePhaseTorus.primeFrequency P a) := by
  rw [ActualPrimeTorusFMZ.sampleFunctional_character,
    ← ActualZeroCollisionCertificate.actual_occurrenceAmplitude,
    OrdinateCollisionCertificate.occurrenceAmplitude_normSq]

/-- Keep the reflected Landau sum and subtract the signed horizontal moments
of orders two through `2J`, leaving the ordinary ordinate amplitude. -/
def reconstructedOrdinateSum (T u : ℝ) (J : ℕ) : ℂ :=
  landauSum T u - ∑ j ∈ Finset.range J,
    ((u:ℂ)^(2*(j+1))/((2*(j+1)).factorial:ℂ))*evenHorizontalMoment T u (j+1)

theorem ordinate_sub_reconstructed (T u : ℝ) (J : ℕ) :
    ordinateSum T u - reconstructedOrdinateSum T u J = horizontalTaylorError T u J := by
  rw [reconstructedOrdinateSum, horizontalTaylorError, horizontalTaylorPolynomial_eq_ordinate_add]
  abel

/-- The reconstructed sum keeps the nonconstant signed horizontal moments.
The resulting precision applies to the square root of the actual pair test. -/
theorem eventually_primeOrbit_gap_landau_precision (k : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∀ᶠ T : ℝ in atTop, ∀ (P : Finset ℕ) (a : ℕ → ℤ) (J : ℕ),
      let u := PrimePhaseTorus.primeFrequency P a
      |u| ≤ (4/3)*Real.log T →
      ((k:ℝ)+4)*(1+(4/3)*Real.sqrt (Real.log T))*Real.log (Real.log T)
        ≤ 2*((J:ℝ)+1) →
      |Real.sqrt (∑ i : Copies T, ∑ j : Copies T,
          Real.cos ((copyOrdinate T i-copyOrdinate T j)*u)) / T -
        ‖reconstructedOrdinateSum T u J / (T:ℂ)‖|
        ≤ K/(Real.log T)^k := by
  obtain ⟨K,hK,hb⟩ := eventually_critical_landau_taylor_precision
  refine ⟨K,hK,?_⟩
  filter_upwards [hb,eventually_gt_atTop (0:ℝ)] with T hb ht
  intro P a J
  dsimp only
  intro hu hJ
  let u := PrimePhaseTorus.primeFrequency P a
  rw [← primeOrbit_character_gap_identity, ActualPrimeTorusFMZ.sampleFunctional_character,
    Complex.normSq_eq_norm_sq,Real.sqrt_sq (norm_nonneg _)]
  have hnorm : ‖ordinateSum T u / (T:ℂ)‖ = ‖ordinateSum T u‖/T := by
    rw [norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos ht]
  rw [← hnorm]
  apply (abs_norm_sub_norm_le _ _).trans
  rw [← sub_div,ordinate_sub_reconstructed]
  exact hb k u J hu hJ

/-- At the zero-count normalization of the pair statistic the Taylor transfer
has error at most a constant divided by height, uniformly up to the tangent.
Both the precision and the Taylor order may depend on the height. -/
theorem eventually_primeOrbit_gap_count_precision :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in atTop, ∀ (P : Finset ℕ) (a : ℕ → ℤ) (J k : ℕ),
      let u := PrimePhaseTorus.primeFrequency P a
      let L := Real.log T
      |u| ≤ (4/3)*L → 2*L ≤ (k:ℝ)*Real.log L →
      ((k:ℝ)+4)*(1+(4/3)*Real.sqrt L)*Real.log L ≤ 2*((J:ℝ)+1) →
      |((∑ i : Copies T, ∑ j : Copies T,
          Real.cos ((copyOrdinate T i-copyOrdinate T j)*u)) -
          ‖reconstructedOrdinateSum T u J‖^2) / (Zeta23.Ncount 0 T : ℝ)| ≤ C/T := by
  obtain ⟨K,hK,hb⟩ := eventually_critical_landau_taylor_precision
  refine ⟨3*K,by positivity,?_⟩
  filter_upwards [hb,eventually_count_pos,eventually_gt_atTop (1:ℝ),
    eventually_ge_atTop K] with T hb hN hT hKT
  intro P a J k
  dsimp only
  intro hu hsize hJ
  let u := PrimePhaseTorus.primeFrequency P a
  let L := Real.log T
  let N : ℝ := Zeta23.Ncount 0 T
  let x := ‖ordinateSum T u‖
  let y := ‖reconstructedOrdinateSum T u J‖
  have ht := zero_lt_one.trans hT
  have hL : 0 < L := Real.log_pos hT
  have hN1 : 1 ≤ N := by
    dsimp only [N]
    exact_mod_cast (Nat.succ_le_of_lt hN)
  have hN0 : 0 < N := by linarith
  have hTk : T*T ≤ L^k := by
    calc
      T*T = Real.exp (2*L) := by rw [two_mul, Real.exp_add, Real.exp_log ht]
      _ ≤ Real.exp ((k:ℝ)*Real.log L) := Real.exp_le_exp.mpr hsize
      _ = L^k := by rw [Real.exp_nat_mul, Real.exp_log hL]
  have hp := hb k u J hu hJ
  rw [← ordinate_sub_reconstructed, norm_div, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos ht] at hp
  have ha : |x-y| ≤ K/T := by
    apply (abs_norm_sub_norm_le _ _).trans
    apply ((div_le_iff₀ ht).mp hp).trans
    apply (le_div_iff₀ ht).mpr
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div]
    apply (div_le_iff₀ (pow_pos hL k)).mpr
    calc
      K*T*T = K*(T*T) := by ring
      _ ≤ K*L^k := mul_le_mul_of_nonneg_left hTk hK.le
  have hx : x ≤ N := norm_ordinateSum_le_count T u
  have hxy : 0 ≤ x+y := add_nonneg (norm_nonneg _) (norm_nonneg _)
  have hs : x+y ≤ 3*N := by
    have hsmall := (abs_le.mp ha).1
    linarith only [hsmall, (div_le_one ht).mpr hKT, hx, hN1]
  rw [← primeOrbit_character_gap_identity, ActualPrimeTorusFMZ.sampleFunctional_character,
    Complex.normSq_eq_norm_sq]
  change |(x^2-y^2)/N| ≤ 3*K/T
  rw [sq_sub_sq, abs_div, abs_mul, abs_of_nonneg hxy, abs_of_pos hN0]
  calc
    _ ≤ ((3*N)*(K/T))/N := div_le_div_of_nonneg_right
      (mul_le_mul hs ha (abs_nonneg _) (by positivity)) hN0.le
    _ = 3*K/T := by field_simp [ht.ne',hN0.ne']

/--
info: 'RiemannResearch.Analysis.ActualZeroOrdinate.eventually_primeOrbit_gap_count_precision' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms eventually_primeOrbit_gap_count_precision

/-- For finite real linear combinations of prime-orbit characters, the horizontal
reconstruction costs at most the sum of the absolute coefficients times `C/T`.
The test, its support, and its Taylor order may be chosen at each height. -/
theorem eventually_weighted_primeOrbit_gap_count_precision {ι : Type*} :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ T : ℝ in atTop,
      ∀ (s : Finset ι) (c : ι → ℝ) (P : ι → Finset ℕ) (a : ι → ℕ → ℤ) (J k : ℕ),
        let u := fun b => PrimePhaseTorus.primeFrequency (P b) (a b)
        let L := Real.log T
        (∀ b ∈ s, |u b| ≤ (4/3)*L) → 2*L ≤ (k:ℝ)*Real.log L →
        ((k:ℝ)+4)*(1+(4/3)*Real.sqrt L)*Real.log L ≤ 2*((J:ℝ)+1) →
        |∑ b ∈ s, c b * (((∑ i : Copies T, ∑ j : Copies T,
            Real.cos ((copyOrdinate T i - copyOrdinate T j) * u b)) -
            ‖reconstructedOrdinateSum T (u b) J‖^2) / (Zeta23.Ncount 0 T : ℝ))| ≤
          (∑ b ∈ s, |c b|) * (C/T) := by
  obtain ⟨C, hC, hsingle⟩ := eventually_primeOrbit_gap_count_precision
  refine ⟨C, hC, ?_⟩
  filter_upwards [hsingle] with T hT
  intro s c P a J k
  dsimp only
  intro hband hk hJ
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro b hb
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left (hT (P b) (a b) J k (hband b hb) hk hJ) (abs_nonneg _)

/--
info: 'RiemannResearch.Analysis.ActualZeroOrdinate.eventually_weighted_primeOrbit_gap_count_precision' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms eventually_weighted_primeOrbit_gap_count_precision

end RiemannResearch.Analysis.ActualZeroOrdinate
