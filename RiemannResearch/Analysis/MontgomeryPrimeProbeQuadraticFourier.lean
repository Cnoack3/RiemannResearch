import RiemannResearch.Analysis.MontgomeryPrimeProbeDiagonalMean

/-! # Uniform Cesàro diagonal for the unscaled Fourier discrepancy -/

noncomputable section
namespace RiemannResearch.Analysis.MontgomeryPrimeTrace
open Filter MeasureTheory Set MontgomeryPositiveGap ZeroOrdinate
open RiemannResearch.RH.Pareto.SpectralObstruction
open scoped Topology BigOperators

theorem continuous_primeLogPolynomial (Y : ℝ) : Continuous (primeLogPolynomial Y) := by
  unfold primeLogPolynomial phase
  fun_prop

theorem continuous_logBoxProbe {Y : ℝ} (hY : 0 < Y) : Continuous (logBoxProbe Y) := by
  have hc : Continuous primeContinuumProbe := by
    rw [funext primeContinuumProbe_eq]
    exact continuous_logPhaseKernel.comp (by fun_prop)
  rw [funext (logBoxProbe_eq_scaled_continuum hY)]
  exact continuous_const.mul (hc.comp (by fun_prop))

theorem continuous_primeLogDiscrepancy {Y : ℝ} (hY : 0 < Y) : Continuous (primeLogDiscrepancy Y) :=
  (continuous_primeLogPolynomial Y).sub (continuous_logBoxProbe hY)

/-- Average over a positive angular-frequency band. -/
def probeBandMean (B : ℝ) (f : ℝ → ℝ) : ℝ := (∫ t in (0:ℝ)..B, f t)/B

theorem probeBandMean_mono {B : ℝ} (hB : 0 ≤ B) {f g : ℝ → ℝ}
    (hf : Continuous f) (hg : Continuous g) (h : ∀ t ∈ Icc 0 B, f t ≤ g t) :
    probeBandMean B f ≤ probeBandMean B g :=
  div_le_div_of_nonneg_right (intervalIntegral.integral_mono_on hB
    (hf.intervalIntegrable 0 B) (hg.intervalIntegrable 0 B) h) hB

theorem probeBandMean_add (B : ℝ) {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g) :
    probeBandMean B (fun t => f t + g t) = probeBandMean B f + probeBandMean B g := by
  simp only [probeBandMean, intervalIntegral.integral_add (hf.intervalIntegrable 0 B)
    (hg.intervalIntegrable 0 B), add_div]

theorem probeBandMean_mul (B a : ℝ) (f : ℝ → ℝ) :
    probeBandMean B (fun t => a*f t) = a * probeBandMean B f := by
  rw [probeBandMean, intervalIntegral.integral_const_mul, probeBandMean]
  ring

theorem probeBandMean_const {B : ℝ} (hB : B ≠ 0) (a : ℝ) :
    probeBandMean B (fun _ => a) = a := by
  simp [probeBandMean, intervalIntegral.integral_const, smul_eq_mul, hB, mul_div_cancel_left₀]

theorem abs_probeBandMean_sub {B : ℝ} (hB : 0 ≤ B) {f g : ℝ → ℝ}
    (hf : Continuous f) (hg : Continuous g) :
    |probeBandMean B f - probeBandMean B g| ≤ probeBandMean B (fun t => |f t - g t|) := by
  unfold probeBandMean
  rw [← sub_div, ← intervalIntegral.integral_sub (hf.intervalIntegrable 0 B)
    (hg.intervalIntegrable 0 B), abs_div, abs_of_nonneg hB]
  exact div_le_div_of_nonneg_right (intervalIntegral.abs_integral_le_integral_abs hB) hB

def probeBandSquare (B : ℝ) (f : ℝ → ℂ) : ℝ := probeBandMean B (fun t => ‖f t‖^2)

theorem logBoxProbe_bandSquare {Y B : ℝ} (hY : 0 < Y) (hB : 0 < B) :
    probeBandSquare B (logBoxProbe Y) ≤ Real.pi * Y / B := by
  let k := Y / (2*Real.pi)
  have hk : 0 < k := by dsimp [k]; positivity
  have he (t : ℝ) : ‖logBoxProbe Y t‖^2 = Y^2 * Real.sinc (Real.pi*(k*t))^2 := by
    rw [logBoxProbe_eq_scaled_continuum hY, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos hY, norm_primeContinuumProbe_eq, mul_pow, sq_abs]
    dsimp [k]
    ring_nf
  unfold probeBandSquare probeBandMean
  simp_rw [he]
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_comp_mul_left
    (fun u => Real.sinc (Real.pi*u)^2) hk.ne', mul_zero, smul_eq_mul, primeSineHoleMass_eq]
  have hm := sineGapMass_lower (mul_nonneg hk.le hB.le)
  apply div_le_div_of_nonneg_right _ hB.le
  have hn : k*B - sineGapMass (k*B) ≤ 1/2 := by linarith
  calc
    _ ≤ Y^2*(k⁻¹*(1/2)) := by gcongr
    _ = _ := by dsimp [k]; field_simp

private theorem sq_error_young (a b : ℂ) {z : ℝ} (hz : 0 < z) :
    |‖a‖^2-‖b‖^2| ≤ (1/z)*‖b‖^2 + (1+z)*‖a-b‖^2 := by
  have hd := (abs_le.mp (abs_norm_sub_norm_le a b)).2
  apply (abs_norm_sq_sub_le a b).trans
  field_simp [hz.ne']
  nlinarith [sq_nonneg (‖b‖ - z*‖a-b‖),
    mul_nonneg (mul_nonneg (norm_nonneg (a-b)) hz.le) (sub_nonneg.mpr hd)]

/-- Comparing band squares requires only continuity and the mean-square approximation error. -/
theorem probeBandSquare_compare {B z : ℝ} (hB : 0 < B) (hz : 0 < z)
    {f g : ℝ → ℂ} (hf : Continuous f) (hg : Continuous g) :
    |probeBandSquare B f - probeBandSquare B g| ≤
      (1/z)*probeBandSquare B g + (1+z)*probeBandSquare B (fun t => f t-g t) := by
  refine (abs_probeBandMean_sub hB.le (hf.norm.pow 2) (hg.norm.pow 2)).trans ?_
  unfold probeBandSquare
  rw [← probeBandMean_mul, ← probeBandMean_mul, ← probeBandMean_add _ (by fun_prop) (by fun_prop)]
  exact probeBandMean_mono hB.le (by fun_prop) (by fun_prop) (fun t _ => sq_error_young _ _ hz)

private theorem normalize_band_error {z Y : ℝ} (hz : 1 ≤ z) (hY : 0 ≤ Y) (hYz : Y ≤ z)
    {f : ℝ → ℂ} {d : ℝ}
    (he : |(∫ t in (0 : ℝ)..z ^ 4, ‖f t‖ ^ 2) - z ^ 4 * d| ≤
      52 * Y * (Y + (Real.log 4 + 4))) :
    |probeBandSquare (z^4) f - d| ≤
      (52*(1+(Real.log 4+4)))/z^2 := by
  have hz0 : 0 < z := by linarith
  have hM : 0 ≤ Real.log 4+4 := by positivity
  unfold probeBandSquare probeBandMean
  rw [div_sub' (pow_ne_zero 4 hz0.ne'), abs_div, abs_of_pos (pow_pos hz0 4)]
  have h2 : Y+(Real.log 4+4) ≤ z*(1+(Real.log 4+4)) := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hz) hM]
  calc
    _ ≤ (52*Y*(Y+(Real.log 4+4)))/z^4 := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact he
    _ ≤ (52*z*(z*(1+(Real.log 4+4))))/z^4 := by gcongr
    _ = _ := by field_simp

/-- Approximation by a finite prime polynomial, uniform in the height cutoff. -/
theorem primeLogDiscrepancy_approx_polynomial :
    ∃ W > (0:ℝ), ∀ {z L : ℝ}, 1 ≤ z → 1 ≤ L →
      probeBandSquare (z^4) (fun t => primeLogDiscrepancy L t-primeLogPolynomial (min z L) t) ≤
        W/z^2 := by
  obtain ⟨K,hK,ht⟩ := primeLogDiscrepancy_quartic_truncation
  let W := 2*K^2+2*Real.pi
  have hW : 0 < W := by dsimp [W]; positivity
  refine ⟨W,hW,fun {z L} hz hL => ?_⟩
  let Y := min z L
  have hY : 1 ≤ Y := le_min hz hL
  have hYz : Y ≤ z := min_le_left _ _
  have hz0 : 0 < z := by linarith
  have hL0 : 0 < L := by linarith
  have hY0 : 0 < Y := by linarith
  have hB : 0 < z^4 := by positivity
  let f := primeLogDiscrepancy L
  let g := primeLogPolynomial Y
  have hf : Continuous f := continuous_primeLogDiscrepancy hL0
  have hg : Continuous g := continuous_primeLogPolynomial Y
  have hc := continuous_logBoxProbe hY0
  have htail (t : ℝ) (h : t ∈ Icc 0 (z^4)) : ‖f t-primeLogDiscrepancy Y t‖ ≤ K/z := by
    by_cases hzL : z ≤ L
    · simpa only [f,Y,min_eq_left hzL] using ht hz hzL (t := t)
        (by simpa [abs_of_nonneg h.1] using h.2)
    · simp only [f,Y,min_eq_right (le_of_not_ge hzL),sub_self,norm_zero]
      positivity
  have hd : probeBandSquare (z^4) (fun t => f t-g t) ≤ W/z^2 := by
    have hp (t : ℝ) (h : t ∈ Icc 0 (z^4)) :
        ‖f t-g t‖^2 ≤ 2*(K/z)^2 + 2*‖logBoxProbe Y t‖^2 := by
      have he : f t-g t = (f t-primeLogDiscrepancy Y t)-logBoxProbe Y t := by
        dsimp [g,primeLogDiscrepancy]; ring
      have hu := (norm_sub_le (f t-primeLogDiscrepancy Y t) (logBoxProbe Y t)).trans
        (add_le_add (htail t h) le_rfl)
      rw [he]
      have ha := pow_le_pow_left₀ (norm_nonneg _) hu 2
      nlinarith [sq_nonneg (K/z - ‖logBoxProbe Y t‖)]
    have hh := probeBandMean_mono hB.le ((hf.sub hg).norm.pow 2)
      (continuous_const.add (continuous_const.mul (hc.norm.pow 2))) hp
    change probeBandSquare (z^4) (fun t => f t-g t) ≤
      probeBandMean (z^4) (fun t => 2*(K/z)^2 + 2*‖logBoxProbe Y t‖^2) at hh
    rw [probeBandMean_add _ (f := fun _ => 2*(K/z)^2) (g := fun t => 2*‖logBoxProbe Y t‖^2)
        continuous_const (continuous_const.mul (hc.norm.pow 2)),
      probeBandMean_const hB.ne', probeBandMean_mul] at hh
    refine hh.trans ?_
    have hbox := logBoxProbe_bandSquare hY0 hB
    have hz2 : z ≤ z^2 := by nlinarith [mul_nonneg hz0.le (sub_nonneg.mpr hz)]
    have hb : Real.pi*Y/z^4 ≤ Real.pi/z^2 := by
      calc
        _ ≤ Real.pi*z^2/z^4 := by gcongr; exact hYz.trans hz2
        _ = _ := by field_simp
    change 2*(K/z)^2+2*probeBandSquare (z^4) (logBoxProbe Y) ≤ _
    calc
      _ ≤ 2*(K/z)^2+2*(Real.pi/z^2) := by gcongr; exact hbox.trans hb
      _ = _ := by dsimp [W]; ring
  exact hd

/-- A joint, quantitative approximation by the finite diagonal. The estimate is uniform
in the height cutoff, including cutoffs below the truncation point. -/
theorem primeLogDiscrepancy_band_diagonal :
    ∃ C > (0 : ℝ), ∀ {z L : ℝ}, 1 ≤ z → 1 ≤ L →
      |probeBandSquare (z^4) (primeLogDiscrepancy L) -
        primeProbePartialDiagonal (min z L)| ≤ C/z := by
  obtain ⟨W,hW,happrox⟩ := primeLogDiscrepancy_approx_polynomial
  let V := 52*(1+(Real.log 4+4))
  have hV : 0 < V := by dsimp [V]; positivity
  refine ⟨primeProbeDiagonal+2*V+2*W, by have := primeProbeDiagonal_pos; positivity,
    fun {z L} hz hL => ?_⟩
  let Y := min z L
  have hY : 1 ≤ Y := le_min hz hL
  have hYz : Y ≤ z := min_le_left _ _
  have hz0 : 0 < z := by linarith
  have hL0 : 0 < L := by linarith
  have hY0 : 0 < Y := by linarith
  have hB : 0 < z^4 := by positivity
  let f := primeLogDiscrepancy L
  let g := primeLogPolynomial Y
  have hf : Continuous f := continuous_primeLogDiscrepancy hL0
  have hg : Continuous g := continuous_primeLogPolynomial Y
  have hd := happrox hz hL
  have he := normalize_band_error hz hY0.le hYz (primeLogPolynomial_mean_square hY0.le (z^4))
  have hz2 : 1 ≤ z^2 := one_le_pow₀ hz
  have hVz : V/z^2 ≤ V := div_le_self hV.le hz2
  have hu : probeBandSquare (z^4) g ≤ primeProbeDiagonal+V := by
    have := (abs_le.mp he).2
    linarith only [this, primeProbePartialDiagonal_le Y, hVz]
  have hh := probeBandSquare_compare hB hz0 hf hg
  have ha := abs_add_le (probeBandSquare (z^4) f-probeBandSquare (z^4) g)
    (probeBandSquare (z^4) g-primeProbePartialDiagonal Y)
  rw [sub_add_sub_cancel] at ha
  apply ha.trans
  calc
    _ ≤ ((1/z)*(primeProbeDiagonal+V)+(1+z)*(W/z^2)) + V/z^2 :=
      add_le_add (hh.trans (add_le_add (mul_le_mul_of_nonneg_left hu (by positivity))
        (mul_le_mul_of_nonneg_left hd (by positivity)))) he
    _ ≤ (primeProbeDiagonal + 2*V + 2*W)/z := by
      field_simp [hz0.ne']
      nlinarith [mul_nonneg (sub_nonneg.mpr hz) hV.le, mul_nonneg (sub_nonneg.mpr hz) hW.le]

private theorem probeBandSquare_sub_le {B : ℝ} (hB : 0 < B) {f g : ℝ → ℂ}
    (hf : Continuous f) (hg : Continuous g) :
    probeBandSquare B (fun t => f t-g t) ≤ 2*probeBandSquare B f+2*probeBandSquare B g := by
  unfold probeBandSquare
  rw [← probeBandMean_mul,← probeBandMean_mul,← probeBandMean_add _ (by fun_prop) (by fun_prop)]
  apply probeBandMean_mono hB.le (by fun_prop) (by fun_prop)
  intro t _
  have h := pow_le_pow_left₀ (norm_nonneg _) (norm_sub_le (f t) (g t)) 2
  nlinarith [sq_nonneg (‖f t‖-‖g t‖)]

/-- Uniform Fourier tails on every nontrivial frequency band. Both log cutoffs may move.
For large bands Montgomery–Vaughan only charges the diagonal of the omitted atoms. -/
theorem primeLogDiscrepancy_uniform_fourier_tail :
    ∀ ε > (0:ℝ), ∀ᶠ M : ℝ in atTop, ∀ {L B : ℝ}, M ≤ L → 1 ≤ B →
      probeBandSquare B (fun t => primeLogDiscrepancy L t-primeLogDiscrepancy M t) < ε := by
  obtain ⟨K,hK,hcut⟩ := primeLogDiscrepancy_quartic_truncation
  obtain ⟨W,hW,happrox⟩ := primeLogDiscrepancy_approx_polynomial
  let V := 52*(1+(Real.log 4+4))
  have hV : 0 < V := by dsimp [V]; positivity
  let C := K^2+2*V+8*W
  have hC : 0 < C := by dsimp [C]; positivity
  have hlim : Tendsto (fun M : ℝ => 2*(primeProbeDiagonal-primeProbePartialDiagonal M)+C/M^2)
      atTop (𝓝 0) := by
    have hd : Tendsto (fun M : ℝ => primeProbeDiagonal-primeProbePartialDiagonal M) atTop
        (𝓝 (primeProbeDiagonal-primeProbeDiagonal)) :=
      tendsto_const_nhds.sub tendsto_primeProbePartialDiagonal
    have hpow : Tendsto (fun M : ℝ => M^2) atTop atTop := tendsto_pow_atTop (by decide)
    have hc := hpow.const_div_atTop C
    simpa only [sub_self,mul_zero,add_zero] using (hd.const_mul 2).add hc
  intro ε hε
  filter_upwards [eventually_ge_atTop (1:ℝ),hlim.eventually (gt_mem_nhds hε)] with M hM heps
  intro L B hML hB
  have hM0 : 0 < M := by linarith
  have hL0 := hM0.trans_le hML
  have hB0 : 0 < B := by linarith
  apply lt_of_le_of_lt _ heps
  by_cases hsmall : B ≤ M^4
  · have hp (t : ℝ) (ht : t ∈ Icc 0 B) :
        ‖primeLogDiscrepancy L t-primeLogDiscrepancy M t‖^2 ≤ (K/M)^2 :=
      pow_le_pow_left₀ (norm_nonneg _) (hcut hM hML
        (by rw [abs_of_nonneg ht.1]; exact ht.2.trans hsmall)) 2
    have hh := probeBandMean_mono hB0.le
      (((continuous_primeLogDiscrepancy hL0).sub (continuous_primeLogDiscrepancy hM0)).norm.pow 2)
      (g := fun _ => (K/M)^2) continuous_const hp
    rw [probeBandMean_const hB0.ne'] at hh
    apply hh.trans
    rw [div_pow]
    have hKC : K^2 ≤ C := by dsimp [C]; linarith
    linarith only [div_le_div_of_nonneg_right hKC (sq_nonneg M),primeProbePartialDiagonal_le M]
  · let z := Real.sqrt (Real.sqrt B)
    have hz0 : 0 ≤ z := Real.sqrt_nonneg _
    have hz4 : z^4 = B := by
      dsimp [z]
      rw [show (4:ℕ) = 2*2 by decide,pow_mul,Real.sq_sqrt (Real.sqrt_nonneg _),Real.sq_sqrt hB0.le]
    have hMz : M ≤ z := by
      apply (pow_le_pow_iff_left₀ hM0.le hz0 (by decide : 4 ≠ 0)).mp
      rw [hz4]
      exact le_of_not_ge hsmall
    have hz := hM.trans hMz
    let Y := min z L
    have hMY : M ≤ Y := le_min hMz hML
    let u := primeLogPolynomial Y
    let v := primeLogPolynomial M
    let f := primeLogDiscrepancy L
    let g := primeLogDiscrepancy M
    have hf : Continuous f := continuous_primeLogDiscrepancy hL0
    have hg : Continuous g := continuous_primeLogDiscrepancy hM0
    have hu : Continuous u := continuous_primeLogPolynomial _
    have hv : Continuous v := continuous_primeLogPolynomial _
    have ef := happrox hz (hM.trans hML)
    have eg := happrox hz hM
    rw [hz4] at ef
    rw [hz4,min_eq_right hMz] at eg
    have e := normalize_band_error hz (hM0.le.trans hMY) (min_le_left z L)
      (primeLogPolynomial_tail_mean_square hM0.le hMY (z^4))
    rw [hz4] at e
    have ed : probeBandSquare B (fun t => u t-v t) ≤
        primeProbeDiagonal-primeProbePartialDiagonal M+V/z^2 := by
      linarith only [(abs_le.mp e).2,primeProbePartialDiagonal_le Y]
    have htot := probeBandSquare_sub_le hB0 (hu.sub hv) ((hg.sub hv).sub (hf.sub hu))
    have er' := probeBandSquare_sub_le hB0 (hg.sub hv) (hf.sub hu)
    have eqfun : (fun t => (u t-v t)-((g t-v t)-(f t-u t))) = (fun t => f t-g t) := by
      funext t
      ring
    change probeBandSquare B (fun t => (u t-v t)-((g t-v t)-(f t-u t))) ≤
      2*probeBandSquare B (fun t => u t-v t)+
      2*probeBandSquare B (fun t => (g t-v t)-(f t-u t)) at htot
    change probeBandSquare B (fun t => (g t-v t)-(f t-u t)) ≤
      2*probeBandSquare B (fun t => g t-v t)+2*probeBandSquare B (fun t => f t-u t) at er'
    rw [eqfun] at htot
    have ec : 2*V+8*W ≤ C := by dsimp [C]; linarith only [sq_nonneg K]
    have hdiv : (2*V+8*W)/z^2 ≤ C/M^2 :=
      div_le_div₀ (by positivity) ec (sq_pos_of_pos hM0) (pow_le_pow_left₀ hM0.le hMz 2)
    have hh : probeBandSquare B (fun t => f t-g t) ≤
        2*(primeProbeDiagonal-primeProbePartialDiagonal M)+(2*V+8*W)/z^2 := by
      change probeBandSquare B (fun t => f t-u t) ≤ W/z^2 at ef
      change probeBandSquare B (fun t => g t-v t) ≤ W/z^2 at eg
      rw [show (2*V+8*W)/z^2 = 2*(V/z^2)+8*(W/z^2) by ring]
      linarith only [htot,er',ef,eg,ed]
    exact hh.trans (add_le_add le_rfl hdiv)

/-- At a fixed cutoff the Cesàro mean recovers exactly its finite diagonal. -/
theorem primeLogDiscrepancy_fixed_cesaro {L : ℝ} (hL : 1 ≤ L) :
    Tendsto (fun B => probeBandSquare B (primeLogDiscrepancy L)) atTop
      (𝓝 (primeProbePartialDiagonal L)) := by
  let z := fun B : ℝ => Real.sqrt (Real.sqrt B)
  have hz : Tendsto z atTop atTop := Real.tendsto_sqrt_atTop.comp Real.tendsto_sqrt_atTop
  obtain ⟨C,_,h⟩ := primeLogDiscrepancy_band_diagonal
  apply (tendsto_sub_nhds_zero_iff).mp
  apply squeeze_zero_norm' _ (hz.const_div_atTop C)
  filter_upwards [hz.eventually_ge_atTop L,eventually_ge_atTop (0:ℝ)] with B hB h0
  have he : (z B)^4 = B := by
    dsimp [z]
    rw [show (4:ℕ) = 2*2 by decide,pow_mul,Real.sq_sqrt (Real.sqrt_nonneg _),Real.sq_sqrt h0]
  simpa only [Real.norm_eq_abs,he,min_eq_right hB] using h (hL.trans hB) hL

/-- The joint Wiener limit for the arithmetic discrepancy over a superlogarithmic band. -/
theorem primeLogDiscrepancy_cesaro {ι : Type*} {l : Filter ι} {L B : ι → ℝ}
    (hL : Tendsto L l atTop) (hB : Tendsto B l atTop) :
    Tendsto (fun i => probeBandSquare (B i) (primeLogDiscrepancy (L i))) l
      (𝓝 primeProbeDiagonal) := by
  let z := fun i => Real.sqrt (Real.sqrt (B i))
  have hz : Tendsto z l atTop := Real.tendsto_sqrt_atTop.comp (Real.tendsto_sqrt_atTop.comp hB)
  have hzL : Tendsto (fun i => min (z i) (L i)) l atTop := by
    apply tendsto_atTop.2
    intro a
    filter_upwards [hz.eventually_ge_atTop a, hL.eventually_ge_atTop a] with i h1 h2
    exact le_min h1 h2
  have hm := tendsto_primeProbePartialDiagonal.comp hzL
  obtain ⟨C, hC, h⟩ := primeLogDiscrepancy_band_diagonal
  have herr : Tendsto (fun i => probeBandSquare (B i) (primeLogDiscrepancy (L i)) -
      primeProbePartialDiagonal (min (z i) (L i))) l (𝓝 0) := by
    apply squeeze_zero_norm' _ (hz.const_div_atTop C)
    filter_upwards [hz.eventually_ge_atTop 1, hL.eventually_ge_atTop 1, hB.eventually_ge_atTop 0]
      with i hi hLi hBi
    have he : (z i)^4 = B i := by
      dsimp [z]
      rw [show (4:ℕ) = 2*2 by decide, pow_mul, Real.sq_sqrt (Real.sqrt_nonneg _), Real.sq_sqrt hBi]
    simpa only [Real.norm_eq_abs, he] using h hi hLi
  simpa [Function.comp_def] using herr.add hm

/--
info: 'RiemannResearch.Analysis.MontgomeryPrimeTrace.primeLogDiscrepancy_uniform_fourier_tail' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms primeLogDiscrepancy_uniform_fourier_tail

/--
info: 'RiemannResearch.Analysis.MontgomeryPrimeTrace.primeLogDiscrepancy_fixed_cesaro' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms primeLogDiscrepancy_fixed_cesaro

/--
info: 'RiemannResearch.Analysis.MontgomeryPrimeTrace.primeLogDiscrepancy_cesaro' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms primeLogDiscrepancy_cesaro

end RiemannResearch.Analysis.MontgomeryPrimeTrace
