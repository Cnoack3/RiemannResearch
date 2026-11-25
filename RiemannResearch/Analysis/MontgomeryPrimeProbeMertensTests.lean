import RiemannResearch.Analysis.MontgomeryPrimeProbeLogSpectrum

/-! # Testing the centered Mertens measure on a long logarithmic interval -/

noncomputable section
namespace RiemannResearch.Analysis.MontgomeryPrimeTrace
open Filter MeasureTheory Set
open scoped Topology BigOperators

/-- The finite prime measure minus length, evaluated on a real test. -/
def primeLogTest (L : ℝ) (g : ℝ → ℝ) : ℝ :=
  (∑ n ∈ Finset.Ioc 0 ⌊Real.exp L⌋₊, primeAtomWeight n * g (Real.log n)) - ∫ y in (0:ℝ)..L, g y

private theorem trunc_integral {Y x : ℝ} (hx : x ∈ Icc 0 Y) (f : ℝ → ℝ) :
    (∫ y in (0:ℝ)..Y, (Ici x).indicator f y) = ∫ y in x..Y, f y := by
  have he : Icc 0 Y ∩ Ici x = Icc x Y := by
    ext v
    exact ⟨fun h => ⟨h.2,h.1.2⟩,fun h => ⟨⟨hx.1.trans h.1,h.2⟩,h.1⟩⟩
  rw [intervalIntegral.integral_of_le (hx.1.trans hx.2), ← integral_Icc_eq_integral_Ioc,
    setIntegral_indicator measurableSet_Ici, he, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le hx.2]

private theorem logAtom_mem {L : ℝ} {n : ℕ} (hn : n ∈ Finset.Ioc 0 ⌊Real.exp L⌋₊) :
    Real.log n ∈ Icc (0:ℝ) L := by
  obtain ⟨h,h'⟩ := Finset.mem_Ioc.mp hn
  have hn1 : 1 ≤ (n:ℝ) := by exact_mod_cast h
  exact ⟨Real.log_nonneg hn1, (Real.log_le_iff_le_exp (by linarith)).2
    ((Nat.le_floor_iff (Real.exp_pos _).le).1 h')⟩

private theorem remainder_product_interval {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b)
    {g' : ℝ → ℝ} (hg' : Continuous g') :
    IntervalIntegrable (fun y => logMertensRemainder y*g' y) volume a b :=
  ((intervalIntegrable_iff_integrableOn_Ioc_of_le hab).2
    (integrableOn_logMertensRemainder.mono_set (fun _ hy => ha.trans_lt hy.1))).mul_continuousOn
      hg'.continuousOn

/-- Centered Abel summation for smooth log tests. The constant is evaluated at the left endpoint. -/
theorem primeLogTest_abel {L : ℝ} (hL : 0 ≤ L) {g g' : ℝ → ℝ}
    (hd : ∀ y, HasDerivAt g (g' y) y) (hg' : Continuous g') :
    primeLogTest L g = mertensCenter*g 0 + logMertensRemainder L*g L -
      ∫ y in (0:ℝ)..L, logMertensRemainder y*g' y := by
  classical
  let s := Finset.Ioc 0 ⌊Real.exp L⌋₊
  let S := fun y => Zeta23.XiPrime.Mfun (Real.exp y)
  let h := fun (n : ℕ) (y:ℝ) => (Ici (Real.log n)).indicator (fun t => primeAtomWeight n*g' t) y
  have hg : Continuous g := continuous_iff_continuousAt.mpr fun y => (hd y).continuousAt
  have hfilter {y : ℝ} (hy : y ≤ L) :
      s.filter (fun n : ℕ => Real.log n ≤ y) = Finset.Ioc 0 ⌊Real.exp y⌋₊ := by
    ext n
    simp only [s, Finset.mem_filter, Finset.mem_Ioc]
    by_cases hn : 0 < n
    · have hnp : 0 < (n:ℝ) := by exact_mod_cast hn
      rw [Real.log_le_iff_le_exp hnp, ← Nat.le_floor_iff (Real.exp_pos y).le]
      exact ⟨fun e => ⟨hn,e.2⟩,fun e =>
        ⟨⟨hn,e.2.trans (Nat.floor_le_floor (Real.exp_le_exp.mpr hy))⟩,e.2⟩⟩
    · simp [hn]
  have hit (n : ℕ) : IntervalIntegrable (h n) volume 0 L := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hL]
    exact ((continuous_const.mul hg').intervalIntegrable (0:ℝ) L).1.indicator measurableSet_Ici
  have hsum {y : ℝ} (hy : y ≤ L) : (∑ n ∈ s, h n y) = S y*g' y := by
    dsimp only [h, S]
    simp only [Set.indicator_apply, Set.mem_Ici]
    rw [← Finset.sum_filter, hfilter hy, Zeta23.XiPrime.Mfun_eq_Ioc, Finset.sum_mul]
    rfl
  have hcalc : (∫ y in (0:ℝ)..L, S y*g' y) =
      S L*g L - ∑ n ∈ s, primeAtomWeight n*g (Real.log n) := by
    calc
      _ = ∫ y in (0:ℝ)..L, ∑ n ∈ s, h n y := by
        apply intervalIntegral.integral_congr
        intro y hy
        rw [uIcc_of_le hL] at hy
        exact (hsum hy.2).symm
      _ = ∑ n ∈ s, ∫ y in (0:ℝ)..L, h n y := intervalIntegral.integral_finsetSum (fun n _ => hit n)
      _ = ∑ n ∈ s, primeAtomWeight n*(g L-g (Real.log n)) := by
        apply Finset.sum_congr rfl
        intro n hn
        rw [show (∫ y in (0:ℝ)..L, h n y) = ∫ y in Real.log n..L, primeAtomWeight n*g' y
            from trunc_integral (logAtom_mem hn) _, intervalIntegral.integral_const_mul,
          intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hd x)
            (hg'.intervalIntegrable _ _)]
      _ = _ := by
        dsimp [S]
        rw [Zeta23.XiPrime.Mfun_eq_Ioc, Finset.sum_mul]
        simp only [mul_sub, Finset.sum_sub_distrib, s, primeAtomWeight]
  have hs (y : ℝ) : S y*g' y = g y+y*g' y + mertensCenter*g' y +
      logMertensRemainder y*g' y - g y := by
    dsimp [S,logMertensRemainder]
    ring
  have hfirst := intervalIntegral.integral_deriv_mul_eq_sub
    (a := (0:ℝ)) (b := L) (u := id) (u' := fun _ => 1) (v := g) (v' := g')
    (fun y _ => hasDerivAt_id y) (fun y _ => hd y)
    intervalIntegrable_const (hg'.intervalIntegrable _ _)
  simp only [one_mul, id_eq, zero_mul, sub_zero] at hfirst
  have hj : Continuous (fun y : ℝ => g y+y*g' y) := hg.add (continuous_id.mul hg')
  have hc : Continuous (fun y : ℝ => mertensCenter*g' y) := continuous_const.mul hg'
  have hr := remainder_product_interval (le_refl 0) hL hg'
  simp_rw [hs] at hcalc
  rw [intervalIntegral.integral_sub
      (f := fun y => g y+y*g' y+mertensCenter*g' y+logMertensRemainder y*g' y)
      (g := g) (((hj.add hc).intervalIntegrable 0 L).add hr)
      (hg.intervalIntegrable 0 L),
    intervalIntegral.integral_add (f := fun y => g y+y*g' y+mertensCenter*g' y)
      (g := fun y => logMertensRemainder y*g' y) ((hj.add hc).intervalIntegrable 0 L) hr,
    intervalIntegral.integral_add (f := fun y => g y+y*g' y)
      (g := fun y => mertensCenter*g' y) (hj.intervalIntegrable 0 L) (hc.intervalIntegrable 0 L),
    hfirst, intervalIntegral.integral_const_mul, intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun y _ => hd y) (hg'.intervalIntegrable _ _)] at hcalc
  change (∑ n ∈ s, primeAtomWeight n*g (Real.log n)) - _ = _
  have he : S L = L+mertensCenter+logMertensRemainder L := by dsimp [S,logMertensRemainder]; ring
  rw [he] at hcalc
  linarith

/-- A strip contributes at most the sum of its prime mass and its length times the test supremum. -/
private theorem primeLogTest_strip {a b H : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) {g : ℝ → ℝ}
    (hg : Continuous g) (hH : 0 ≤ H) (hbound : ∀ y ∈ Icc 0 b, |g y| ≤ H) :
    |primeLogTest b g - primeLogTest a g| ≤
      ((b-a)*2+2*Zeta23.XiPrime.KM)*H := by
  classical
  let s := Finset.Ioc 0 ⌊Real.exp a⌋₊
  let S := Finset.Ioc 0 ⌊Real.exp b⌋₊
  have hsub : s ⊆ S := Finset.Ioc_subset_Ioc_right (Nat.floor_le_floor (Real.exp_le_exp.mpr hab))
  have hp (n : ℕ) : 0 ≤ primeAtomWeight n :=
    div_nonneg ArithmeticFunction.vonMangoldt_nonneg (Nat.cast_nonneg _)
  have hdiff (f : ℕ → ℝ) : (∑ n ∈ S, f n) - ∑ n ∈ s, f n = ∑ n ∈ S \ s, f n := by
    have h := Finset.sum_sdiff (f := f) hsub
    linarith
  have hmass := hdiff primeAtomWeight
  have hm (x : ℝ) : (∑ n ∈ Finset.Ioc 0 ⌊Real.exp x⌋₊, primeAtomWeight n) =
      Zeta23.XiPrime.Mfun (Real.exp x) := (Zeta23.XiPrime.Mfun_eq_Ioc _).symm
  have ha' := Zeta23.XiPrime.abs_Mfun_sub_log_le (Real.one_le_exp ha)
  have hb' := Zeta23.XiPrime.abs_Mfun_sub_log_le (Real.one_le_exp (ha.trans hab))
  rw [Real.log_exp] at ha' hb'
  have hW : (∑ n ∈ S \ s, primeAtomWeight n) ≤ b-a+2*Zeta23.XiPrime.KM := by
    rw [← hmass, show S = Finset.Ioc 0 ⌊Real.exp b⌋₊ from rfl,
      show s = Finset.Ioc 0 ⌊Real.exp a⌋₊ from rfl, hm, hm]
    linarith only [(abs_le.mp ha').1, (abs_le.mp hb').2]
  have hsum : |∑ n ∈ S \ s, primeAtomWeight n*g (Real.log n)| ≤
      (b-a+2*Zeta23.XiPrime.KM)*H := calc
    _ ≤ ∑ n ∈ S \ s, |primeAtomWeight n*g (Real.log n)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ n ∈ S \ s, primeAtomWeight n*H := by
      apply Finset.sum_le_sum
      intro n hn
      rw [abs_mul, abs_of_nonneg (hp n)]
      exact mul_le_mul_of_nonneg_left (hbound _ (logAtom_mem (Finset.mem_sdiff.mp hn).1)) (hp n)
    _ ≤ _ := by rw [← Finset.sum_mul]; exact mul_le_mul_of_nonneg_right hW hH
  have hi : |∫ y in a..b, g y| ≤ (b-a)*H := by
    have h := intervalIntegral.norm_integral_le_of_norm_le_const (C := H)
      (f := g) (a := a) (b := b) (fun y hy => hbound y (by
        rw [uIoc_of_le hab] at hy
        exact ⟨ha.trans hy.1.le, hy.2⟩))
    simpa [Real.norm_eq_abs, abs_of_nonneg (sub_nonneg.mpr hab), mul_comm] using h
  have he : primeLogTest b g - primeLogTest a g =
      (∑ n ∈ S \ s, primeAtomWeight n*g (Real.log n)) - ∫ y in a..b, g y := by
    rw [← hdiff, primeLogTest, primeLogTest, ← intervalIntegral.integral_add_adjacent_intervals
      (hg.intervalIntegrable (0:ℝ) a) (hg.intervalIntegrable a b)]
    dsimp [s,S]
    ring
  rw [he]
  exact (abs_sub _ _).trans ((add_le_add hsum hi).trans_eq (by ring))

/-- Only the derivative on the interior enters the uniform test bound. The two unit strips
are estimated with their actual prime masses, including cutoff atoms. -/
theorem primeLogTest_uniform :
    ∃ C > (0 : ℝ), ∀ {L H J : ℝ} {g g' : ℝ → ℝ}, 2 ≤ L → 0 ≤ H → 0 ≤ J →
      (∀ y, HasDerivAt g (g' y) y) → Continuous g' →
      (∀ y ∈ Icc 0 L, |g y| ≤ H) → (∀ y ∈ Icc 1 (L-1), |g' y| ≤ J) →
      |primeLogTest L g| ≤ C*(H+J) := by
  obtain ⟨D,hD,hR⟩ := logMertensRemainder_inverse_square
  let V := ∫ y in Ioi (0:ℝ), |logMertensRemainder y|
  have hV : 0 ≤ V := integral_nonneg fun _ => abs_nonneg _
  let K := Zeta23.XiPrime.KM
  have hK : 0 ≤ K := Zeta23.XiPrime.KM_nonneg
  refine ⟨4+4*K+2*D+V, by positivity, fun {L H J g g'} hL hH hJ hd hgc hg hj => ?_⟩
  let b := L-1
  have hb : 1 ≤ b := by dsimp [b]; linarith
  have hbL : b ≤ L := by dsimp [b]; linarith
  have h0b : 0 ≤ b := by linarith
  have hc : Continuous g := continuous_iff_continuousAt.mpr fun y => (hd y).continuousAt
  have hzero : primeLogTest 0 g = 0 := by simp [primeLogTest, primeAtomWeight]
  have hleft := primeLogTest_strip (a := 0) (b := 1) le_rfl zero_le_one hc hH
    (fun y hy => hg _ ⟨hy.1, by linarith [hy.2]⟩)
  have hright := primeLogTest_strip h0b hbL hc hH hg
  have hr (y : ℝ) (hy : 0 ≤ y) : |logMertensRemainder y| ≤ D :=
    (hR y hy).trans (div_le_self hD.le (by nlinarith [sq_nonneg y]))
  have he (y : ℝ) (hy : y ∈ Icc 0 L) : |logMertensRemainder y*g y| ≤ D*H := by
    rw [abs_mul]
    exact mul_le_mul (hr y hy.1) (hg y hy) (abs_nonneg _) hD.le
  have hint : |∫ y in (1:ℝ)..b, logMertensRemainder y*g' y| ≤ J*V := by
    have hi := remainder_product_interval zero_le_one hb hgc
    have hab : IntegrableOn (fun y => |logMertensRemainder y|) (Ioi 0) :=
      integrableOn_logMertensRemainder.abs
    have hsmall : Ioc 1 b ⊆ Ioi (0:ℝ) := fun _ hy => zero_lt_one.trans hy.1
    calc
      _ ≤ ∫ y in (1:ℝ)..b, |logMertensRemainder y*g' y| :=
        intervalIntegral.abs_integral_le_integral_abs hb
      _ ≤ ∫ y in Ioi (0:ℝ), J*|logMertensRemainder y| := by
        rw [intervalIntegral.integral_of_le hb]
        apply (integral_mono_ae hi.1.abs ((hab.mono_set hsmall).const_mul J) ?_).trans
          (setIntegral_mono_set (hab.const_mul J) (Eventually.of_forall fun _ => by positivity)
            (Eventually.of_forall fun _ h => hsmall h))
        filter_upwards [ae_restrict_mem measurableSet_Ioc] with y hy
        rw [abs_mul,mul_comm]
        exact mul_le_mul_of_nonneg_right (hj y ⟨hy.1.le,hy.2⟩) (abs_nonneg _)
      _ = _ := integral_const_mul _ _
  have hmid : primeLogTest b g - primeLogTest 1 g =
      logMertensRemainder b*g b - logMertensRemainder 1*g 1 -
        ∫ y in (1:ℝ)..b, logMertensRemainder y*g' y := by
    rw [primeLogTest_abel h0b hd hgc, primeLogTest_abel zero_le_one hd hgc,
      ← intervalIntegral.integral_add_adjacent_intervals
        (remainder_product_interval (le_refl 0) zero_le_one hgc)
        (remainder_product_interval zero_le_one hb hgc)]
    ring
  have hp := (abs_sub _ _).trans (add_le_add
    ((abs_sub _ _).trans (add_le_add (he b ⟨h0b,hbL⟩) (he 1 ⟨zero_le_one,by linarith⟩))) hint)
  rw [← hmid] at hp
  rw [hzero, sub_zero] at hleft
  calc
    _ = |(primeLogTest L g-primeLogTest b g) + (primeLogTest b g-primeLogTest 1 g) +
          primeLogTest 1 g| := by ring_nf
    _ ≤ (|primeLogTest L g-primeLogTest b g|+|primeLogTest b g-primeLogTest 1 g|) +
          |primeLogTest 1 g| :=
      (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ _ := by
      dsimp [b,K] at *
      nlinarith only [hright,hp,hleft,mul_nonneg hH hV,mul_nonneg hJ hK,mul_nonneg hJ hD.le,hJ]

end RiemannResearch.Analysis.MontgomeryPrimeTrace
