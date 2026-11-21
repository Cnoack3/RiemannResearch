import RiemannResearch.Analysis.LogarithmicPrimePairTriangle
import RiemannResearch.Analysis.LogarithmicPrimePairSieve
import RiemannResearch.Analysis.ActualZeroLoglogRate
import RiemannResearch.Analysis.ActualConsecutiveTripleFourier
import RiemannResearch.Analysis.MangoldtCumulativeDivergence
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Actual logarithmic pair weights tested on rational FMZ modes

The multiplicative character attached to the pair (n,n+h) has frequency
log((n+h)/n). Its value at the identity is one. For 0<h<n the ratio is
strictly between one and two, and its rational Landau main term vanishes.
This applies to all prime powers in the original observable.

The uniform estimate used below is the repository's rational-mode extension
of Ford–Meng–Zaharescu, https://arxiv.org/abs/1511.06814.
-/
noncomputable section
open Finset Filter
open scoped BigOperators Topology ArithmeticFunction
namespace RiemannResearch.Analysis.LogarithmicPrimePairs
open ActualZeroOrdinate

private abbrev block (A B X : ℝ) := Ioc ⌊A*X⌋₊ ⌊B*X⌋₊

def pairCoefficient (u X : ℝ) (n h : ℕ) : ℝ :=
  (u-(h:ℝ)/Real.log X) * Λ n * Λ (n+h) / (X*Real.log X)

def pairModeTest (A B u X : ℝ) (f : ℕ → ℕ → ℂ) : ℂ :=
  ∑ h ∈ Ioc 0 (shiftWidth u X), ∑ n ∈ block A B X, (pairCoefficient u X n h : ℂ) * f (n+h) n

def pairModeMass (A B u X : ℝ) : ℝ :=
  ∑ h ∈ Ioc 0 (shiftWidth u X), ∑ n ∈ block A B X,
    |pairCoefficient u X n h| * rationalModeWeight (n+h) n ^ 2

private theorem sum_coefficients (A B u X : ℝ) :
    (∑ h ∈ Ioc 0 (shiftWidth u X), ∑ n ∈ block A B X, pairCoefficient u X n h) =
    trianglePairAverage A B u X := by
  simp only [trianglePairAverage, pairBlock, pairCoefficient, block, sum_div, mul_sum, mul_assoc]

theorem abs_triangle_le_pairModeMass (A B u X : ℝ) :
    |trianglePairAverage A B u X| ≤ pairModeMass A B u X := by
  rw [← sum_coefficients]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum ?_)
  intro h _
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum ?_)
  intro n _
  have hw : 1 ≤ rationalModeWeight (n+h) n := le_add_of_nonneg_right (abs_nonneg _)
  have hsq : 1 ≤ rationalModeWeight (n+h) n ^ 2 := by nlinarith [sq_nonneg (rationalModeWeight (n+h) n-1)]
  exact le_mul_of_one_le_right (abs_nonneg _) hsq

/-- Evaluation at the identity of the prime torus retains the entire arithmetic mass. -/
theorem pairModeTest_at_identity (A B u X : ℝ) :
    pairModeTest A B u X (fun _ _ => 1) = (trianglePairAverage A B u X : ℂ) := by
  rw [← sum_coefficients]
  simp [pairModeTest]

theorem rational_main_short_shift {n h : ℕ} (hh : 0 < h) (hn : h < n) :
    rationalFMZMain (n+h) n = 0 := by
  have hlt : n < n+h := by omega
  have hnd : ¬ n ∣ n+h := by
    intro hd
    have hd' : n ∣ h := by simpa using hd
    exact (not_le.mpr hn) (Nat.le_of_dvd hh hd')
  simp [rationalFMZMain, hlt,
    rationalLandauMain_eq_vonMangoldt_div_sqrt (by omega : 1 ≤ n) hlt, hnd]

private theorem eventually_short {A u : ℝ} (hA : 0 < A) (hu : 0 < u) :
    ∀ᶠ X : ℝ in atTop, (shiftWidth u X : ℝ) < A*X := by
  have hl : Tendsto (fun X : ℝ => Real.log X / X) atTop (𝓝 0) := by
    simpa using Real.tendsto_pow_log_div_pow_atTop (1:ℝ) 1 (by norm_num)
  filter_upwards [(hl.const_mul u).eventually (eventually_lt_nhds
    (show u*0 < A by simpa using hA)), eventually_gt_atTop (1:ℝ)] with X hx hX
  have hp : 0 < X := by linarith
  have hlt : u*Real.log X < A*X := (div_lt_iff₀ hp).mp (by simpa [mul_div_assoc] using hx)
  exact (Nat.floor_le (mul_pos hu (Real.log_pos hX)).le).trans_lt hlt

/-- The FMZ main functional is identically zero on this family once the
logarithmic shift is shorter than the first site. -/
theorem eventually_pairModeTest_main_zero {A u : ℝ} (hA : 0 < A) (B : ℝ) (hu : 0 < u) :
    ∀ᶠ X : ℝ in atTop, pairModeTest A B u X rationalFMZMain = 0 := by
  filter_upwards [eventually_short hA hu] with X hshort
  apply sum_eq_zero
  intro h hh
  apply sum_eq_zero
  intro n hn
  have hn' := (mem_Ioc.mp hn).1
  have hh' := (mem_Ioc.mp hh).2
  have hc : shiftWidth u X ≤ ⌊A*X⌋₊ := Nat.le_floor hshort.le
  rw [rational_main_short_shift (mem_Ioc.mp hh).1 (by omega), mul_zero]

private theorem coefficient_nonneg {u X : ℝ} (hu : 0 < u) (hX : 1 < X) (n h : ℕ)
    (hh : h ∈ Ioc 0 (shiftWidth u X)) : 0 ≤ pairCoefficient u X n h := by
  have hl := Real.log_pos hX
  have hh' : (h:ℝ) ≤ u*Real.log X :=
    (show (h:ℝ) ≤ shiftWidth u X by exact_mod_cast (mem_Ioc.mp hh).2).trans
    (Nat.floor_le (mul_pos hu hl).le)
  exact div_nonneg (mul_nonneg (mul_nonneg (sub_nonneg.mpr ((div_le_iff₀ hl).mpr hh'))
    ArithmeticFunction.vonMangoldt_nonneg) ArithmeticFunction.vonMangoldt_nonneg)
    (mul_nonneg (by linarith) hl.le)

private theorem height_sq_le {A B u X : ℝ} (hB : 0 < B) (hu : 0 < u)
    (hX : 1 < X) (hL : 1 ≤ Real.log X) (hbig : B + u ≤ X)
    {n h : ℕ} (hn : n ∈ block A B X) (hh : h ∈ Ioc 0 (shiftWidth u X)) :
    rationalModeWeight (n+h) n ^ 2 ≤ (5*Real.log X)^2 := by
  let L := Real.log X
  let H := shiftWidth u X
  have hx : 0 < X := by linarith
  have hH : (H:ℝ) ≤ u*L := Nat.floor_le (mul_pos hu (Real.log_pos hX)).le
  change 1 ≤ L at hL
  have nh := (mem_Ioc.mp hn).2
  have nlo := (mem_Ioc.mp hn).1
  have hh' := (mem_Ioc.mp hh).2
  have hmax : (n:ℝ)+h ≤ X^2 := calc
    _ ≤ (⌊B*X⌋₊:ℝ)+(H:ℝ) := by exact_mod_cast Nat.add_le_add nh hh'
    _ ≤ B*X+u*L := add_le_add (Nat.floor_le (mul_pos hB hx).le) hH
    _ ≤ (B+u)*X := by nlinarith [mul_le_mul_of_nonneg_left (Real.log_le_self hx.le) hu.le]
    _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_right hbig hx.le]
  have hlg (m : ℕ) (hm : 1 ≤ m) (hm' : (m:ℝ) ≤ X^2) :
      0 ≤ Real.log m ∧ Real.log m ≤ 2*L :=
    ⟨Real.log_nonneg (by exact_mod_cast hm),
      (Real.log_le_log (by exact_mod_cast (show 0 < m by omega)) hm').trans_eq
        (by rw [Real.log_pow]; norm_num [L])⟩
  have hln := hlg n (by omega) (by linarith [Nat.cast_nonneg (α := ℝ) h])
  have hlm := hlg (n+h) (by omega) (by push_cast; exact hmax)
  have hw : rationalModeWeight (n+h) n ≤ 5*L := by
    unfold rationalModeWeight
    rw [abs_of_nonneg (add_nonneg hlm.1 hln.1)]
    linarith
  have hw0 : 0 ≤ rationalModeWeight (n+h) n := by unfold rationalModeWeight; positivity
  exact pow_le_pow_left₀ hw0 hw 2

/-- The squared rational heights cost at most two powers of the logarithm
relative to the actual value of the pair polynomial at the identity. -/
theorem eventually_pairModeMass_le_triangle (A : ℝ) {B u : ℝ} (hB : 0 < B) (hu : 0 < u) :
    ∀ᶠ X : ℝ in atTop, pairModeMass A B u X ≤ (5*Real.log X)^2*trianglePairAverage A B u X := by
  filter_upwards [eventually_gt_atTop (1:ℝ),Real.tendsto_log_atTop.eventually_ge_atTop 1,
    eventually_ge_atTop (B+u)] with X hX hL hbig
  rw [← sum_coefficients]
  simp only [pairModeMass,mul_sum]
  apply sum_le_sum
  intro h hh
  apply sum_le_sum
  intro n hn
  have hc := coefficient_nonneg hu hX n h hh
  rw [abs_of_nonneg hc,mul_comm ((5*Real.log X)^2)]
  exact mul_le_mul_of_nonneg_left (height_sq_le hB hu hX hL hbig hn hh) hc

private theorem triangle_le_width_sharp (A B u : ℝ) {X : ℝ} (hX : 1 < X) :
    trianglePairAverage A B u X ≤ u*sharpPairAverage A B u X := by
  have hl := Real.log_pos hX
  unfold trianglePairAverage sharpPairAverage
  rw [sum_comm (s := Ioc ⌊A*X⌋₊ ⌊B*X⌋₊), ← mul_div_assoc, mul_sum]
  apply div_le_div_of_nonneg_right _ (mul_nonneg (by linarith) hl.le)
  apply sum_le_sum
  intro h _
  exact mul_le_mul_of_nonneg_right (sub_le_self _ (div_nonneg (Nat.cast_nonneg _) hl.le))
    (pairBlock_nonneg A B X h)

/-- The prime-only upper sieve reduces the cubic Fourier-mass bound to a quadratic one. -/
theorem eventually_pairModeMass_sq_of_sieve (published : GPYPrimePairSieve)
    {A B u : ℝ} (hA : 0 < A) (hAB : A < B) (hu : 0 < u) :
    ∃ C > (0:ℝ), ∀ᶠ X : ℝ in atTop, pairModeMass A B u X ≤ C*(Real.log X)^2 := by
  obtain ⟨M,hM,hm⟩ := eventually_sharp_bounded_of_sieve published hA hAB hu
  refine ⟨25*u*M,by positivity, ?_⟩
  filter_upwards [hm,eventually_pairModeMass_le_triangle A (hA.trans hAB) hu,
    eventually_gt_atTop (1:ℝ)] with X hs hT hX
  have ht := (triangle_le_width_sharp A B u hX).trans (mul_le_mul_of_nonneg_left hs hu.le)
  exact hT.trans ((mul_le_mul_of_nonneg_left ht (sq_nonneg _)).trans_eq (by ring))

/-- A single PNT bound pays for one Mangoldt factor in the weighted Fourier mass. -/
theorem eventually_pairModeMass_le (A : ℝ) {B u : ℝ} (hB : 0 < B) (hu : 0 < u) :
    ∀ᶠ X : ℝ in atTop, pairModeMass A B u X ≤ (100*B*u^2)*(Real.log X)^3 := by
  have hpsi := (MangoldtCumulativeDivergence.psi_ratio_tendsto.comp
    (tendsto_id.const_mul_atTop hB)).eventually (eventually_lt_nhds (by norm_num : (1:ℝ)<2))
  filter_upwards [hpsi, eventually_window_mangoldt hB hu, eventually_gt_atTop (1:ℝ),
    Real.tendsto_log_atTop.eventually_ge_atTop 1, eventually_ge_atTop (B+u)]
    with X hsum hΛ hX hL hbig
  let L := Real.log X
  let H := shiftWidth u X
  have hx : 0 < X := by linarith
  have hl : 0 < L := Real.log_pos hX
  change 1 ≤ L at hL
  have hH : (H:ℝ) ≤ u*L := Nat.floor_le (mul_pos hu hl).le
  have hprefix : (∑ n ∈ block A B X, Λ n) ≤ 2*(B*X) := by
    have hsub : block A B X ⊆ Icc 0 ⌊B*X⌋₊ :=
      fun n hn => mem_Icc.mpr ⟨Nat.zero_le n,(mem_Ioc.mp hn).2⟩
    have hle := sum_le_sum_of_subset_of_nonneg (f := fun n => Λ n) hsub
      (fun _ _ _ => ArithmeticFunction.vonMangoldt_nonneg)
    change Chebyshev.psi (B*X)/(B*X) < 2 at hsum
    rw [← Chebyshev.psi_eq_sum_Icc] at hle
    exact hle.trans ((div_lt_iff₀ (mul_pos hB hx)).mp hsum).le
  have hpoint (h : ℕ) (hh : h ∈ Ioc 0 H) (n : ℕ) (hn : n ∈ block A B X) :
      |pairCoefficient u X n h| * rationalModeWeight (n+h) n ^ 2 ≤
        (2*u/X)*(5*L)^2 * Λ n := by
    have nh := (mem_Ioc.mp hn).2
    have hh' := (mem_Ioc.mp hh).2
    have hweight := height_sq_le hB hu hX hL hbig hn hh
    have hcn := coefficient_nonneg hu hX n h hh
    have hcap : Λ (n+h) ≤ 2*L := hΛ _ (Nat.add_le_add nh hh')
    have hw' : u-(h:ℝ)/L ≤ u := sub_le_self _ (div_nonneg (Nat.cast_nonneg _) hl.le)
    have hfirst : pairCoefficient u X n h ≤ (2*u/X)*Λ n := by
      unfold pairCoefficient
      apply (div_le_iff₀ (mul_pos hx hl)).mpr
      calc
        _ ≤ (u*Λ n)*(2*L) :=
          mul_le_mul (mul_le_mul_of_nonneg_right hw' ArithmeticFunction.vonMangoldt_nonneg)
            hcap ArithmeticFunction.vonMangoldt_nonneg
              (mul_nonneg hu.le ArithmeticFunction.vonMangoldt_nonneg)
        _ = _ := by dsimp only [L]; field_simp [hx.ne']
    rw [abs_of_nonneg hcn]
    calc
      _ ≤ ((2*u/X)*Λ n)*(5*L)^2 := mul_le_mul hfirst
        hweight (sq_nonneg _) (mul_nonneg (by positivity) ArithmeticFunction.vonMangoldt_nonneg)
      _ = _ := by ring
  let D := (2*u/X)*(5*L)^2
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hr (h : ℕ) (hh : h ∈ Ioc 0 H) :
      (∑ n ∈ block A B X, |pairCoefficient u X n h| * rationalModeWeight (n+h) n ^ 2) ≤
        D*(2*(B*X)) := by
    calc
      _ ≤ ∑ n ∈ block A B X, D*Λ n := sum_le_sum (hpoint h hh)
      _ = _ := (mul_sum ..).symm
      _ ≤ _ := mul_le_mul_of_nonneg_left hprefix hD
  calc
    _ ≤ ∑ _h ∈ Ioc 0 H, D*(2*(B*X)) := sum_le_sum hr
    _ = (H:ℝ)*(D*(2*(B*X))) := by simp
    _ ≤ (u*L)*(D*(2*(B*X))) := mul_le_mul_of_nonneg_right hH (by positivity)
    _ = _ := by dsimp [D,L]; field_simp [hx.ne']; ring

/-- Uniform FMZ domination applied to the actual, normalized, moving pair coefficients. -/
theorem eventually_sampled_pairs_le_mass {A B u : ℝ} (hA : 0 < A) (hu : 0 < u)
    (T : ℝ → ℝ) (hT : Tendsto T atTop atTop) :
    ∃ K > (0:ℝ), ∀ᶠ X : ℝ in atTop,
      ‖pairModeTest A B u X (fun m n => ordinateSum (T X) (Real.log ((m:ℝ)/n))/(T X : ℂ))‖ ≤
        (K*horizontalLogRate (T X))*pairModeMass A B u X := by
  obtain ⟨K,hK,hbound⟩ := eventually_centeredRationalOrdinate_remainder_loglog
  refine ⟨K,hK, ?_⟩
  filter_upwards [hT.eventually hbound,eventually_short hA hu] with X hb hshort
  have hc : shiftWidth u X ≤ ⌊A*X⌋₊ := Nat.le_floor hshort.le
  unfold pairModeTest pairModeMass
  simp only [mul_sum]
  refine (_root_.norm_sum_le _ _).trans (sum_le_sum ?_)
  intro h hh
  refine (_root_.norm_sum_le _ _).trans (sum_le_sum ?_)
  intro n hn
  have hn' := (mem_Ioc.mp hn).1
  obtain ⟨hh0,hh1⟩ := mem_Ioc.mp hh
  have hne : n+h ≠ n := by omega
  have he := hb (n+h) n (by omega) (by omega)
  rw [rational_main_short_shift hh0 (by omega), sub_zero] at he
  simp only [centeredRationalOrdinate, if_neg hne, sub_zero] at he
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  exact (mul_le_mul_of_nonneg_left he (abs_nonneg _)).trans_eq (by ring)

/-- Even at height exp X the ordinate functional tends to zero. The value
at the identity of the same test is the triangular prime-pair statistic. -/
theorem tendsto_sampled_pairs_exp {A B u : ℝ} (hA : 0 < A) (hAB : A < B) (hu : 0 < u) :
    Tendsto (fun X : ℝ => pairModeTest A B u X
      (fun m n => ordinateSum (Real.exp X) (Real.log ((m:ℝ)/n))/(Real.exp X:ℂ)))
      atTop (𝓝 0) := by
  obtain ⟨K,hK,h⟩ := eventually_sampled_pairs_le_mass (B := B) hA hu Real.exp Real.tendsto_exp_atTop
  have hlog : Tendsto (fun X : ℝ => (Real.log X)^5/X) atTop (𝓝 0) := by
    simpa using Real.tendsto_pow_log_div_pow_atTop (1:ℝ) 5 (by norm_num)
  have lim := hlog.const_mul (K*(100*B*u^2))
  rw [mul_zero] at lim
  apply squeeze_zero_norm' _ lim
  filter_upwards [h, eventually_pairModeMass_le A (hA.trans hAB) hu, eventually_gt_atTop (1:ℝ)]
    with X hb hm hX
  rw [horizontalLogRate, Real.log_exp] at hb
  refine hb.trans ((mul_le_mul_of_nonneg_left hm (by positivity)).trans_eq ?_)
  ring


/-- With the prime-only upper sieve, every height exp((log X)^(2+ε)) suffices for
the moving rational pair test. -/
theorem tendsto_sampled_pairs_logPower_of_sieve (published : GPYPrimePairSieve)
    {A B u ε : ℝ} (hA : 0 < A) (hAB : A < B) (hu : 0 < u) (hε : 0 < ε) :
    let T := fun X : ℝ => Real.exp ((Real.log X) ^ (2 + ε))
    Tendsto (fun X : ℝ => pairModeTest A B u X (fun m n =>
      ordinateSum (T X) (Real.log ((m : ℝ) / n)) / (T X : ℂ))) atTop (𝓝 0) := by
  intro T
  have hT : Tendsto T atTop atTop :=
    Real.tendsto_exp_atTop.comp ((tendsto_rpow_atTop (by linarith : 0 < 2 + ε)).comp
      Real.tendsto_log_atTop)
  obtain ⟨K, hK, hb⟩ := eventually_sampled_pairs_le_mass (B := B) hA hu T hT
  obtain ⟨C, hC, hm⟩ := eventually_pairModeMass_sq_of_sieve published hA hAB hu
  have hsmall := (Real.tendsto_pow_log_div_pow_atTop ε 2 hε).comp Real.tendsto_log_atTop
  have lim := hsmall.const_mul (K * C * (2 + ε)^2)
  rw [mul_zero] at lim
  apply squeeze_zero_norm' _ lim
  filter_upwards [hb, hm, eventually_gt_atTop (1 : ℝ)] with X hbound hmass hX
  have hL := Real.log_pos hX
  have hpow := Real.rpow_pos_of_pos hL ε
  have hlarge := Real.rpow_pos_of_pos hL (2 + ε)
  have hr : 0 ≤ horizontalLogRate (T X) := by
    dsimp [T, horizontalLogRate]
    rw [Real.log_exp]
    exact div_nonneg (sq_nonneg _) hlarge.le
  refine hbound.trans ((mul_le_mul_of_nonneg_left hmass (mul_nonneg hK.le hr)).trans_eq ?_)
  change K * horizontalLogRate (T X) * (C * (Real.log X)^2) =
    K * C * (2 + ε)^2 * ((Real.log (Real.log X))^2 / (Real.log X)^ε)
  dsimp [horizontalLogRate, T]
  rw [Real.log_exp, Real.log_rpow hL, Real.rpow_add hL, Real.rpow_two]
  field_simp [hL.ne', hpow.ne'] <;> ring_nf <;> norm_num [Real.rpow_two]

/-- At fixed X, splitting the rational frequency arbitrarily among three
consecutive ordinates gives the same zero main term under the gap-energy hypothesis. -/
theorem tendsto_fixed_triple_test_of_gap (A B u X : ℝ)
    (hshort : shiftWidth u X ≤ ⌊A*X⌋₊) (a b : ℕ → ℕ → ℝ) (hg : VanishingCutoffGapEnergy) :
    Tendsto (fun T : ℝ => pairModeTest A B u X (fun m n =>
      interiorTriplePhaseSum T (a m n) (b m n) (Real.log ((m:ℝ)/n)-a m n-b m n)/(T:ℂ)))
      atTop (𝓝 0) := by
  have hs (n h : ℕ) (hn : n ∈ block A B X) (hh : h ∈ Ioc 0 (shiftWidth u X)) :
      Tendsto (fun T : ℝ =>
        (pairCoefficient u X n h : ℂ) * (interiorTriplePhaseSum T (a (n+h) n) (b (n+h) n)
          (Real.log ((↑(n+h):ℝ)/n)-a (n+h) n-b (n+h) n)/(T:ℂ))) atTop (𝓝 0) := by
    obtain ⟨hh0,hh1⟩ := mem_Ioc.mp hh
    have hn' := (mem_Ioc.mp hn).1
    have he := tendsto_interiorTriple_rational_of_gap (n := n+h) (m := n)
      (by omega) (by omega) (by omega)
      (a (n+h) n) (b (n+h) n) (Real.log ((↑(n+h):ℝ)/n)-a (n+h) n-b (n+h) n) (by ring) hg
    rw [rational_main_short_shift hh0 (by omega)] at he
    simpa using he.const_mul (pairCoefficient u X n h : ℂ)
  simpa [pairModeTest] using tendsto_finsetSum (Ioc 0 (shiftWidth u X)) (fun h hh =>
    tendsto_finsetSum (block A B X) (fun n hn => hs n h hn hh))

end RiemannResearch.Analysis.LogarithmicPrimePairs
