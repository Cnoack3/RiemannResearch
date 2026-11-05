/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.RH.QCofinalProfileTransfer
import RiemannResearch.Analysis.CofinalLogCutoffs
import RiemannResearch.NumberTheory.PrimeNumberTheorem.MertensStretchedDecay
import RiemannResearch.Analysis.StretchedExponentialBounds
import RiemannResearch.RH.CanonicalMobiusLogEnvelopeEnergy
import RiemannResearch.RH.CanonicalMobiusStretchedEnergy
import RiemannResearch.Analysis.MertensExponentialEntropy
import RiemannResearch.RH.QCofinalDisplacementMoments

/-!
# Preservation of the quantitative unconditional Mertens rate

The positive finite probe uses heads just below the square-root scale. Every
coefficient strictly below `a (1 / 2) ^ (1 / 11)` follows for any input Mertens
coefficient `a` at the shifted iterated-logarithmic profile.
-/
noncomputable section
open Filter
open scoped Topology BigOperators ENNReal
namespace RiemannResearch.RH.QMertensFirstMoment
open ZetaTwoHilbert QAnnihilatorTailEscape Pareto RiemannResearch.Analysis
open RiemannResearch.NumberTheory.PrimeNumberTheorem

/-- The harmonic cutoff `ceil(1 / ε)` gives an entropy-sized loss uniformly
over every physical site for any relative Mertens bound `ε`. -/
theorem abs_defect_le_mertens_entropy_slope (N : ℕ) (hN : 0<N) (ε : ℝ) (hε : 0<ε)
    (hε1 : ε ≤ 1) (hsmall : ε * (1 + Real.log (1 / ε)) ≤ 1 / 2)
    (hM : ∀ y : ℝ, (N : ℝ) ≤ y → |M y| ≤ ε * y) (n : ℕ) :
    |qSequence (defect N) n| ≤ (2 / (N : ℝ) + 8 * (ε * (1 + Real.log (1 / ε)))) * n := by
  let K : ℕ := ⌈1 / ε⌉₊
  let E := ε * (1 + Real.log (1 / ε))
  have hN0 : (0 : ℝ)<N := by exact_mod_cast hN
  have hεi : (1 : ℝ) ≤ 1 / ε := (le_div_iff₀ hε).mpr (by simpa using hε1)
  have hlog : 0 ≤ Real.log (1 / ε) := Real.log_nonneg hεi
  have hE : ε ≤ E := by dsimp [E]; nlinarith only [mul_nonneg hε.le hlog]
  have hKlo : 1 / ε ≤ (K : ℝ) := Nat.le_ceil _
  have hKhi : (K : ℝ) ≤ 2 * (1 / ε) := by
    have hk : (K : ℝ) ≤ 1 / ε + 1 := (Nat.ceil_lt_add_one (one_div_pos.mpr hε).le).le
    linarith only [hk,hεi]
  have hK0 : (0 : ℝ)<K := (one_div_pos.mpr hε).trans_le hKlo
  have hKlog := Real.log_le_log hK0 hKhi
  rw [Real.log_mul (by norm_num : (2 : ℝ)≠0) (one_div_pos.mpr hε).ne'] at hKlog
  have hlog2 := Real.log_le_sub_one_of_pos (by norm_num : 0 < (2 : ℝ))
  have hHar : (harmonic K : ℝ) + 1 ≤ 3 * (1 + Real.log (1 / ε)) := by
    linarith only [harmonic_le_one_add_log K,hKlog,hlog2,hlog]
  have hHm := (canonicalMobius_energy_of_uniform_mertens_log N hN ε hε hε1 hsmall hM).1
  have hnat : ∀ t : ℕ, N ≤ t → |∑ d ∈ Finset.Icc 1 t,
      (ArithmeticFunction.moebius d : ℝ)| ≤ ε * (t : ℝ) := by
    intro t hNt
    have hi := M_nat_difference 0 t (Nat.zero_le t)
    have hset : Finset.Ioc 0 t = Finset.Icc 1 t := by
      ext d
      simp only [Finset.mem_Ioc, Finset.mem_Icc]
      omega
    have hzero : M (0 : ℝ) = 0 := by
      have hz : Finset.Iic (0 : ℕ) = {0} := by ext n; simp
      simp [M, hz]
    rw [hset, Nat.cast_zero, hzero, sub_zero] at hi
    rw [← hi]
    exact hM _ (by exact_mod_cast hNt)
  obtain rfl | hn := Nat.eq_zero_or_pos n
  · simp
  have hd : qSequence (defect N) n = 1 - Pareto.canonicalMobiusHead N n := by
    change qSequenceLinear (qOne - QMobiusExactHead.exactHead N) n = _
    rw [map_sub]
    change qSequence qOne n - qSequence (QMobiusExactHead.exactHead N) n = _
    rw [QMobiusExactHead.exactHead_sequence]
    simp [qOneSequence, hn.ne']
  by_cases hhead : n ≤ N
  · rw [hd, canonicalMobiusHead_exact N n hn hhead, sub_self, abs_zero]
    have hE0 : 0 ≤ ε * (1 + Real.log (1 / ε)) := hε.le.trans hE
    positivity
  have hnN : (N : ℝ) ≤ n := by exact_mod_cast (show N ≤ n by omega)
  have hconst : 2 ≤ (2 / (N : ℝ)) * (n : ℝ) := by
    simpa only [div_mul_cancel₀ _ hN0.ne'] using
      mul_le_mul_of_nonneg_left hnN (show 0 ≤ 2 / (N : ℝ) by positivity)
  by_cases hnear : n ≤ K * N
  · have hw := canonicalMobiusHead_harmonic_window_bound N n K ε (5 * E) hε.le
      (mul_nonneg (by norm_num) (hε.le.trans hE)) (by omega) hnear hnat hHm
    rw [hd]
    have hatt : |1-canonicalMobiusHead N n| ≤ 1+|canonicalMobiusHead N n| := by
      simpa only [sub_eq_add_neg, abs_neg, abs_one] using abs_add_le (1 : ℝ) (-(canonicalMobiusHead N n))
    have hH : ε * ((harmonic K : ℝ) + 1) ≤ 3 * E := by
      dsimp only [E]; nlinarith only [mul_le_mul_of_nonneg_left hHar hε.le]
    change _ ≤ (2 / (N : ℝ) + 8 * E) * (n : ℝ)
    nlinarith only [hatt,hw,mul_le_mul_of_nonneg_left hH (Nat.cast_nonneg n),hconst]
  · have hKN : (K : ℝ) * (N : ℝ) ≤ n := by exact_mod_cast (show K * N ≤ n by omega)
    have hKN' := (mul_le_mul_of_nonneg_right hKlo hN0.le).trans hKN
    have hNr : (N : ℝ) / ε ≤ n := by
      calc
        _ = (1 / ε) * (N : ℝ) := by ring
        _ ≤ _ := hKN'
    have ha := (div_le_iff₀ hε).mp hNr
    change _ ≤ (2 / (N : ℝ) + 8 * E) * (n : ℝ)
    nlinarith only [abs_defect_le_three_mul N n hN,ha,hconst,
      mul_le_mul_of_nonneg_right hE (Nat.cast_nonneg n),mul_nonneg hε.le (Nat.cast_nonneg n)]

end RiemannResearch.RH.QMertensFirstMoment
namespace RiemannResearch.RH.QSquarefreeDisplacementRigidity
open ZetaTwoHilbert QAnnihilatorTailEscape RiemannResearch.Analysis
open RiemannResearch.Analysis.CofinalMoments RiemannResearch.NumberTheory.PrimeNumberTheorem

local notation "Pₛ" => (fun x : ℝ => logProductPower (1 / 11) (6 + Real.log x))

private theorem real_psi_tendsto : Tendsto Pₛ atTop atTop :=
  (tendsto_logProductPower_atTop (1 / 11) (by norm_num)).comp
    (tendsto_atTop_add_const_left atTop 6 Real.tendsto_log_atTop)

private theorem eventually_sharp_stretched_slope (a c C : ℝ) (hc : 0<c) (hca : c<a)
    (hM : ∀ᶠ x : ℝ in atTop, |M x| ≤ (C * Real.exp (-a * Pₛ x)) * x) :
    ∀ᶠ N : ℕ in atTop, ∀ n : ℕ, |qSequence (defect N) n| ≤ (n : ℝ) * Real.exp (-c * Pₛ (N : ℝ)) := by
  obtain ⟨d, hcd, hda⟩ := exists_between hca
  have hd : 0<d := hc.trans hcd
  have hD : Tendsto (fun x : ℝ => Real.exp ((a-d) * Pₛ x)) atTop atTop :=
    Real.tendsto_exp_atTop.comp (Tendsto.const_mul_atTop (sub_pos.mpr hda) real_psi_tendsto)
  have hM' : ∀ᶠ x : ℝ in atTop, |M x| ≤ Real.exp (-d * Pₛ x) * x := by
    filter_upwards [hM, hD.eventually (eventually_ge_atTop C), eventually_ge_atTop (0 : ℝ)] with x hx hC hx0
    refine hx.trans (mul_le_mul_of_nonneg_right ?_ hx0)
    calc
      _ ≤ Real.exp ((a-d) * Pₛ x) * Real.exp (-a * Pₛ x) := mul_le_mul_of_nonneg_right hC (Real.exp_pos _).le
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  obtain ⟨x₀,hx₀⟩ := eventually_atTop.1 hM'
  have hnat : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hP : Tendsto (fun N : ℕ => Pₛ (N : ℝ)) atTop atTop := real_psi_tendsto.comp hnat
  have hlog := Real.tendsto_log_atTop.comp hnat
  have hL : Tendsto (fun N : ℕ => 6 + Real.log (N : ℝ)) atTop atTop := tendsto_atTop_add_const_left atTop 6 hlog
  have hPL := (tendsto_logProductPower_div_self (1 / 11) (by norm_num) (by norm_num)).comp hL
  have h6 : Tendsto (fun N : ℕ => d * Pₛ (N : ℝ)) atTop atTop := Tendsto.const_mul_atTop hd hP
  obtain ⟨B,hB,hdec⟩ := stretchedExp_le_inverse_square (d-c) 1 (sub_pos.mpr hcd) (by norm_num)
  filter_upwards [hnat.eventually (eventually_ge_atTop x₀), eventually_ge_atTop (1 : ℕ),
    hlog.eventually (eventually_ge_atTop 6), h6.eventually (eventually_ge_atTop 6),
    hPL.eventually (gt_mem_nhds (show (0 : ℝ)<1 / (2 * d) by positivity)),
    hP.eventually (eventually_ge_atTop (max 1 (B * (10 + 8 * d))))] with N hx hN hlogN h6N hPLN hBN n
  let p := Pₛ (N : ℝ)
  let E := Real.exp (-d * p)
  have hp : 1 ≤ p := (le_max_left _ _).trans hBN
  have hp0 : 0<p := zero_lt_one.trans_le hp
  have hNr : (0 : ℝ)<N := by exact_mod_cast (show 0<N by omega)
  change 6 ≤ Real.log (N : ℝ) at hlogN
  have hLN : 0<6 + Real.log (N : ℝ) := by linarith only [hlogN]
  have hsmall : 2 * d * p < 6 + Real.log (N : ℝ) := by
    change p / (6 + Real.log (N : ℝ)) < 1 / (2 * d) at hPLN
    have hv := mul_lt_mul_of_pos_left ((div_lt_iff₀ hLN).mp hPLN) (by positivity : 0<2 * d)
    have his : (2 * d) * (1 / (2 * d) * (6 + Real.log (N : ℝ))) = 6 + Real.log (N : ℝ) := by field_simp [hd.ne']
    rw [his] at hv
    linarith only [hv]
  have hdp : d * p ≤ Real.log (N : ℝ) := by nlinarith only [hsmall,hlogN]
  have hInv : 1 / (N : ℝ) ≤ E := by
    simpa only [E,neg_mul,Real.exp_neg,Real.exp_log hNr,one_div] using Real.exp_le_exp.mpr (neg_le_neg hdp)
  have hE : 0<E := Real.exp_pos _
  have hE1 : E ≤ 1 := Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hd.le) hp0.le)
  have hEnt : E * (1 + Real.log (1 / E)) ≤ 1 / 2 := by
    simpa only [E,p,neg_mul] using exponential_entropy_small (d * Pₛ (N : ℝ)) h6N
  have htail (y : ℝ) (hy : (N : ℝ) ≤ y) : |M y| ≤ E * y := by
    apply (hx₀ y (hx.trans hy)).trans (mul_le_mul_of_nonneg_right ?_ (hNr.le.trans hy))
    have hm := logProductPower_mono (1 / 11) (by norm_num) (show 1 ≤ 6 + Real.log (N : ℝ) by linarith)
      (show 6 + Real.log (N : ℝ) ≤ 6 + Real.log y by linarith only [Real.log_le_log hNr hy])
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left hm (neg_nonpos.mpr hd.le))
  have hdom := QMertensFirstMoment.abs_defect_le_mertens_entropy_slope N hN E hE hE1 hEnt htail n
  have heq : Real.log (1 / E) = d * p := by simp [E,one_div,Real.log_inv]
  have hlin : 10 + 8 * d * p ≤ (10 + 8 * d) * p := by nlinarith only [hp]
  have hKp : B * (10 + 8 * d) ≤ p := (le_max_right _ _).trans hBN
  have hdec' : Real.exp (-(d-c) * p) ≤ B / p ^ 2 := by simpa only [Real.rpow_one] using hdec p hp
  have habs : (10 + 8 * d * p) * Real.exp (-(d-c) * p) ≤ 1 := by
    calc
      _ ≤ ((10 + 8 * d) * p) * (B / p ^ 2) := mul_le_mul hlin hdec' (Real.exp_pos _).le (by positivity)
      _ = (B * (10 + 8 * d)) / p := by field_simp [hp0.ne'] <;> ring
      _ ≤ 1 := (div_le_iff₀ hp0).mpr (by simpa using hKp)
  have hcombine : Real.exp (-(d-c) * p) * Real.exp (-c * p) = E := by
    change _ = Real.exp (-d * p)
    rw [← Real.exp_add]; congr 1; ring
  have hslope : 2 / (N : ℝ) + 8 * (E * (1 + Real.log (1 / E))) ≤ Real.exp (-c * p) := by
    rw [heq]
    calc
      _ = 2 * (1 / (N : ℝ)) + 8 * (E * (1 + d * p)) := by ring
      _ ≤ 2 * E + 8 * (E * (1 + d * p)) := add_le_add (mul_le_mul_of_nonneg_left hInv zero_le_two) le_rfl
      _ = (10 + 8 * d * p) * E := by ring
      _ = (10 + 8 * d * p) * (Real.exp (-(d-c) * p) * Real.exp (-c * p)) := congrArg ((10 + 8 * d * p)*·) hcombine.symm
      _ = ((10 + 8 * d * p) * Real.exp (-(d-c) * p)) * Real.exp (-c * p) := by ring
      _ ≤ _ := by simpa only [one_mul] using mul_le_mul_of_nonneg_right habs (Real.exp_pos (-c * p)).le
  simpa only [mul_comm (n : ℝ)] using hdom.trans (mul_le_mul_of_nonneg_right hslope (Nat.cast_nonneg n))

/-- The log-log factor in the positive profile permits any strict coefficient
below `θ ^ (1 / 11)` at power-sized legal heads. -/
private theorem stretched_scaled_head (θ t : ℝ) (hθ : 0<θ) (hθ1 : θ<1) (ht : 0<t)
    (htθ : t<θ ^ (1 / 11 : ℝ)) : ∀ᶠ X : ℕ in atTop, ∃ N : ℕ, Squarefree (N + 1) ∧ 0<N ∧ (X : ℝ) ^ θ ≤ (N : ℝ) ∧ (N : ℝ) ≤ 4 * (X : ℝ) ^ θ ∧ t * Pₛ (X : ℝ) ≤ Pₛ (N : ℝ) := by
  let v := t ^ 11
  have hv : v < θ := by
    calc
      _ = t ^ (11 : ℝ) := (Real.rpow_natCast t 11).symm
      _ < (θ ^ (1 / 11 : ℝ)) ^ (11 : ℝ) := Real.rpow_lt_rpow ht.le htθ (by norm_num)
      _ = _ := by rw [← Real.rpow_mul hθ.le]; norm_num
  have hvt : v ^ (1 / 11 : ℝ) = t := by
    dsimp only [v]
    rw [← Real.rpow_natCast, ← Real.rpow_mul ht.le]
    norm_num
  have hnat : Tendsto (fun X : ℕ => (X : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  let L := fun n : ℕ => 6 + Real.log (n : ℝ)
  have hL : Tendsto L atTop atTop := tendsto_atTop_add_const_left atTop 6 (Real.tendsto_log_atTop.comp hnat)
  have hll := Real.tendsto_log_atTop.comp hL
  have hθL := Tendsto.const_mul_atTop hθ hL
  filter_upwards [vk_exists_scaled_head θ hθ hθ1, eventually_ge_atTop (1 : ℕ),
    hθL.eventually (eventually_ge_atTop 1), hL.eventually (eventually_ge_atTop 1),
    hll.eventually (eventually_ge_atTop ((-θ * Real.log θ) / (θ-v)))] with X hsc hX hθL1 hs1 hbudget
  obtain ⟨N,hsf,hN,hlo,hhi,_⟩ := hsc
  refine ⟨N,hsf,hN,hlo,hhi,?_⟩
  have hX0 : (0 : ℝ)<X := by exact_mod_cast (show 0<X by omega)
  have hlog := Real.log_le_log (Real.rpow_pos_of_pos hX0 _) hlo
  rw [Real.log_rpow hX0] at hlog
  have hlow : θ * L X ≤ L N := by dsimp only [L]; linarith
  have hs0 : 0<L X := zero_lt_one.trans_le hs1
  have hθs0 : 0<θ * L X := mul_pos hθ hs0
  change (-θ * Real.log θ) / (θ-v) ≤ Real.log (L X) at hbudget
  have hh := (div_le_iff₀ (sub_pos.mpr hv)).mp hbudget
  have hprod : v * (L X * Real.log (L X)) ≤ L N * Real.log (L N) := by
    calc
      _ ≤ (θ * L X) * (Real.log θ + Real.log (L X)) := by
        nlinarith only [mul_le_mul_of_nonneg_right hh hs0.le]
      _ = (θ * L X) * Real.log (θ * L X) := by rw [Real.log_mul hθ.ne' hs0.ne']
      _ ≤ _ := mul_le_mul hlow (Real.log_le_log hθs0 hlow)
        (Real.log_nonneg hθL1) (hθs0.le.trans hlow)
  have hsprod := mul_nonneg hs0.le (Real.log_nonneg hs1)
  have hv0 : 0 ≤ v := pow_nonneg ht.le _
  change t * ((L X * Real.log (L X)) ^ (1 / 11 : ℝ)) ≤ (L N * Real.log (L N)) ^ (1 / 11 : ℝ)
  calc
    _ = (v * (L X * Real.log (L X))) ^ (1 / 11 : ℝ) := by rw [Real.mul_rpow hv0 hsprod,hvt]
    _ ≤ _ := Real.rpow_le_rpow (mul_nonneg hv0 hsprod) hprod (by norm_num)

/-- Every rate below the square-root factor for the input Mertens coefficient
suffices along arbitrarily sparse physical cutoffs. -/
theorem riemannHypothesis_of_cofinal_stretched_harmonic_prefix (a b C : ℝ) (hb : 0 ≤ b)
    (hba : b < a * (1 / 2 : ℝ) ^ (1 / 11 : ℝ))
    (hM : ∀ᶠ x : ℝ in atTop, |M x| ≤ (C * Real.exp (-a * Pₛ x)) * x)
    (hgood : ∃ᶠ X : ℕ in atTop, minimumHarmonicPrefix X ≤ Real.exp (b * Pₛ (X : ℝ))) : RiemannHypothesis := by
  obtain ⟨θ,c,hθ,hhalf,hc,hca,hgap⟩ := exists_profile_cutoff_parameters (by norm_num : (0 : ℝ)<1 / 11) hb hba
  have hratio : b / c < θ ^ (1 / 11 : ℝ) := (div_lt_iff₀ hc).mpr (by simpa only [mul_comm c] using hgap)
  obtain ⟨t,hbt,htθ⟩ := exists_between hratio
  have ht : 0<t := (div_nonneg hb hc.le).trans_lt hbt
  apply riemannHypothesis_of_witness_mean_zero
  exact witness_mean_zero_of_cofinal_profile_fraction (fun n : ℕ => Pₛ (n : ℝ)) c θ b t hc hθ hhalf hb
    (by simpa only [mul_comm t c] using (div_lt_iff₀ hc).mp hbt)
    (real_psi_tendsto.comp tendsto_natCast_atTop_atTop)
    (eventually_sharp_stretched_slope a c C hc hca hM) (stretched_scaled_head θ t hθ (by linarith) ht htθ) hgood

/-- A single rate is both a kernel-derived unconditional ordinary Mertens
coefficient and the coefficient entering the sharp `2 ^ (-1 / 11)` transfer. -/
theorem exists_ordinary_mertens_rate_and_sharp_cofinal_stretched_RH :
    ∃ a C : ℝ, 0<a ∧ 0 ≤ C ∧ (∀ x : ℝ, 1 ≤ x → |M x| ≤ C * x * Real.exp (-a * Pₛ x)) ∧ (Filter.liminf (fun X : ℕ => ENNReal.ofReal (Real.log (2 + minimumHarmonicPrefix X) / Pₛ (X : ℝ)))
        atTop < ENNReal.ofReal (a * (1 / 2 : ℝ) ^ (1 / 11 : ℝ)) → RiemannHypothesis) := by
  obtain ⟨a,ha,C,hC,hM⟩ := M_stretched_loglog_bound
  have hM' : ∀ x : ℝ, 1 ≤ x → |M x| ≤ C * x * Real.exp (-a * Pₛ x) := hM
  refine ⟨a,C,ha,hC,hM',?_⟩
  intro hlim
  have hP : Tendsto (fun X : ℕ => Pₛ (X : ℝ)) atTop atTop := real_psi_tendsto.comp tendsto_natCast_atTop_atTop
  obtain ⟨b,hb,hba,hf⟩ := exists_frequently_exp_of_liminf_log_ratio_lt
    (H:=minimumHarmonicPrefix) (φ:=fun X : ℕ => Pₛ (X : ℝ))
    (by positivity : 0<a * (1 / 2 : ℝ) ^ (1 / 11 : ℝ)) (hP.eventually (eventually_gt_atTop 0)) hlim
  apply riemannHypothesis_of_cofinal_stretched_harmonic_prefix a b C hb.le hba _ hf
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
  calc
    _ ≤ _ := hM' x hx
    _ = _ := by ring

/-- The project supplies a positive unconditional rate for arbitrarily sparse
one-sided good cutoffs. -/
theorem exists_cofinal_stretched_harmonic_rate :
    ∃ t : ℝ, 0<t ∧ ∀ b : ℝ, 0 ≤ b → b<t →
      (∃ᶠ X : ℕ in atTop, minimumHarmonicPrefix X ≤ Real.exp (b * Pₛ (X : ℝ))) → RiemannHypothesis := by
  obtain ⟨a,C,ha,hC,hM,_⟩ := exists_ordinary_mertens_rate_and_sharp_cofinal_stretched_RH
  refine ⟨a * (1 / 2 : ℝ) ^ (1 / 11 : ℝ),by positivity,?_⟩
  intro b hb hbt hf
  apply riemannHypothesis_of_cofinal_stretched_harmonic_prefix a b C hb hbt _ hf
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
  calc
    _ ≤ _ := hM x hx
    _ = _ := by ring

/-- No external ordinary Mertens result occurs in this criterion's type. -/
theorem exists_riemannHypothesis_of_liminf_stretched_harmonic_prefix :
    ∃ t : ℝ, 0<t ∧ (Filter.liminf (fun X : ℕ => ENNReal.ofReal
      (Real.log (2 + minimumHarmonicPrefix X) / Pₛ (X : ℝ))) atTop < ENNReal.ofReal t → RiemannHypothesis) := by
  obtain ⟨a,C,ha,hC,hM,h⟩ := exists_ordinary_mertens_rate_and_sharp_cofinal_stretched_RH
  exact ⟨a * (1 / 2 : ℝ) ^ (1 / 11 : ℝ),by positivity,h⟩

end RiemannResearch.RH.QSquarefreeDisplacementRigidity

noncomputable section
namespace RiemannResearch.NumberTheory.PrimeNumberTheorem

/-- The ordinary Mertens function has a negative unit jump at a prime. -/
theorem M_prime_jump (p : ℕ) (hp : p.Prime) :
    M (p : ℝ) - M ((p-1 : ℕ) : ℝ) = -1 := by
  have hset : Finset.Ioc (p-1) p = {p} := by
    ext n
    simp only [Finset.mem_Ioc,Finset.mem_singleton]
    have hpos := hp.pos
    omega
  simpa [hset,ArithmeticFunction.moebius_apply_prime hp] using
    M_nat_difference (p-1) p (Nat.sub_le _ _)

/-- An absolute relative envelope on the full tail pays for the reciprocal
head scale: Bertrand supplies a prime and its predecessor inside `[N,2N]`. -/
theorem reciprocal_head_le_four_relative_mertens (N : ℕ) (hN : 0<N) (ε : ℝ)
    (hM : ∀ y : ℝ, (N : ℝ) ≤ y → |M y| ≤ ε * y) : 1 / (4 * (N : ℝ)) ≤ ε := by
  have hNR : (0 : ℝ)<N := by exact_mod_cast hN
  have he : 0 ≤ ε := by
    by_contra! he
    exact (not_lt_of_ge ((abs_nonneg _).trans (hM (N : ℝ) le_rfl))) (mul_neg_of_neg_of_pos he hNR)
  obtain ⟨p,hp,hNp,hp2⟩ := Nat.exists_prime_lt_and_le_two_mul N hN.ne'
  have hpred : N ≤ p-1 := by omega
  have hpR : (p : ℝ) ≤ 2 * (N : ℝ) := by exact_mod_cast hp2
  have hpr : ((p-1 : ℕ) : ℝ) ≤ p := by exact_mod_cast Nat.sub_le p 1
  have hmass : (1 : ℝ)≤|M (p : ℝ)|+|M ((p-1 : ℕ) : ℝ)| := by
    calc
      1 = |M (p : ℝ)-M ((p-1 : ℕ) : ℝ)| := by rw [M_prime_jump p hp]; norm_num
      _ ≤ _ := by simpa only [sub_eq_add_neg,abs_neg] using abs_add_le (M (p : ℝ)) (-(M ((p-1 : ℕ) : ℝ)))
  apply (div_le_iff₀ (by positivity : 0<4 * (N : ℝ))).mpr
  nlinarith only [hmass, hM (p : ℝ) (by exact_mod_cast hNp.le),
    hM ((p-1 : ℕ) : ℝ) (by exact_mod_cast hpred), mul_le_mul_of_nonneg_left hpR he,
    mul_le_mul_of_nonneg_left hpr he]

end RiemannResearch.NumberTheory.PrimeNumberTheorem
namespace RiemannResearch.RH.QMertensFirstMoment
open ZetaTwoHilbert QAnnihilatorTailEscape RiemannResearch.NumberTheory.PrimeNumberTheorem

/-- The all-site defect slope is bounded purely by the entropy of the ordinary
Mertens envelope; the reciprocal cutoff cost is absorbed arithmetically. -/
theorem abs_defect_le_pure_mertens_entropy_slope (N : ℕ) (hN : 0<N) (ε : ℝ) (hε : 0<ε)
    (hε1 : ε ≤ 1) (hsmall : ε * (1 + Real.log (1 / ε)) ≤ 1 / 2)
    (hM : ∀ y : ℝ, (N : ℝ) ≤ y → |M y|≤ε * y) (n : ℕ) :
    |qSequence (defect N) n| ≤ (16 * (ε * (1 + Real.log (1 / ε)))) * n := by
  have hNR : (0 : ℝ)<N := by exact_mod_cast hN
  have hf := reciprocal_head_le_four_relative_mertens N hN ε hM
  have hrec : 2 / (N : ℝ) ≤ 8 * ε := by
    calc
      _ = 8 * (1 / (4 * (N : ℝ))) := by field_simp [hNR.ne'] <;> ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hf (by norm_num)
  have hi : (1 : ℝ) ≤ 1 / ε := (le_div_iff₀ hε).mpr (by simpa using hε1)
  have hE : ε ≤ ε * (1 + Real.log (1 / ε)) := by nlinarith only [mul_nonneg hε.le (Real.log_nonneg hi)]
  apply (abs_defect_le_mertens_entropy_slope N hN ε hε hε1 hsmall hM n).trans
  exact mul_le_mul_of_nonneg_right (by linarith only [hrec,hE]) (Nat.cast_nonneg n)

end RiemannResearch.RH.QMertensFirstMoment
