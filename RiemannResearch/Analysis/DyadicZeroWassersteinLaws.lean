import RiemannResearch.Analysis.ActualZeroDiscrepancy
import RiemannResearch.RH.WeilExplicitFormula.GammaFacts.Complete
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import RiemannResearch.Analysis.DyadicZeroWassersteinFourier
import RiemannResearch.Analysis.ActualZeroDisplacementMoments
import RiemannResearch.Analysis.ActualZeroAbelPairing
import RiemannResearch.Analysis.ActualZeroHeightTransfer
import RiemannResearch.Analysis.MontgomeryLocalMass
import RiemannResearch.Analysis.ActualZeroCountUpper
import RiemannResearch.Analysis.ActualZeroCountNormalization
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-! # Dyadic zero laws, the horizontal moment and the height witness

All sums count each actual zero with its analytic multiplicity. The window is
left-open and right-closed. The Wasserstein distance is written in its
Kantorovich--Rubinstein dual form with the sum metric, using anchored tests.
For large positive U both measures are probabilities with compact support.

The integrated gamma remainder and Backlund discrepancy below prove the classical cumulative Riemann--von Mangoldt estimate used
in Brent, Platt and Trudgian, Math. Comp. 90 (2021), 2923--2935, §2,
https://doi.org/10.1090/mcom/3652 . Right endpoint convention changes cost
O(log T) by the unit-window count. The horizontal input is Selberg's density
bound as stated in Ford and Zaharescu, Lemma 2,
https://www.ford126.web.illinois.edu/wwwpapers/fz.pdf .
-/
noncomputable section
open Filter MeasureTheory Set Zeta23
open scoped BigOperators Topology ENNReal
namespace RiemannResearch.Analysis.DyadicZeroWasserstein
open ActualZeroOrdinate PrimeTorusHaar MontgomeryLocalMass

abbrev Space (P : Finset ℕ) := ℝ × ℝ × Torus P
abbrev Occ (U : ℝ) := WindowCopies U (2 * U)

def height (U t : ℝ) := (t - U) / U

def coord (P : Finset ℕ) (U : ℝ) (ρ : ℂ) : Space P :=
  (ρ.re, height U ρ.im, primeOrbit P ρ.im)

def unif : Measure ℝ := volume.restrict (Ioc 0 1)

instance : IsProbabilityMeasure unif := by
  constructor
  simp [unif, Real.volume_Ioc]

def nu (P : Finset ℕ) : Measure (Space P) :=
  (Measure.dirac (1 / 2 : ℝ)).prod (unif.prod (haar P))

instance (P : Finset ℕ) : IsProbabilityMeasure (nu P) := by unfold nu; infer_instance

def mu (P : Finset ℕ) (U : ℝ) : Measure (Space P) :=
  (Ncount U (2 * U) : ℝ≥0∞)⁻¹ • ∑ i : Occ U, Measure.dirac (coord P U i.1.val)

def mass (U : ℝ) : ℝ := Ncount U (2 * U)

theorem mu_probability (P : Finset ℕ) {U : ℝ} (hN : 0 < Ncount U (2 * U)) :
    IsProbabilityMeasure (mu P U) := by
  constructor
  simp only [mu, Measure.smul_apply, Measure.finsetSum_apply, MeasurableSet.univ,
    measure_univ, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one, smul_eq_mul]
  rw [show Fintype.card (Occ U) = Ncount U (2 * U) from card_windowCopies _ _]
  exact ENNReal.inv_mul_cancel (by exact_mod_cast hN.ne') (by simp)

def massSum (U : ℝ) (F : ℂ → ℝ) := ∑ i : Occ U, F i.1.val

theorem massSum_sub_half (U : ℝ) (F : ℂ → ℝ) :
    massSum U (fun ρ => F ρ - 1 / 2) = massSum U F - mass U / 2 := by
  simp only [massSum, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [show Fintype.card (Occ U) = Ncount U (2 * U) from card_windowCopies _ _]
  unfold mass
  ring

theorem integral_mu (P : Finset ℕ) (U : ℝ) (f : C(Space P, ℝ)) :
    (∫ x, f x ∂mu P U) = massSum U (fun ρ => f (coord P U ρ)) / mass U := by
  rw [mu, integral_smul_measure, integral_finsetSum_measure]
  · simp [massSum, mass, integral_dirac, div_eq_mul_inv, mul_comm]
  · intro i hi
    apply integrable_dirac
    simp

def cost (P : Finset ℕ) (x y : Space P) : ℝ :=
  |x.1 - y.1| + |x.2.1 - y.2.1| + ∑ p : P, dist (x.2.2 p) (y.2.2 p)

def Admissible (P : Finset ℕ) (f : C(Space P, ℝ)) : Prop :=
  f (1 / 2, 0, 0) = 0 ∧ ∀ x y, |f x - f y| ≤ cost P x y

def differences (P : Finset ℕ) (μ ν : Measure (Space P)) : Set ℝ :=
  {r | ∃ f : C(Space P, ℝ), Admissible P f ∧ r = |(∫ x, f x ∂μ) - ∫ x, f x ∂ν|}

def wassersteinOne (P : Finset ℕ) (μ ν : Measure (Space P)) : ℝ :=
  sSup (differences P μ ν)

/-- The coupling definition, for comparison with the dual convention above. -/
def transportOne (P : Finset ℕ) (μ ν : Measure (Space P)) : ℝ :=
  sInf {a | ∃ π : Measure (Space P × Space P),
    π.map Prod.fst = μ ∧ π.map Prod.snd = ν ∧
    a = ∫ xy, cost P xy.1 xy.2 ∂π}

def CompactProbabilitySupport {X : Type*} [TopologicalSpace X] [MeasurableSpace X]
    (μ : Measure X) : Prop := ∃ K : Set X, IsCompact K ∧ μ K = 1

/-- Classical Kantorovich--Rubinstein duality, restricted to compactly
supported probability laws for the displayed cost. See Kellerer,
"Duality theorems for marginal problems", Z. Wahrscheinlichkeitstheorie
verw. Gebiete 67 (1984), and Villani, *Optimal Transport*, Theorem 5.10. -/
def CompactKR : Prop := ∀ (P : Finset ℕ) (μ ν : Measure (Space P)),
  IsProbabilityMeasure μ → IsProbabilityMeasure ν →
  CompactProbabilitySupport μ → CompactProbabilitySupport ν →
  transportOne P μ ν = wassersteinOne P μ ν

theorem mu_compact (P : Finset ℕ) {U : ℝ} (hN : 0 < Ncount U (2 * U)) :
    CompactProbabilitySupport (mu P U) := by
  let K := Set.range (fun i : Occ U => coord P U i.1.val)
  have hf : K.Finite := Set.finite_range _
  have hmem (i : Occ U) : coord P U i.1.val ∈ K := ⟨i, rfl⟩
  refine ⟨K, hf.isCompact, ?_⟩
  calc
    mu P U K = mu P U univ := by
      simp only [mu, Measure.smul_apply, Measure.finsetSum_apply, hf.measurableSet,
        MeasurableSet.univ]
      congr 1
      apply Finset.sum_congr rfl
      intro i hi
      simp [Measure.dirac_apply', hf.measurableSet, hmem i]
    _ = 1 := (mu_probability P hN).measure_univ

theorem nu_compact (P : Finset ℕ) : CompactProbabilitySupport (nu P) := by
  let I := Icc (0 : ℝ) 1
  refine ⟨I ×ˢ (I ×ˢ (univ : Set (Torus P))),
    isCompact_Icc.prod (isCompact_Icc.prod isCompact_univ), ?_⟩
  have hi : unif I = 1 := by
    rw [unif, Measure.restrict_apply measurableSet_Icc,
      inter_eq_right.mpr (Ioc_subset_Icc_self : Ioc (0 : ℝ) 1 ⊆ I)]
    norm_num [Real.volume_Ioc]
  rw [nu, Measure.prod_prod, Measure.prod_prod, hi, measure_univ,
    Measure.dirac_apply' _ measurableSet_Icc]
  norm_num [I, Set.indicator]

theorem height_test (P : Finset ℕ) :
    Admissible P (⟨fun x => x.2.1, continuous_fst.comp continuous_snd⟩ : C(Space P, ℝ)) := by
  constructor
  · rfl
  · intro x y
    change |x.2.1 - y.2.1| ≤ _
    unfold cost
    linarith [abs_nonneg (x.1 - y.1), Finset.sum_nonneg (s := Finset.univ)
      (fun (p : P) _ => dist_nonneg (x := x.2.2 p) (y := y.2.2 p))]

theorem integral_nu_height (P : Finset ℕ) : (∫ x : Space P, x.2.1 ∂nu P) = 1 / 2 := by
  rw [nu, Measure.dirac_prod, integral_map (by fun_prop) (by fun_prop)]
  change (∫ x : ℝ × Torus P, x.1 ∂unif.prod (haar P)) = _
  rw [integral_fun_fst (μ := unif) (ν := haar P) (fun x : ℝ => x)]
  simp only [Measure.real, measure_univ, ENNReal.toReal_one, one_smul]
  rw [unif, ← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1),
    integral_id]
  norm_num

theorem occ_bounds {U : ℝ} (i : Occ U) : U < i.1.val.im ∧ i.1.val.im ≤ 2 * U := by
  have h := i.1.property
  rw [Set.Finite.mem_toFinset] at h
  exact ⟨h.2.1, h.2.2⟩

theorem massSum_weighted (U : ℝ) (F : ℂ → ℝ) :
    massSum U F = ∑ ρ ∈ (zerosIn_finite U (2 * U)).toFinset, (zeroMult ρ : ℝ) * F ρ := by
  classical
  simp [massSum, Occ, WindowCopies, Fintype.sum_sigma]
  exact Finset.sum_attach _ (fun ρ : ℂ => (zeroMult ρ : ℝ) * F ρ)

/-- Selberg's density input gives a height-sized total horizontal displacement.
Dividing by the dyadic mass gives its contribution to W1. -/
theorem horizontal_sum (hs : UniformSelbergDensity (1 / 4)) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ᶠ U : ℝ in atTop,
      massSum U (fun ρ => |ρ.re - 1 / 2|) ≤ D * U := by
  obtain ⟨C, T₀, hC, hT₀, hD⟩ := hs
  refine ⟨16 * C, by positivity, ?_⟩
  filter_upwards [eventually_ge_atTop T₀, eventually_ge_atTop (2 : ℝ),
    eventually_count_pos] with U hT hU hpos
  have h2 : 1 < 2 * U := by linarith
  have hc2 : 0 < Ncount 0 (2 * U) := hpos.trans_le (Ncount_mono le_rfl (by linarith))
  have hn : 0 < (Ncount 0 (2 * U) : ℝ) := by exact_mod_cast hc2
  have h := displacementMoment_le_of_selberg (T := 2 * U) (C := C) (a := 1 / 4) 0 h2 hC
    (by norm_num) (hD _ (by linarith))
  simp only [displacementMoment, zero_add, pow_one, Nat.factorial_one, Nat.cast_one, mul_one] at h
  have hfull : ∑ i : Copies (2 * U), copyDisplacement (2 * U) i ≤ 16 * C * U := by
    field_simp [ne_of_gt hn] at h
    apply le_of_not_gt
    intro hbad
    nlinarith [mul_pos (Real.log_pos h2) (sub_pos.mpr hbad)]
  rw [massSum_weighted]
  have hsub : (zerosIn_finite U (2 * U)).toFinset ⊆ cutoff (2 * U) := by
    intro ρ hρ
    rw [Set.Finite.mem_toFinset] at hρ
    obtain ⟨hz, hl, hr⟩ := hρ
    exact mem_cutoff.mpr ⟨hz, by linarith, hr⟩
  apply (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)).trans
  change realSum (2 * U) (fun ρ => |ρ.re - 1 / 2|) ≤ _
  rw [realSum_eq_copies]
  exact hfull

theorem dyadic_mass_bounds :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ᶠ U : ℝ in atTop,
      c * U * Real.log U ≤ mass U ∧ mass U ≤ C * U * Real.log U := by
  let c : ℝ := 1 / (4 * Real.pi)
  have hc : 0 < c := by dsimp [c]; positivity
  have hsmall : c < 1 / (2 * Real.pi) := by dsimp [c]; gcongr <;> nlinarith [Real.pi_pos]
  have hl := Assembly.eventually_N_ge_log_of_lt zetaZeroConfig
    (RvM.riemannVonMangoldt gammaFacts) hsmall
  obtain ⟨B, hB, hb⟩ := exists_count_le_height_log
  refine ⟨c, 4 * B, hc, by positivity, ?_⟩
  filter_upwards [hl, eventually_ge_atTop (9 : ℝ)] with U hL hU
  refine ⟨by simpa [mass, zetaZeroConfig_N] using hL, ?_⟩
  have hm : mass U ≤ (Ncount 0 (2 * U) : ℝ) := by
    unfold mass
    exact_mod_cast (Ncount_mono (show 0 ≤ U by linarith) (le_refl (2 * U)))
  have hlog : Real.log (2 * U) ≤ 2 * Real.log U := by
    rw [Real.log_mul (by norm_num) (by linarith)]
    linarith [Real.log_le_log (by norm_num : (0 : ℝ) < 2) (by linarith : 2 ≤ U)]
  apply hm.trans ((hb (2 * U) (by linarith)).trans _)
  nlinarith [mul_le_mul_of_nonneg_left hlog (show 0 ≤ B * (2 * U) by positivity)]

def countMain (t : ℝ) := t / (2 * Real.pi) * (Real.log (t / (2 * Real.pi)) - 1)

def slope (t : ℝ) := Real.log (t / (2 * Real.pi)) / (2 * Real.pi)

def countError (t : ℝ) := (Ncount 0 t : ℝ) - countMain t

def CumulativeRvM : Prop := ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ t : ℝ in atTop,
    |countError t| ≤ C * Real.log t

/-- Exact Abel summation for the finite multiplicity window. -/
theorem window_abel {U : ℝ} (hu : 0 < U) (H H' : ℝ → ℝ)
    (hd : ∀ t, HasDerivAt H (H' t) t) (hc : Continuous H') :
    massSum U (fun ρ => H ρ.im) = (Ncount 0 (2 * U) : ℝ) * H (2 * U) -
      (Ncount 0 U : ℝ) * H U - ∫ t in U..2 * U, (Ncount 0 t : ℝ) * H' t := by
  have hu2 : U ≤ 2 * U := by linarith
  have hi : IntervalIntegrable (fun t => (H' t : ℂ)) volume 0 (2 * U) :=
    (Complex.continuous_ofReal.comp hc).intervalIntegrable _ _
  have h := ActualZeroAbelPairing.abelPairing_count_eq_actual_sum_sub (a := U) (b := 2 * U)
    (F := fun t => (H t : ℂ)) hu.le hu2
    (fun t _ => Complex.ofRealCLM.hasFDerivAt.comp_hasDerivAt t (hd t)) hi
  rw [sum_sub_eq_window_sum U (2 * U) hu.le hu2 _] at h
  have hni := (ActualZeroAbelPairing.count_mul_intervalIntegrable
    (show 0 ≤ 2 * U by linarith) hi).mono_set (by
      rw [uIcc_of_le hu2, uIcc_of_le (by linarith : 0 ≤ 2 * U)]
      exact Icc_subset_Icc hu.le le_rfl)
  apply_fun Complex.re at h
  simp only [IntegratedCountingPairing.abelPairing, Complex.sub_re] at h
  have hreal : (∫ t in U..2 * U, (Ncount 0 t : ℂ) * (H' t : ℂ)).re =
      ∫ t in U..2 * U, (Ncount 0 t : ℝ) * H' t := by
    simpa using (intervalIntegral.intervalIntegral_re hni).symm
  simp only [Complex.ofRealCLM_apply] at h
  rw [hreal] at h
  rw [massSum_weighted]
  simpa [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im] using h.symm

private theorem interval_count_integrable {U : ℝ} (hu : 0 < U) :
    IntervalIntegrable (fun t => (Ncount 0 t : ℝ)) volume U (2 * U) := by
  have h := ActualZeroAbelPairing.count_mul_intervalIntegrable (show 0 ≤ 2 * U by linarith)
    (g := fun _ => (1 : ℂ)) intervalIntegrable_const
  have h' := h.mono_set (c := U) (d := 2 * U) (by
    rw [uIcc_of_le (by linarith : U ≤ 2 * U), uIcc_of_le (by linarith : 0 ≤ 2 * U)]
    exact Icc_subset_Icc hu.le le_rfl)
  simpa only [mul_one, Complex.norm_natCast] using h'.norm

/-- Two endpoint terms and the signed integral of the discrepancy against H'. -/
theorem abel_estimate {U K L : ℝ} (hu : 0 < U) {H H' B d : ℝ → ℝ}
    (hH : ∀ t, HasDerivAt H (H' t) t) (hcH : Continuous H')
    (hd : ContinuousOn d (Icc U (2 * U)))
    (hB : ∀ t ∈ Icc U (2 * U), HasDerivAt B (d t) t)
    (hbH : ∀ t ∈ Icc U (2 * U), |H t| ≤ K)
    (hbD : ∀ t ∈ Icc U (2 * U), |H' t| ≤ L) :
    |massSum U (fun ρ => H ρ.im) - ∫ t in U..2 * U, H t * d t| ≤
      K * (|(Ncount 0 U : ℝ) - B U| + |(Ncount 0 (2 * U) : ℝ) - B (2 * U)|) +
      L * (∫ t in U..2 * U, |(Ncount 0 t : ℝ) - B t|) := by
  let E := fun t : ℝ => (Ncount 0 t : ℝ) - B t
  have hul : U ≤ 2 * U := by linarith
  have ic : uIcc U (2 * U) = Icc U (2 * U) := uIcc_of_le hul
  have hcB : ContinuousOn B (uIcc U (2 * U)) := by
    rw [ic]; exact fun t ht => (hB t ht).continuousAt.continuousWithinAt
  have hc : Continuous H := continuous_iff_continuousAt.mpr (fun t => (hH t).continuousAt)
  have hiB : IntervalIntegrable B volume U (2 * U) := hcB.intervalIntegrable
  have hiN := interval_count_integrable hu
  have hiE : IntervalIntegrable E volume U (2 * U) := hiN.sub hiB
  have hiBH := hiB.mul_continuousOn hcH.continuousOn
  have hiNH := hiN.mul_continuousOn hcH.continuousOn
  have hbp := intervalIntegral.integral_mul_deriv_eq_deriv_mul
    (u := H) (v := B) (u' := H') (v' := d)
    (fun t _ => hH t) (fun t ht => hB t (ic ▸ ht))
    (hcH.intervalIntegrable _ _) (by rw [←ic] at hd; exact hd.intervalIntegrable)
  have heq : massSum U (fun ρ => H ρ.im) - (∫ t in U..2 * U, H t * d t) =
      E (2 * U) * H (2 * U) - E U * H U - ∫ t in U..2 * U, E t * H' t := by
    rw [window_abel hu H H' hH hcH, hbp]
    dsimp [E]
    simp_rw [sub_mul, mul_comm (H' _) (B _)]
    rw [intervalIntegral.integral_sub hiNH hiBH]
    ring
  have hi : |∫ t in U..2 * U, E t * H' t| ≤ L * (∫ t in U..2 * U, |E t|) := by
    rw [← intervalIntegral.integral_const_mul]
    rw [← Real.norm_eq_abs]
    apply (intervalIntegral.norm_integral_le_integral_norm
      (μ := volume) (f := fun t => E t * H' t) hul).trans
    apply intervalIntegral.integral_mono_on hul
      (hiE.mul_continuousOn hcH.continuousOn).norm
      (by simpa only [Real.norm_eq_abs] using hiE.norm.const_mul L)
    intro t ht
    rw [Real.norm_eq_abs, abs_mul, mul_comm L]
    exact mul_le_mul_of_nonneg_left (hbD t ht) (abs_nonneg _)
  have ha (t : ℝ) (ht : t ∈ Icc U (2 * U)) : |E t * H t| ≤ K * |E t| := by
    rw [abs_mul, mul_comm K]
    exact mul_le_mul_of_nonneg_left (hbH t ht) (abs_nonneg _)
  rw [heq]
  apply (abs_sub _ _).trans
  have h := (abs_sub _ _).trans (add_le_add (ha (2 * U) ⟨hul, le_rfl⟩) (ha U ⟨le_rfl, hul⟩))
  dsimp [E] at *
  linarith [add_le_add h hi]

theorem countMain_deriv {t : ℝ} (ht : 0 < t) : HasDerivAt countMain (slope t) t := by
  have hp : 0 < 2 * Real.pi := by positivity
  have h := ((hasDerivAt_id t).div_const (2 * Real.pi)).mul
    ((((hasDerivAt_id t).div_const (2 * Real.pi)).log (div_ne_zero ht.ne' hp.ne')).sub_const 1)
  convert h using 1 <;>
    first | rfl | (try dsimp [countMain, slope, id]; field_simp [ht.ne', Real.pi_ne_zero] <;> ring)

section
open ActualZeroDiscrepancy

/-- Signed variation of the gamma remainder, on every interval above one. -/
theorem smoothCount_main_variation :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u v : ℝ, 1 ≤ u → u ≤ v →
      |(smoothCount v - countMain v) - (smoothCount u - countMain u)| ≤
        C * (u⁻¹ - v⁻¹) := by
  obtain ⟨c, hc⟩ := gammaFacts.stirling
  let C := |c|
  have hC : 0 ≤ C := abs_nonneg _
  let F := fun t => smoothCount t - countMain t
  have hμ := RvM.mu_continuous gammaFacts
  have hd (t : ℝ) (ht : 1 ≤ t) : HasDerivAt F (Zeta23.mu t - slope t) t :=
    (intervalIntegral.integral_hasDerivAt_right (hμ.intervalIntegrable 0 t)
      hμ.stronglyMeasurable.stronglyMeasurableAtFilter hμ.continuousAt).sub
        (countMain_deriv (by linarith))
  have hb (t : ℝ) (ht : 1 ≤ t) : |Zeta23.mu t - slope t| ≤ C / t^2 := by
    have ht0 : 0 ≤ t := by linarith
    have h := hc t (by simpa only [abs_of_nonneg ht0] using ht)
    rw [abs_of_nonneg ht0] at h
    simpa only [slope, div_eq_mul_inv, one_mul, mul_comm] using
      h.trans (div_le_div_of_nonneg_right (le_abs_self c) (sq_nonneg t))
  have hanti (a : ℝ) (ha : |a| ≤ 1) :
      AntitoneOn (fun t => a * F t + C * t⁻¹) (Ici 1) := by
    have hd' (t : ℝ) (ht : 1 ≤ t) : HasDerivAt (fun t => a * F t + C * t⁻¹)
        (a * (Zeta23.mu t - slope t) + C * (-(t ^ 2)⁻¹)) t :=
      ((hd t ht).const_mul a).add ((hasDerivAt_inv (show t ≠ 0 by linarith)).const_mul C)
    apply antitoneOn_of_deriv_nonpos (convex_Ici 1)
    · intro t ht
      exact (hd' t ht).continuousAt.continuousWithinAt
    · intro t ht
      exact (hd' t (interior_subset ht)).differentiableAt.differentiableWithinAt
    · intro t ht
      have h1 : 1 ≤ t := interior_subset ht
      rw [(hd' t h1).deriv]
      have h : a * (Zeta23.mu t - slope t) ≤ C / t^2 :=
        (le_abs_self (a * (Zeta23.mu t - slope t))).trans (by
          rw [abs_mul]
          exact (mul_le_mul_of_nonneg_right ha (abs_nonneg _)).trans
            (by simpa using hb t h1))
      simpa only [mul_neg, div_eq_mul_inv, ← sub_eq_add_neg, sub_nonpos] using h
  refine ⟨C, hC, fun u v hu huv => ?_⟩
  have hh := hanti 1 (by norm_num) hu (hu.trans huv) huv
  have hl := hanti (-1) (by norm_num) hu (hu.trans huv) huv
  dsimp only [F] at hh hl
  apply abs_le.mpr
  constructor <;> linarith

/-- Actual zeta zeros counted with analytic multiplicity satisfy the global
cumulative Riemann–von Mangoldt estimate used by the dyadic height laws. -/
theorem actual_cumulativeRvM : CumulativeRvM := by
  obtain ⟨A, hA, ha⟩ := exists_abs_discrepancy_le_log
  obtain ⟨C, hC, hc⟩ := smoothCount_main_variation
  let B := C + |smoothCount 1 - countMain 1|
  have hB : 0 ≤ B := add_nonneg hC (abs_nonneg _)
  refine ⟨3*A+B, by linarith, ?_⟩
  filter_upwards [eventually_ge_atTop (4 : ℝ)] with t ht
  have ht₀ : 0 < t := by linarith
  have hlog : 1 ≤ Real.log t := by
    have h4 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 * 2 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
      ring
    linarith only [Real.log_two_gt_d9, Real.log_le_log (by norm_num : (0 : ℝ) < 4) ht, h4]
  have hlog' : Real.log (t+4) ≤ 2 * Real.log t := by
    have h := Real.log_le_log (by linarith : 0 < t+4) (by nlinarith : t+4 ≤ t*t)
    simpa only [Real.log_mul ht₀.ne' ht₀.ne', two_mul] using h
  have hvar := hc 1 t le_rfl (by linarith)
  have hsm : |smoothCount t - countMain t| ≤ B := by
    have hh := abs_add_le ((smoothCount t - countMain t) - (smoothCount 1 - countMain 1))
      (smoothCount 1 - countMain 1)
    rw [sub_add_cancel] at hh
    have hle : C * (1⁻¹ - t⁻¹) ≤ C := by
      rw [inv_one, mul_sub, mul_one]
      exact sub_le_self _ (mul_nonneg hC (inv_nonneg.mpr ht₀.le))
    exact hh.trans (add_le_add (hvar.trans hle) le_rfl)
  have hd : countError t = discrepancy t + (smoothCount t - countMain t) := by
    unfold countError discrepancy
    ring
  rw [hd]
  apply (abs_add_le _ _).trans
  have hD := ha t ht₀.le
  have hm := mul_le_mul_of_nonneg_left hlog' hA.le
  have hB' := mul_le_mul_of_nonneg_left hlog hB
  nlinarith [mul_le_mul_of_nonneg_left hlog hA.le]

end

theorem slope_continuous {U : ℝ} (hu : 0 < U) : ContinuousOn slope (Icc U (2 * U)) := by
  intro t ht
  have hpos : 0 < t / (2 * Real.pi) := div_pos (hu.trans_le ht.1) (by positivity)
  exact (((continuousAt_id.div_const _).log hpos.ne').div_const _).continuousWithinAt

theorem height_main_integral {U : ℝ} (hu : 0 < U) :
    (∫ t in U..2 * U, (height U t - 1 / 2) * slope t) =
      U * (3 / 4 - Real.log 2) / (2 * Real.pi) := by
  let F := fun t : ℝ =>
    ((t ^ 2 / (2 * U) - 3 * t / 2) * Real.log (t / (2 * Real.pi)) -
      t ^ 2 / (4 * U) + 3 * t / 2) / (2 * Real.pi)
  have hp : (2 * Real.pi : ℝ) ≠ 0 := by positivity
  have hd (t : ℝ) (ht : 0 < t) : HasDerivAt F ((height U t - 1 / 2) * slope t) t := by
    have hi := hasDerivAt_id t
    have hlog := (hi.div_const (2 * Real.pi)).log (div_ne_zero ht.ne' hp)
    have hpow := hasDerivAt_pow 2 t
    have h := ((((hpow.div_const (2 * U)).sub ((hi.const_mul 3).div_const 2)).mul hlog).sub
      (hpow.div_const (4 * U))).add ((hi.const_mul 3).div_const 2)
    convert h.div_const (2 * Real.pi) using 1 <;> first | rfl |
      (try dsimp [F, height, slope, id]; field_simp [ht.ne', hu.ne', Real.pi_ne_zero] <;> ring)
  have hu' : U ≤ 2 * U := by linarith
  have hc : ContinuousOn (fun t => (height U t - 1 / 2) * slope t) (uIcc U (2 * U)) := by
    rw [uIcc_of_le hu']
    have hc : Continuous (fun t => height U t - 1 / 2) := by unfold height; fun_prop
    exact hc.continuousOn.mul (slope_continuous hu)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t ht => hd t (hu.trans_le ((uIcc_of_le hu' ▸ ht).1))) hc.intervalIntegrable]
  have hl : Real.log ((2 * U) / (2 * Real.pi)) =
      Real.log 2 + Real.log (U / (2 * Real.pi)) := by
    rw [show (2 * U) / (2 * Real.pi) = 2 * (U / (2 * Real.pi)) by ring,
      Real.log_mul (by norm_num) (div_ne_zero hu.ne' hp)]
  dsimp [F]
  rw [hl]
  field_simp [hu.ne', hp]
  ring

/-- The signed bias before count-normalization, with the classical O(log U)
endpoint error. -/
theorem height_bias :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ U : ℝ in atTop,
      |massSum U (fun ρ => height U ρ.im - 1 / 2) -
         U * (3 / 4 - Real.log 2) / (2 * Real.pi)| ≤ C * Real.log U := by
  obtain ⟨C, hC, h⟩ := actual_cumulativeRvM
  obtain ⟨T, hT⟩ := eventually_atTop.1 h
  refine ⟨6 * C, by positivity, ?_⟩
  filter_upwards [eventually_ge_atTop T, eventually_ge_atTop (2 : ℝ)] with U hut hu
  have up : 0 < U := by linarith
  have e (t : ℝ) (ht : t ∈ Icc U (2 * U)) : |countError t| ≤ 2 * C * Real.log U := by
    have hl := Real.log_le_log (up.trans_le ht.1) ht.2
    rw [Real.log_mul (by norm_num) up.ne'] at hl
    have hl2 := Real.log_le_log (by norm_num : (0 : ℝ) < 2) hu
    have htlog : Real.log t ≤ 2 * Real.log U := by linarith
    exact (hT t (hut.trans ht.1)).trans (by nlinarith [mul_le_mul_of_nonneg_left htlog hC])
  have bound := abel_estimate (H := fun t => height U t - 1 / 2) (H' := fun _ => 1 / U)
    (B := countMain) (d := slope) (K := 1) (L := 1 / U) up
    (fun t => by
      convert ((((hasDerivAt_id t).sub_const U).div_const U).sub_const (1 / 2)) using 1 <;> rfl)
    continuous_const (slope_continuous up) (fun t ht => countMain_deriv (up.trans_le ht.1)) (by
      intro t ht
      have h0 : 0 ≤ height U t := div_nonneg (sub_nonneg.mpr ht.1) up.le
      have h1 : height U t ≤ 1 := (div_le_iff₀ up).2 (by linarith [ht.2])
      exact abs_le.mpr ⟨by linarith, by linarith⟩) (fun _ _ => (abs_of_nonneg (by positivity)).le)
  rw [height_main_integral up] at bound
  have hle : U ≤ 2 * U := by linarith
  have hI := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := U) (b := 2 * U) (C := 2 * C * Real.log U) (f := fun t => |countError t|) (by
      intro t ht
      rw [uIoc_of_le hle] at ht
      simpa [Real.norm_eq_abs] using e t ⟨ht.1.le, ht.2⟩)
  have hIe : (∫ t in U..2 * U, |countError t|) ≤ (2 * C * Real.log U) * U := by
    apply (le_abs_self _).trans
    rw [Real.norm_eq_abs, show 2 * U - U = U by ring, abs_of_pos up] at hI
    linarith
  have he1 := e U ⟨le_rfl, hle⟩
  have he2 := e (2 * U) ⟨hle, le_rfl⟩
  change _ ≤ 1 * (|countError U| + |countError (2 * U)|) +
    (1 / U) * (∫ t in U..2 * U, |countError t|) at bound
  apply bound.trans
  have he := mul_le_mul_of_nonneg_left hIe (show 0 ≤ 1 / U by positivity)
  rw [show (1 / U) * ((2 * C * Real.log U) * U) = 2 * C * Real.log U by field_simp] at he
  linarith

/-- The coefficient of the dyadic counting density is exact. -/
theorem dyadic_mass_limit :
    Tendsto (fun U : ℝ => mass U / (U * Real.log U)) atTop (𝓝 (1 / (2 * Real.pi))) := by
  apply tendsto_order.2
  constructor
  · intro a ha
    let q := (a + 1 / (2 * Real.pi)) / 2
    have hq : q < 1 / (2 * Real.pi) := by dsimp [q]; linarith
    have h := Assembly.eventually_N_ge_log_of_lt zetaZeroConfig
      (RvM.riemannVonMangoldt gammaFacts) hq
    filter_upwards [h, eventually_gt_atTop (1 : ℝ)] with U hn hu
    apply (lt_div_iff₀ (mul_pos (by linarith) (Real.log_pos hu))).2
    have h' : q * U * Real.log U ≤ mass U := by simpa [mass, zetaZeroConfig_N] using hn
    have haq : a < q := by dsimp [q]; linarith
    exact (mul_lt_mul_of_pos_right haq (mul_pos (by linarith) (Real.log_pos hu))).trans_le
      (by simpa [mul_assoc] using h')
  · intro b hb
    let q := (b + 1 / (2 * Real.pi)) / 2
    have hq : 1 / (2 * Real.pi) < q := by dsimp [q]; linarith
    have h := Assembly.eventually_N_le_log_of_lt zetaZeroConfig
      (RvM.riemannVonMangoldt gammaFacts) hq
    filter_upwards [h, eventually_gt_atTop (1 : ℝ)] with U hn hu
    apply (div_lt_iff₀ (mul_pos (by linarith) (Real.log_pos hu))).2
    have h' : mass U ≤ q * (U * Real.log U) := by simpa [mass, zetaZeroConfig_N, mul_assoc] using hn
    have hqb : q < b := by dsimp [q]; linarith
    exact h'.trans_lt (mul_lt_mul_of_pos_right hqb (mul_pos (by linarith) (Real.log_pos hu)))

/-- First-order signed height bias in the normalized probability measure. -/
theorem height_mean_limit (P : Finset ℕ) :
    Tendsto (fun U : ℝ => Real.log U * ((∫ x : Space P, x.2.1 ∂mu P U) - 1 / 2))
      atTop (𝓝 (3 / 4 - Real.log 2)) := by
  let k := (3 / 4 - Real.log 2) / (2 * Real.pi)
  let h := fun U => massSum U (fun ρ => height U ρ.im - 1 / 2)
  obtain ⟨B, hB, hb⟩ := height_bias
  have herr : Tendsto (fun U : ℝ => h U / U - k) atTop (𝓝 0) := by
    apply squeeze_zero_norm' (a := fun U : ℝ => (B * Real.log U) / U)
    · filter_upwards [hb, eventually_gt_atTop (1 : ℝ)] with U he hu
      have up : 0 < U := by linarith
      rw [Real.norm_eq_abs, show h U / U - k = (h U - U * k) / U by field_simp, abs_div, abs_of_pos up]
      exact div_le_div_of_nonneg_right (by simpa only [h, k, mul_div_assoc] using he) up.le
    · have z := Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.const_mul B
      simpa [id_eq, mul_div_assoc] using z
  have hn : Tendsto (fun U : ℝ => h U / U) atTop (𝓝 k) := by
    simpa using herr.add_const k
  have hq := hn.div dyadic_mass_limit (by positivity : (1 / (2 * Real.pi) : ℝ) ≠ 0)
  have heq : k / (1 / (2 * Real.pi)) = 3 / 4 - Real.log 2 := by dsimp [k]; field_simp
  rw [heq] at hq
  apply hq.congr'
  obtain ⟨c, C, hc, hC, hm⟩ := dyadic_mass_bounds
  filter_upwards [hm, eventually_gt_atTop (1 : ℝ)] with U hm hu
  have up : 0 < U := by linarith
  have hl := Real.log_pos hu
  have hmpos : 0 < mass U := lt_of_lt_of_le (by positivity) hm.1
  let f : C(Space P, ℝ) := ⟨fun x => x.2.1, continuous_fst.comp continuous_snd⟩
  change _ = Real.log U * ((∫ x, f x ∂mu P U) - 1 / 2)
  rw [integral_mu]
  change (h U / U) / (mass U / (U * Real.log U)) =
    Real.log U * (massSum U (fun ρ => height U ρ.im) / mass U - 1 / 2)
  dsimp only [h]
  rw [massSum_sub_half]
  field_simp [hmpos.ne', hl.ne', up.ne']

end RiemannResearch.Analysis.DyadicZeroWasserstein
