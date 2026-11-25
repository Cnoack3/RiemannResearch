import RiemannResearch.Analysis.DyadicZeroWasserstein
import RiemannResearch.Analysis.PrimePhaseWindows
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Topology.Instances.EReal.Lemmas

/-!
# Additive angular witnesses for the dyadic one-zero law

The sum cost permits the height and all single-coordinate angular witnesses to
be used simultaneously. The Fourier input for the first harmonic is the
dyadic count-normalized Ford–Zaharescu limit in `PrimePhaseWindows`.
-/

noncomputable section
open Filter MeasureTheory Set Zeta23
open scoped Topology BigOperators
namespace RiemannResearch.Analysis.DyadicZeroWasserstein
open ActualZeroOrdinate PrimeTorusHaar MontgomeryLocalMass PoissonHaar
open PrimePhaseWindows

local instance : Fact (0 < (1 : ℝ)) := ⟨zero_lt_one⟩

/-- A real angular character at integer frequency. -/
def harmonicCosine (k : ℤ) : C(CircleSpace, ℝ) :=
  ⟨fun z => (fourier k z).re, Complex.continuous_re.comp (fourier k).continuous⟩

theorem harmonicCosine_primePhase (k : ℤ) (p : ℕ) (t : ℝ) :
    harmonicCosine k (PrimePhaseTorus.primePhase p t) =
      Real.cos ((k : ℝ) * Real.log p * t) := by
  change (fourier k (PrimePhaseTorus.primePhase p t)).re = _
  rw [PrimePhaseTorus.fourier_primePhase]
  have hc (u : ℝ) : (Complex.exp (Complex.I * (u : ℂ))).re = Real.cos u := by
    simp [Complex.exp_re, Complex.mul_re, Complex.mul_im]
  exact hc _

theorem integral_harmonicCosine {k : ℤ} (hk : k ≠ 0) :
    (∫ z, harmonicCosine k z ∂(AddCircle.haarAddCircle (T := 1))) = 0 := by
  let m := AddCircle.haarAddCircle (T := 1)
  have hi : Integrable (fourier k : C(CircleSpace, ℂ)) m :=
    (integrable_const ‖(fourier k : C(CircleSpace, ℂ))‖).mono'
      (fourier k).continuous.aestronglyMeasurable
      (Eventually.of_forall (fun x => (fourier k).norm_coe_le_norm x))
  have hz : (∫ z, fourier k z ∂m) = 0 := by
    have h := ZeroOrdinate.haarIntegral_fourier k
    change (∫ z : CircleSpace, fourier k z ∂AddCircle.haarAddCircle) = _ at h
    simpa only [m, if_neg hk] using h
  change (∫ z, RCLike.re (fourier k z) ∂m) = 0
  rw [integral_re hi, hz] <;> simp

/-- Cumulative real sums and the physical window use exactly the same
multiplicities. -/
theorem massSum_eq_realSum_sub {U : ℝ} (hU : 0 ≤ U) (F : ℂ → ℝ) :
    massSum U F = realSum (2 * U) F - realSum U F := by
  rw [massSum_weighted]
  have h := congrArg Complex.re
    (sum_sub_eq_window_sum U (2 * U) hU (by linarith) (fun ρ => (F ρ : ℂ)))
  simpa [sum, realSum, Complex.re_sum, Complex.mul_re] using h.symm

/-- The empirical angular marginal minus its Haar mean. -/
def angularBias (p : ℕ) (w : C(CircleSpace, ℝ)) (U : ℝ) : ℝ :=
  massSum U (fun ρ => w (PrimePhaseTorus.primePhase p ρ.im)) / mass U -
    ∫ z, w z ∂(AddCircle.haarAddCircle (T := 1))

private theorem integrable_nu_test (P : Finset ℕ) (f : C(Space P, ℝ)) :
    Integrable f (nu P) := by
  obtain ⟨K,hK,hm⟩ := nu_compact P
  obtain ⟨M,hM⟩ := hK.bddAbove_image f.continuous.norm.continuousOn
  have hfull : ∀ᵐ x ∂nu P, x ∈ K :=
    ae_iff.mpr ((prob_compl_eq_zero_iff hK.measurableSet).2 hm)
  apply (integrable_const M).mono' f.continuous.aestronglyMeasurable
  filter_upwards [hfull] with x hx
  exact hM ⟨x,hx,rfl⟩

private theorem integral_nu_angle (P : Finset ℕ) (p : P) (w : C(CircleSpace, ℝ)) :
    (∫ x : Space P, w (x.2.2 p) ∂nu P) =
      ∫ z, w z ∂(AddCircle.haarAddCircle (T := 1)) := by
  rw [nu, Measure.dirac_prod, integral_map (by fun_prop) (by fun_prop)]
  change (∫ x : ℝ × Torus P, w (x.2 p) ∂unif.prod (haar P)) = _
  rw [integral_fun_snd (μ := unif) (ν := haar P) (fun z => w (z p))]
  simp only [Measure.real, measure_univ, ENNReal.toReal_one, one_smul]
  have hm := measurePreserving_eval (fun _ : P => AddCircle.haarAddCircle (T := 1)) p
  calc
    (∫ z : Torus P, w (z p) ∂haar P) =
        ∫ t, w t ∂(Measure.map (Function.eval p) (haar P)) :=
      (integral_map hm.measurable.aemeasurable w.continuous.aestronglyMeasurable).symm
    _ = _ := by exact congrArg (fun m => ∫ z, w z ∂m) hm.map_eq

/-- Each angular test has its own unit Lipschitz budget in the sum metric.
The height limit and the finitely many signed angular limits are added. -/
theorem eventually_horizontal_add_angular_lower (P : Finset ℕ)
    (w : P → C(CircleSpace, ℝ)) (b : P → ℝ)
    (hw : ∀ p, w p 0 = 0)
    (hlip : ∀ p x y, |w p x - w p y| ≤ dist x y)
    (hb : ∀ p : P, Tendsto (fun U => Real.log U * angularBias p (w p) U) atTop (𝓝 (b p)))
    {c : ℝ} (hc : c < 3 / 4 - Real.log 2 + ∑ p, b p) :
    ∀ᶠ U : ℝ in atTop, massSum U (fun ρ => |ρ.re - 1 / 2|) / mass U + c / Real.log U ≤
      wassersteinOne P (mu P U) (nu P) := by
  classical
  let h : C(Space P, ℝ) := ⟨fun x => x.2.1, continuous_fst.comp continuous_snd⟩
  let g : C(Space P, ℝ) := ⟨fun x => |x.1 - 1 / 2| + x.2.1, by fun_prop⟩
  let a (p : P) : C(Space P, ℝ) :=
    ⟨fun x => w p (x.2.2 p), (w p).continuous.comp ((continuous_apply p).comp
      (continuous_snd.comp continuous_snd))⟩
  let f : C(Space P, ℝ) := g + ∑ p, a p
  have hf (x : Space P) : f x = (|x.1 - 1 / 2| + x.2.1) + ∑ p, w p (x.2.2 p) := by
    simp [f, g, a]
  have had : Admissible P f := by
    constructor
    · simp [hf, hw]
    · intro x y
      rw [hf, hf]
      unfold cost
      rw [add_sub_add_comm, add_sub_add_comm (|x.1 - 1 / 2|) x.2.1, ← Finset.sum_sub_distrib]
      apply (abs_add_le _ _).trans
      apply add_le_add
      · apply (abs_add_le _ _).trans
        refine add_le_add ?_ le_rfl
        simpa only [sub_sub_sub_cancel_right] using
          (abs_abs_sub_abs_le_abs_sub (x.1 - 1 / 2) (y.1 - 1 / 2))
      · exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun p _ =>
          hlip p (x.2.2 p) (y.2.2 p)))
  have htarget : (∫ x, f x ∂nu P) = 1 / 2 + ∑ p, ∫ z, w p z ∂AddCircle.haarAddCircle := by
    have hg : (∫ x, g x ∂nu P) = 1 / 2 := by
      rw [← integral_nu_height P]
      simp only [nu, Measure.dirac_prod]
      rw [integral_map (by fun_prop) g.continuous.aestronglyMeasurable,
          integral_map (by fun_prop) (by fun_prop)]
      simp [g]
    have ha : ∀ p ∈ (Finset.univ : Finset P), Integrable (fun x => a p x) (nu P) :=
      fun p _ => integrable_nu_test P (a p)
    simp only [f, ContinuousMap.add_apply, ContinuousMap.sum_apply]
    rw [integral_add (integrable_nu_test P g) (integrable_finsetSum _ ha),
      integral_finsetSum _ ha, hg]
    congr 1
    apply Finset.sum_congr rfl
    exact fun p _ => integral_nu_angle P p (w p)
  have he (U : ℝ) : (∫ x, f x ∂mu P U) =
      massSum U (fun ρ => |ρ.re - 1 / 2|) / mass U + (∫ x, h x ∂mu P U) +
      ∑ p, massSum U (fun ρ => w p (PrimePhaseTorus.primePhase p ρ.im)) / mass U := by
    rw [integral_mu, integral_mu]
    simp only [hf, coord, h, massSum, primeOrbit, ContinuousMap.coe_mk,
      Finset.sum_add_distrib, add_div]
    congr 1
    rw [Finset.sum_comm]
    simp [div_eq_mul_inv, Finset.sum_mul]
  have hsum := tendsto_finsetSum Finset.univ (fun (p : P) _ => hb p)
  have ht := (height_mean_limit P).add hsum
  have hgt := (tendsto_order.1 ht).1 c hc
  obtain ⟨a₀,b₀,ha₀,hb₀,hm⟩ := dyadic_mass_bounds
  filter_upwards [hm, hgt, eventually_gt_atTop (1 : ℝ)] with U hm ht hU
  have hL := Real.log_pos hU
  have hu : 0 < U := by linarith
  have hpos : 0 < mass U := lt_of_lt_of_le (by positivity) hm.1
  have hn : 0 < Ncount U (2*U) := by unfold mass at hpos; exact_mod_cast hpos
  let _ := mu_probability P hn
  obtain ⟨A,hA⟩ := anchored_integral_bound P _ (mu_compact P hn)
  obtain ⟨B,hB⟩ := anchored_integral_bound P _ (nu_compact P)
  have hbb : BddAbove (differences P (mu P U) (nu P)) := by
    refine ⟨A+B, ?_⟩
    rintro _ ⟨j,hj,rfl⟩
    exact (abs_sub _ _).trans (add_le_add (hA j hj) (hB j hj))
  have hs : c / Real.log U ≤ (∫ x, h x ∂mu P U) - 1 / 2 + ∑ p : P, angularBias p (w p) U := by
    apply (div_le_iff₀ hL).2
    simpa only [h, Pi.add_apply, Finset.sum_apply, ContinuousMap.coe_mk, add_mul, Finset.sum_mul,
      mul_comm (Real.log U)] using ht.le
  have hmem : |(∫ x, f x ∂mu P U) - ∫ x, f x ∂nu P| ∈ differences P (mu P U) (nu P) :=
    ⟨f, had, rfl⟩
  apply le_trans _ (le_csSup hbb hmem)
  apply le_trans _ (le_abs_self _)
  rw [htarget, he]
  simp only [angularBias, Finset.sum_sub_distrib] at hs
  linarith only [hs]

/-- An anchored angular test with unit Lipschitz constant. -/
def firstCosineTest : C(CircleSpace, ℝ) :=
  ⟨fun z => (1 - harmonicCosine 1 z) / (2 * Real.pi), by fun_prop⟩

private theorem harmonicCosine_one_eq_norm (z : CircleSpace) :
    harmonicCosine 1 z = Real.cos (2 * Real.pi * ‖z‖) := by
  induction z using QuotientAddGroup.induction_on with
  | _ x =>
    change (fourier 1 (x : AddCircle (1 : ℝ))).re = _
    rw [fourier_coe_apply, UnitAddCircle.norm_eq]
    have hpos : 0 < 2 * Real.pi := by positivity
    have harg : |2 * Real.pi * x - (round x : ℝ) * (2 * Real.pi)| =
        2 * Real.pi * |x - (round x : ℝ)| := by
      rw [show 2 * Real.pi * x - (round x : ℝ) * (2 * Real.pi) =
        (2 * Real.pi) * (x - (round x : ℝ)) by ring, abs_mul, abs_of_pos hpos]
    rw [← harg, Real.cos_abs, Real.cos_sub_int_mul_two_pi]
    simp [Complex.exp_re, Complex.mul_re, Complex.mul_im, mul_assoc]

theorem firstCosineTest_lipschitz (x y : CircleSpace) :
    |firstCosineTest x - firstCosineTest y| ≤ dist x y := by
  change |(1 - harmonicCosine 1 x) / (2 * Real.pi) -
      (1 - harmonicCosine 1 y) / (2 * Real.pi)| ≤ _
  rw [← sub_div, sub_sub_sub_cancel_left, abs_div, abs_of_pos (by positivity : 0 < 2 * Real.pi)]
  apply (div_le_iff₀ (by positivity : 0 < 2 * Real.pi)).2
  rw [harmonicCosine_one_eq_norm, harmonicCosine_one_eq_norm]
  apply (Real.abs_cos_sub_cos_le _ _).trans
  rw [← mul_sub, abs_mul, abs_of_pos (by positivity : 0 < 2 * Real.pi), mul_comm (dist x y)]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  simpa only [dist_eq_norm, norm_sub_rev] using abs_norm_sub_norm_le y x

theorem tendsto_log_angularBias_firstCosine {p : ℕ} (hp : p.Prime) :
    Tendsto (fun U => Real.log U * angularBias p firstCosineTest U) atTop
      (𝓝 (Real.log p / (2 * Real.pi * Real.sqrt p))) := by
  have hi : Integrable (harmonicCosine 1) (AddCircle.haarAddCircle (T := 1)) :=
    (integrable_const ‖harmonicCosine 1‖).mono' (harmonicCosine 1).continuous.aestronglyMeasurable
      (Eventually.of_forall (fun x => (harmonicCosine 1).norm_coe_le_norm x))
  have hhaar : (∫ x, firstCosineTest x ∂AddCircle.haarAddCircle) = 1 / (2 * Real.pi) := by
    change (∫ x : CircleSpace, (1 - harmonicCosine 1 x) / (2 * Real.pi)
      ∂AddCircle.haarAddCircle) = _
    rw [integral_div, integral_sub (integrable_const _) hi,
      integral_harmonicCosine (by decide : (1 : ℤ) ≠ 0)]
    simp
  have h := (tendsto_log_mul_dyadicPrimeCosineMean hp).neg.div_const (2 * Real.pi)
  have hk : -(-Real.log p / Real.sqrt p) / (2 * Real.pi) =
      Real.log p / (2 * Real.pi * Real.sqrt p) := by
    field_simp [Real.pi_ne_zero, (Real.sqrt_pos.2 (Nat.cast_pos.mpr hp.pos)).ne']
  rw [hk] at h
  apply h.congr'
  obtain ⟨a,b,ha,hb,hm⟩ := dyadic_mass_bounds
  filter_upwards [hm, eventually_gt_atTop (1 : ℝ)] with U hm hU
  have hu : 0 < U := by linarith
  have hlog := Real.log_pos hU
  have hn : 0 < mass U := lt_of_lt_of_le (by positivity) hm.1
  let F := fun ρ : ℂ => Real.cos (Real.log p * ρ.im)
  have hsum : massSum U (fun ρ => firstCosineTest (PrimePhaseTorus.primePhase p ρ.im)) =
      (mass U - massSum U F) / (2 * Real.pi) := by
    simp only [massSum, firstCosineTest, ContinuousMap.coe_mk, harmonicCosine_primePhase,
      Int.cast_one, one_mul, div_eq_mul_inv, ← Finset.sum_mul, Finset.sum_sub_distrib,
      Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one, F]
    rw [show Fintype.card (Occ U) = Ncount U (2 * U) from card_windowCopies _ _]
    rfl
  have hmean : dyadicPrimeCosineMean p U = massSum U F / mass U := by
    rw [massSum_eq_realSum_sub hu.le F]
    rfl
  simp only [angularBias, hhaar, hsum, hmean]
  field_simp [hn.ne', Real.pi_ne_zero]
  ring

/-- The explicit first-character bound is unconditional for every fixed finite
prime set. Quantification over every strictly smaller constant also covers an
infinite extended-real lower limit. -/
theorem eventually_horizontal_add_primeCosine_lower (P : Finset ℕ)
    (hP : ∀ p ∈ P, Nat.Prime p) {c : ℝ}
    (hc : c < 3 / 4 - Real.log 2 + ∑ p ∈ P, Real.log p / (2 * Real.pi * Real.sqrt p)) :
    ∀ᶠ U : ℝ in atTop, massSum U (fun ρ => |ρ.re - 1 / 2|) / mass U + c / Real.log U ≤
      wassersteinOne P (mu P U) (nu P) := by
  apply eventually_horizontal_add_angular_lower P (fun _ => firstCosineTest)
    (fun p => Real.log (p : ℕ) / (2 * Real.pi * Real.sqrt (p : ℕ)))
  · intro p
    simp [firstCosineTest, harmonicCosine]
  · exact fun _ => firstCosineTest_lipschitz
  · exact fun p => tendsto_log_angularBias_firstCosine (hP p p.property)
  · rw [Finset.sum_coe_sort P (fun q : ℕ => Real.log q / (2 * Real.pi * Real.sqrt q))]
    exact hc

/-- The extended-real lower limit retains the possibility of divergence.
The estimate for every strictly smaller constant is sufficient. -/
theorem le_liminf_scaled_wasserstein (P : Finset ℕ) (B : ℝ)
    (h : ∀ c < B, ∀ᶠ U : ℝ in atTop,
      massSum U (fun ρ => |ρ.re - 1 / 2|) / mass U + c / Real.log U ≤
        wassersteinOne P (mu P U) (nu P)) :
    (B : EReal) ≤ liminf (fun U : ℝ =>
      ((Real.log U * (wassersteinOne P (mu P U) (nu P) -
        massSum U (fun ρ => |ρ.re - 1 / 2|) / mass U) : ℝ) : EReal)) atTop := by
  have ht : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hlim : Tendsto (fun n : ℕ => ((B - 1 / ((n : ℝ) + 1) : ℝ) : EReal))
      atTop (𝓝 (B : EReal)) :=
    EReal.tendsto_coe.mpr (by simpa only [sub_zero] using ht.const_sub B)
  apply le_of_tendsto' hlim
  intro n
  let c : ℝ := B - 1 / ((n : ℝ) + 1)
  have hc : c < B := sub_lt_self _ (by positivity)
  apply Filter.le_liminf_of_le (by isBoundedDefault)
  filter_upwards [h c hc, eventually_gt_atTop (1 : ℝ)] with U hu hU
  apply EReal.coe_le_coe_iff.mpr
  have hdiv := (div_le_iff₀ (Real.log_pos hU)).mp
    (show c / Real.log U ≤ wassersteinOne P (mu P U) (nu P) -
        massSum U (fun ρ => |ρ.re - 1 / 2|) / mass U by linarith)
  simpa only [mul_comm (Real.log U)] using hdiv

theorem primeCosine_le_liminf_scaled_wasserstein (P : Finset ℕ)
    (hP : ∀ p ∈ P, Nat.Prime p) :
    ((3 / 4 - Real.log 2 + ∑ p ∈ P, Real.log p / (2 * Real.pi * Real.sqrt p) : ℝ) : EReal) ≤
      liminf (fun U : ℝ => ((Real.log U * (wassersteinOne P (mu P U) (nu P) -
        massSum U (fun ρ => |ρ.re - 1 / 2|) / mass U) : ℝ) : EReal)) atTop :=
  le_liminf_scaled_wasserstein P _ (fun _ hc => eventually_horizontal_add_primeCosine_lower P hP hc)

end RiemannResearch.Analysis.DyadicZeroWasserstein
