import RiemannResearch.RH.MertensFirstMomentEnvelope
import RiemannResearch.RH.QSquarefreeVKDisplacement
import RiemannResearch.NumberTheory.PrimeNumberTheorem.Wiener

/-!
# A weighted first absolute moment at the Vinogradov–Korobov scale

Gerhold, Acta Arith. 142 (2010), eq. (2), DOI 10.4064/aa142-2-8, records
the Mertens estimate used here as an explicit arithmetic hypothesis.
Signed pairing uses an envelope linear in the witness. Any rate c strictly
smaller than the Mertens exponent a is admissible in the first-moment test.
-/
noncomputable section
open Filter
open scoped Topology
namespace RiemannResearch.RH.QMertensFirstMoment
open RiemannResearch.Analysis RiemannResearch.NumberTheory.PrimeNumberTheorem
open ZetaTwoHilbert ZetaTwoProbability QSquarefreeDisplacementRigidity

private theorem vk_absorbs_log (t : ℝ) (ht : 0 < t) :
    ∀ᶠ y : ℝ in atTop, Real.log y ≤ Real.exp (t * vkProfile y) := by
  have hL := Real.tendsto_log_atTop.comp Real.tendsto_log_atTop
  filter_upwards [vkProfile_dominates_logLog_sq t ht,
    hL.eventually (eventually_ge_atTop (1 : ℝ)),
    Real.tendsto_log_atTop.eventually (eventually_gt_atTop (0 : ℝ))] with y h hs hy
  change 1 ≤ Real.log (Real.log y) at hs
  have hlt : Real.log (Real.log y) ≤ t * vkProfile y := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hs) (show 0 ≤ Real.log (Real.log y) by linarith)]
  simpa only [Real.exp_log hy] using Real.exp_le_exp.mpr hlt

/-- Uniform domination in the cutoff and all physical sites. The additive
constant 2 has finite first moment for every element of the Q Hilbert space. -/
theorem errorEnvelope_eventually_le_vk (a c : ℝ) (hc : 0 < c) (hca : c < a) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ᶠ N : ℕ in atTop, ∀ n : ℕ,
      errorEnvelope N n (Real.exp (-a * vkProfile (N : ℝ))) ≤
        2 + K * ((n : ℝ) * Real.exp (-c * vkProfile (n : ℝ))) := by
  let s := (a + c) / 2
  let v := (s + c) / 2
  let δ := (s - v) / (s * c)
  have hcs : c < s := by dsimp [s]; linarith
  have hsa : s < a := by dsimp [s]; linarith
  have hcv : c < v := by dsimp [v]; linarith
  have hvs : v < s := by dsimp [v]; linarith
  have hs : 0 < s := hc.trans hcs
  have ha : 0 < a := hc.trans hca
  have hδ : 0 < δ := div_pos (sub_pos.mpr hvs) (mul_pos hs hc)
  have hδeq : s * (δ * c) = s - v := by
    dsimp [δ]
    field_simp [hs.ne', hc.ne'] <;> ring
  let K := 3 + 5 * (a / (a - s))
  have hquot : 0 ≤ a / (a - s) := div_nonneg ha.le (sub_pos.mpr hsa).le
  have hK : 3 ≤ K := by dsimp [K]; linarith
  have hK0 : 0 ≤ K := by linarith
  refine ⟨K, hK0, ?_⟩
  obtain ⟨X, hX⟩ := eventually_atTop.1 (vk_absorbs_log (v - c) (sub_pos.mpr hcv))
  have hnat : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  filter_upwards [hnat.eventually (eventually_ge_atTop X),
    hnat.eventually (vkProfile_eventual_log_increment δ hδ),
    hnat.eventually vkProfile_eventually_mono,
    hnat.eventually (vkProfile_tendsto_atTop.eventually (eventually_ge_atTop (0 : ℝ))),
    eventually_ge_atTop (1 : ℕ)] with N hNX hinc hmono hPN hN n
  have hnr0 : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have hne : 0 ≤ (n : ℝ) * Real.exp (-c * vkProfile (n : ℝ)) :=
    mul_nonneg hnr0 (Real.exp_pos _).le
  rw [errorEnvelope]
  split_ifs with hsmall
  · linarith [mul_nonneg hK0 hne]
  have hNn : N ≤ n := by omega
  have hNnr : (N : ℝ) ≤ n := by exact_mod_cast hNn
  have hNr : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hnr := hNr.trans_le hNnr
  have hPn := hPN.trans (hmono (n : ℝ) hNnr)
  by_cases hcut : (N : ℝ) ≤ (n : ℝ) * Real.exp (-c * vkProfile (n : ℝ))
  · apply (min_le_left _ _).trans
    linarith [mul_le_mul_of_nonneg_right hK hne]
  · apply (min_le_right _ _).trans
    have hl := Real.log_lt_log (mul_pos hnr (Real.exp_pos _)) (lt_of_not_ge hcut)
    rw [Real.log_mul hnr.ne' (Real.exp_pos _).ne', Real.log_exp] at hl
    have hspan : Real.log (n : ℝ) - Real.log (N : ℝ) ≤ c * vkProfile (n : ℝ) := by linarith
    have hinc' := (hinc (n : ℝ) hNnr).trans (mul_le_mul_of_nonneg_left hspan hδ.le)
    have hx := mul_le_mul_of_nonneg_left hinc' hs.le
    have hprod : s * (δ * (c * vkProfile (n : ℝ))) = (s - v) * vkProfile (n : ℝ) := by
      rw [← hδeq]; ring
    rw [hprod] at hx
    have he_s : Real.exp (-s * vkProfile (N : ℝ)) ≤ Real.exp (-v * vkProfile (n : ℝ)) :=
      Real.exp_le_exp.mpr (by linarith only [hx])
    have hea_s : Real.exp (-a * vkProfile (N : ℝ)) ≤ Real.exp (-s * vkProfile (N : ℝ)) :=
      Real.exp_le_exp.mpr (by nlinarith [mul_nonneg (sub_pos.mpr hsa).le hPN])
    have he_a := hea_s.trans he_s
    have he_v : Real.exp (-v * vkProfile (n : ℝ)) ≤ Real.exp (-c * vkProfile (n : ℝ)) :=
      Real.exp_le_exp.mpr (by nlinarith [mul_nonneg (sub_pos.mpr hcv).le hPn])
    have hlTerm : Real.exp (-a * vkProfile (N : ℝ)) * Real.log (n : ℝ) ≤
        Real.exp (-c * vkProfile (n : ℝ)) := by
      calc
        _ ≤ Real.exp (-v * vkProfile (n : ℝ)) * Real.exp ((v - c) * vkProfile (n : ℝ)) :=
          mul_le_mul he_a (hX n (hNX.trans hNnr))
            (Real.log_nonneg (by exact_mod_cast (show 1 ≤ n by omega))) (Real.exp_pos _).le
        _ = _ := by rw [← Real.exp_add]; congr 1; ring
    have hEnt := (exponential_entropy_le a s (vkProfile (N : ℝ)) hs.le hsa).trans
      (mul_le_mul_of_nonneg_left (he_s.trans he_v) hquot)
    have hcoeff : Real.exp (-a * vkProfile (N : ℝ)) * (2 + Real.log (n : ℝ)) +
        5 * (Real.exp (-a * vkProfile (N : ℝ)) *
          (1 + Real.log (1 / Real.exp (-a * vkProfile (N : ℝ))))) ≤
        K * Real.exp (-c * vkProfile (n : ℝ)) := by
      dsimp only [K]
      linarith only [hlTerm, hEnt, he_a.trans he_v]
    linarith only [mul_le_mul_of_nonneg_left hcoeff hnr0]

/-- A Mertens exponent a controls signed witness pairings for every weighted
first-moment exponent c<a. After removing the charge at 0 the series is,
up to the constant zeta(2), the sum of (1+|d(n)|) exp(-c Φ(n))/n. -/
theorem residual_zero_of_vk_weighted_first_moment (a c : ℝ)
    (hc : 0 < c) (hca : c < a)
    (hM : ∀ᶠ x : ℝ in atTop, |M x| ≤ Real.exp (-a * vkProfile x) * x)
    (hd : Summable (fun n : ℕ => positiveQWeight n * ((n : ℝ) *
      Real.exp (-c * vkProfile (n : ℝ))) * (1 + |qSequence displacement n|))) :
    ZetaTwoOptimizerStage.limitingResidual = 0 := by
  classical
  choose p hpl hpp using (fun j : ℕ => Nat.exists_infinite_primes (j + 2))
  let q : ℕ → ℕ := fun j => p j - 1
  have hq : Tendsto q atTop atTop := by
    apply tendsto_atTop.2
    intro k
    filter_upwards [eventually_ge_atTop k] with j hj
    have := hpl j
    dsimp [q]; omega
  have hlegal : ∀ᶠ j : ℕ in atTop, Squarefree (q j + 1) := by
    apply Eventually.of_forall
    intro j
    have hqp : q j + 1 = p j := by have := hpl j; dsimp [q]; omega
    rw [hqp]; exact (hpp j).squarefree
  have hqr : Tendsto (fun j => (q j : ℝ)) atTop atTop :=
    (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop).comp hq
  let ε : ℕ → ℝ := fun j => Real.exp (-a * vkProfile (q j : ℝ))
  have ha := hc.trans hca
  have hlarge : ∀ᶠ j : ℕ in atTop, 6 ≤ a * vkProfile (q j : ℝ) :=
    (Tendsto.const_mul_atTop ha (vkProfile_tendsto_atTop.comp hqr)).eventually
      (eventually_ge_atTop (6 : ℝ))
  have hε : ∀ᶠ j : ℕ in atTop, 0 < ε j ∧ ε j ≤ 1 ∧
      ε j * (1 + Real.log (1 / ε j)) ≤ 1 / 2 := by
    filter_upwards [hlarge] with j hj
    refine ⟨Real.exp_pos _, Real.exp_le_one_iff.mpr (by linarith), ?_⟩
    simpa only [ε, neg_mul] using exponential_entropy_small (a * vkProfile (q j : ℝ)) hj
  obtain ⟨x₀, hx₀⟩ := eventually_atTop.1 hM
  have htail : ∀ᶠ j : ℕ in atTop, ∀ y : ℝ, (q j : ℝ) ≤ y → |M y| ≤ ε j * y := by
    filter_upwards [hqr.eventually (eventually_ge_atTop x₀),
      hqr.eventually vkProfile_eventually_mono] with j hj hm y hy
    apply (hx₀ y (hj.trans hy)).trans
    apply mul_le_mul_of_nonneg_right _ ((Nat.cast_nonneg (q j)).trans hy)
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonpos_left (hm y hy) (neg_nonpos.mpr ha.le))
  obtain ⟨K, hK, henv⟩ := errorEnvelope_eventually_le_vk a c hc hca
  let F : ℕ → ℝ := fun n => positiveQWeight n * (1 + |qSequence displacement n|)
  let H : ℕ → ℝ := fun n => positiveQWeight n * ((n : ℝ) *
    Real.exp (-c * vkProfile (n : ℝ))) * (1 + |qSequence displacement n|)
  have hF : Summable F := by
    refine (positiveQWeight_summable.add
      (qSequence_product_summable qOne displacement).abs).congr ?_
    intro n
    by_cases hn : n = 0
    · subst n; simp [F, positiveQWeight]
    · simp [F, qOneSequence, hn, abs_mul, abs_of_nonneg (positiveQWeight_nonneg n), mul_add]
  refine residual_zero_of_summable_mertens_first_moment q hq ε hlegal hε htail
    (fun n => 2 * F n + K * H n) ((hF.mul_left 2).add (hd.mul_left K)) ?_
  filter_upwards [hq.eventually henv] with j hj n
  have h := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (hj n) (positiveQWeight_nonneg n))
    (show 0 ≤ 1 + |qSequence displacement n| by positivity)
  change positiveQWeight n * errorEnvelope (q j) n (Real.exp (-a * vkProfile (q j : ℝ))) *
    (1 + |qSequence displacement n|) ≤ 2 * F n + K * H n
  apply h.trans
  dsimp [F, H]
  exact le_of_eq (by ring)

/-- RH follows from the weighted first moment via vanishing of the residual. -/
theorem riemannHypothesis_of_vk_weighted_first_moment (a c : ℝ)
    (hc : 0 < c) (hca : c < a)
    (hM : ∀ᶠ x : ℝ in atTop, |M x| ≤ Real.exp (-a * vkProfile x) * x)
    (hd : Summable (fun n : ℕ => positiveQWeight n * ((n : ℝ) *
      Real.exp (-c * vkProfile (n : ℝ))) * (1 + |qSequence displacement n|))) :
    RiemannHypothesis :=
  rh_of_zero_projection_residual (residual_zero_of_vk_weighted_first_moment a c hc hca hM hd)

/-- The strict first-moment pointwise coefficient is b<a. The convergent
comparison series is the repository's 1/(n (log n)^2) in Wiener.lean. -/
theorem riemannHypothesis_of_vk_first_moment_exponential_displacement
    (a b C D : ℝ) (hb : 0 < b) (hba : b < a)
    (hM : ∀ᶠ x : ℝ in atTop, |M x| ≤ (C * Real.exp (-a * vkProfile x)) * x)
    (hd : ∀ᶠ n : ℕ in atTop, |qSequence displacement n| ≤
      D * Real.exp (b * vkProfile (n : ℝ))) : RiemannHypothesis := by
  let a' := (a + b) / 2
  let c := (a' + b) / 2
  have hba' : b < a' := by dsimp [a']; linarith
  have ha'a : a' < a := by dsimp [a']; linarith
  have hbc : b < c := by dsimp [c]; linarith
  have hca' : c < a' := by dsimp [c]; linarith
  apply riemannHypothesis_of_vk_weighted_first_moment a' c (hb.trans hbc) hca'
    (QSquarefreeMertensProfileCriterion.mertens_vk_absorb_constant a a' C ha'a hM)
  let t := (c - b) / 2
  have ht : 0 < t := by dsimp [t]; linarith
  let A : ℝ := 1 + |D|
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hs := summable_inv_mul_log_sq.mul_left (A / zetaTwo)
  apply hs.of_norm_bounded_eventually_nat
  have hnat : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  filter_upwards [hd, hnat.eventually (vk_absorbs_log t ht),
    hnat.eventually (vkProfile_tendsto_atTop.eventually (eventually_ge_atTop (0 : ℝ))),
    eventually_ge_atTop (2 : ℕ)] with n hnD hlog hV hn
  let V := vkProfile (n : ℝ)
  have hn1 : (1 : ℝ) < n := by exact_mod_cast (show 1 < n by omega)
  have hnr : (0 : ℝ) < n := by linarith
  have hlpos := Real.log_pos hn1
  have hbexp : 1 ≤ Real.exp (b * V) := Real.one_le_exp_iff.mpr (mul_nonneg hb.le hV)
  have hd' := hnD.trans (mul_le_mul_of_nonneg_right (le_abs_self D)
    (Real.exp_pos (b * V)).le)
  have hmajor : 1 + |qSequence displacement n| ≤ A * Real.exp (b * V) := by
    dsimp only [A]
    linarith only [hd', hbexp]
  have he : Real.exp (-c * V) * (1 + |qSequence displacement n|) ≤
      A * Real.exp ((b - c) * V) := by
    calc
      _ ≤ Real.exp (-c * V) * (A * Real.exp (b * V)) :=
        mul_le_mul_of_nonneg_left hmajor (Real.exp_pos _).le
      _ = _ := by rw [mul_left_comm, ← Real.exp_add]; congr 2; ring
  have hsquare := mul_self_le_mul_self hlpos.le hlog
  change Real.log (n : ℝ) * Real.log (n : ℝ) ≤ Real.exp (t * V) * Real.exp (t * V) at hsquare
  have hex : (Real.exp (t * V) * Real.exp (t * V)) * Real.exp ((b - c) * V) = 1 := by
    rw [← Real.exp_add, ← Real.exp_add]
    have hz : t * V + t * V + (b - c) * V = 0 := by dsimp [t]; ring
    rw [hz, Real.exp_zero]
  have hsave : Real.exp ((b - c) * V) ≤ 1 / (Real.log (n : ℝ)) ^ 2 := by
    apply (le_div_iff₀ (sq_pos_of_pos hlpos)).mpr
    have hs' := mul_le_mul_of_nonneg_right hsquare (Real.exp_pos ((b - c) * V)).le
    rw [hex] at hs'
    linarith only [hs']
  have hh := he.trans (mul_le_mul_of_nonneg_left hsave hA)
  change ‖positiveQWeight n * ((n : ℝ) * Real.exp (-c * V)) *
      (1 + |qSequence displacement n|)‖ ≤
    (A / zetaTwo) * ((n : ℝ) * (Real.log (n : ℝ)) ^ 2)⁻¹
  have hterm_nonneg : 0 ≤ positiveQWeight n * ((n : ℝ) * Real.exp (-c * V)) *
      (1 + |qSequence displacement n|) :=
    mul_nonneg (mul_nonneg (positiveQWeight_nonneg n)
      (mul_nonneg hnr.le (Real.exp_pos _).le)) (by positivity)
  rw [Real.norm_eq_abs, abs_of_nonneg hterm_nonneg]
  calc
    _ = (positiveQWeight n * (n : ℝ)) *
        (Real.exp (-c * V) * (1 + |qSequence displacement n|)) := by ring
    _ ≤ (positiveQWeight n * (n : ℝ)) * (A * (1 / (Real.log (n : ℝ)) ^ 2)) :=
      mul_le_mul_of_nonneg_left hh (mul_nonneg (positiveQWeight_nonneg n) hnr.le)
    _ = _ := by
      unfold positiveQWeight
      field_simp [zetaTwo_pos.ne', hnr.ne', hlpos.ne']
      <;> ring

/-- The contribution of the constant sequence to the VK weighted first
moment is finite for every positive rate. -/
theorem summable_vk_first_moment_constant (c : ℝ) (hc : 0 < c) :
    Summable (fun n : ℕ => positiveQWeight n *
      ((n : ℝ) * Real.exp (-c * vkProfile (n : ℝ)))) := by
  apply (summable_inv_mul_log_sq.mul_left (1 / zetaTwo)).of_norm_bounded_eventually_nat
  have hnat : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  filter_upwards [hnat.eventually (vk_absorbs_log (c / 2) (by positivity)),
    eventually_ge_atTop (2 : ℕ)] with n hlog hn
  let V := vkProfile (n : ℝ)
  have hn1 : (1 : ℝ) < n := by exact_mod_cast (show 1 < n by omega)
  have hnr : (0 : ℝ) < n := by linarith
  have hlpos := Real.log_pos hn1
  have hsquare := mul_self_le_mul_self hlpos.le hlog
  change Real.log (n : ℝ) * Real.log (n : ℝ) ≤
    Real.exp (c / 2 * V) * Real.exp (c / 2 * V) at hsquare
  have hex : (Real.exp (c / 2 * V) * Real.exp (c / 2 * V)) * Real.exp (-c * V) = 1 := by
    rw [← Real.exp_add, ← Real.exp_add]
    have hz : c / 2 * V + c / 2 * V + -c * V = 0 := by ring
    rw [hz, Real.exp_zero]
  have hsave : Real.exp (-c * V) ≤ 1 / (Real.log (n : ℝ)) ^ 2 := by
    apply (le_div_iff₀ (sq_pos_of_pos hlpos)).mpr
    have hs := mul_le_mul_of_nonneg_right hsquare (Real.exp_pos (-c * V)).le
    rw [hex] at hs
    linarith only [hs]
  change ‖positiveQWeight n * ((n : ℝ) * Real.exp (-c * V))‖ ≤
    (1 / zetaTwo) * ((n : ℝ) * (Real.log (n : ℝ)) ^ 2)⁻¹
  have hterm : 0 ≤ positiveQWeight n * ((n : ℝ) * Real.exp (-c * V)) :=
    mul_nonneg (positiveQWeight_nonneg n) (mul_nonneg hnr.le (Real.exp_pos _).le)
  rw [Real.norm_eq_abs, abs_of_nonneg hterm]
  calc
    _ = (positiveQWeight n * (n : ℝ)) * Real.exp (-c * V) := by ring
    _ ≤ (positiveQWeight n * (n : ℝ)) * (1 / (Real.log (n : ℝ)) ^ 2) :=
      mul_le_mul_of_nonneg_left hsave (mul_nonneg (positiveQWeight_nonneg n) hnr.le)
    _ = _ := by
      unfold positiveQWeight
      field_simp [zetaTwo_pos.ne', hnr.ne', hlpos.ne']
      <;> ring

/-- Only the first absolute moment of the actual displacement is required.
A fixed ordinary Mertens prefactor costs an arbitrarily small rate loss. -/
theorem residual_zero_of_vk_displacement_absolute_moment (a c C : ℝ)
    (hc : 0 < c) (hca : c < a)
    (hM : ∀ᶠ x : ℝ in atTop, |M x| ≤ (C * Real.exp (-a * vkProfile x)) * x)
    (hd : Summable (fun n : ℕ => positiveQWeight n * ((n : ℝ) *
      Real.exp (-c * vkProfile (n : ℝ))) * |qSequence displacement n|)) :
    ZetaTwoOptimizerStage.limitingResidual = 0 := by
  let a' := (a + c) / 2
  have ha' : c < a' := by dsimp [a']; linarith
  have h'a : a' < a := by dsimp [a']; linarith
  apply residual_zero_of_vk_weighted_first_moment a' c hc ha'
    (QSquarefreeMertensProfileCriterion.mertens_vk_absorb_constant a a' C h'a hM)
  refine ((summable_vk_first_moment_constant c hc).add hd).congr ?_
  intro n
  ring

/-- Under the published Mertens premise the pure moment is equivalent to
zero projection residual at any fixed interior exponent. -/
theorem residual_zero_iff_vk_displacement_absolute_moment (a c C : ℝ)
    (hc : 0 < c) (hca : c < a)
    (hM : ∀ᶠ x : ℝ in atTop, |M x| ≤ (C * Real.exp (-a * vkProfile x)) * x) :
    ZetaTwoOptimizerStage.limitingResidual = 0 ↔
      Summable (fun n : ℕ => positiveQWeight n * ((n : ℝ) *
      Real.exp (-c * vkProfile (n : ℝ))) * |qSequence displacement n|) := by
  constructor
  · intro hr
    rw [displacement_eq_zero_of_residual_eq_zero hr]
    have hzero (n : ℕ) : qSequence (0 : QHilbert) n = 0 := by
      cases n <;> simp [qSequence]
    simp only [hzero, abs_zero, mul_zero, summable_zero]
  · exact residual_zero_of_vk_displacement_absolute_moment a c C hc hca hM

/-- The pure moment criterion implies Mathlib's RH. -/
theorem riemannHypothesis_of_vk_displacement_absolute_moment (a c C : ℝ)
    (hc : 0 < c) (hca : c < a)
    (hM : ∀ᶠ x : ℝ in atTop, |M x| ≤ (C * Real.exp (-a * vkProfile x)) * x)
    (hd : Summable (fun n : ℕ => positiveQWeight n * ((n : ℝ) *
      Real.exp (-c * vkProfile (n : ℝ))) * |qSequence displacement n|)) :
    RiemannHypothesis :=
  rh_of_zero_projection_residual
    (residual_zero_of_vk_displacement_absolute_moment a c C hc hca hM hd)

/-- A physical growth rate strictly inside the ordinary Mertens saving forces the
actual squarefree projection residual to vanish. -/
theorem residual_zero_of_vk_exponential_displacement (a b C D : ℝ)
    (hb : 0 < b) (hba : b < a)
    (hM : ∀ᶠ x : ℝ in atTop, |M x| ≤ (C * Real.exp (-a * vkProfile x)) * x)
    (hd : ∀ᶠ n : ℕ in atTop, |qSequence displacement n| ≤
      D * Real.exp (b * vkProfile n)) :
    ZetaTwoOptimizerStage.limitingResidual = 0 := by
  let c := (a + b) / 2
  have hbc : b < c := by dsimp only [c]; linarith
  have hca : c < a := by dsimp only [c]; linarith
  apply residual_zero_of_vk_displacement_absolute_moment a c C (hb.trans hbc) hca hM
  apply ((summable_vk_first_moment_constant (c - b) (sub_pos.mpr hbc)).mul_left D).of_norm_bounded_eventually_nat
  filter_upwards [hd] with n hn
  let t := vkProfile n
  have hq := positiveQWeight_nonneg n
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  change ‖positiveQWeight n * ((n : ℝ) * Real.exp (-c * t)) *
    |qSequence displacement n|‖ ≤ D * (positiveQWeight n * ((n : ℝ) * Real.exp (-(c-b) * t)))
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (mul_nonneg hq
    (mul_nonneg hn0 (Real.exp_pos _).le)) (abs_nonneg _))]
  calc
    _ ≤ (positiveQWeight n * ((n : ℝ) * Real.exp (-c * t))) *
        (D * Real.exp (b * t)) := mul_le_mul_of_nonneg_left hn
          (mul_nonneg hq (mul_nonneg hn0 (Real.exp_pos _).le))
    _ = (D * (positiveQWeight n * (n : ℝ))) *
        (Real.exp (-c * t) * Real.exp (b * t)) := by ring
    _ = _ := by
      rw [← Real.exp_add, show -c * t + b * t = -(c-b) * t by ring]
      ring

/-- The boxed VK condition is equivalent to zero squarefree projection error
under the ordinary Mertens bound alone. -/
theorem residual_zero_iff_vk_log_displacement (a C : ℝ) (ha : 0 < a)
    (hM : ∀ᶠ x : ℝ in atTop, |M x| ≤ (C * Real.exp (-a * vkProfile x)) * x) :
    ZetaTwoOptimizerStage.limitingResidual = 0 ↔
      Tendsto (fun n : ℕ => Real.log (2 + |qSequence displacement n|) /
        vkProfile (n : ℝ)) atTop (𝓝 0) := by
  have hV : Tendsto (fun n : ℕ => vkProfile (n : ℝ)) atTop atTop :=
    vkProfile_tendsto_atTop.comp tendsto_natCast_atTop_atTop
  constructor
  · intro hr
    rw [displacement_eq_zero_of_residual_eq_zero hr]
    have hz (n : ℕ) : qSequence (0 : QHilbert) n = 0 := by cases n <;> simp [qSequence]
    simpa only [hz, abs_zero, add_zero] using hV.const_div_atTop (Real.log 2)
  · intro hd
    have hb : 0 < a / 2 := by positivity
    apply residual_zero_of_vk_exponential_displacement a (a/2) C 1 hb (by linarith) hM
    filter_upwards [hd.eventually (gt_mem_nhds hb), hV.eventually (eventually_gt_atTop (0 : ℝ))]
      with n hn hp
    have he := Real.exp_le_exp.mpr ((div_lt_iff₀ hp).mp hn).le
    rw [Real.exp_log (by positivity)] at he
    linarith

end RiemannResearch.RH.QMertensFirstMoment
