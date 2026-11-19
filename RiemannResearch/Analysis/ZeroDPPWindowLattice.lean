import RiemannResearch.Analysis.ZeroDPPWindowVariance
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Tactic.Linarith

/-!
# Integer-valued windows and shrinking-width collision detection

Yamada's integer-count variance condition is given with its exact excess
term for translated windows of actual zero occurrences. See Yamada,
https://doi.org/10.1143/PTP.25.579, and Kuna, Lebowitz
and Speer, *Realizability of point processes*, (2.7)–(2.8),
https://arxiv.org/abs/math-ph/0612075. A one-sided bound on one shrinking
unfolded width detects excess equal-ordinate pairs and suffices for density
one of simple critical zeros and vanishing logarithmic DPP vacancy.
-/

noncomputable section
open Filter MeasureTheory Zeta23
open scoped BigOperators Topology
namespace RiemannResearch.Analysis.ZeroDPPCorrelation
open ActualZeroOrdinate ActualZeroCollisionCertificate ActualZeroWindowVariance
open OrdinateWindowVariance MontgomeryPositiveGap
open RiemannResearch.Probability.DPP.ZeroOrdinateInfinite

/-- The integer number of actual occurrences inside the translated clipped window. -/
def translatedWindowCard (T h t : ℝ) : ℕ :=
  (Finset.univ.filter (fun c : Copies T =>
    t ∈ Set.Ioc (max 0 (c.1.1.im - h)) (min T c.1.1.im))).card

theorem actualWindowCount_eq_card (T h t : ℝ) :
    actualWindowCount T h t = (translatedWindowCard T h t : ℝ) := by
  classical
  simp [actualWindowCount, windowCount, windowPulse, pulse, Set.indicator,
    translatedWindowCard, Finset.sum_boole]

/-- The integer-count excess in Yamada's bound, integrated over translations. -/
def windowLatticeExcess (T h : ℝ) (k : ℕ) : ℝ :=
  (∫ t, actualWindowCount T h t ^ 2 - (2 * (k : ℝ) + 1) * actualWindowCount T h t +
    (k : ℝ) * (k + 1) * pulse 0 T t) / T

private theorem lattice_integrand_nonneg (T h t : ℝ) (k : ℕ) :
    0 ≤ actualWindowCount T h t ^ 2 - (2 * (k : ℝ) + 1) * actualWindowCount T h t +
      (k : ℝ) * (k + 1) * pulse 0 T t := by
  by_cases ht : t ∈ Set.Ioc (0 : ℝ) T
  · have hp : pulse 0 T t = 1 := Set.indicator_of_mem ht _
    rw [hp, actualWindowCount_eq_card]
    let n := translatedWindowCard T h t
    change 0 ≤ (n : ℝ) ^ 2 - (2 * (k : ℝ) + 1) * n + k * (k + 1) * 1
    have he : (n : ℝ) ^ 2 - (2 * (k : ℝ) + 1) * n + k * (k + 1) * 1 =
        (n - (k : ℝ)) * (n - (k : ℝ) - 1) := by ring
    rw [he]
    by_cases hn : n ≤ k
    · have hn' : (n : ℝ) ≤ k := by exact_mod_cast hn
      exact mul_nonneg_of_nonpos_of_nonpos (sub_nonpos.mpr hn') (by linarith)
    · have hn' : ((k + 1 : ℕ) : ℝ) ≤ n := by exact_mod_cast (Nat.succ_le_of_lt (lt_of_not_ge hn))
      push_cast at hn'
      exact mul_nonneg (by linarith) (by linarith)
  · have hp : pulse 0 T t = 0 := Set.indicator_of_notMem ht _
    have hW : actualWindowCount T h t * pulse 0 T t = actualWindowCount T h t :=
      windowCount_mul_support _ _ _ _ _
    rw [hp, mul_zero] at hW
    rw [hp, ← hW]
    norm_num

theorem windowLatticeExcess_nonneg {T : ℝ} (hT : 0 ≤ T) (h : ℝ) (k : ℕ) :
    0 ≤ windowLatticeExcess T h k :=
  div_nonneg (integral_nonneg (fun t => lattice_integrand_nonneg T h t k)) hT

/-- The finite-height Yamada identity includes all coincident ordinates and
uses the actual clipped mean. The integer k can be chosen after the height. -/
theorem variance_eq_latticeExcess (T h m : ℝ) (k : ℕ) (hT : 0 < T) (hh : 0 ≤ h)
    (hfloor : ∀ c : Copies T, h ≤ c.1.1.im) (hm : (Ncount 0 T : ℝ) * h = T * m) :
    (∫ t, actualCenteredCount T h m t ^ 2) / T =
      (m - k) * ((k : ℝ) + 1 - m) + windowLatticeExcess T h k := by
  have hc : Integrable (actualWindowCount T h) := windowCount_integrable _ _ _ _
  have hc2 : Integrable (fun t => actualWindowCount T h t ^ 2) := windowCount_sq_integrable _ _ _ _
  have hI := (integral_actualWindowCount T h hh hfloor).trans hm
  have hC := integral_centeredCount_sq (Finset.univ : Finset (Copies T)) (fun c => c.1.1.im) T h m
  change (∫ t, actualCenteredCount T h m t ^ 2) = (∫ t, actualWindowCount T h t ^ 2) -
    (2 * m) * (∫ t, actualWindowCount T h t) + m ^ 2 * max T 0 at hC
  have hsub : Integrable (fun t : ℝ => actualWindowCount T h t ^ 2 -
      (2 * (k : ℝ) + 1) * actualWindowCount T h t) := hc2.sub (hc.const_mul _)
  rw [hC, windowLatticeExcess,
    integral_add hsub ((pulse_integrable 0 T).const_mul ((k : ℝ) * (k + 1))),
    integral_sub hc2 (hc.const_mul (2 * (k : ℝ) + 1)), integral_const_mul, integral_const_mul,
    integral_pulse, sub_zero, max_eq_left hT.le, hI]
  field_simp [hT.ne']
  <;> ring

private theorem eventually_supported_width (B : ℝ) :
    ∀ᶠ T : ℝ in atTop, ∀ R : ℝ, 0 ≤ R → R ≤ B →
      0 ≤ R / (Real.log T / (2 * Real.pi)) ∧
        ∀ c : Copies T, R / (Real.log T / (2 * Real.pi)) ≤ c.1.1.im := by
  obtain ⟨d, hd, hfloor⟩ := exists_ordinate_floor
  filter_upwards [eventually_gt_atTop (1 : ℝ),
    Real.tendsto_log_atTop.eventually_ge_atTop (2 * Real.pi * B / d)] with T hT hL R hR hRB
  have hscale := div_pos (Real.log_pos hT) (show 0 < 2 * Real.pi by positivity)
  refine ⟨div_nonneg hR hscale.le, fun c => ?_⟩
  apply LE.le.trans _ (hfloor T c)
  apply (div_le_iff₀ hscale).2
  have h := (div_le_iff₀ hd).1 hL
  rw [← mul_div_assoc]
  apply (le_div_iff₀ (by positivity : 0 < 2 * Real.pi)).2
  nlinarith only [h, mul_le_mul_of_nonneg_right hRB (show 0 ≤ 2 * Real.pi by positivity)]

private theorem mean_width_identity {T : ℝ} (hT : 1 < T) (R : ℝ) :
    unfoldedWindowMean T R = R * ((Ncount 0 T : ℝ) / (T * Real.log T / (2 * Real.pi))) := by
  unfold unfoldedWindowMean
  field_simp [(zero_lt_one.trans hT).ne', (Real.log_pos hT).ne', Real.pi_ne_zero]
  <;> ring

/-- The exact nonnegative excess applies simultaneously to every unfolded
width in any bounded interval and to every integer k. -/
theorem eventually_unfolded_lattice_identity (B : ℝ) :
    ∀ᶠ T : ℝ in atTop, ∀ R : ℝ, 0 ≤ R → R ≤ B → ∀ k : ℕ,
      unfoldedWindowVariance T R =
        (unfoldedWindowMean T R - k) * ((k : ℝ) + 1 - unfoldedWindowMean T R) +
          windowLatticeExcess T (R / (Real.log T / (2 * Real.pi))) k := by
  filter_upwards [eventually_supported_width B, eventually_gt_atTop (1 : ℝ)] with T ht hT R hR hRB k
  obtain ⟨hw, hfloor⟩ := ht R hR hRB
  apply variance_eq_latticeExcess T _ _ k (zero_lt_one.trans hT) hw hfloor
  unfold unfoldedWindowMean
  field_simp [(zero_lt_one.trans hT).ne']

/-- At fixed positive width, every number strictly below the Yamada
lower bound is eventually below the actual normalized window variance. -/
theorem eventually_lt_variance_of_lt_lattice {R a : ℝ} (hR : 0 ≤ R) (k : ℕ)
    (ha : a < (R - k) * ((k : ℝ) + 1 - R)) :
    ∀ᶠ T : ℝ in atTop, a < unfoldedWindowVariance T R := by
  have hm := unfoldedWindowMean_tendsto R
  have hc : Tendsto (fun _ : ℝ => (k : ℝ) + 1) atTop (𝓝 ((k : ℝ) + 1)) := tendsto_const_nhds
  have he := (hm.sub_const (k : ℝ)).mul (hc.sub hm)
  filter_upwards [eventually_unfolded_lattice_identity R, eventually_gt_atTop (0 : ℝ),
    he.eventually (lt_mem_nhds ha)] with T hI hT hl
  rw [hI R hR le_rfl k]
  exact hl.trans_le (le_add_of_nonneg_right (windowLatticeExcess_nonneg hT.le _ _))

/-- The same unconditional lower bound holds simultaneously on the
reconstructed translated windows of a saturated DPP. -/
theorem sampled_lattice_lower_ae (q : ℕ → ℝ) (b : ℝ) (hb : 0 < b) (hbπ : b ≤ 2 * Real.pi)
    (hq : ContainsHarmonics q b) :
    ∀ᵐ x ∂limitingLaw q, ∀ R : ℝ, 0 ≤ R → ∀ k : ℕ, ∀ a : ℝ,
      a < (R - k) * ((k : ℝ) + 1 - R) →
        ∀ᶠ T : ℝ in atTop, a < sampledUnfoldedWindowVariance x T R := by
  filter_upwards [sampledUnfoldedWindowVariance_eq_ae q b hb hbπ hq] with x hx
  intro R hR k a ha
  simpa only [hx] using eventually_lt_variance_of_lt_lattice hR k ha

/-- One moving positive unfolded width tending to zero suffices for the
collision-density limit, provided its variance has one-sided slope at most
one. The height and width limits need not be exchanged. -/
theorem collision_limit_of_shrinking_window_upper (r err : ℝ → ℝ)
    (hr : Tendsto r atTop (𝓝 0)) (hrp : ∀ᶠ T : ℝ in atTop, 0 < r T)
    (herr : Tendsto err atTop (𝓝 0))
    (hu : ∀ᶠ T : ℝ in atTop, unfoldedWindowVariance T (r T) / r T ≤ 1 + err T) :
    Tendsto (fun T : ℝ => (actualCollision T : ℝ) / (T * Real.log T / (2 * Real.pi)))
      atTop (𝓝 1) := by
  let n := fun T : ℝ => (Ncount 0 T : ℝ) / (T * Real.log T / (2 * Real.pi))
  have hn : Tendsto n atTop (𝓝 1) := tendsto_count_div_mainTerm
  have hupper := (hr.mul (hn.pow 2)).add (herr.const_add 1)
  simp only [one_pow, zero_mul, zero_add, add_zero] at hupper
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hn hupper
  · filter_upwards [eventually_gt_atTop (1 : ℝ)] with T hT
    have hC : Ncount 0 T ≤ actualCollision T := by rw [actualCollision_eq_count_add_excess]; omega
    apply div_le_div_of_nonneg_right (by exact_mod_cast hC)
    exact div_nonneg (mul_nonneg (zero_le_one.trans hT.le) (Real.log_nonneg hT.le)) (by positivity)
  · filter_upwards [hrp, hu, hr.eventually (gt_mem_nhds (zero_lt_one : (0 : ℝ) < 1)),
      eventually_supported_width 1, eventually_gt_atTop (1 : ℝ)] with T hrT hv hb hs hT
    have ht := zero_lt_one.trans hT
    obtain ⟨hw, hfloor⟩ := hs (r T) hrT.le hb.le
    have hmean : (Ncount 0 T : ℝ) * (r T / (Real.log T / (2 * Real.pi))) =
        T * unfoldedWindowMean T (r T) := by
      unfold unfoldedWindowMean
      field_simp [ht.ne']
    have hE : unfoldedWindowEnergy T (r T) =
        unfoldedWindowMean T (r T) ^ 2 + unfoldedWindowVariance T (r T) :=
      actual_triangle_eq_mean_sq_add_variance T _ _ ht hw hfloor hmean
    have h0 : unfoldedWindowEnergy T 0 = 0 := by
      unfold unfoldedWindowEnergy
      rw [physicalTriangle_eq_collision_add_positive_gaps hT le_rfl]
      simp
    have hC := (unfoldedWindowEnergy_secant_bounds hT (le_refl 0) hrT).1
    rw [h0, sub_zero, sub_zero, hE, add_div, mean_width_identity hT] at hC
    have hsquare : (r T * n T) ^ 2 / r T = r T * (n T) ^ 2 := by
      field_simp [hrT.ne']
      <;> ring
    change (actualCollision T : ℝ) / (T * Real.log T / (2 * Real.pi)) + 2 * positiveGapMass T 0 ≤
      (r T * n T) ^ 2 / r T + unfoldedWindowVariance T (r T) / r T at hC
    rw [hsquare] at hC
    change _ ≤ r T * (n T) ^ 2 + (1 + err T)
    linarith only [hC, hv, positiveGapMass_nonneg hT 0]

/-- A single shrinking-width one-sided bound gives both density one of
simple critical copies and vanishing relative logarithmic DPP deletions. -/
theorem density_one_and_vacancy_of_shrinking_window_upper (r err : ℝ → ℝ)
    (hr : Tendsto r atTop (𝓝 0)) (hrp : ∀ᶠ T : ℝ in atTop, 0 < r T)
    (herr : Tendsto err atTop (𝓝 0))
    (hu : ∀ᶠ T : ℝ in atTop, unfoldedWindowVariance T (r T) / r T ≤ 1 + err T) :
    Tendsto (fun T : ℝ => (simpleCriticalCount T : ℝ) / (Ncount 0 T : ℝ)) atTop (𝓝 1) ∧
      Tendsto (fun T : ℝ => cutoffVacancy (fun k => Real.log ((k : ℝ) + 1)) T /
        (Ncount 0 T : ℝ)) atTop (𝓝 0) := by
  have h := (density_one_of_collision_limit (collision_limit_of_shrinking_window_upper r err hr hrp herr hu)).1
  exact ⟨h, logarithmic_relativeVacancy_tendsto_zero_iff.mpr h⟩


/-- Every deleted logarithmic representative costs at least two additional
ordered equal-ordinate pairs. Equality holds for fibre sizes one and two. -/
theorem twice_logarithmic_vacancy_add_count_le_collision (T : ℝ) :
    2 * cutoffVacancy (fun k => Real.log ((k : ℝ) + 1)) T + Ncount 0 T ≤
      (actualCollision T : ℝ) := by
  have hs (n : ℕ) : 3 * (n : ℝ) ≤ (n : ℝ) ^ 2 + 2 := by
    by_cases he : n ≤ 1
    · interval_cases n <;> norm_num
    · have h : (2 : ℝ) ≤ n := by exact_mod_cast (by omega : 2 ≤ n)
      nlinarith only [mul_nonneg (show 0 ≤ (n : ℝ) - 1 by linarith) (sub_nonneg.mpr h)]
  have h := Finset.sum_le_sum (s := actualOrdinateSupport T)
    (fun τ _ => hs (actualOrdinateMultiplicity T τ))
  have hN := congrArg (Nat.cast : ℕ → ℝ) (actualCount_eq_sum_ordinateMultiplicity T)
  have hC := congrArg (Nat.cast : ℕ → ℝ) (actualCollision_eq_sum_multiplicity_sq T)
  simp only [Nat.cast_sum, Nat.cast_pow] at hN hC
  rw [← Finset.mul_sum, Finset.sum_add_distrib, ← hN, ← hC] at h
  simp only [Finset.sum_const, nsmul_eq_mul] at h
  rw [logarithmic_cutoff_vacancy]
  linarith

/-- At each fixed positive unfolded width, twice the mean number of
logarithmic deletions is eventually bounded by the variance excess over
the Bernoulli value. The bound retains actual equal-ordinate collisions. -/
theorem twice_mean_logarithmic_vacancy_le_window_excess {R : ℝ} (hR : 0 < R) :
    ∀ᶠ T : ℝ in atTop, 2 * meanWindowVacancy (fun k => Real.log ((k : ℝ) + 1)) T R ≤
      unfoldedWindowVariance T R - unfoldedWindowMean T R * (1 - unfoldedWindowMean T R) := by
  let q := fun k : ℕ => Real.log ((k : ℝ) + 1)
  filter_upwards [eventually_meanWindowVacancy_eq hR.le,
    eventually_unfoldedWindowEnergy_eq_mean_sq_add_variance hR.le,
    eventually_gt_atTop (1 : ℝ),
    tendsto_count_div_mainTerm.eventually (lt_mem_nhds (zero_lt_one : (0 : ℝ) < 1))]
    with T hmv hE hT hc
  let A := T * Real.log T / (2 * Real.pi)
  have hA : 0 < A := div_pos (mul_pos (zero_lt_one.trans hT) (Real.log_pos hT)) (by positivity)
  have hN : (Ncount 0 T : ℝ) ≠ 0 := by intro h; simp [h] at hc
  have hm : unfoldedWindowMean T R = R * ((Ncount 0 T : ℝ) / A) := mean_width_identity hT R
  have hd : meanWindowVacancy q T R = R * (cutoffVacancy q T / A) := by
    rw [hmv q, hm]
    field_simp [hN, hA.ne']
    <;> ring
  have hb : 2 * (cutoffVacancy q T / A) + (Ncount 0 T : ℝ) / A ≤ (actualCollision T : ℝ) / A := by
    rw [← mul_div_assoc, ← add_div]
    exact div_le_div_of_nonneg_right (twice_logarithmic_vacancy_add_count_le_collision T) hA.le
  have h0 : unfoldedWindowEnergy T 0 = 0 := by
    unfold unfoldedWindowEnergy
    rw [physicalTriangle_eq_collision_add_positive_gaps hT le_rfl]
    simp
  have hsec := (unfoldedWindowEnergy_secant_bounds hT (le_refl 0) hR).1
  rw [h0, sub_zero, sub_zero] at hsec
  have hu : (actualCollision T : ℝ) / A ≤ unfoldedWindowEnergy T R / R := by
    change (actualCollision T : ℝ) / A + 2 * positiveGapMass T 0 ≤ unfoldedWindowEnergy T R / R at hsec
    linarith only [hsec, positiveGapMass_nonneg hT 0]
  have ht := (le_div_iff₀ hR).1 hu
  have hb' := mul_le_mul_of_nonneg_left hb hR.le
  change 2 * meanWindowVacancy q T R ≤ _
  rw [hd]
  nlinarith only [ht, hb', hm, hE]

private theorem exists_positive_gap_floor (T : ℝ) :
    ∃ d : ℝ, 0 < d ∧ ∀ i j : Copies T, copyOrdinate T i ≠ copyOrdinate T j →
      d ≤ |copyOrdinate T i - copyOrdinate T j| := by
  classical
  let g := fun z : Copies T × Copies T => |copyOrdinate T z.1 - copyOrdinate T z.2|
  let A := insert (1 : ℝ) ((Finset.univ.image g).filter (fun x => 0 < x))
  have hn : A.Nonempty := ⟨1, Finset.mem_insert_self _ _⟩
  let d := A.min' hn
  have hd : 0 < d := by
    have hm : d ∈ A := Finset.min'_mem A hn
    rcases Finset.mem_insert.mp hm with he | hf
    · rw [he]
      exact zero_lt_one
    · exact (Finset.mem_filter.mp hf).2
  refine ⟨d, hd, fun i j hij => ?_⟩
  apply Finset.min'_le A _
  apply Finset.mem_insert_of_mem
  exact Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨(i,j), Finset.mem_univ _, rfl⟩,
    abs_pos.mpr (sub_ne_zero.mpr hij)⟩

private theorem physical_energy_below_gaps (T h : ℝ) (hh : 0 ≤ h)
    (hgap : ∀ i j : Copies T, copyOrdinate T i ≠ copyOrdinate T j →
      h ≤ |copyOrdinate T i - copyOrdinate T j|) :
    actualPhysicalTriangleEnergy T h = h * (actualCollision T : ℝ) / T := by
  classical
  unfold actualPhysicalTriangleEnergy actualCollision OrdinateCollisionCertificate.occurrenceCollision
  simp only [Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  change max (h - |copyOrdinate T i - copyOrdinate T j|) 0 =
    h * (if copyOrdinate T i = copyOrdinate T j then 1 else 0)
  by_cases he : copyOrdinate T i = copyOrdinate T j
  · simp [he, max_eq_left hh]
  · rw [if_neg he, mul_zero, max_eq_right (sub_nonpos.mpr (hgap i j he))]

/-- At each finite height the window variance has an exact quadratic
expansion below the first positive gap. Its linear coefficient is the
normalized equal-ordinate pair count with all multiplicities. -/
theorem exists_variance_polynomial_near_zero (T : ℝ) (hT : 1 < T) :
    ∃ d : ℝ, 0 < d ∧ ∀ R : ℝ, 0 ≤ R → R ≤ d →
      unfoldedWindowVariance T R =
        R * ((actualCollision T : ℝ) / (T * Real.log T / (2 * Real.pi))) -
          (R * ((Ncount 0 T : ℝ) / (T * Real.log T / (2 * Real.pi)))) ^ 2 := by
  obtain ⟨d, hd, hg⟩ := exists_positive_gap_floor T
  obtain ⟨a, ha, hfloor⟩ := exists_ordinate_floor
  let L := Real.log T / (2 * Real.pi)
  have hL : 0 < L := div_pos (Real.log_pos hT) (by positivity)
  have ht := zero_lt_one.trans hT
  refine ⟨min d a * L, mul_pos (lt_min hd ha) hL, fun R hR hsmall => ?_⟩
  have hw : R / L ≤ min d a := (div_le_iff₀ hL).2 hsmall
  have hh : 0 ≤ R / L := div_nonneg hR hL.le
  have he := physical_energy_below_gaps T (R / L) hh
    (fun i j hij => hw.trans ((min_le_left d a).trans (hg i j hij)))
  have hmean : (Ncount 0 T : ℝ) * (R / L) = T * unfoldedWindowMean T R := by
    change (Ncount 0 T : ℝ) * (R / L) = T * (((Ncount 0 T : ℝ) * (R / L)) / T)
    field_simp [ht.ne']
  have hdec := actual_triangle_eq_mean_sq_add_variance T (R / L) (unfoldedWindowMean T R) ht hh
    (fun c => hw.trans ((min_le_right d a).trans (hfloor T c))) hmean
  change actualPhysicalTriangleEnergy T (R / L) =
    unfoldedWindowMean T R ^ 2 + unfoldedWindowVariance T R at hdec
  rw [he, mean_width_identity hT R] at hdec
  have hscale : (R / L) * (actualCollision T : ℝ) / T =
      R * ((actualCollision T : ℝ) / (T * Real.log T / (2 * Real.pi))) := by
    dsimp only [L]
    field_simp [ht.ne', (Real.log_pos hT).ne', Real.pi_ne_zero]
    <;> ring
  linarith only [hdec, hscale]

/-- There exists a single positive width tending to zero on which the
variance slope reads the normalized collision mass with vanishing error.
The width is allowed to depend on the actual finite gaps at its cutoff. -/
theorem exists_shrinking_width_reading_collisions :
    ∃ r : ℝ → ℝ, Tendsto r atTop (𝓝 0) ∧ (∀ᶠ T : ℝ in atTop, 0 < r T) ∧
      Tendsto (fun T : ℝ => unfoldedWindowVariance T (r T) / r T -
        (actualCollision T : ℝ) / (T * Real.log T / (2 * Real.pi))) atTop (𝓝 0) := by
  classical
  let r := fun T : ℝ => if h : 1 < T then
    min (exists_variance_polynomial_near_zero T h).choose T⁻¹ else 1
  have hp : ∀ᶠ T : ℝ in atTop, 0 < r T := by
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with T hT
    simp only [r, dif_pos hT]
    exact lt_min (exists_variance_polynomial_near_zero T hT).choose_spec.1
      (inv_pos.mpr (zero_lt_one.trans hT))
  have hr : Tendsto r atTop (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds tendsto_inv_atTop_zero
      (hp.mono fun _ h => h.le)
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with T hT
    simp only [r, dif_pos hT]
    exact min_le_right _ _
  refine ⟨r, hr, hp, ?_⟩
  have hh := (hr.mul (tendsto_count_div_mainTerm.pow 2)).neg
  simp only [zero_mul, neg_zero] at hh
  apply hh.congr'
  filter_upwards [eventually_gt_atTop (1 : ℝ), hp] with T hT hrT
  have he := (exists_variance_polynomial_near_zero T hT).choose_spec.2 (r T) hrT.le
    (show r T ≤ (exists_variance_polynomial_near_zero T hT).choose by
      dsimp only [r]
      rw [dif_pos hT]
      exact min_le_left _ _)
  rw [he]
  field_simp [hrT.ne']
  <;> ring

/-- The equal-ordinate collision limit is equivalent to the existence of
one shrinking width with asymptotically unit variance slope. -/
theorem collision_limit_iff_exists_shrinking_variance_slope :
    Tendsto (fun T : ℝ => (actualCollision T : ℝ) / (T * Real.log T / (2 * Real.pi)))
        atTop (𝓝 1) ↔
      ∃ r : ℝ → ℝ, Tendsto r atTop (𝓝 0) ∧ (∀ᶠ T : ℝ in atTop, 0 < r T) ∧
        Tendsto (fun T => unfoldedWindowVariance T (r T) / r T) atTop (𝓝 1) := by
  constructor
  · intro h
    obtain ⟨r, hr, hp, he⟩ := exists_shrinking_width_reading_collisions
    refine ⟨r, hr, hp, ?_⟩
    simpa using he.add h
  · rintro ⟨r, hr, hp, hv⟩
    let err := fun T => unfoldedWindowVariance T (r T) / r T - 1
    have he : Tendsto err atTop (𝓝 0) := by simpa [err] using hv.sub_const 1
    apply collision_limit_of_shrinking_window_upper r err hr hp he
    exact Eventually.of_forall fun T => by dsimp [err]; linarith

end RiemannResearch.Analysis.ZeroDPPCorrelation
