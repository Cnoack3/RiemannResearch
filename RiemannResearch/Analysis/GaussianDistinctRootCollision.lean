/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.Analysis.GaussianAbsoluteCollision
import RiemannResearch.Analysis.ActualOrdinateCollisionCertificates
import RiemannResearch.Analysis.SineGaussianMoment
import RiemannResearch.Analysis.GLSSArgumentVarianceCalibration
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Gaussian counts of projected pairs from distinct zeta zeros

The unit-intensity GUE bulk benchmark uses the two-point determinant
of the sine kernel. For the determinantal correlation formula and its GUE
normalization see P. J. Forrester and J. L. Lebowitz, *Local Central Limit
Theorem for Determinantal Point Processes*, J. Stat. Phys. 157 (2014),
§1, doi:10.1007/s10955-014-1071-2. The arithmetic comparison retains every
copy of each root and removes the exact contribution of pairs from the same
complex root. Reflection then detects off-line roots of any multiplicity.
-/

noncomputable section
open Filter MeasureTheory Zeta23
open scoped BigOperators Topology
namespace RiemannResearch.Analysis.ActualZeroOrdinate
open ActualZeroCollisionCertificate OrdinateCollisionCertificate

/-- The GUE two-point intensity integrated against the full signed Gaussian gap test. -/
def sinePalmGaussianMass (a : ℝ) : ℝ :=
  ∫ x : ℝ, Real.exp (-a * x^2) * (1 - Real.sinc (Real.pi * x)^2)

theorem sinePalmGaussianMass_nonneg (a : ℝ) : 0 ≤ sinePalmGaussianMass a := by
  apply integral_nonneg
  intro x
  apply mul_nonneg (Real.exp_nonneg _)
  have h := sq_le_sq₀ (abs_nonneg (Real.sinc (Real.pi*x))) zero_le_one
  have hs := h.mpr (Real.abs_sinc_le_one _)
  rw [sq_abs, one_pow] at hs
  linarith

theorem sinePalmGaussianMass_tendsto :
    Tendsto sinePalmGaussianMass atTop (𝓝 0) := by
  have hp : Tendsto (fun a : ℝ => a ^ (3 / 2 : ℝ)) atTop atTop :=
    by
      apply tendsto_atTop.2
      intro c
      filter_upwards [eventually_ge_atTop (1 : ℝ), eventually_ge_atTop c] with a ha hca
      calc
        c ≤ a := hca
        _ = a ^ (1 : ℝ) := (Real.rpow_one _).symm
        _ ≤ _ := Real.rpow_le_rpow_of_exponent_le ha (by norm_num)
  have hd := (tendsto_inv_atTop_zero.comp hp).const_mul (Real.pi ^ (5 / 2 : ℝ) / 6)
  simp only [mul_zero] at hd
  apply squeeze_zero' (Eventually.of_forall sinePalmGaussianMass_nonneg) _ hd
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with a ha
  apply (GaussianGapTests.sine_gaussian_moment_le ha).trans_eq
  simp [div_eq_mul_inv, mul_inv_rev, mul_comm, mul_left_comm]

/-- Number of ordered equal-height pairs with different complex roots. -/
def distinctRootCollisionCount (T : ℝ) : ℕ := by
  classical
  exact ∑ p ∈ cutoff T, ∑ q ∈ cutoff T,
    if p ≠ q ∧ p.im = q.im then zeroMult p * zeroMult q else 0

private theorem copy_sum_nat (T : ℝ) (f : ℂ → ℕ) :
    (∑ i : Copies T, f i.1.1) = ∑ z ∈ cutoff T, zeroMult z * f z := by
  classical
  have h := (realSum_eq_copies T (fun z => (f z : ℝ))).symm
  unfold realSum at h
  have hcast : ((∑ i : Copies T, f i.1.1 : ℕ) : ℝ) =
      ((∑ z ∈ cutoff T, zeroMult z * f z : ℕ) : ℝ) := by
    push_cast
    exact h
  exact_mod_cast hcast

private theorem copy_pair_sum_nat (T : ℝ) (f : ℂ → ℂ → ℕ) :
    (∑ i : Copies T, ∑ j : Copies T, f i.1.1 j.1.1) =
      ∑ p ∈ cutoff T, ∑ q ∈ cutoff T, (zeroMult p * zeroMult q) * f p q := by
  classical
  calc
    _ = ∑ i : Copies T, ∑ q ∈ cutoff T, zeroMult q * f i.1.1 q :=
      Finset.sum_congr rfl fun i _ => copy_sum_nat T (f i.1.1)
    _ = ∑ p ∈ cutoff T, zeroMult p * (∑ q ∈ cutoff T, zeroMult q * f p q) :=
      copy_sum_nat T (fun p => ∑ q ∈ cutoff T, zeroMult q * f p q)
    _ = _ := by simp only [Finset.mul_sum, mul_assoc]

private theorem distinctRootCollision_eq_copies (T : ℝ) :
    distinctRootCollisionCount T = ∑ i : Copies T, ∑ j : Copies T,
      if i.1.1 ≠ j.1.1 ∧ copyOrdinate T i = copyOrdinate T j then 1 else 0 := by
  classical
  rw [show (∑ i : Copies T, ∑ j : Copies T,
      if i.1.1 ≠ j.1.1 ∧ copyOrdinate T i = copyOrdinate T j then 1 else 0) =
      ∑ p ∈ cutoff T, ∑ q ∈ cutoff T, (zeroMult p * zeroMult q) *
        (if p ≠ q ∧ p.im = q.im then 1 else 0) from
      copy_pair_sum_nat T (fun p q => if p ≠ q ∧ p.im = q.im then 1 else 0)]
  simp [distinctRootCollisionCount, mul_ite]

/-- Full horizontal collision equals the analytic diagonal plus the cross-root atom. -/
theorem actualCollision_eq_rootDiagonal_add (T : ℝ) :
    actualCollision T =
      multiplicityCollision (cutoff T) zeroMult + distinctRootCollisionCount T := by
  classical
  change (∑ i : Copies T, ∑ j : Copies T,
    if i.1.1.im = j.1.1.im then 1 else 0) = _
  rw [copy_pair_sum_nat T (fun p q => if p.im = q.im then 1 else 0)]
  have splitTerm (p q : ℂ) :
      (zeroMult p * zeroMult q) * (if p.im = q.im then 1 else 0) =
        (if p = q then (zeroMult p)^2 else 0) +
        (if p ≠ q ∧ p.im = q.im then zeroMult p * zeroMult q else 0) := by
    by_cases e : p = q
    · subst q; simp [pow_two]
    · by_cases h : p.im = q.im <;> simp [e, h]
  unfold multiplicityCollision distinctRootCollisionCount
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  simp_rw [splitTerm, Finset.sum_add_distrib]
  simp [hp]

/-- An off-line root and its reflection contribute both orientations, with multiplicity. -/
theorem reflected_pair_le_distinctRootCollision {T : ℝ} {p : ℂ} (hp : p ∈ cutoff T)
    (hoff : p.re ≠ 1 / 2) : 2 * (zeroMult p)^2 ≤ distinctRootCollisionCount T := by
  classical
  let q := reflect p
  have hq : q ∈ cutoff T := reflect_mem hp
  have him : q.im = p.im := reflect_im p
  have hm : zeroMult q = zeroMult p := zetaSeam.mult_reflect p (mem_cutoff.mp hp).1
  have hne : p ≠ q := by
    intro he
    have h := congrArg Complex.re he
    change p.re = (reflect p).re at h
    rw [reflect_re] at h
    exact hoff (by linarith)
  let val (r s : ℂ) : ℕ := if r ≠ s ∧ r.im = s.im then zeroMult r * zeroMult s else 0
  let row (r : ℂ) := ∑ s ∈ cutoff T, val r s
  have hpq : val p q ≤ row p := Finset.single_le_sum (fun s _ => Nat.zero_le (val p s)) hq
  have hqp : val q p ≤ row q := Finset.single_le_sum (fun s _ => Nat.zero_le (val q s)) hp
  have hsub : ({p,q} : Finset ℂ) ⊆ cutoff T := by
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl
    · exact hp
    · exact hq
  have hrows : row p + row q ≤ distinctRootCollisionCount T := by
    change row p + row q ≤ ∑ r ∈ cutoff T, row r
    simpa [hne] using (Finset.sum_le_sum_of_subset (f := row) hsub)
  have h1 : (zeroMult p)^2 ≤ row p := by simpa [val, hne, him, hm, pow_two] using hpq
  have h2 : (zeroMult p)^2 ≤ row q := by simpa [val, hne.symm, him, hm, pow_two] using hqp
  omega

theorem distinctRootCollision_zero_of_critical {T : ℝ} (h : ∀ p ∈ cutoff T, p.re = 1 / 2) :
    distinctRootCollisionCount T = 0 := by
  classical
  have hi := (distinctOrdinate_injective_iff T).mpr h
  unfold distinctRootCollisionCount
  refine Finset.sum_eq_zero fun p hp => Finset.sum_eq_zero fun q hq => ?_
  have hn : ¬ (p ≠ q ∧ p.im = q.im) := by
    rintro ⟨hne,he⟩
    have he' : (⟨p,hp⟩ : DistinctZeros T) = ⟨q,hq⟩ :=
      hi (show distinctOrdinate T ⟨p,hp⟩ = distinctOrdinate T ⟨q,hq⟩ from he)
    exact hne (congrArg Subtype.val he')
  simp [hn]

theorem distinctRootCollision_lt_two_iff (T : ℝ) :
    distinctRootCollisionCount T < 2 ↔ ∀ p ∈ cutoff T, p.re = 1 / 2 := by
  constructor
  · intro h p hp
    by_contra he
    have hpos := multiplicity_pos hp
    have hsq : 0 < (zeroMult p)^2 := by positivity
    have hfloor := reflected_pair_le_distinctRootCollision hp he
    omega
  · intro h
    rw [distinctRootCollision_zero_of_critical h]
    decide

/-- The distinct-root Gaussian keeps all multiplicity weights at different ordinates. -/
def distinctRootGaussianMass (a T : ℝ) : ℝ :=
  (distinctRootCollisionCount T : ℝ) + unequalGaussianTotal a T

theorem distinctRootGaussianMass_eq_sum {T : ℝ} (hN : 0 < Ncount 0 T) (a : ℝ) :
    distinctRootGaussianMass a T = ∑ i : Copies T, ∑ j : Copies T,
      if i.1.1 = j.1.1 then 0 else Real.exp (-a * (gaussianSeparation T i j)^2) := by
  classical
  rw [distinctRootGaussianMass, distinctRootCollision_eq_copies, unequalGaussianTotal_eq_sum a T hN]
  simp only [Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  by_cases h : i.1.1 = j.1.1
  · have he : copyOrdinate T i = copyOrdinate T j := congrArg Complex.im h
    simp [unequalGaussianTerm,h,he]
  · by_cases he : copyOrdinate T i = copyOrdinate T j
    · simp [unequalGaussianTerm,h,he,gaussianSeparation]
    · simp [unequalGaussianTerm,h,he]

theorem distinctRootGaussianMass_tendsto {T : ℝ} (hT : 1 < T) :
    Tendsto (fun k : ℕ => distinctRootGaussianMass ((k:ℝ)+1) T) atTop
      (𝓝 (distinctRootCollisionCount T : ℝ)) := by
  simpa only [distinctRootGaussianMass, unequalGaussianTotal, mul_zero, add_zero] using
    ((MontgomeryPositiveGap.unequalGaussian_tendsto_zero_at_fixed_height hT).const_mul
      (Ncount 0 T : ℝ)).const_add (distinctRootCollisionCount T : ℝ)

/-- The reconstructed power is corrected by the exact analytic repeat count. -/
def reconstructedDistinctRootMass (a T : ℝ) : ℝ :=
  absoluteGaussianExcess a T - (multiplicityExcess (cutoff T) zeroMult : ℝ)

/-- The full Gaussian power is corrected by the square of each complex root multiplicity. -/
theorem reconstructedDistinctRootMass_eq_power_sub_rootDiagonal (a T : ℝ) :
    reconstructedDistinctRootMass a T =
      (Ncount 0 T : ℝ) *
        reconstructedGaussianPowerWithAllowance a T (gaussianCollisionAllowance T) -
      (multiplicityCollision (cutoff T) zeroMult : ℝ) := by
  have hc : multiplicityCount (cutoff T) zeroMult = Ncount 0 T := (count_eq_sum T).symm
  rw [reconstructedDistinctRootMass, absoluteGaussianExcess,
    multiplicityCollision_eq_count_add_excess, hc, Nat.cast_add]
  ring

theorem reconstructedDistinctRoot_quarter_error {T a : ℝ} (hN : 0 < Ncount 0 T) (ha : 0 < a) :
    |distinctRootGaussianMass a T - reconstructedDistinctRootMass a T| ≤ 1 / 4 := by
  have hs := actualCollision_eq_rootDiagonal_add T
  rw [multiplicityCollision_eq_count_add_excess] at hs
  have hc : multiplicityCount (cutoff T) zeroMult = Ncount 0 T := (count_eq_sum T).symm
  rw [hc] at hs
  have hs' := congrArg (fun n : ℕ => (n : ℝ)) hs
  simp only [Nat.cast_add] at hs'
  have herr := absolute_gaussian_quarter_error hN ha
  rw [distinctRootGaussianMass, reconstructedDistinctRootMass]
  convert herr using 2
  linarith

/-- The cubic repulsion bound gives an explicit sufficient bandwidth for half a model pair. -/
theorem sineGaussian_half_pair_of_bandwidth {T a : ℝ} (ha : 0 < a)
    (hband : (Ncount 0 T : ℝ) * Real.pi ^ (5 / 2 : ℝ) ≤ 3 * a ^ (3 / 2 : ℝ)) :
    (Ncount 0 T : ℝ) * sinePalmGaussianMass a ≤ 1 / 2 := by
  have he := mul_le_mul_of_nonneg_left (GaussianGapTests.sine_gaussian_moment_le ha)
    (Nat.cast_nonneg (Ncount 0 T) : 0 ≤ (Ncount 0 T : ℝ))
  apply he.trans
  rw [← mul_div_assoc]
  apply (div_le_iff₀ (by positivity)).mpr
  linarith only [hband]

/-- Compare the reconstructed, analytically corrected count to the sine law in ordered pairs. -/
def sineRootGaussianTest (a T : ℝ) : Prop :=
  (Ncount 0 T : ℝ) * sinePalmGaussianMass a ≤ 1 / 2 ∧
    reconstructedDistinctRootMass a T - (Ncount 0 T : ℝ) * sinePalmGaussianMass a < 5 / 4

theorem critical_of_sineRootGaussianTest {T a : ℝ} (hN : 0 < Ncount 0 T) (ha : 0 < a)
    (htest : sineRootGaussianTest a T) : ∀ p ∈ cutoff T, p.re = 1 / 2 := by
  apply (distinctRootCollision_lt_two_iff T).mp
  obtain ⟨hmodel, hactual⟩ := htest
  have h := (abs_le.mp (reconstructedDistinctRoot_quarter_error hN ha)).2
  rw [distinctRootGaussianMass] at h
  have hlt : (distinctRootCollisionCount T : ℝ) < 2 := by
    linarith only [hmodel, hactual, h, unequalGaussianTotal_nonneg a T]
  exact_mod_cast hlt

/-- At a critical finite cutoff all sufficiently narrow integer Gaussian tests pass. -/
theorem eventually_sineRootGaussianTest_of_critical {T : ℝ} (hT : 1 < T)
    (hN : 0 < Ncount 0 T) (hline : ∀ p ∈ cutoff T, p.re = 1 / 2) :
    ∀ᶠ k : ℕ in atTop, sineRootGaussianTest ((k : ℝ) + 1) T := by
  have hk : Tendsto (fun k : ℕ => (k : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
  have hmodel := (sinePalmGaussianMass_tendsto.comp hk).const_mul (Ncount 0 T : ℝ)
  simp only [mul_zero, Function.comp_def] at hmodel
  have hactual := distinctRootGaussianMass_tendsto hT
  rw [distinctRootCollision_zero_of_critical hline, Nat.cast_zero] at hactual
  filter_upwards [hmodel.eventually_lt_const (by norm_num : (0 : ℝ) < 1 / 2),
    hactual.eventually_lt_const (by norm_num : (0 : ℝ) < 1)] with k hm hsmall
  refine ⟨hm.le, ?_⟩
  have he := (abs_le.mp (reconstructedDistinctRoot_quarter_error hN
    (show 0 < (k : ℝ) + 1 by positivity))).1
  have hpos := mul_nonneg (Nat.cast_nonneg (Ncount 0 T) : 0 ≤ (Ncount 0 T : ℝ))
    (sinePalmGaussianMass_nonneg ((k : ℝ) + 1))
  linarith only [he, hsmall, hpos]

/-- The comparison is exact at each nonempty finite cutoff and allows repeated critical zeros. -/
theorem sineRootGaussian_finite_iff {T : ℝ} (hT : 1 < T) (hN : 0 < Ncount 0 T) :
    (∃ k : ℕ, sineRootGaussianTest ((k : ℝ) + 1) T) ↔ ∀ p ∈ cutoff T, p.re = 1 / 2 := by
  constructor
  · rintro ⟨k, hk⟩
    exact critical_of_sineRootGaussianTest hN (by positivity) hk
  · intro h
    exact (eventually_sineRootGaussianTest_of_critical hT hN h).exists

end RiemannResearch.Analysis.ActualZeroOrdinate
