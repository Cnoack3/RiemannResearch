/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QFullCofinalHarmonic
import RiemannResearch.Analysis.OrthogonalDistanceBound
import RiemannResearch.Analysis.FiniteHarmonicBounds
import RiemannResearch.RH.BaezDuarteNaturalApproximation
import RiemannResearch.RH.ArithmeticCumulativeBasic
import RiemannResearch.RH.QFullDisplacement
import RiemannResearch.RH.QFullResidueProjection
import RiemannResearch.RH.QOptimizerParityRH
import RiemannResearch.RH.QParetoClosedProjectionComparison
import RiemannResearch.RH.QParetoEquivalence
import RiemannResearch.RH.QShiftedReciprocal
import RiemannResearch.RH.ZetaTwoHilbertSpace
import RiemannResearch.RH.ZetaTwoParetoTransfer
import RiemannResearch.RH.ZetaTwoProbability
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Analysis.Normed.Group.Tannery
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Product distance for the full-conductor displacement

The exact product pairing and finite harmonic bound follow equation (4.9)
and Corollary 6.7 of Christian Noack's Full_Conductor_RH_Projection_Machinery.
The harmonic escape uses the repository's checked uniform Mertens defect slope.
For classical context, see Walfisz's estimate in equation (2) of Gerhold,
Acta Arith. 142 (2010), https://doi.org/10.4064/aa142-2-8.

The product criterion is equivalent to natural-dilation approximation.
The reverse implication from RH uses Theorem 1 of Báez-Duarte,
"A strengthening of the Nyman-Beurling criterion for the Riemann hypothesis",
Rend. Lincei Mat. Appl. 14 (2003), 5–11, https://arxiv.org/abs/math/0202141.
The analytic implication is an explicit premise of the RH equivalence.
-/

noncomputable section
open Filter
open scoped BigOperators Topology
namespace RiemannResearch.RH.QFullDisplacement
open ZetaTwoHilbert ZetaTwoProbability QShiftedReciprocal QFullResidueProjection
open ArithmeticCumulative

/-- Multiplication by the unnormalized residue at positive conductors.
At zero the extension uses the zero residue modulo one. -/
def scaledResidueProduct (f : QHilbert) (m : ℕ) : QHilbert :=
  encodeQ (fun n => qSequence f n * ((n % max 1 m : ℕ) : ℝ)) (by
    apply Summable.of_nonneg_of_le
      (fun n => mul_nonneg (positiveQWeight_nonneg n) (sq_nonneg _))
      _ ((qSequence_square_summable f).mul_right ((↑(max 1 m) : ℝ) ^ 2))
    intro n
    have hm : 0 < max 1 m := lt_of_lt_of_le Nat.zero_lt_one (le_max_left _ _)
    have h : ((n % max 1 m : ℕ) : ℝ) ≤ (↑(max 1 m) : ℝ) :=
      by exact_mod_cast (Nat.mod_lt n hm).le
    have hs : ((n % max 1 m : ℕ) : ℝ) ^ 2 ≤ (↑(max 1 m) : ℝ) ^ 2 :=
      pow_le_pow_left₀ (Nat.cast_nonneg _) h 2
    rw [mul_pow, ← mul_assoc]
    exact mul_le_mul_of_nonneg_left hs (mul_nonneg (positiveQWeight_nonneg n) (sq_nonneg _)))

theorem qSequence_scaledResidueProduct (f : QHilbert) (m : ℕ) :
    qSequence (scaledResidueProduct f m) = fun n => qSequence f n * ((n % max 1 m : ℕ) : ℝ) :=
  qSequence_encodeQ _ _ (by simp)

theorem qSequence_normalizedResidueProduct (f : QHilbert) (m : ℕ) :
    qSequence ((m : ℝ)⁻¹ • scaledResidueProduct f m) =
      fun n => qSequence f n * qSequence (qResidue m) n := by
  change qSequenceLinear ((m : ℝ)⁻¹ • scaledResidueProduct f m) = _
  rw [map_smul]
  change (m : ℝ)⁻¹ • qSequence (scaledResidueProduct f m) = _
  rw [qSequence_scaledResidueProduct, qSequence_qResidue]
  funext n
  by_cases hm : m = 0
  · simp [hm, residueFraction]
  rw [max_eq_right (Nat.one_le_iff_ne_zero.mpr hm)]
  simp only [Pi.smul_apply, smul_eq_mul, residueFraction, div_eq_mul_inv]
  ring

theorem inner_scaledResidueProduct (u f : QHilbert) (m : ℕ) :
    inner ℝ u (scaledResidueProduct f m) =
      ∑' n : ℕ, positiveQWeight n * qSequence u n * qSequence f n * ((n % max 1 m : ℕ) : ℝ) := by
  rw [qInner_weighted, qSequence_scaledResidueProduct]
  simp only [mul_assoc]

private theorem residueEnergy_summable (f : QHilbert) (m : ℕ) :
    Summable (fun n : ℕ => positiveQWeight n * (qSequence f n) ^ 2 * ((n % max 1 m : ℕ) : ℝ)) := by
  apply (qSequence_product_summable f (scaledResidueProduct f m)).congr
  intro n
  rw [qSequence_scaledResidueProduct]
  ring

/-- The exact signed product identity of equation (4.9). -/
theorem residueProduct_energy_identity (m : ℕ) :
    (∑' n : ℕ, positiveQWeight n * (qSequence displacement n) ^ 2 *
      ((n % max 1 m : ℕ) : ℝ)) =
      inner ℝ (B pResidual) (scaledResidueProduct displacement m) -
        inner ℝ witness (scaledResidueProduct displacement m) := by
  calc
    _ = inner ℝ displacement (scaledResidueProduct displacement m) := by
      rw [inner_scaledResidueProduct]
      apply tsum_congr
      intro n
      ring
    _ = _ := by rw [witness, inner_sub_left]; ring

/-- The smaller of the two signed prefixes is at most half their absolute mass. -/
theorem twice_minimumHarmonicPrefix_le (X : ℕ) :
    2 * minimumHarmonicPrefix X ≤
      ∑ n ∈ Finset.range (X + 1), |qSequence displacement n| / (n : ℝ) := by
  have h : harmonicSide 1 X + harmonicSide (-1) X =
      ∑ n ∈ Finset.range (X + 1), |qSequence displacement n| / (n : ℝ) := by
    unfold harmonicSide
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro n _
    rw [← add_div]
    simp only [one_mul, neg_one_mul]
    rcases le_total (qSequence displacement n) 0 with hn | hn
    · rw [max_eq_right hn, max_eq_left (neg_nonneg.mpr hn), zero_add, abs_of_nonpos hn]
    · rw [max_eq_left hn, max_eq_right (neg_nonpos.mpr hn), add_zero, abs_of_nonneg hn]
  rw [← h, two_mul]
  exact add_le_add (min_le_left _ _) (min_le_right _ _)

/-- Cauchy–Schwarz on the physical head, retaining the exact reciprocal sum. -/
theorem harmonicPrefix_cauchy (f : QHilbert) (X : ℕ) :
    (∑ n ∈ Finset.range (X + 1), |qSequence f n| / (n : ℝ)) ^ 2 ≤
      (∑ n ∈ Finset.range (X + 1), (n : ℝ)⁻¹) *
        (zetaTwo * ∑ n ∈ Finset.range (X + 1),
          positiveQWeight n * (qSequence f n) ^ 2 * (n : ℝ)) := by
  let a (n : ℕ) := Real.sqrt ((n : ℝ)⁻¹)
  let b (n : ℕ) := a n * |qSequence f n|
  have ha (n : ℕ) : a n ^ 2 = (n : ℝ)⁻¹ := Real.sq_sqrt (by positivity)
  have hab (n : ℕ) : a n * b n = |qSequence f n| / (n : ℝ) := by
    calc
      a n * b n = a n ^ 2 * |qSequence f n| := by dsimp [b]; ring
      _ = _ := by rw [ha]; ring
  have hb (n : ℕ) : b n ^ 2 =
      zetaTwo * (positiveQWeight n * (qSequence f n) ^ 2 * (n : ℝ)) := by
    dsimp [b]
    rw [mul_pow, ha, sq_abs]
    by_cases hn : n = 0
    · simp [hn]
    have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn
    unfold positiveQWeight
    field_simp [hnR, zetaTwo_pos.ne']
  simpa only [hab, ha, hb, ← Finset.mul_sum] using
    Finset.sum_mul_sq_le_sq_mul_sq (Finset.range (X + 1)) a b

theorem residueEnergy_head_le (f : QHilbert) (X m : ℕ) (hXm : X < m) :
    (∑ n ∈ Finset.range (X + 1), positiveQWeight n * (qSequence f n) ^ 2 * (n : ℝ)) ≤
      ∑' n : ℕ, positiveQWeight n * (qSequence f n) ^ 2 * ((n % max 1 m : ℕ) : ℝ) := by
  calc
    _ = ∑ n ∈ Finset.range (X + 1), positiveQWeight n *
        (qSequence f n) ^ 2 * ((n % max 1 m : ℕ) : ℝ) := by
      apply Finset.sum_congr rfl
      intro n hn
      have hn' : n < m := (Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)).trans_lt hXm
      rw [Nat.mod_eq_of_lt (hn'.trans_le (le_max_right _ _))]
    _ ≤ _ := (residueEnergy_summable f m).sum_le_tsum _
      (fun n _ => mul_nonneg (mul_nonneg (positiveQWeight_nonneg n) (sq_nonneg _))
        (Nat.cast_nonneg _))


/-- The correction in (4.9) converges to the Pareto normal pairing, which is zero. -/
theorem residueProduct_correction_tendsto_zero :
    Tendsto (fun m : ℕ => inner ℝ (B pResidual) (scaledResidueProduct displacement m))
      atTop (𝓝 0) := by
  let a (n : ℕ) := positiveQWeight n * qSequence pResidual n * qSequence displacement n
  have ha : Summable (fun n => |a n|) := (qSequence_product_summable pResidual displacement).abs
  let θ (m n : ℕ) := ((n % max 1 m : ℕ) : ℝ) / ((n : ℝ) + 1)
  have hpoint (n : ℕ) : Tendsto (fun m => a n * θ m n) atTop
      (𝓝 (a n * ((n : ℝ) / ((n : ℝ) + 1)))) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_gt_atTop n] with m hm
    dsimp [θ]
    rw [Nat.mod_eq_of_lt (hm.trans_le (le_max_right _ _))]
  have hdom (m n : ℕ) : ‖a n * θ m n‖ ≤ |a n| := by
    have hn : ((n % max 1 m : ℕ) : ℝ) ≤ (n : ℝ) :=
      by exact_mod_cast Nat.mod_le n (max 1 m)
    have ht : θ m n ≤ 1 := by
      apply (div_le_iff₀ (by positivity : 0 < (n : ℝ) + 1)).mpr
      linarith
    have hθ : 0 ≤ θ m n := by dsimp only [θ]; positivity
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hθ]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left ht (abs_nonneg (a n))
  have ht := tendsto_tsum_of_dominated_convergence ha hpoint (Eventually.of_forall hdom)
  have he (m : ℕ) : inner ℝ (B pResidual) (scaledResidueProduct displacement m) =
      ∑' n, a n * θ m n := by
    rw [inner_scaledResidueProduct]
    apply tsum_congr
    intro n
    rw [qSequence_B]
    dsimp [a, θ]
    ring
  have hp : inner ℝ (ZetaTwoParetoTransfer.toPareto displacement)
      (ZetaTwoParetoTransfer.toPareto pResidual) = 0 := by
    unfold pResidual
    rw [QParetoClosedProjectionComparison.toPareto_sub,
      QParetoClosedProjectionComparison.toPareto_pFit]
    exact Submodule.inner_right_of_mem_orthogonal
      ((toPareto_mem_iff displacement).mpr displacement_mem)
      (Submodule.sub_starProjection_mem_orthogonal (K := paretoClosure) _)
  rw [pareto_inner_identity, real_inner_comm pResidual displacement,
    real_inner_comm (B pResidual) displacement] at hp
  have hz : inner ℝ pResidual displacement - inner ℝ (B pResidual) displacement = 0 :=
    (mul_eq_zero.mp hp).resolve_left zetaTwo_pos.ne'
  rw [qInner_weighted pResidual displacement, qInner_weighted (B pResidual) displacement,
    ← (qSequence_product_summable pResidual displacement).tsum_sub
      (qSequence_product_summable (B pResidual) displacement)] at hz
  have hlim : (∑' n, a n * ((n : ℝ) / ((n : ℝ) + 1))) = 0 := by
    rw [← hz]
    apply tsum_congr
    intro n
    rw [qSequence_B]
    dsimp [a]
    field_simp; ring
  simpa only [← he, hlim] using ht

/-- The Q-distance of the physical product d times the legal atom g_m. -/
def residueProductDistance (m : ℕ) : ℝ :=
  Metric.infDist ((m : ℝ)⁻¹ • scaledResidueProduct displacement m) (closure : Set QHilbert)

theorem scaled_residueProductDistance (m : ℕ) (hm : 0 < m) :
    (m : ℝ) * residueProductDistance m =
      Metric.infDist (scaledResidueProduct displacement m) (closure : Set QHilbert) := by
  have hmr : (0 : ℝ) < m := by exact_mod_cast hm
  rw [residueProductDistance, closure.infDist_eq_norm_sub_starProjection,
    closure.infDist_eq_norm_sub_starProjection, map_smul, ← smul_sub, norm_smul,
    Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hmr), ← mul_assoc,
    mul_inv_cancel₀ hmr.ne', one_mul]

/-- The exact finite harmonic coefficient in the bound is the harmonic number H_X. -/
theorem residueProduct_finite_distance_bound (X m : ℕ) (hXm : X < m) :
    (2 * minimumHarmonicPrefix X) ^ 2 ≤
      zetaTwo * (harmonic X : ℝ) *
        (|inner ℝ (B pResidual) (scaledResidueProduct displacement m)| +
          ‖witness‖ * ((m : ℝ) * residueProductDistance m)) := by
  have hs : 0 ≤ 2 * minimumHarmonicPrefix X := by
    unfold minimumHarmonicPrefix harmonicSide
    exact mul_nonneg (by norm_num) (le_min
      (Finset.sum_nonneg fun n _ => div_nonneg (le_max_right _ _) (Nat.cast_nonneg n))
      (Finset.sum_nonneg fun n _ => div_nonneg (le_max_right _ _) (Nat.cast_nonneg n)))
  have hsq := pow_le_pow_left₀ hs (twice_minimumHarmonicPrefix_le X) 2
  have hcs := hsq.trans (harmonicPrefix_cauchy displacement X)
  have hsum : (∑ n ∈ Finset.range (X + 1), (n : ℝ)⁻¹) = (harmonic X : ℝ) := by
    rw [Finset.sum_range_succ', RiemannResearch.Analysis.harmonic_cast_range]
    simp [Nat.cast_succ, one_div]
  rw [hsum, ← mul_assoc, mul_comm (harmonic X : ℝ) zetaTwo] at hcs
  apply hcs.trans
  apply mul_le_mul_of_nonneg_left _ (mul_nonneg zetaTwo_pos.le
    (RiemannResearch.Analysis.harmonic_nonnegative X))
  have hp := residueEnergy_head_le displacement X m hXm
  rw [residueProduct_energy_identity] at hp
  have hw := closure.abs_real_inner_le_norm_mul_infDist_of_mem_orthogonal
    witness_mem_orthogonal (scaledResidueProduct displacement m)
  rw [← scaled_residueProductDistance m (by omega)] at hw
  linarith only [hp, hw,
    le_abs_self (inner ℝ (B pResidual) (scaledResidueProduct displacement m)),
    neg_le_abs (inner ℝ witness (scaledResidueProduct displacement m))]


/-- Failure of full legal approximation forces escape after every fixed polylog loss. -/
theorem residueProductDistance_polylog_escape (hr : qResidual ≠ 0)
    (k : ℝ) (hk : 0 ≤ k) :
    Tendsto (fun m : ℕ => (m : ℝ) * residueProductDistance m /
      (1 + Real.log (m : ℝ)) ^ k) atTop atTop := by
  let bExp : ℝ := (k + 1) / 2
  have hbExp : 0 ≤ bExp := by dsimp [bExp]; positivity
  have hshift : Tendsto (fun m : ℕ => m - 1) atTop atTop := by
    apply tendsto_atTop.2
    intro n
    filter_upwards [eventually_ge_atTop (n + 1)] with m hm
    omega
  have hlogShift : Tendsto (fun m : ℕ => Real.log ((m - 1 : ℕ) : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp hshift)
  have hcorr : ∀ᶠ m : ℕ in atTop,
      |inner ℝ (B pResidual) (scaledResidueProduct displacement m)| ≤ 1 :=
    ((tendsto_order.1 (by simpa using residueProduct_correction_tendsto_zero.abs :
      Tendsto (fun m => |inner ℝ (B pResidual) (scaledResidueProduct displacement m)|)
        atTop (𝓝 0))).2 1 zero_lt_one).mono fun _ h => h.le
  apply tendsto_atTop.2
  intro b
  let c : ℝ := max b 0
  let D : ℝ := zetaTwo * (1 + ‖witness‖ * c) * (3 : ℝ) ^ (k + 1)
  have hc : 0 ≤ c := le_max_right _ _
  have hcoef : 0 ≤ zetaTwo * (1 + ‖witness‖ * c) :=
    mul_nonneg zetaTwo_pos.le (by positivity)
  have hD : 0 ≤ D := mul_nonneg hcoef (Real.rpow_nonneg (by norm_num) _)
  have hK : D < (D + 1) ^ 2 := by nlinarith [sq_nonneg D]
  have hescape := (minimumHarmonicPrefix_log_escape hr bExp hbExp).comp hshift
  filter_upwards [(tendsto_atTop.1 hescape) (D + 1), (tendsto_atTop.1 hlogShift) 1,
    hcorr, eventually_ge_atTop (3 : ℕ)] with m hesc hlog hcorr hm
  let X : ℕ := m - 1
  let l : ℝ := Real.log (X : ℝ)
  let L : ℝ := 1 + Real.log (m : ℝ)
  change D + 1 ≤ minimumHarmonicPrefix X / l ^ bExp at hesc
  change 1 ≤ l at hlog
  change b ≤ (m : ℝ) * residueProductDistance m / L ^ k
  have hl : 0 < l := by linarith
  have hXm : X < m := by dsimp [X]; omega
  have hX2 : (2 : ℝ) ≤ (X : ℝ) := by exact_mod_cast (show 2 ≤ X by dsimp [X]; omega)
  have hXpos : (0 : ℝ) < (X : ℝ) := by linarith
  have hmr : (m : ℝ) = (X : ℝ) + 1 := by
    exact_mod_cast (show m = X + 1 by dsimp [X]; omega)
  have hlogMono : l ≤ Real.log (m : ℝ) :=
    Real.log_le_log hXpos (by linarith)
  have hL1 : 1 ≤ L := by dsimp [L]; linarith
  have hL : 0 < L := by linarith
  have hlogUpper : Real.log (m : ℝ) ≤ 2 * l := by
    have hsq : (m : ℝ) ≤ (X : ℝ) ^ 2 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hX2) (Nat.cast_nonneg (α := ℝ) X)]
    simpa only [Real.log_pow, Nat.cast_ofNat, l] using
      Real.log_le_log (by linarith : 0 < (m : ℝ)) hsq
  have hLupper : L ≤ 3 * l := by dsimp [L]; linarith
  have hLk : 1 ≤ L ^ k := Real.one_le_rpow hL1 hk
  have hLkpos : 0 < L ^ k := Real.rpow_pos_of_pos hL k
  have hLp : 0 < l ^ (k + 1) := Real.rpow_pos_of_pos hl _
  have hH := (le_div_iff₀ (Real.rpow_pos_of_pos hl bExp)).mp hesc
  have hHs := pow_le_pow_left₀
    (mul_nonneg (by linarith : 0 ≤ D + 1) (Real.rpow_nonneg hl.le _)) hH 2
  rw [mul_pow, pow_two (l ^ bExp), ← Real.rpow_add hl,
    show bExp + bExp = k + 1 by dsimp [bExp]; ring] at hHs
  by_contra hbad
  have hbd := (div_le_iff₀ hLkpos).mp (le_of_lt (lt_of_not_ge hbad))
  have hdist : (m : ℝ) * residueProductDistance m ≤ c * L ^ k :=
    hbd.trans (mul_le_mul_of_nonneg_right (le_max_left b 0) hLkpos.le)
  have hsum : |inner ℝ (B pResidual) (scaledResidueProduct displacement m)| +
      ‖witness‖ * ((m : ℝ) * residueProductDistance m) ≤
        L ^ k * (1 + ‖witness‖ * c) := by
    calc
      _ ≤ L ^ k + ‖witness‖ * (c * L ^ k) :=
        add_le_add (hcorr.trans hLk) (mul_le_mul_of_nonneg_left hdist (norm_nonneg _))
      _ = _ := by ring
  have hHarm : (harmonic X : ℝ) ≤ L :=
    (harmonic_le_one_add_log X).trans (by dsimp [L]; linarith)
  have hbound : (2 * minimumHarmonicPrefix X) ^ 2 ≤ D * l ^ (k + 1) := calc
    _ ≤ zetaTwo * (harmonic X : ℝ) *
        (L ^ k * (1 + ‖witness‖ * c)) :=
      (residueProduct_finite_distance_bound X m hXm).trans
        (mul_le_mul_of_nonneg_left hsum (mul_nonneg zetaTwo_pos.le
          (RiemannResearch.Analysis.harmonic_nonnegative X)))
    _ ≤ zetaTwo * L * (L ^ k * (1 + ‖witness‖ * c)) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hHarm zetaTwo_pos.le) (by positivity)
    _ = (zetaTwo * (1 + ‖witness‖ * c)) * L ^ (k + 1) := by
      rw [Real.rpow_add hL, Real.rpow_one]
      ring
    _ ≤ (zetaTwo * (1 + ‖witness‖ * c)) * (3 * l) ^ (k + 1) :=
      mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hL.le hLupper (by positivity)) hcoef
    _ = _ := by rw [Real.mul_rpow (by norm_num : 0 ≤ (3 : ℝ)) hl.le]; dsimp [D]; ring
  have hstrict := mul_lt_mul_of_pos_right hK hLp
  nlinarith only [hHs, hbound, hstrict, sq_nonneg (minimumHarmonicPrefix X)]

/-- RH failure forces escape along the entire conductor sequence. -/
theorem residueProductDistance_polylog_escape_of_not_RH (hRH : ¬ RiemannHypothesis)
    (k : ℝ) (hk : 0 ≤ k) :
    Tendsto (fun m : ℕ => (m : ℝ) * residueProductDistance m /
      (1 + Real.log (m : ℝ)) ^ k) atTop atTop :=
  residueProductDistance_polylog_escape
    (fun hr => hRH (riemannHypothesis_of_qOne_mem_full_closure (qResidual_eq_zero_iff.mp hr)))
    k hk

/-- A finite bound at arbitrarily large conductors is the cofinal form of finite liminf. -/
theorem qResidual_eq_zero_iff_cofinal_residueProductDistance (k : ℝ) (hk : 0 ≤ k) :
    qResidual = 0 ↔ ∃ C : ℝ, 0 ≤ C ∧ ∃ᶠ m : ℕ in atTop,
      (m : ℝ) * residueProductDistance m / (1 + Real.log (m : ℝ)) ^ k ≤ C := by
  constructor
  · intro hr
    have hd := displacement_eq_zero_of_qResidual_eq_zero hr
    have hz (m : ℕ) : scaledResidueProduct displacement m = 0 := by
      apply qSequence_injective
      rw [qSequence_scaledResidueProduct, hd]
      change (fun n => qSequenceLinear 0 n * _) = qSequenceLinear 0
      funext n
      simp
    refine ⟨0, le_rfl, (Eventually.of_forall ?_).frequently⟩
    intro m
    simp [residueProductDistance, hz, closure.infDist_eq_norm_sub_starProjection]
  · rintro ⟨C, _, hC⟩
    by_contra hr
    have he := (tendsto_atTop.1 (residueProductDistance_polylog_escape hr k hk)) (C + 1)
    obtain ⟨m, hm, hCm⟩ := (hC.and_eventually he).exists
    linarith

/-- The forward RH test uses only the actual full-conductor displacement and the cofinal bound. -/
theorem riemannHypothesis_of_cofinal_residueProductDistance (k : ℝ) (hk : 0 ≤ k)
    (h : ∃ C : ℝ, 0 ≤ C ∧ ∃ᶠ m : ℕ in atTop,
      (m : ℝ) * residueProductDistance m / (1 + Real.log (m : ℝ)) ^ k ≤ C) :
    RiemannHypothesis :=
  riemannHypothesis_of_qOne_mem_full_closure
    (qResidual_eq_zero_iff.mp ((qResidual_eq_zero_iff_cofinal_residueProductDistance k hk).mpr h))

/-- The published natural-dilation approximation condition is equivalent to the cofinal test. -/
theorem naturalApproximation_iff_cofinal_residueProductDistance (k : ℝ) (hk : 0 ≤ k) :
    Pareto.BaezDuarte.NaturalApproximation ↔
      ∃ C : ℝ, 0 ≤ C ∧ ∃ᶠ m : ℕ in atTop,
        (m : ℝ) * residueProductDistance m / (1 + Real.log (m : ℝ)) ^ k ≤ C := by
  have hspace : paretoClosure = Pareto.CoefficientStabilization.closedSpace := by
    unfold paretoClosure legalSpan Pareto.CoefficientStabilization.closedSpace
    rw [QParetoEquivalence.map_span_range]
    simp only [ZetaTwoParetoTransfer.toPareto_residueAtom, Analysis.ExhaustiveWalk.dictionaryClosure]
  rw [Pareto.BaezDuarte.naturalApproximation_iff_one_mem,
    ← qResidual_eq_zero_iff_cofinal_residueProductDistance k hk, qResidual_eq_zero_iff,
    ← toPareto_mem_iff, hspace, ZetaTwoParetoTransfer.toPareto_qOne]

/-- The reverse direction uses the published Báez-Duarte approximation, explicitly supplied. -/
theorem riemannHypothesis_iff_cofinal_residueProductDistance
    (hBD : RiemannHypothesis → Pareto.BaezDuarte.NaturalApproximation)
    (k : ℝ) (hk : 0 ≤ k) :
    RiemannHypothesis ↔ ∃ C : ℝ, 0 ≤ C ∧ ∃ᶠ m : ℕ in atTop,
      (m : ℝ) * residueProductDistance m / (1 + Real.log (m : ℝ)) ^ k ≤ C :=
  ⟨fun hRH => (naturalApproximation_iff_cofinal_residueProductDistance k hk).mp (hBD hRH),
    riemannHypothesis_of_cofinal_residueProductDistance k hk⟩

end RiemannResearch.RH.QFullDisplacement
