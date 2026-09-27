/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.IncreasingAbelConvergence
import RiemannResearch.RH.DampedMobiusUniformHalfRange
import RiemannResearch.RH.DampedMobiusHalfHilbertRate
import RiemannResearch.Analysis.IncreasingLogWeights
import RiemannResearch.Analysis.MovingBandAsymptotics

/-!
# Natural-order convergence in a shrinking subhalf band

The half-damped Möbius cutoff limit remains valid when damping approaches
one half from below and the conductor amplification stays bounded.
In particular, every fixed logarithmic band
  0 ≤ 1/2 - ε ≤ A / log(M+1)
has the same limit as M tends to infinity. The quantitative strengthening
uses the endpoint quarter-logarithmic error rate: with L(M)=6+log(M+1),
full norm convergence holds whenever
  (1/2-epsilon) log(M+1) - (1/4) log L(M) -> -infinity.
Every band with coefficient c<1/4 has error at most C L(M)^(c-1/4);
the critical coefficient with bounded additive margin gives uniform
signed energy bounds. The margin is a parameter condition, with no
unproved arithmetic hypothesis.

The unconditional arithmetic input is the previously checked half-damping
Hilbert convergence. The proof retains the signs in complete vector
prefixes and uses increasing-weight Abel regularity. This does not prove
finite energy at any fixed damping below one half, and does not approach
the zero-damping hypothesis needed for RH.

Source for the underlying endpoint membership statement: J.-F. Burnol,
"On an analytic estimate in the theory of the Riemann zeta function and
a theorem of Baez-Duarte", Section 4, Lemma 4.1,
https://arxiv.org/abs/math/0202166. The moving-band transfer is a direct
finite Abel argument; no mathematical novelty claim is made.
-/

noncomputable section
open Filter Set
open scoped Topology BigOperators
namespace RiemannResearch.RH.Pareto
open RiemannResearch.Analysis

/-- Subhalf damping may move with the conductor cutoff, with any common
finite bound on its multiplicative conductor amplification. -/
theorem dampedMobius_moving_subhalf_tendsto
    (ε : ℕ → ℝ) (hε : ∀ j, ε j ≤ (1 / 2 : ℝ))
    (hεlim : Tendsto ε atTop (𝓝 (1 / 2)))
    (M : ℕ → ℕ) (hM : Tendsto M atTop atTop)
    {B : ℝ} (hB : 0 < B)
    (hband : ∀ j, ((M j + 1 : ℕ) : ℝ) ^ ((1 / 2 : ℝ) - ε j) ≤ B) :
    Tendsto (fun j => arithmeticFloorHilbertPartial (dampedMobiusWeight (ε j)) (M j))
      atTop (𝓝 (dampedMobiusHalfRangeLimit (1 / 2) le_rfl)) := by
  have hf := (dampedMobiusHalfRangeLimit_spec (1 / 2) le_rfl).2
  have hp : Tendsto (signedVectorPrefix
      (fun m => -arithmeticResidueTerm (dampedMobiusWeight (1 / 2)) m)) atTop
        (𝓝 (dampedMobiusHalfRangeLimit (1 / 2) le_rfl)) := by
    convert hf using 1
    funext n
    simp only [signedVectorPrefix, Finset.sum_neg_distrib, arithmeticFloorHilbertPartial]
  have hw (j : ℕ) : Monotone
      (fun n : ℕ => ((n + 1 : ℕ) : ℝ) ^ ((1 / 2 : ℝ) - ε j)) := by
    intro i k hik
    exact Real.rpow_le_rpow (by positivity)
      (by exact_mod_cast Nat.add_le_add_right hik 1) (sub_nonneg.mpr (hε j))
  have hwlim (n : ℕ) :
      Tendsto (fun j => ((n + 1 : ℕ) : ℝ) ^ ((1 / 2 : ℝ) - ε j))
        atTop (𝓝 1) := by
    have h := (Real.continuous_const_rpow
      (by positivity : (((n + 1 : ℕ) : ℝ)) ≠ 0)).tendsto (0 : ℝ)
    simpa only [Function.comp_def, Real.rpow_zero] using
      h.comp (by simpa using hεlim.const_sub (1 / 2 : ℝ))
  have h := signedVector_increasing_weights_joint_tendsto _ hp
    (fun j n => ((n + 1 : ℕ) : ℝ) ^ ((1 / 2 : ℝ) - ε j)) hw
    (fun j n => by positivity) hwlim M hM hB hband
  simpa only [dampedMobiusPartial_from_half,
    show ∀ j, -(ε j - 1 / 2) = (1 / 2 : ℝ) - ε j by intro j; ring] using h

/-- The damping convergence follows automatically from a common bound on
(1/2-epsilon) log(M+1). Thus a full band of width A/log(M+1) below the
endpoint has the endpoint's full signed Hilbert limit. -/
theorem dampedMobius_logarithmic_subhalf_band_tendsto
    (ε : ℕ → ℝ) (hε : ∀ j, ε j ≤ (1 / 2 : ℝ))
    (M : ℕ → ℕ) (hM : Tendsto M atTop atTop)
    (A : ℝ)
    (hband : ∀ j, ((1 / 2 : ℝ) - ε j) * Real.log ((M j + 1 : ℕ) : ℝ) ≤ A) :
    Tendsto (fun j => arithmeticFloorHilbertPartial (dampedMobiusWeight (ε j)) (M j))
      atTop (𝓝 (dampedMobiusHalfRangeLimit (1 / 2) le_rfl)) := by
  have hlog : Tendsto (fun j => Real.log ((M j + 1 : ℕ) : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp
      (tendsto_natCast_atTop_atTop.comp ((tendsto_add_atTop_nat 1).comp hM))
  have hrecip : Tendsto (fun j => A / Real.log ((M j + 1 : ℕ) : ℝ))
      atTop (𝓝 0) := by
    simpa only [mul_zero, div_eq_mul_inv, Function.comp_def] using
      (tendsto_inv_atTop_zero.comp hlog).const_mul A
  have hd : Tendsto (fun j => (1 / 2 : ℝ) - ε j) atTop (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall (fun j => sub_nonneg.mpr (hε j))) _ hrecip
    filter_upwards [hlog.eventually (eventually_gt_atTop (0 : ℝ))] with j hj
    exact (le_div_iff₀ hj).mpr (hband j)
  have hεlim : Tendsto ε atTop (𝓝 (1 / 2)) := by
    have h := hd.const_sub (1 / 2)
    simpa only [sub_sub_cancel, sub_zero] using h
  apply dampedMobius_moving_subhalf_tendsto ε hε hεlim M hM (Real.exp_pos A)
  intro j
  rw [Real.rpow_def_of_pos (by positivity)]
  exact Real.exp_le_exp.mpr (by simpa only [mul_comm] using hband j)

/-- The entire logarithmic band converges uniformly. The conductor and the
damping are independently quantified inside the band, and the bound uses
the complete infinite physical Hilbert norm. -/
theorem dampedMobius_logarithmic_subhalf_band_uniform
    (A : ℝ) :
    ∀ η : ℝ, 0 < η → ∃ J : ℕ, ∀ M : ℕ, J ≤ M → ∀ ε : ℝ,
      ε ≤ (1 / 2 : ℝ) →
      ((1 / 2 : ℝ) - ε) * Real.log ((M + 1 : ℕ) : ℝ) ≤ A →
      ‖arithmeticFloorHilbertPartial (dampedMobiusWeight ε) M -
        dampedMobiusHalfRangeLimit (1 / 2) le_rfl‖ ≤ η := by
  intro η hη
  by_contra h
  push Not at h
  choose M hMJ ε hε hband hbad using h
  have hM : Tendsto M atTop atTop := by
    apply tendsto_atTop.mpr
    intro b
    filter_upwards [eventually_ge_atTop b] with j hj
    exact hj.trans (hMJ j)
  have hc := dampedMobius_logarithmic_subhalf_band_tendsto ε hε M hM A hband
  obtain ⟨J, hJ⟩ := Metric.tendsto_atTop.mp hc η hη
  have hgood : ‖arithmeticFloorHilbertPartial (dampedMobiusWeight (ε J)) (M J) -
      dampedMobiusHalfRangeLimit (1 / 2) le_rfl‖ < η := by
    simpa only [dist_eq_norm] using hJ J le_rfl
  linarith [hbad J]

/-- A single signed energy budget works for every finite cutoff in a
fixed logarithmic subhalf band. The budget also bounds every finite
physical signed off-diagonal head independently of its head cutoff. -/
theorem dampedMobius_logarithmic_subhalf_band_signed_bounds
    (A : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ M : ℕ, ∀ ε : ℝ, ε ≤ (1 / 2 : ℝ) →
      ((1 / 2 : ℝ) - ε) * Real.log ((M + 1 : ℕ) : ℝ) ≤ A →
      (‖arithmeticFloorHilbertPartial (dampedMobiusWeight ε) M‖ ≤ C) ∧
      (dampedMobiusGramOffDiagonal ε M ≤ C ^ 2) ∧
      ∀ H : ℕ, dampedMobiusHeadOffDiagonal ε H M ≤ C ^ 2 := by
  obtain ⟨B, hB, hb⟩ := dampedMobius_half_range_uniform_norm_bound
  refine ⟨2 * Real.exp A * B, by positivity, fun M ε hε hband => ?_⟩
  have hp (n : ℕ) :
      ‖signedVectorPrefix
        (fun m => -arithmeticResidueTerm (dampedMobiusWeight (1 / 2)) m) n‖ ≤ B := by
    simpa only [signedVectorPrefix, Finset.sum_neg_distrib,
      arithmeticFloorHilbertPartial] using hb (1 / 2) le_rfl n
  have hw : Monotone (fun n : ℕ => ((n + 1 : ℕ) : ℝ) ^ ((1 / 2 : ℝ) - ε)) := by
    intro i j hij
    exact Real.rpow_le_rpow (by positivity)
      (by exact_mod_cast Nat.add_le_add_right hij 1) (sub_nonneg.mpr hε)
  have ht : ((M + 1 : ℕ) : ℝ) ^ ((1 / 2 : ℝ) - ε) ≤ Real.exp A := by
    rw [Real.rpow_def_of_pos (by positivity)]
    exact Real.exp_le_exp.mpr (by simpa only [mul_comm] using hband)
  have hn : ‖arithmeticFloorHilbertPartial (dampedMobiusWeight ε) M‖ ≤
      2 * Real.exp A * B := by
    rw [dampedMobiusPartial_from_half, show -(ε - 1 / 2) = (1 / 2 : ℝ) - ε by ring]
    apply (signedVector_increasing_weight_norm_le _ _ hw
      (fun n => by positivity) hB hp M).trans
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ht (by norm_num)) hB
  have hsq : ‖arithmeticFloorHilbertPartial (dampedMobiusWeight ε) M‖ ^ 2 ≤
      (2 * Real.exp A * B) ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr hn
  refine ⟨hn, (dampedMobius_offDiagonal_le_partial_norm_sq ε M).trans hsq, fun H => ?_⟩
  have hphead := paretoHeadPairing_self_le H
    (arithmeticFloorHilbertPartial (dampedMobiusWeight ε) M)
  rw [dampedMobius_partial_head_eq_signed] at hphead
  linarith [dampedMobiusHeadDiagonal_nonneg ε H M]

/-- The whole finite signed Gram energy also converges in the logarithmic
subhalf band; the conclusion is about cutoff vectors, not a hypothetical
infinite vector at a fixed subhalf damping. -/
theorem dampedMobius_logarithmic_subhalf_band_energy_tendsto
    (ε : ℕ → ℝ) (hε : ∀ j, ε j ≤ (1 / 2 : ℝ))
    (M : ℕ → ℕ) (hM : Tendsto M atTop atTop)
    (A : ℝ)
    (hband : ∀ j, ((1 / 2 : ℝ) - ε j) * Real.log ((M j + 1 : ℕ) : ℝ) ≤ A) :
    Tendsto (fun j =>
      ‖arithmeticFloorHilbertPartial (dampedMobiusWeight (ε j)) (M j)‖ ^ 2) atTop
      (𝓝 (∑' n : ℕ, positiveWeight n *
        (dampedMobiusPrefix (1 / 2) n - (n : ℝ) *
          (1 / riemannZeta (1 + ((1 / 2 : ℝ) : ℂ))).re) ^ 2)) := by
  have h := (dampedMobius_logarithmic_subhalf_band_tendsto ε hε M hM A hband).norm.pow 2
  simpa only [hilbert_norm_weighted_sq,
    (dampedMobiusHalfRangeLimit_spec (1 / 2) le_rfl).1] using h

/-- A harmless successor shift in the logarithmic rate costs at most two. -/
private theorem halfRate_log_successor_le (N : ℕ) :
    (6 + Real.log ((N + 1 : ℕ) : ℝ)) ^ (-1 / 4 : ℝ) ≤
      2 * (6 + Real.log ((N + 2 : ℕ) : ℝ)) ^ (-1 / 4 : ℝ) := by
  let a : ℝ := 6 + Real.log ((N + 1 : ℕ) : ℝ)
  let b : ℝ := 6 + Real.log ((N + 2 : ℕ) : ℝ)
  have hlog : 0 ≤ Real.log ((N + 1 : ℕ) : ℝ) :=
    Real.log_nonneg (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le N))
  have ha : 0 < a := by dsimp [a]; linarith
  have hb : 0 < b := by
    have h := Real.log_nonneg (show (1 : ℝ) ≤ ((N + 2 : ℕ) : ℝ) by exact_mod_cast (by omega : 1 ≤ N + 2))
    dsimp [b]; linarith
  have hblog : Real.log ((N + 2 : ℕ) : ℝ) ≤
      Real.log (2 : ℝ) + Real.log ((N + 1 : ℕ) : ℝ) := by
    rw [← Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by positivity)]
    apply Real.log_le_log (by positivity)
    push_cast
    nlinarith [Nat.cast_nonneg (α := ℝ) N]
  have hlog2 : Real.log (2 : ℝ) ≤ 1 := by
    linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]
  have hba : b ≤ 2 * a := by dsimp [a, b]; linarith
  have hp : b ^ (1 / 4 : ℝ) ≤ 2 * a ^ (1 / 4 : ℝ) := by
    calc
      _ ≤ (2 * a) ^ (1 / 4 : ℝ) := Real.rpow_le_rpow hb.le hba (by norm_num)
      _ = (2 : ℝ) ^ (1 / 4 : ℝ) * a ^ (1 / 4 : ℝ) := Real.mul_rpow (by norm_num) ha.le
      _ ≤ 2 * a ^ (1 / 4 : ℝ) := by
        apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg ha.le _)
        simpa using Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
          (by norm_num : (1 / 4 : ℝ) ≤ 1)
  change a ^ (-1 / 4 : ℝ) ≤ 2 * b ^ (-1 / 4 : ℝ)
  rw [show (-1 / 4 : ℝ) = -(1 / 4 : ℝ) by ring,
    Real.rpow_neg ha.le, Real.rpow_neg hb.le, inv_eq_one_div, inv_eq_one_div, mul_one_div]
  exact (div_le_div_iff₀ (Real.rpow_pos_of_pos ha _) (Real.rpow_pos_of_pos hb _)).mpr
    (by simpa using hp)

/-- Quantitative undamping from the endpoint. Every complete signed
cutoff is controlled by the endpoint logarithmic error rate multiplied
by its conductor amplification. This assertion is uniform in damping. -/
theorem dampedMobius_subhalf_quantitative_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ M : ℕ, ∀ ε : ℝ, ε ≤ (1 / 2 : ℝ) →
      ‖arithmeticFloorHilbertPartial (dampedMobiusWeight ε) M -
        dampedMobiusHalfRangeLimit (1 / 2) le_rfl‖ ≤
          C * (((M + 1 : ℕ) : ℝ) ^ ((1 / 2 : ℝ) - ε) *
            (6 + Real.log ((M + 1 : ℕ) : ℝ)) ^ (-1 / 4 : ℝ)) := by
  obtain ⟨C, hC, herror⟩ := dampedMobius_half_cutoffs_log_rate
  refine ⟨4 * C, by positivity, fun M ε hε => ?_⟩
  let δ : ℝ := (1 / 2 : ℝ) - ε
  have hδ : 0 ≤ δ := sub_nonneg.mpr hε
  let u := fun m => -arithmeticResidueTerm (dampedMobiusWeight (1 / 2)) m
  let f := dampedMobiusHalfRangeLimit (1 / 2) le_rfl
  let R := fun m : ℕ => C * (6 + Real.log ((m + 1 : ℕ) : ℝ)) ^ (-1 / 4 : ℝ)
  let w := fun n : ℕ => ((n + 1 : ℕ) : ℝ) ^ δ
  have hw : Monotone w := by
    intro i j hij
    exact Real.rpow_le_rpow (by positivity)
      (by exact_mod_cast Nat.add_le_add_right hij 1) hδ
  have hwn (n : ℕ) : 0 ≤ w n := by dsimp [w]; positivity
  have hwzero : w 0 = 1 := by simp [w]
  have hu (n : ℕ) : ‖signedVectorPrefix u (n + 1) - f‖ ≤ R (n + 1) := by
    simpa only [u, f, R, signedVectorPrefix, Finset.sum_neg_distrib,
      arithmeticFloorHilbertPartial] using herror (n + 1)
  cases M with
  | zero =>
    have he := herror 0
    have heq : arithmeticFloorHilbertPartial (dampedMobiusWeight ε) 0 =
        arithmeticFloorHilbertPartial (dampedMobiusWeight (1 / 2)) 0 := by
      simp [arithmeticFloorHilbertPartial]
    rw [heq]
    norm_num only [Nat.zero_add, Nat.cast_one, Real.one_rpow, Real.log_one,
      add_zero, one_mul] at he ⊢
    apply he.trans
    nlinarith [Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 6) (-1 / 4 : ℝ)]
  | succ N =>
    have hb := signedVector_increasing_weight_residual_le u w f R hw hwn hu N
    rw [hwzero, one_smul] at hb
    have hscalar := increasingPower_logProfile_sum_le hδ
      (by norm_num : (0 : ℝ) < 6) (by norm_num : (0 : ℝ) ≤ 1 / 4)
      (by norm_num : (1 / 4 : ℝ) < 1) N
    rw [show -(1 / 4 : ℝ) = (-1 / 4 : ℝ) by ring] at hscalar
    let p := (6 + Real.log ((N + 2 : ℕ) : ℝ)) ^ (-1 / 4 : ℝ)
    let q := (6 + Real.log ((N + 1 : ℕ) : ℝ)) ^ (-1 / 4 : ℝ)
    have hp : 0 ≤ p := by dsimp [p]; positivity
    have hq : 0 ≤ q := by dsimp [q]; positivity
    have hshift : q ≤ 2 * p := halfRate_log_successor_le N
    have hs : (∑ n ∈ Finset.range N, (w (n + 1) - w n) * R (n + 1)) ≤
        (4 / 3 : ℝ) * C * (w N - 1) * q := by
      have hfactor : (∑ n ∈ Finset.range N, (w (n + 1) - w n) * R (n + 1)) =
          C * (∑ n ∈ Finset.range N,
            (((n : ℝ) + 2) ^ δ - ((n : ℝ) + 1) ^ δ) *
              (6 + Real.log ((n : ℝ) + 2)) ^ (-1 / 4 : ℝ)) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro n hn
        dsimp [w, R]
        push_cast
        ring
      rw [hfactor]
      apply (mul_le_mul_of_nonneg_left hscalar hC).trans_eq
      dsimp [w, q]
      push_cast
      ring
    have hfinal : ‖(∑ n ∈ Finset.range (N + 1), w n • u n) - f‖ ≤
        4 * C * (w (N + 1) * p) := by
      have hR : R (N + 1) = C * p := by
        dsimp only [R, p]
      rw [hR] at hb
      have hwp : w N * q ≤ 2 * w N * p :=
        (mul_le_mul_of_nonneg_left hshift (hwn N)).trans_eq (by ring)
      have hcs : C * (w N - 1) * q ≤ C * w N * q := by
        nlinarith [mul_nonneg hC hq]
      have hcp : C * w N * q ≤ 2 * C * w N * p := by
        calc
          C * w N * q = C * (w N * q) := by ring
          _ ≤ C * (2 * w N * p) := mul_le_mul_of_nonneg_left hwp hC
          _ = 2 * C * w N * p := by ring
      have hmono : C * w N * p ≤ C * w (N + 1) * p := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (hw (Nat.le_succ N)) hC) hp
      nlinarith [mul_nonneg (mul_nonneg hC (hwn N)) hp]
    rw [dampedMobiusPartial_from_half,
      show -(ε - 1 / 2) = δ by dsimp [δ]; ring]
    simpa only [u, f, w, p, δ, Nat.succ_eq_add_one, Nat.add_assoc] using hfinal

/-- The amplified quarter-logarithmic rate is enough for joint
subhalf convergence. Damping convergence and bounded amplification
are not assumptions; the norm majorant directly tends to zero. -/
theorem dampedMobius_moving_subhalf_rate_tendsto
    (ε : ℕ → ℝ) (hε : ∀ j, ε j ≤ (1 / 2 : ℝ)) (M : ℕ → ℕ)
    (hrate : Tendsto (fun j =>
      ((M j + 1 : ℕ) : ℝ) ^ ((1 / 2 : ℝ) - ε j) *
        (6 + Real.log ((M j + 1 : ℕ) : ℝ)) ^ (-1 / 4 : ℝ)) atTop (𝓝 0)) :
    Tendsto (fun j => arithmeticFloorHilbertPartial (dampedMobiusWeight (ε j)) (M j))
      atTop (𝓝 (dampedMobiusHalfRangeLimit (1 / 2) le_rfl)) := by
  obtain ⟨C, hC, hbound⟩ := dampedMobius_subhalf_quantitative_bound
  have hlim := hrate.const_mul C
  simp only [mul_zero] at hlim
  apply Metric.tendsto_atTop.mpr
  intro η hη
  obtain ⟨J, hJ⟩ := Metric.tendsto_atTop.mp hlim η hη
  refine ⟨J, fun j hj => ?_⟩
  rw [dist_eq_norm]
  apply (hbound (M j) (ε j) (hε j)).trans_lt
  have h := hJ j hj
  rw [dist_zero_right, Real.norm_eq_abs] at h
  exact lt_of_le_of_lt (le_abs_self _) h

/-- The sharp sufficient moving margin from the quarter-log endpoint
rate. No fixed positive distance below the half endpoint satisfies it. -/
theorem dampedMobius_moving_subhalf_margin_tendsto
    (ε : ℕ → ℝ) (hε : ∀ j, ε j ≤ (1 / 2 : ℝ))
    (M : ℕ → ℕ) (hM : Tendsto M atTop atTop)
    (hmargin : Tendsto (fun j =>
      ((1 / 2 : ℝ) - ε j) * Real.log ((M j + 1 : ℕ) : ℝ) -
        (1 / 4 : ℝ) * Real.log (6 + Real.log ((M j + 1 : ℕ) : ℝ)))
      atTop atBot) :
    Tendsto (fun j => arithmeticFloorHilbertPartial (dampedMobiusWeight (ε j)) (M j))
      atTop (𝓝 (dampedMobiusHalfRangeLimit (1 / 2) le_rfl)) := by
  apply dampedMobius_moving_subhalf_rate_tendsto ε hε M
  simpa only [neg_div] using (conductor_amplification_tendsto_zero_of_margin M hM
    (fun j => (1 / 2 : ℝ) - ε j) (fun j => sub_nonneg.mpr (hε j))
    (1 / 4 : ℝ) hmargin).2

/-- Every coefficient strictly below one quarter gives a full
log-logarithmic band. The theorem concerns the finite cutoff vectors. -/
theorem dampedMobius_loglog_subhalf_band_tendsto
    (ε : ℕ → ℝ) (hε : ∀ j, ε j ≤ (1 / 2 : ℝ))
    (M : ℕ → ℕ) (hM : Tendsto M atTop atTop) (c : ℝ) (hc : c < 1 / 4)
    (hband : ∀ᶠ j in atTop,
      ((1 / 2 : ℝ) - ε j) * Real.log ((M j + 1 : ℕ) : ℝ) ≤
        c * Real.log (6 + Real.log ((M j + 1 : ℕ) : ℝ))) :
    Tendsto (fun j => arithmeticFloorHilbertPartial (dampedMobiusWeight (ε j)) (M j))
      atTop (𝓝 (dampedMobiusHalfRangeLimit (1 / 2) le_rfl)) := by
  apply dampedMobius_moving_subhalf_rate_tendsto ε hε M
  simpa only [neg_div] using (conductor_amplification_tendsto_zero_of_strict_coefficient M hM
    (fun j => (1 / 2 : ℝ) - ε j) (fun j => sub_nonneg.mpr (hε j))
    (1 / 4 : ℝ) c hc hband).2

/-- A full band with any divergent slack below the critical margin
converges uniformly, including slack slower than log-log-log conductor. -/
theorem dampedMobius_sharp_margin_subhalf_band_uniform
    (ω : ℕ → ℝ) (hω : Tendsto ω atTop atTop) :
    ∀ η : ℝ, 0 < η → ∃ J : ℕ, ∀ M : ℕ, J ≤ M → ∀ ε : ℝ,
      ε ≤ (1 / 2 : ℝ) →
      ((1 / 2 : ℝ) - ε) * Real.log ((M + 1 : ℕ) : ℝ) ≤
        (1 / 4 : ℝ) * Real.log (6 + Real.log ((M + 1 : ℕ) : ℝ)) - ω M →
      ‖arithmeticFloorHilbertPartial (dampedMobiusWeight ε) M -
        dampedMobiusHalfRangeLimit (1 / 2) le_rfl‖ ≤ η := by
  intro η hη
  by_contra h
  push Not at h
  choose M hMJ ε hε hband hbad using h
  have hM : Tendsto M atTop atTop := by
    apply tendsto_atTop.mpr
    intro b
    filter_upwards [eventually_ge_atTop b] with j hj
    exact hj.trans (hMJ j)
  have hm : Tendsto (fun j =>
      ((1 / 2 : ℝ) - ε j) * Real.log ((M j + 1 : ℕ) : ℝ) -
        (1 / 4 : ℝ) * Real.log (6 + Real.log ((M j + 1 : ℕ) : ℝ)))
      atTop atBot := by
    have hneg : Tendsto (fun j => -ω (M j)) atTop atBot :=
      tendsto_neg_atTop_atBot.comp (hω.comp hM)
    apply tendsto_atBot.mpr
    intro b
    filter_upwards [tendsto_atBot.mp hneg b] with j hj
    linarith [hband j]
  have hc := dampedMobius_moving_subhalf_margin_tendsto ε hε M hM hm
  obtain ⟨J, hJ⟩ := Metric.tendsto_atTop.mp hc η hη
  have hgood := hJ J le_rfl
  rw [dist_eq_norm] at hgood
  linarith [hbad J]

/-- The complete error bound in exponential-margin form. Taking the
margin bound to be `-ω M` gives the explicit uniform rate `C * exp (-ω M)`. -/
theorem dampedMobius_subhalf_margin_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ M : ℕ, ∀ ε A : ℝ, ε ≤ (1 / 2 : ℝ) →
      ((1 / 2 : ℝ) - ε) * Real.log ((M + 1 : ℕ) : ℝ) -
        (1 / 4 : ℝ) * Real.log (6 + Real.log ((M + 1 : ℕ) : ℝ)) ≤ A →
      ‖arithmeticFloorHilbertPartial (dampedMobiusWeight ε) M -
        dampedMobiusHalfRangeLimit (1 / 2) le_rfl‖ ≤ C * Real.exp A := by
  obtain ⟨C, hC, hb⟩ := dampedMobius_subhalf_quantitative_bound
  refine ⟨C, hC, fun M ε A hε hband => (hb M ε hε).trans ?_⟩
  apply mul_le_mul_of_nonneg_left _ hC
  have hx : 0 < 6 + Real.log ((M + 1 : ℕ) : ℝ) := by
    have hlog : 0 ≤ Real.log ((M + 1 : ℕ) : ℝ) :=
      Real.log_nonneg (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le M))
    linarith
  rw [Real.rpow_def_of_pos (by positivity), mul_comm (Real.log _) ((1 / 2 : ℝ) - ε),
    show (-1 / 4 : ℝ) = -(1 / 4 : ℝ) by ring,
    exp_mul_log_rpow_eq_exp_margin _ _ _ hx]
  exact Real.exp_le_exp.mpr hband

/-- The exact critical quarter-log-log band has a uniform signed energy
budget. A bounded margin proves boundedness; a margin tending to minus
infinity is required by the convergence theorem above. -/
theorem dampedMobius_critical_loglog_band_signed_bounds (A : ℝ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ M : ℕ, ∀ ε : ℝ, ε ≤ (1 / 2 : ℝ) →
      ((1 / 2 : ℝ) - ε) * Real.log ((M + 1 : ℕ) : ℝ) ≤
        (1 / 4 : ℝ) * Real.log (6 + Real.log ((M + 1 : ℕ) : ℝ)) + A →
      (‖arithmeticFloorHilbertPartial (dampedMobiusWeight ε) M‖ ≤ B) ∧
      (dampedMobiusGramOffDiagonal ε M ≤ B ^ 2) ∧
      ∀ H : ℕ, dampedMobiusHeadOffDiagonal ε H M ≤ B ^ 2 := by
  obtain ⟨C, hC, hb⟩ := dampedMobius_subhalf_margin_bound
  let f := dampedMobiusHalfRangeLimit (1 / 2) le_rfl
  let B := ‖f‖ + C * Real.exp A
  have hB : 0 ≤ B := by dsimp [B]; positivity
  refine ⟨B, hB, fun M ε hε hband => ?_⟩
  have herr := hb M ε A hε (by linarith)
  have hn : ‖arithmeticFloorHilbertPartial (dampedMobiusWeight ε) M‖ ≤ B := by
    have htri := norm_add_le
      (arithmeticFloorHilbertPartial (dampedMobiusWeight ε) M - f) f
    rw [sub_add_cancel] at htri
    dsimp [B]
    linarith
  have hsq : ‖arithmeticFloorHilbertPartial (dampedMobiusWeight ε) M‖ ^ 2 ≤ B ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) hB).mpr hn
  refine ⟨hn, (dampedMobius_offDiagonal_le_partial_norm_sq ε M).trans hsq, fun H => ?_⟩
  have hphead := paretoHeadPairing_self_le H
    (arithmeticFloorHilbertPartial (dampedMobiusWeight ε) M)
  rw [dampedMobius_partial_head_eq_signed] at hphead
  linarith [dampedMobiusHeadDiagonal_nonneg ε H M]

/-- Full signed Gram energy converges throughout the sharp sufficient
moving band. The limit is the actual half-endpoint energy. -/
theorem dampedMobius_moving_subhalf_margin_energy_tendsto
    (ε : ℕ → ℝ) (hε : ∀ j, ε j ≤ (1 / 2 : ℝ))
    (M : ℕ → ℕ) (hM : Tendsto M atTop atTop)
    (hmargin : Tendsto (fun j =>
      ((1 / 2 : ℝ) - ε j) * Real.log ((M j + 1 : ℕ) : ℝ) -
        (1 / 4 : ℝ) * Real.log (6 + Real.log ((M j + 1 : ℕ) : ℝ)))
      atTop atBot) :
    Tendsto (fun j =>
      ‖arithmeticFloorHilbertPartial (dampedMobiusWeight (ε j)) (M j)‖ ^ 2) atTop
      (𝓝 (∑' n : ℕ, positiveWeight n *
        (dampedMobiusPrefix (1 / 2) n - (n : ℝ) *
          (1 / riemannZeta (1 + ((1 / 2 : ℝ) : ℂ))).re) ^ 2)) := by
  have h := (dampedMobius_moving_subhalf_margin_tendsto ε hε M hM hmargin).norm.pow 2
  simpa only [hilbert_norm_weighted_sq,
    (dampedMobiusHalfRangeLimit_spec (1 / 2) le_rfl).1] using h

/-- At a fixed subhalf damping the unconditional cutoff growth gains a
quarter logarithm over its power scale. This does not give finite energy
or convergence at that fixed damping. -/
theorem dampedMobius_subhalf_log_improved_growth :
    ∃ C₀ C₁ : ℝ, 0 ≤ C₀ ∧ 0 ≤ C₁ ∧ ∀ M : ℕ, ∀ ε : ℝ, ε ≤ (1 / 2 : ℝ) →
      ‖arithmeticFloorHilbertPartial (dampedMobiusWeight ε) M‖ ≤
        C₀ + C₁ * (((M + 1 : ℕ) : ℝ) ^ ((1 / 2 : ℝ) - ε) *
          (6 + Real.log ((M + 1 : ℕ) : ℝ)) ^ (-1 / 4 : ℝ)) := by
  obtain ⟨C, hC, hb⟩ := dampedMobius_subhalf_quantitative_bound
  let f := dampedMobiusHalfRangeLimit (1 / 2) le_rfl
  refine ⟨‖f‖, C, norm_nonneg _, hC, fun M ε hε => ?_⟩
  have herr := hb M ε hε
  have htri := norm_add_le
    (arithmeticFloorHilbertPartial (dampedMobiusWeight ε) M - f) f
  rw [sub_add_cancel] at htri
  linarith

/-- Explicit error rate in each log-logarithmic band. A coefficient
`c < 1/4` leaves the decay exponent `1/4-c`; no asymptotic notation is used. -/
theorem dampedMobius_loglog_band_error_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ M : ℕ, ∀ ε c : ℝ, ε ≤ (1 / 2 : ℝ) →
      ((1 / 2 : ℝ) - ε) * Real.log ((M + 1 : ℕ) : ℝ) ≤
        c * Real.log (6 + Real.log ((M + 1 : ℕ) : ℝ)) →
      ‖arithmeticFloorHilbertPartial (dampedMobiusWeight ε) M -
        dampedMobiusHalfRangeLimit (1 / 2) le_rfl‖ ≤
          C * (6 + Real.log ((M + 1 : ℕ) : ℝ)) ^ (c - 1 / 4) := by
  obtain ⟨C, hC, hb⟩ := dampedMobius_subhalf_margin_bound
  refine ⟨C, hC, fun M ε c hε hband => ?_⟩
  have hx : 0 < 6 + Real.log ((M + 1 : ℕ) : ℝ) := by
    have hlog : 0 ≤ Real.log ((M + 1 : ℕ) : ℝ) :=
      Real.log_nonneg (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le M))
    linarith
  have h := hb M ε ((c - 1 / 4) *
    Real.log (6 + Real.log ((M + 1 : ℕ) : ℝ))) hε (by nlinarith)
  rw [Real.rpow_def_of_pos hx, mul_comm (Real.log _) (c - 1 / 4)]
  exact h

end RiemannResearch.RH.Pareto
