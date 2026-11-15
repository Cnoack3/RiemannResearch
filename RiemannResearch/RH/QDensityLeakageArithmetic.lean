/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QDensityLeakage
import RiemannResearch.RH.QDensityAugmentedSpan
import RiemannResearch.RH.QDensityMetric
import RiemannResearch.RH.QFullResidueProjection
import RiemannResearch.RH.QOptimizerParityRH
import RiemannResearch.RH.ZetaTwoHilbertSpace
import RiemannResearch.RH.ZetaTwoProbability
import RiemannResearch.RH.ArithmeticCumulativeBasic
import Mathlib.Tactic.Abel
import RiemannResearch.RH.QFiniteEnergyBounds
import RiemannResearch.RH.QCRTFiniteCollocation
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Quantitative leakage and finite-conductor arithmetic certificates

Source: the user's density-leakage investigation following commit 848b7130,
13 November 2026. The estimates and finite-period obstruction are elementary
consequences of the actual residue quotients and orthogonal projections.

The exact signed errors and norm-square remainders are retained. The complete
inverse-square tail gives a k^(-1/2) normalized error, hence a k^(-3/2) error
after subtracting the leading leakage vector w / (zetaTwo * k).
No assertion here supplies w = 0.

A cofinal scalar pairing and a moving finite-stage inverse-Gram energy both
converge to the squared constant residual. Their zero-limit conditions remain
Open arithmetic premises. No density image is an exact finite residue
synthesis; this finite-span obstruction does not exclude closed-span membership.

Published context, supporting the RH interpretation rather than a new
arithmetic provider:
* B. Bagchi, Proc. Indian Acad. Sci. (Math. Sci.) 116 (2006), 137--146,
  Theorem 1 and equivalent-weight observation, https://arxiv.org/abs/math/0607733.
* L. Baez-Duarte, Rend. Lincei Mat. Appl. 14 (2003), 5--11, Theorem 1,
  https://www.bdim.eu/item?id=RLIN_2003_9_14_1_5_0.
* S. Bettin, J. B. Conrey, D. W. Farmer, Proc. Steklov Inst. Math. 280
  suppl. 2 (2013), S30--S36, Theorem 1, https://arxiv.org/abs/1211.5191.
  That rate theorem assumes RH and an additional moment bound and is not used
  as an unconditional provider in any proof below.
-/

noncomputable section
open Filter
open scoped BigOperators Topology
namespace RiemannResearch.RH.QDensityLeakageArithmetic
open ZetaTwoHilbert ZetaTwoProbability QDensityMetric QFullResidueProjection
open QDensityLeakage

/-- The exact approximation error vanishes on the full head below k. -/
theorem approximation_error_head_zero (k n : ℕ) (hk : 0 < k) (hn : n < k) :
    qSequence (approximation k - qOne) n = 0 := by
  rw [approximation_error_sequence k n hk, Nat.mod_eq_of_lt hn]
  by_cases hn0 : n = 0
  · simp [hn0, qOneSequence]
  · simp [qOneSequence, hn0, Nat.cast_ne_zero.mpr hn0]

/-- An unconditional complete-tail rate; no projection residual is set to zero. -/
theorem approximation_error_norm_sq_le (k : ℕ) (hk : 2 ≤ k) :
    ‖approximation k - qOne‖ ^ 2 ≤ 1 / (zetaTwo * (k - 1 : ℕ)) := by
  have h := QFiniteEnergyBounds.norm_sq_le_head_tail
    (approximation k - qOne) (k - 1) (by omega) 1 zero_le_one
    (approximation_error_abs_le_one k · (by omega))
  have hh : (∑ n ∈ Finset.range (k - 1),
      (qSequence (approximation k - qOne) (n + 1)) ^ 2 / (n + 1 : ℝ) ^ 2) = 0 := by
    apply Finset.sum_eq_zero
    intro n hn
    rw [approximation_error_head_zero k (n + 1) (by omega)
      (by have := Finset.mem_range.mp hn; omega)]
    simp
  rw [hh] at h
  simpa only [zero_add, one_pow, one_div_mul_one_div] using h

/-- Pythagoras retains the part of the approximation error lying in V. -/
theorem scaled_leakage_error_pythagoras (k : ℕ) (hk : 2 ≤ k) :
    ‖(zetaTwo * (k : ℝ)) • leakage (qResidue k) -
        (qOne - closure.starProjection qOne)‖ ^ 2 +
      ‖closure.starProjection (approximation k - qOne)‖ ^ 2 =
        ‖approximation k - qOne‖ ^ 2 := by
  let e := approximation k - qOne
  have ho := Submodule.inner_right_of_mem_orthogonal
    (closure.starProjection_apply_mem e)
    (Submodule.sub_starProjection_mem_orthogonal (K := closure) e)
  rw [inner_sub_right, real_inner_self_eq_norm_sq, real_inner_comm] at ho
  rw [scaled_residue_leakage_error_eq k hk, Submodule.starProjection_orthogonal_val,
    norm_sub_sq_real]
  dsimp [e] at ho
  linarith

/-- The normalized leakage approaches its possibly nonzero limit at rate k^(-1/2). -/
theorem scaled_leakage_error_norm_sq_le (k : ℕ) (hk : 2 ≤ k) :
    ‖(zetaTwo * (k : ℝ)) • leakage (qResidue k) -
        (qOne - closure.starProjection qOne)‖ ^ 2 ≤
      1 / (zetaTwo * (k - 1 : ℕ)) := by
  have h := scaled_leakage_error_pythagoras k hk
  have ht := approximation_error_norm_sq_le k hk
  nlinarith [sq_nonneg ‖closure.starProjection (approximation k - qOne)‖]

/-- The full error of any legal competitor splits into leakage and a retained square. -/
theorem legal_approximation_error_identity (k : ℕ) (hk : 2 ≤ k)
    (f : QHilbert) (hf : f ∈ closure) :
    ‖approximation k - f‖ ^ 2 =
      ‖(zetaTwo * (k : ℝ)) • leakage (qResidue k)‖ ^ 2 +
      ‖closure.starProjection (approximation k) - f‖ ^ 2 := by
  have ho := Submodule.inner_right_of_mem_orthogonal
    (closure.sub_mem (closure.starProjection_apply_mem (approximation k)) hf)
    (Submodule.sub_starProjection_mem_orthogonal (K := closure) (approximation k))
  rw [real_inner_comm] at ho
  rw [scaled_residue_leakage_eq k hk]
  have he : approximation k - f =
      (approximation k - closure.starProjection (approximation k)) +
        (closure.starProjection (approximation k) - f) := by abel
  rw [he, norm_add_sq_real, ho]
  ring

/-- Only a scalar pairing is needed to detect the squared constant residual. -/
theorem scaled_leakage_mean_tendsto :
    Tendsto (fun k : ℕ => (zetaTwo * (k : ℝ)) *
      inner ℝ qOne (leakage (qResidue k))) atTop
      (𝓝 (‖qOne - closure.starProjection qOne‖ ^ 2)) := by
  have hcont : Continuous (fun x : QHilbert => inner ℝ qOne x) :=
    continuous_const.inner continuous_id
  have ht := (hcont.tendsto _).comp scaled_residue_leakage_tendsto
  have ho := Submodule.inner_right_of_mem_orthogonal
    (closure.starProjection_apply_mem qOne)
    (Submodule.sub_starProjection_mem_orthogonal (K := closure) qOne)
  have he : inner ℝ qOne (qOne - closure.starProjection qOne) =
      ‖qOne - closure.starProjection qOne‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, inner_sub_left, ho, sub_zero]
  simpa only [Function.comp_def, inner_smul_right, he] using ht

/-- A cofinal scalar cancellation criterion, with its arithmetic premise explicit. -/
theorem one_mem_iff_cofinal_scaled_leakage_mean_zero (c : ℕ → ℕ)
    (hc : Tendsto c atTop atTop) :
    qOne ∈ closure ↔
      Tendsto (fun j => (zetaTwo * (c j : ℝ)) *
        inner ℝ qOne (leakage (qResidue (c j)))) atTop (𝓝 0) := by
  constructor
  · intro h
    have ht := scaled_leakage_mean_tendsto.comp hc
    simpa only [Function.comp_def, Submodule.starProjection_eq_self_iff.mpr h,
      sub_self, norm_zero, zero_pow (by decide : 2 ≠ 0)] using ht
  · intro ht
    have he := tendsto_nhds_unique (scaled_leakage_mean_tendsto.comp hc) ht
    have hz := norm_eq_zero.mp (sq_eq_zero_iff.mp he)
    exact Submodule.starProjection_eq_self_iff.mp (sub_eq_zero.mp hz).symm

/-- Every finite divisor synthesis is genuinely periodic in its physical coordinates. -/
theorem trial_sequence_periodic (L : ℕ) (f : QHilbert)
    (hf : f ∈ QCRTFiniteCollocation.trialSpace L) (n : ℕ) :
    qSequence f (n + L) = qSequence f n := by
  induction hf using Submodule.span_induction with
  | mem g hg =>
    rcases hg with ⟨d, hd, rfl⟩
    simp only [qSequence_qResidue, ArithmeticCumulative.residueFraction]
    rw [Nat.add_mod, Nat.mod_eq_zero_of_dvd (Nat.dvd_of_mem_divisors hd),
      add_zero, Nat.mod_mod]
  | zero => simp [show qSequence (0 : QHilbert) = 0 from qSequenceLinear.map_zero]
  | add x y hx hy ihx ihy =>
    change qSequenceLinear (x + y) (n + L) = qSequenceLinear (x + y) n
    simp only [map_add, Pi.add_apply]
    exact congrArg₂ (· + ·) ihx ihy
  | smul c x hx ih =>
    change qSequenceLinear (c • x) (n + L) = qSequenceLinear (c • x) n
    simp only [map_smul, Pi.smul_apply, smul_eq_mul]
    exact congrArg (c * ·) ih

/-- The residue quotient cannot be cancelled exactly at a finite matching conductor. -/
theorem approximation_not_mem_trial (L k : ℕ) (hL : 0 < L)
    (hk : 2 ≤ k) (hkL : k ∣ L) :
    approximation k ∉ QCRTFiniteCollocation.trialSpace L := by
  intro hm
  have hp := trial_sequence_periodic L (approximation k) hm 1
  rw [approximation_sequence k (1 + L) (by omega),
    approximation_sequence k 1 (by omega)] at hp
  have h1 : 1 % k = 1 := Nat.mod_eq_of_lt (by omega)
  rw [Nat.add_mod, Nat.mod_eq_zero_of_dvd hkL, add_zero, Nat.mod_mod, h1] at hp
  norm_num only [Nat.cast_one, Nat.cast_add, div_one] at hp
  have hp' : (1 : ℝ) + L = 1 := by
    have := (div_eq_iff (by positivity : (1 : ℝ) + L ≠ 0)).mp hp
    linarith
  have hLR : (0 : ℝ) < L := by exact_mod_cast hL
  linarith

/-- A finite legal competitor gives an explicit bound for the unknown constant residual. -/
theorem constant_residual_norm_le_certificate (k : ℕ) (hk : 2 ≤ k)
    (f : QHilbert) (hf : f ∈ closure) :
    ‖qOne - closure.starProjection qOne‖ ≤
      ‖approximation k - f‖ + Real.sqrt (1 / (zetaTwo * (k - 1 : ℕ))) := by
  have hp := closureᗮ.norm_starProjection_apply_le (qOne - f)
  rw [map_sub, Submodule.starProjection_orthogonal_apply_eq_zero hf,
    sub_zero, Submodule.starProjection_orthogonal_val] at hp
  have ht := norm_add_le (qOne - approximation k) (approximation k - f)
  have he : qOne - approximation k + (approximation k - f) = qOne - f := by abel
  rw [he, norm_sub_rev qOne (approximation k)] at ht
  have hb := Real.le_sqrt_of_sq_le (approximation_error_norm_sq_le k hk)
  linarith

/-- Explicit finite inverse-Gram competitors suffice exactly when the constant is legal. -/
theorem one_mem_iff_cofinal_candidate_error_zero (c : ℕ → ℕ)
    (hc : Tendsto c atTop atTop) :
    qOne ∈ closure ↔
      Tendsto (fun j => ‖approximation (c j) - candidate j‖) atTop (𝓝 0) := by
  constructor
  · intro h
    have ht := ((approximation_tendsto.comp hc).sub (candidate_tendsto_qOne h)).norm
    simpa only [Function.comp_def, sub_self, norm_zero] using ht
  · intro h
    have hdiff : Tendsto (fun j => approximation (c j) - candidate j) atTop (𝓝 0) :=
      tendsto_zero_iff_norm_tendsto_zero.mpr h
    have ht : Tendsto candidate atTop (𝓝 qOne) := by
      simpa only [Function.comp_def, sub_sub_cancel, sub_zero] using
        (approximation_tendsto.comp hc).sub hdiff
    have he := tendsto_nhds_unique candidate_tendsto_projection ht
    exact Submodule.starProjection_eq_self_iff.mp he


/-- Finite projections of the moving residue quotients converge to the actual residual. -/
theorem moving_stage_residual_tendsto (c : ℕ → ℕ) (hc : Tendsto c atTop atTop) :
    Tendsto (fun j => approximation (c j) -
      (stage j).starProjection (approximation (c j))) atTop
      (𝓝 (qOne - closure.starProjection qOne)) := by
  have hb : ∀ j,
      ‖(approximation (c j) - (stage j).starProjection (approximation (c j))) -
        (qOne - candidate j)‖ ≤ ‖approximation (c j) - qOne‖ := by
    intro j
    rw [candidate_eq_projection j]
    have he : (approximation (c j) - (stage j).starProjection (approximation (c j))) -
        (qOne - (stage j).starProjection qOne) =
          (stage j)ᗮ.starProjection (approximation (c j) - qOne) := by
      rw [map_sub, Submodule.starProjection_orthogonal_val,
        Submodule.starProjection_orthogonal_val]
    rw [he]
    exact (stage j)ᗮ.norm_starProjection_apply_le _
  have ha : Tendsto (fun j => ‖approximation (c j) - qOne‖) atTop (𝓝 0) := by
    simpa only [Function.comp_def, sub_self, norm_zero] using
      ((approximation_tendsto.comp hc).sub (tendsto_const_nhds (x := qOne))).norm
  have he : Tendsto (fun j =>
      (approximation (c j) - (stage j).starProjection (approximation (c j))) -
        (qOne - candidate j)) atTop (𝓝 0) :=
    tendsto_zero_iff_norm_tendsto_zero.mpr
      (squeeze_zero (fun _ => norm_nonneg _) hb ha)
  have ht := he.add ((tendsto_const_nhds (x := qOne)).sub candidate_tendsto_projection)
  simpa only [sub_add_cancel, zero_add] using ht

/-- The full finite inverse-Gram energy has a limit; its value need not be zero. -/
theorem moving_stage_error_tendsto (c : ℕ → ℕ) (hc : Tendsto c atTop atTop) :
    Tendsto (fun j => ‖approximation (c j) -
      (stage j).starProjection (approximation (c j))‖ ^ 2) atTop
      (𝓝 (‖qOne - closure.starProjection qOne‖ ^ 2)) :=
  (moving_stage_residual_tendsto c hc).norm.pow 2

/-- The missing arithmetic assertion can be expressed entirely by finite Gram energies. -/
theorem one_mem_iff_moving_stage_error_zero (c : ℕ → ℕ)
    (hc : Tendsto c atTop atTop) :
    qOne ∈ closure ↔
      Tendsto (fun j => ‖approximation (c j) -
        (stage j).starProjection (approximation (c j))‖ ^ 2) atTop (𝓝 0) := by
  constructor
  · intro h
    simpa only [Submodule.starProjection_eq_self_iff.mpr h, sub_self, norm_zero,
      zero_pow (by decide : 2 ≠ 0)] using moving_stage_error_tendsto c hc
  · intro h
    have he := tendsto_nhds_unique (moving_stage_error_tendsto c hc) h
    have hz := norm_eq_zero.mp (sq_eq_zero_iff.mp he)
    exact Submodule.starProjection_eq_self_iff.mp (sub_eq_zero.mp hz).symm

/-- Conditional RH consequence. The cofinal scalar cancellation has no provider here. -/
theorem riemannHypothesis_of_cofinal_scaled_leakage_mean_zero (c : ℕ → ℕ)
    (hc : Tendsto c atTop atTop)
    (h : Tendsto (fun j => (zetaTwo * (c j : ℝ)) *
      inner ℝ qOne (leakage (qResidue (c j)))) atTop (𝓝 0)) :
    RiemannHypothesis :=
  riemannHypothesis_of_qOne_mem_full_closure
    ((one_mem_iff_cofinal_scaled_leakage_mean_zero c hc).mpr h)

/-- Divisibility enlarges the finite legal dictionary. -/
theorem trialSpace_mono_dvd (L M : ℕ) (hM : 0 < M) (hLM : L ∣ M) :
    QCRTFiniteCollocation.trialSpace L ≤ QCRTFiniteCollocation.trialSpace M := by
  apply Submodule.span_le.mpr
  rintro f ⟨d, hd, rfl⟩
  exact QCRTFiniteCollocation.residue_mem_trial M d hM
    ((Nat.dvd_of_mem_divisors hd).trans hLM)

/-- Even changing the finite conductor cannot produce exact residue-quotient cancellation. -/
theorem approximation_not_mem_any_trial (L k : ℕ) (hL : 0 < L) (hk : 2 ≤ k) :
    approximation k ∉ QCRTFiniteCollocation.trialSpace L := by
  intro h
  have hM : 0 < k * L := Nat.mul_pos (by omega) hL
  exact approximation_not_mem_trial (k * L) k hM hk (dvd_mul_right k L)
    (trialSpace_mono_dvd L (k * L) hM (dvd_mul_left L k) h)

/-- No density image B g_k is an exact finite residue synthesis.
This is not a statement about the closed legal span. -/
theorem density_atom_not_mem_any_trial (L k : ℕ) (hL : 0 < L) (hk : 2 ≤ k) :
    B (qResidue k) ∉ QCRTFiniteCollocation.trialSpace L := by
  intro h
  have hM : 0 < k * L := Nat.mul_pos (by omega) hL
  have hB := trialSpace_mono_dvd L (k * L) hM (dvd_mul_left L k) h
  have hg := QCRTFiniteCollocation.residue_mem_trial (k * L) k hM (dvd_mul_right k L)
  apply approximation_not_mem_trial (k * L) k hM hk (dvd_mul_right k L)
  rw [approximation_eq_density_combination]
  exact (QCRTFiniteCollocation.trialSpace (k * L)).sub_mem
    ((QCRTFiniteCollocation.trialSpace (k * L)).smul_mem _ hB)
    ((QCRTFiniteCollocation.trialSpace (k * L)).smul_mem _ hg)

/-- info: 'RiemannResearch.RH.QDensityLeakageArithmetic.approximation_error_norm_sq_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms approximation_error_norm_sq_le

/-- info: 'RiemannResearch.RH.QDensityLeakageArithmetic.scaled_leakage_error_norm_sq_le' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms scaled_leakage_error_norm_sq_le

/-- info: 'RiemannResearch.RH.QDensityLeakageArithmetic.legal_approximation_error_identity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms legal_approximation_error_identity

/-- info: 'RiemannResearch.RH.QDensityLeakageArithmetic.one_mem_iff_cofinal_scaled_leakage_mean_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms one_mem_iff_cofinal_scaled_leakage_mean_zero

/-- info: 'RiemannResearch.RH.QDensityLeakageArithmetic.approximation_not_mem_trial' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms approximation_not_mem_trial

/-- info: 'RiemannResearch.RH.QDensityLeakageArithmetic.constant_residual_norm_le_certificate' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms constant_residual_norm_le_certificate

/-- info: 'RiemannResearch.RH.QDensityLeakageArithmetic.one_mem_iff_cofinal_candidate_error_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms one_mem_iff_cofinal_candidate_error_zero

/-- info: 'RiemannResearch.RH.QDensityLeakageArithmetic.riemannHypothesis_of_cofinal_scaled_leakage_mean_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms riemannHypothesis_of_cofinal_scaled_leakage_mean_zero

/-- info: 'RiemannResearch.RH.QDensityLeakageArithmetic.density_atom_not_mem_any_trial' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms density_atom_not_mem_any_trial
/-- info: 'RiemannResearch.RH.QDensityLeakageArithmetic.one_mem_iff_moving_stage_error_zero' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms one_mem_iff_moving_stage_error_zero
open QCRTFiniteCollocation

/-- Every finite legal vector lies in a single positive divisor dictionary. -/
theorem exists_trialSpace_of_mem_legalSpan (f : QHilbert) (hf : f ∈ legalSpan) :
    ∃ L : ℕ, 0 < L ∧ f ∈ trialSpace L := by
  induction hf using Submodule.span_induction with
  | mem g hg =>
    rcases hg with ⟨i, rfl⟩
    exact ⟨i + 2, by omega, residue_mem_trial (i + 2) (i + 2)
      (by omega) (dvd_refl _)⟩
  | zero => exact ⟨1, by omega, (trialSpace 1).zero_mem⟩
  | add x y hx hy ihx ihy =>
    obtain ⟨L, hL, hxL⟩ := ihx
    obtain ⟨M, hM, hyM⟩ := ihy
    have hLM : 0 < L * M := Nat.mul_pos hL hM
    exact ⟨L * M, hLM, (trialSpace (L * M)).add_mem
      (trialSpace_mono_dvd L (L * M) hLM (dvd_mul_right L M) hxL)
      (trialSpace_mono_dvd M (L * M) hLM (dvd_mul_left M L) hyM)⟩
  | smul c x hx ih =>
    obtain ⟨L, hL, hxL⟩ := ih
    exact ⟨L, hL, (trialSpace L).smul_mem c hxL⟩

/-- A density atom is never an exact finite synthesis, even if its closed-span
membership is subsequently established. -/
theorem density_atom_not_mem_legalSpan (k : ℕ) (hk : 2 ≤ k) :
    B (qResidue k) ∉ legalSpan := by
  intro h
  obtain ⟨L, hL, hm⟩ := exists_trialSpace_of_mem_legalSpan _ h
  exact density_atom_not_mem_any_trial L k hL hk hm

theorem density_atom_error_pos (k : ℕ) (hk : 2 ≤ k)
    (a : QHilbert) (ha : a ∈ legalSpan) :
    0 < ‖B (qResidue k) - a‖ := by
  apply norm_pos_iff.mpr
  intro he
  exact density_atom_not_mem_legalSpan k hk ((sub_eq_zero.mp he).symm ▸ ha)

/-- info: 'RiemannResearch.RH.QDensityLeakageArithmetic.exists_trialSpace_of_mem_legalSpan' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms exists_trialSpace_of_mem_legalSpan

/-- info: 'RiemannResearch.RH.QDensityLeakageArithmetic.density_atom_not_mem_legalSpan' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms density_atom_not_mem_legalSpan

/-- info: 'RiemannResearch.RH.QDensityLeakageArithmetic.density_atom_error_pos' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms density_atom_error_pos
end RiemannResearch.RH.QDensityLeakageArithmetic
