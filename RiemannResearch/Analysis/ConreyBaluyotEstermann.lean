/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Analysis.Meromorphic.Basic
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.NumberTheory.LSeries.ZMod
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.InfiniteSum.Group
import RiemannResearch.RH.ChebyshevEnergyCriterion

/-!
# Estermann series for the Conrey–Baluyot mollified moment

S. A. C. Baluyot, *On the Zeros of Riemann's Zeta-function* (2017),
equations (3.1.5) and (3.1.7) and the proof of Lemma 3.1.3, pp. 95–97,
give the series, the finite Hurwitz identity and the reflected formula.
https://urresearch.rochester.edu/fileDownloadForInstitutionalItem.action?itemFileId=183460&itemId=33320

Write the two exponents as u and v. Baluyot's spectral line uses
u = s + α and v = s + β. Positive-index terms use the standard additive
character of ZMod K. In the finite Hurwitz formula the zero residue class
represents the fraction 1 in the source. The inverse residue in the
functional equation is the inverse of the supplied unit of ZMod K.
-/

open Complex Set Filter
open scoped BigOperators Topology
noncomputable section
namespace RiemannResearch.Analysis.ConreyBaluyot

/-- Terms of the actual double Dirichlet series, with zero terms at either zero index. -/
def estermannTerm {K : ℕ} [NeZero K] (h : ZMod K) (u v : ℂ) (p : ℕ × ℕ) : ℂ :=
  ZMod.stdAddChar (h * (p.1 : ZMod K) * (p.2 : ZMod K)) *
    (LSeries.term (fun _ => 1) u p.1 * LSeries.term (fun _ => 1) v p.2)

/-- The Estermann Dirichlet series with the two exponents written separately. -/
def estermannSeries {K : ℕ} [NeZero K] (h : ZMod K) (u v : ℂ) : ℂ :=
  ∑' p : ℕ × ℕ, estermannTerm h u v p

private def residueIndicator {K : ℕ} [NeZero K] (a x : ZMod K) : ℂ :=
  if x = a then 1 else 0

/-- The progression L-function for the residue class a modulo K. -/
def residueLFunction {K : ℕ} [NeZero K] (a : ZMod K) (u : ℂ) : ℂ :=
  ZMod.LFunction (residueIndicator a) u

/-- The finite Hurwitz continuation of the two-exponent Estermann series. -/
def estermann {K : ℕ} [NeZero K] (h : ZMod K) (u v : ℂ) : ℂ :=
  ∑ a : ZMod K, ∑ b : ZMod K,
    ZMod.stdAddChar (h * a * b) * (residueLFunction a u * residueLFunction b v)

private theorem summable_norm_residueTerm {K : ℕ} [NeZero K] (a : ZMod K) {u : ℂ}
    (hu : 1 < u.re) :
    Summable (fun m : ℕ => ‖LSeries.term (fun n => residueIndicator a (n : ZMod K)) u m‖) := by
  have hs : Summable (LSeries.term (fun n : ℕ => residueIndicator a (n : ZMod K)) u) :=
    ZMod.LSeriesSummable_of_one_lt_re (residueIndicator a) hu
  exact hs.norm

private theorem estermannTerm_eq_sum_residues {K : ℕ} [NeZero K] (h : ZMod K) (u v : ℂ)
    (p : ℕ × ℕ) :
    estermannTerm h u v p = ∑ a : ZMod K, ∑ b : ZMod K,
      ZMod.stdAddChar (h * a * b) *
        (LSeries.term (fun n => residueIndicator a (n : ZMod K)) u p.1 *
          LSeries.term (fun n => residueIndicator b (n : ZMod K)) v p.2) := by
  classical
  by_cases hm : p.1 = 0
  · simp [estermannTerm, LSeries.term_def, hm]
  by_cases hn : p.2 = 0
  · simp [estermannTerm, LSeries.term_def, hn]
  simp [estermannTerm, hm, hn, residueIndicator, ite_div, ite_mul, mul_ite]

/-- Absolute summability on the joint half-plane. -/
theorem summable_norm_estermannTerm {K : ℕ} [NeZero K] (h : ZMod K) {u v : ℂ}
    (hu : 1 < u.re) (hv : 1 < v.re) : Summable (fun p => ‖estermannTerm h u v p‖) := by
  have hu' : Summable (fun m : ℕ => ‖LSeries.term (fun _ => 1) u m‖) :=
    (show Summable (LSeries.term (fun _ => 1) u) from
      ZMod.LSeriesSummable_of_one_lt_re (fun _ : ZMod K => 1) hu).norm
  have hv' : Summable (fun n : ℕ => ‖LSeries.term (fun _ => 1) v n‖) :=
    (show Summable (LSeries.term (fun _ => 1) v) from
      ZMod.LSeriesSummable_of_one_lt_re (fun _ : ZMod K => 1) hv).norm
  convert hu'.mul_norm hv' using 1
  funext p
  simp [estermannTerm, ZMod.stdAddChar_apply, Circle.norm_coe]

/-- Exact residue-class decomposition of the absolutely convergent double series. -/
theorem estermannSeries_eq_estermann {K : ℕ} [NeZero K] (h : ZMod K) {u v : ℂ}
    (hu : 1 < u.re) (hv : 1 < v.re) :
    estermannSeries h u v = estermann h u v := by
  classical
  let term (a : ZMod K) (z : ℂ) :=
    LSeries.term (fun n => residueIndicator a (n : ZMod K)) z
  have hs (a b : ZMod K) :
      Summable (fun p : ℕ × ℕ => ZMod.stdAddChar (h * a * b) *
        (term a u p.1 * term b v p.2)) :=
    (summable_mul_of_summable_norm
      (summable_norm_residueTerm a hu) (summable_norm_residueTerm b hv)).mul_left _
  unfold estermannSeries estermann
  simp_rw [estermannTerm_eq_sum_residues h u v]
  change (∑' p : ℕ × ℕ, ∑ a : ZMod K, ∑ b : ZMod K,
    ZMod.stdAddChar (h * a * b) * (term a u p.1 * term b v p.2)) = _
  have hh (a : ZMod K) (t : Finset (ZMod K)) :
      Summable (fun p : ℕ × ℕ => ∑ b ∈ t, ZMod.stdAddChar (h * a * b) *
        (term a u p.1 * term b v p.2)) := by
    induction t using Finset.induction_on with
    | empty => simp
    | @insert b t hb ih =>
      simpa only [Finset.sum_insert hb] using (hs a b).add ih
  rw [Summable.tsum_finsetSum (fun a _ => hh a Finset.univ)]
  apply Finset.sum_congr rfl
  intro a _
  rw [Summable.tsum_finsetSum (fun b _ => hs a b)]
  apply Finset.sum_congr rfl
  intro b _
  rw [tsum_mul_left, ← tsum_mul_tsum_of_summable_norm
    (summable_norm_residueTerm a hu) (summable_norm_residueTerm b hv)]
  simp only [residueLFunction, ZMod.LFunction_eq_LSeries _ hu,
    ZMod.LFunction_eq_LSeries _ hv]
  rfl

/-- The term at positive indices uses the ordinary exponential phase of Baluyot's series. -/
theorem estermannTerm_intCast {K : ℕ} [NeZero K] (H : ℤ) (u v : ℂ) {m n : ℕ}
    (hm : m ≠ 0) (hn : n ≠ 0) :
    estermannTerm (H : ZMod K) u v (m, n) =
      exp (2 * (Real.pi : ℂ) * I * ((H : ℂ) * (m : ℂ) * (n : ℂ)) / (K : ℂ)) /
        ((m : ℂ) ^ u * (n : ℂ) ^ v) := by
  have hcast : (H : ZMod K) * (m : ZMod K) * (n : ZMod K) =
      (((H * (m : ℤ) * (n : ℤ)) : ℤ) : ZMod K) := by push_cast; rfl
  unfold estermannTerm
  dsimp only
  rw [hcast, ZMod.stdAddChar_coe]
  simp [hm, hn, div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm]

/-- Either order of summation is justified by absolute convergence. -/
theorem estermannSeries_eq_iterated_tsum {K : ℕ} [NeZero K] (h : ZMod K) {u v : ℂ}
    (hu : 1 < u.re) (hv : 1 < v.re) :
    estermannSeries h u v = ∑' m : ℕ, ∑' n : ℕ, estermannTerm h u v (m, n) :=
  (summable_norm_estermannTerm h hu hv).of_norm.tsum_prod

private theorem residueLFunction_eq_hurwitzZeta {K : ℕ} [NeZero K]
    (a : ZMod K) (u : ℂ) :
    residueLFunction a u = (K : ℂ) ^ (-u) *
      HurwitzZeta.hurwitzZeta (ZMod.toAddCircle a) u := by
  classical
  simp [residueLFunction, residueIndicator, ZMod.LFunction, ite_mul]

/-- The finite Hurwitz-zeta formula. The zero class represents the fraction 1. -/
theorem estermann_eq_sum_hurwitzZeta {K : ℕ} [NeZero K] (h : ZMod K) (u v : ℂ) :
    estermann h u v =
      (K : ℂ) ^ (-u - v) *
        ∑ a : ZMod K, ∑ b : ZMod K, ZMod.stdAddChar (h * a * b) *
          (HurwitzZeta.hurwitzZeta (ZMod.toAddCircle a) u *
            HurwitzZeta.hurwitzZeta (ZMod.toAddCircle b) v) := by
  classical
  have hK : (K : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne K)
  have he : -u - v = -u + -v := sub_eq_add_neg _ _
  rw [he, Complex.cpow_add _ _ hK]
  simp only [estermann, residueLFunction_eq_hurwitzZeta, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring

/-- The character-twisted L-function associated to one residue parameter. -/
def estermannTwist {K : ℕ} [NeZero K] (a : ZMod K) (u : ℂ) : ℂ :=
  ZMod.LFunction (fun b => ZMod.stdAddChar (a * b)) u

private theorem LFunction_eq_sum_residueLFunction {K : ℕ} [NeZero K]
    (Φ : ZMod K → ℂ) (u : ℂ) :
    ZMod.LFunction Φ u = ∑ a : ZMod K, Φ a * residueLFunction a u := by
  simp only [ZMod.LFunction, residueLFunction_eq_hurwitzZeta, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  ring

/-- Regroup the continuation into one sum of progression and additive-twist L-functions. -/
theorem estermann_eq_sum_twist_mul_residue {K : ℕ} [NeZero K]
    (h : ZMod K) (u v : ℂ) :
    estermann h u v = ∑ b : ZMod K, estermannTwist (h * b) u * residueLFunction b v := by
  classical
  rw [estermann, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  rw [estermannTwist, LFunction_eq_sum_residueLFunction, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro a _
  rw [show h * a * b = h * b * a by ring]
  ring

/-- Interchanging the two exponents preserves the Estermann function. -/
theorem estermann_swap {K : ℕ} [NeZero K] (h : ZMod K) (u v : ℂ) :
    estermann h u v = estermann h v u := by
  classical
  unfold estermann
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro a _
  rw [show h * a * b = h * b * a by ring]
  ring

/-- The progression of multiples of K contributes the scaled Riemann zeta function. -/
theorem residueLFunction_zero {K : ℕ} [NeZero K] (u : ℂ) :
    residueLFunction (0 : ZMod K) u = (K : ℂ) ^ (-u) * riemannZeta u := by
  simp [residueLFunction_eq_hurwitzZeta, HurwitzZeta.hurwitzZeta_zero]

private theorem meromorphicAt_residueLFunction {K : ℕ} [NeZero K] (a : ZMod K) (z : ℂ) :
    MeromorphicAt (residueLFunction a) z := by
  have hdiff := (HurwitzZeta.differentiable_hurwitzZeta_sub_hurwitzZeta
    (ZMod.toAddCircle a) 0).analyticAt z
  have hzeta := RiemannResearch.RH.ChebyshevMellin.riemannZeta_meromorphicAt_everywhere z
  have hh : MeromorphicAt (HurwitzZeta.hurwitzZeta (ZMod.toAddCircle a)) z := by
    convert hdiff.meromorphicAt.add hzeta using 1
    funext x
    simp [HurwitzZeta.hurwitzZeta_zero]
  have hK : (K : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne K)
  have hp : AnalyticAt ℂ (fun w : ℂ => (K : ℂ) ^ (-w)) z := by
    simp only [Complex.cpow_def_of_ne_zero hK]
    fun_prop
  rw [show residueLFunction a = fun w : ℂ => (K : ℂ) ^ (-w) *
      HurwitzZeta.hurwitzZeta (ZMod.toAddCircle a) w from
    funext (residueLFunction_eq_hurwitzZeta a)]
  exact hp.meromorphicAt.mul hh

private theorem meromorphicAt_fintype_sum {ι : Type*} [Fintype ι] {f : ι → ℂ → ℂ} {z : ℂ}
    (hf : ∀ a, MeromorphicAt (f a) z) :
    MeromorphicAt (fun s : ℂ => ∑ a, f a s) z := by
  have he : (∑ a, f a) = (fun s : ℂ => ∑ a, f a s) := by
    funext s
    simp only [Finset.sum_apply]
  rw [← he]
  exact MeromorphicAt.sum (fun a _ => hf a)

/-- Meromorphic continuation in the shared spectral variable of Baluyot's series. -/
theorem meromorphic_estermann_shifted {K : ℕ} [NeZero K] (h : ZMod K) (α β : ℂ) :
    Meromorphic (fun s : ℂ => estermann h (s + α) (s + β)) := by
  intro z
  unfold estermann
  apply meromorphicAt_fintype_sum
  intro a
  apply meromorphicAt_fintype_sum
  intro b
  have hc : AnalyticAt ℂ (fun _ : ℂ => ZMod.stdAddChar (h * a * b)) z := analyticAt_const
  have hα : AnalyticAt ℂ (fun s : ℂ => s + α) z := analyticAt_id.add analyticAt_const
  have hβ : AnalyticAt ℂ (fun s : ℂ => s + β) z := analyticAt_id.add analyticAt_const
  have hl : MeromorphicAt (residueLFunction a ∘ (fun s : ℂ => s + α)) z := by
    apply MeromorphicAt.comp_analyticAt _ hα
    exact meromorphicAt_residueLFunction a (z + α)
  have hr : MeromorphicAt (residueLFunction b ∘ (fun s : ℂ => s + β)) z := by
    apply MeromorphicAt.comp_analyticAt _ hβ
    exact meromorphicAt_residueLFunction b (z + β)
  exact hc.meromorphicAt.mul (hl.mul hr)

/-- The only possible singularities are at the two shifted arguments equal to one. -/
theorem analyticAt_estermann_shifted {K : ℕ} [NeZero K] (h : ZMod K) (α β : ℂ)
    {z : ℂ} (hα : z + α ≠ 1) (hβ : z + β ≠ 1) :
    AnalyticAt ℂ (fun s : ℂ => estermann h (s + α) (s + β)) z := by
  let U : Set ℂ := {s : ℂ | s + α ≠ 1} ∩ {s : ℂ | s + β ≠ 1}
  have hU : IsOpen U :=
    (isOpen_compl_singleton.preimage (continuous_id.add continuous_const :
      Continuous (fun s : ℂ => s + α))).inter
      (isOpen_compl_singleton.preimage (continuous_id.add continuous_const :
        Continuous (fun s : ℂ => s + β)))
  have hd : DifferentiableOn ℂ (fun s : ℂ => estermann h (s + α) (s + β)) U := by
    intro s hs
    apply DifferentiableAt.differentiableWithinAt
    unfold estermann residueLFunction
    apply DifferentiableAt.fun_sum
    intro a _
    apply DifferentiableAt.fun_sum
    intro b _
    have hc : DifferentiableAt ℂ (fun _ : ℂ => ZMod.stdAddChar (h * a * b)) s := by
      fun_prop
    exact hc.mul
      (((ZMod.differentiableAt_LFunction (residueIndicator a) (s + α) (Or.inl hs.1)).comp s
        (differentiableAt_id.add_const α)).mul
        ((ZMod.differentiableAt_LFunction (residueIndicator b) (s + β) (Or.inl hs.2)).comp s
        (differentiableAt_id.add_const β)))
  exact hd.analyticAt (hU.mem_nhds ⟨hα, hβ⟩)

private theorem sum_stdAddChar_mul {K : ℕ} [NeZero K] (a : ZMod K) :
    (∑ b : ZMod K, ZMod.stdAddChar (a * b)) = if a = 0 then (K : ℂ) else 0 := by
  classical
  by_cases ha : a = 0
  · simp [ha, ZMod.card]
  · simpa [ha, AddChar.mulShift, mul_comm] using
      (AddChar.sum_eq_zero_of_ne_one ((ZMod.isPrimitive_stdAddChar K) ha))

private theorem estermannTwist_residue_one {K : ℕ} [NeZero K] (a : ZMod K) :
    Tendsto (fun z : ℂ => (z - 1) * estermannTwist a z) (𝓝[≠] 1)
      (𝓝 (if a = 0 then 1 else 0)) := by
  have hK : (K : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne K)
  have hh := ZMod.LFunction_residue_one (fun b : ZMod K => ZMod.stdAddChar (a * b))
  simp only [div_eq_mul_inv, ← Finset.sum_mul, sum_stdAddChar_mul] at hh
  by_cases ha : a = 0 <;> simpa [ha, estermannTwist, hK] using hh

private theorem residueLFunction_residue_one {K : ℕ} [NeZero K] (a : ZMod K) :
    Tendsto (fun z : ℂ => (z - 1) * residueLFunction a z) (𝓝[≠] 1) (𝓝 (K : ℂ)⁻¹) := by
  classical
  simpa [residueLFunction, residueIndicator, ite_div, one_div] using
    ZMod.LFunction_residue_one (residueIndicator a)

private theorem unit_mul_eq_zero_iff {K : ℕ} [NeZero K] (h : (ZMod K)ˣ) (b : ZMod K) :
    (h : ZMod K) * b = 0 ↔ b = 0 := by
  constructor
  · intro hb
    calc
      b = (↑h⁻¹ : ZMod K) * ((h : ZMod K) * b) := by rw [← mul_assoc, Units.inv_mul, one_mul]
      _ = 0 := by rw [hb, mul_zero]
  · rintro rfl
    exact mul_zero _

/-- The left residue, also when the second exponent varies and tends to a point other than 1. -/
theorem estermann_residue_left {K : ℕ} [NeZero K] (h : (ZMod K)ˣ)
    {f : ℂ → ℂ} {v : ℂ} (hf : Tendsto f (𝓝[≠] 1) (𝓝 v)) (hv : v ≠ 1) :
    Tendsto (fun z : ℂ => (z - 1) * estermann (h : ZMod K) z (f z)) (𝓝[≠] 1)
      (𝓝 ((K : ℂ) ^ (-v) * riemannZeta v)) := by
  classical
  have hterm (b : ZMod K) :
      Tendsto (fun z : ℂ => ((z - 1) * estermannTwist ((h : ZMod K) * b) z) *
        residueLFunction b (f z)) (𝓝[≠] 1)
        (𝓝 (((if b = 0 then 1 else 0) : ℂ) * residueLFunction b v)) := by
    have hc := (ZMod.differentiableAt_LFunction (residueIndicator b) v (Or.inl hv)).continuousAt
    have ht := estermannTwist_residue_one ((h : ZMod K) * b)
    simp only [unit_mul_eq_zero_iff] at ht
    exact ht.mul (hc.tendsto.comp hf)
  have hsum := tendsto_finsetSum Finset.univ (fun b _ => hterm b)
  simpa [estermann_eq_sum_twist_mul_residue, Finset.mul_sum, mul_assoc, ite_mul,
    residueLFunction_zero] using hsum

/-- The leading double-pole coefficient on the diagonal is exactly 1/K. -/
theorem estermann_diagonal_doublePole_limit {K : ℕ} [NeZero K] (h : (ZMod K)ˣ) :
    Tendsto (fun z : ℂ => (z - 1) ^ 2 * estermann (h : ZMod K) z z) (𝓝[≠] 1)
      (𝓝 (K : ℂ)⁻¹) := by
  classical
  have hterm (b : ZMod K) :
      Tendsto (fun z : ℂ => ((z - 1) * estermannTwist ((h : ZMod K) * b) z) *
        ((z - 1) * residueLFunction b z)) (𝓝[≠] 1)
        (𝓝 (((if b = 0 then 1 else 0) : ℂ) * (K : ℂ)⁻¹)) := by
    have ht := estermannTwist_residue_one ((h : ZMod K) * b)
    simp only [unit_mul_eq_zero_iff] at ht
    exact ht.mul (residueLFunction_residue_one b)
  have hsum := tendsto_finsetSum Finset.univ (fun b _ => hterm b)
  have hfun : (fun z : ℂ => (z - 1) ^ 2 * estermann (h : ZMod K) z z) =
      fun z : ℂ => ∑ b : ZMod K, ((z - 1) * estermannTwist ((h : ZMod K) * b) z) *
        ((z - 1) * residueLFunction b z) := by
    funext z
    rw [estermann_eq_sum_twist_mul_residue, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b _
    ring
  rw [hfun]
  simpa [ite_mul] using hsum

private theorem estermannTwist_eq_expZeta {K : ℕ} [NeZero K]
    (a : ZMod K) {u : ℂ} (hu : u ≠ 1) :
    estermannTwist a u = HurwitzZeta.expZeta (ZMod.toAddCircle a) u :=
  ZMod.LFunction_stdAddChar_eq_expZeta a u (Or.inr hu)

private theorem sum_twist_mul_residue_reindex {K : ℕ} [NeZero K]
    (c k i : ZMod K) (hik : i * k = 1) (u v : ℂ) :
    (∑ a : ZMod K, estermannTwist (c * a) u * residueLFunction (k * a) v) =
      estermann (c * i) u v := by
  classical
  let e : ZMod K ≃ ZMod K :=
    { toFun := fun a => k * a
      invFun := fun b => i * b
      left_inv := fun a => by
        change i * (k * a) = a
        rw [← mul_assoc, hik, one_mul]
      right_inv := fun b => by
        change k * (i * b) = b
        have hki : k * i = 1 := by rwa [mul_comm]
        rw [← mul_assoc, hki, one_mul] }
  rw [estermann_eq_sum_twist_mul_residue]
  calc
    _ = ∑ a : ZMod K, estermannTwist ((c * i) * e a) u * residueLFunction (e a) v := by
      apply Finset.sum_congr rfl
      intro a _
      change _ = estermannTwist ((c * i) * (k * a)) u * residueLFunction (k * a) v
      have he : (c * i) * (k * a) = c * a := by
        rw [mul_assoc c i, ← mul_assoc i k, hik, one_mul]
      rw [he]
    _ = _ := e.sum_comp (fun a => estermannTwist ((c * i) * a) u * residueLFunction a v)

private theorem exp_pair_eq_two_mul_cos (x y : ℂ) :
    exp (x * I) * exp (y * I) + exp (-x * I) * exp (-y * I) =
      2 * cos (x + y) := by
  rw [← Complex.exp_add, ← Complex.exp_add,
    show x * I + y * I = (x + y) * I by ring,
    show -x * I + -y * I = -(x + y) * I by ring]
  unfold Complex.cos
  ring

/-- Estermann's functional equation with exact phases and the inverse residue class.
The exclusions are the exceptional values of the pointwise Hurwitz functional equations. -/
theorem estermann_one_sub {K : ℕ} [NeZero K] (h : (ZMod K)ˣ)
    {u v : ℂ} (hu : ∀ n : ℕ, u ≠ 1 - (n : ℂ)) (hv : ∀ n : ℕ, v ≠ 1 - (n : ℂ)) :
    estermann (h : ZMod K) (1 - u) (1 - v) =
      2 * (K : ℂ) ^ (u + v - 1) * (2 * (Real.pi : ℂ)) ^ (-u - v) *
        Gamma u * Gamma v *
          (cos ((Real.pi : ℂ) * (u - v) / 2) * estermann (↑h⁻¹ : ZMod K) u v +
            cos ((Real.pi : ℂ) * (u + v) / 2) * estermann (-(↑h⁻¹ : ZMod K)) u v) := by
  classical
  let archimedean (z : ℂ) := (2 * (Real.pi : ℂ)) ^ (-z) * Gamma z
  let angle (z : ℂ) := (Real.pi : ℂ) * z / 2
  let negativePhase (z : ℂ) := exp (-(angle z) * I)
  let positivePhase (z : ℂ) := exp (angle z * I)
  let leftFactor (z : ℂ) := (K : ℂ) ^ (z - 1) * archimedean z
  let rightFactor (z : ℂ) := (K : ℂ) ^ z * archimedean z
  let k : ZMod K := h
  let i : ZMod K := ↑h⁻¹
  have hik : i * k = 1 := Units.inv_mul h
  have hu1 : u ≠ 1 := by simpa using hu 0
  have hv0 : 1 - v ≠ 1 := by
    intro he
    apply hv 1
    calc
      v = 1 - (1 - v) := by ring
      _ = 1 - ((1 : ℕ) : ℂ) := by simp [he]
  have huNeg : ∀ n : ℕ, u ≠ -(n : ℂ) := by
    intro n hn
    apply hu (n + 1)
    rw [hn, Nat.cast_succ]
    ring
  have hK : (K : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne K)
  have hπ : (2 * (Real.pi : ℂ)) ≠ 0 := by
    exact mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero)
  have hphaseNeg (z : ℂ) : -(angle z) * I = -(Real.pi : ℂ) * I * z / 2 := by
    dsimp [angle]
    ring
  have hphasePos (z : ℂ) : angle z * I = (Real.pi : ℂ) * I * z / 2 := by
    dsimp [angle]
    ring
  have hR (a : ZMod K) :
      residueLFunction a (1 - u) = leftFactor u *
        (negativePhase u * estermannTwist a u + positivePhase u * estermannTwist (-a) u) := by
    rw [residueLFunction_eq_hurwitzZeta,
      HurwitzZeta.hurwitzZeta_one_sub _ huNeg (Or.inr hu1),
      show -(1-u) = u-1 by ring,
      estermannTwist_eq_expZeta _ hu1, estermannTwist_eq_expZeta _ hu1]
    simp only [map_neg, leftFactor, archimedean, negativePhase, positivePhase,
      hphaseNeg, hphasePos]
    ring
  have hT (a : ZMod K) :
      estermannTwist a (1 - v) = rightFactor v *
        (positivePhase v * residueLFunction a v + negativePhase v * residueLFunction (-a) v) := by
    rw [estermannTwist_eq_expZeta _ hv0, HurwitzZeta.expZeta_one_sub _ hv]
    simp only [residueLFunction_eq_hurwitzZeta, map_neg, rightFactor, archimedean,
      negativePhase, positivePhase, hphaseNeg, hphasePos]
    have hp : (K : ℂ) ^ v * (K : ℂ) ^ (-v) = 1 := by
      rw [← Complex.cpow_add v (-v) hK, add_neg_cancel, Complex.cpow_zero]
    calc
      _ = ((K : ℂ) ^ v * (K : ℂ) ^ (-v)) *
          ((2 * (Real.pi : ℂ)) ^ (-v) * Gamma v *
            (exp ((Real.pi : ℂ) * I * v / 2) *
              HurwitzZeta.hurwitzZeta (ZMod.toAddCircle a) v +
              exp (-(Real.pi : ℂ) * I * v / 2) *
                HurwitzZeta.hurwitzZeta (-ZMod.toAddCircle a) v)) := by rw [hp, one_mul]
      _ = _ := by ring
  have hpp :
      (∑ a : ZMod K, estermannTwist a u * residueLFunction (k * a) v) = estermann i u v := by
    simpa using sum_twist_mul_residue_reindex 1 k i hik u v
  have hpn :
      (∑ a : ZMod K, estermannTwist a u * residueLFunction (-(k * a)) v) =
        estermann (-i) u v := by
    simpa using sum_twist_mul_residue_reindex 1 (-k) (-i) (by simpa using hik) u v
  have hnp :
      (∑ a : ZMod K, estermannTwist (-a) u * residueLFunction (k * a) v) =
        estermann (-i) u v := by
    simpa using sum_twist_mul_residue_reindex (-1) k i hik u v
  have hnn :
      (∑ a : ZMod K, estermannTwist (-a) u * residueLFunction (-(k * a)) v) =
        estermann i u v := by
    simpa using sum_twist_mul_residue_reindex (-1) (-k) (-i) (by simpa using hik) u v
  have hsumPhase :
      negativePhase u * negativePhase v + positivePhase u * positivePhase v =
        2 * cos ((Real.pi : ℂ) * (u + v) / 2) := by
    have he : angle u + angle v = (Real.pi : ℂ) * (u + v) / 2 := by
      dsimp [angle]
      ring
    simpa only [he, add_comm] using exp_pair_eq_two_mul_cos (angle u) (angle v)
  have hdiffPhase :
      negativePhase u * positivePhase v + positivePhase u * negativePhase v =
        2 * cos ((Real.pi : ℂ) * (u - v) / 2) := by
    have he : angle u + -angle v = (Real.pi : ℂ) * (u - v) / 2 := by
      dsimp [angle]
      ring
    simpa only [he, neg_neg, add_comm] using exp_pair_eq_two_mul_cos (angle u) (-angle v)
  change estermann k (1-u) (1-v) = _
  calc
    _ = ∑ a : ZMod K,
        (leftFactor u * (negativePhase u * estermannTwist a u +
          positivePhase u * estermannTwist (-a) u)) *
          (rightFactor v * (positivePhase v * residueLFunction (k * a) v +
            negativePhase v * residueLFunction (-(k * a)) v)) := by
      rw [estermann_swap k (1-u) (1-v), estermann_eq_sum_twist_mul_residue]
      apply Finset.sum_congr rfl
      intro a _
      rw [hR a, hT (k * a)]
      ring
    _ = leftFactor u * rightFactor v * ∑ a : ZMod K,
        ((negativePhase u * positivePhase v) *
            (estermannTwist a u * residueLFunction (k * a) v) +
          (negativePhase u * negativePhase v) *
            (estermannTwist a u * residueLFunction (-(k * a)) v) +
          (positivePhase u * positivePhase v) *
            (estermannTwist (-a) u * residueLFunction (k * a) v) +
          (positivePhase u * negativePhase v) *
            (estermannTwist (-a) u * residueLFunction (-(k * a)) v)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      ring
    _ = leftFactor u * rightFactor v *
        ((negativePhase u * positivePhase v + positivePhase u * negativePhase v) *
          estermann i u v +
          (negativePhase u * negativePhase v + positivePhase u * positivePhase v) *
            estermann (-i) u v) := by
      simp only [Finset.sum_add_distrib, ← Finset.mul_sum, hpp, hpn, hnp, hnn]
      ring
    _ = _ := by
      rw [hdiffPhase, hsumPhase]
      dsimp only [leftFactor, rightFactor, archimedean, i]
      rw [show u + v - 1 = (u - 1) + v by ring, Complex.cpow_add _ _ hK,
        show -u - v = -u + -v by ring, Complex.cpow_add _ _ hπ]
      ring

/-- The residue at the left shifted pole, with the other zeta factor evaluated there. -/
theorem estermann_shifted_residue_left {K : ℕ} [NeZero K] (h : (ZMod K)ˣ)
    {α β : ℂ} (hne : α ≠ β) :
    Tendsto (fun s : ℂ => (s - (1 - α)) * estermann (h : ZMod K) (s + α) (s + β))
      (𝓝[≠] (1 - α)) (𝓝 ((K : ℂ) ^ (-(1 - α + β)) * riemannZeta (1 - α + β))) := by
  have hg : Tendsto (fun t : ℂ => t - α + β) (𝓝[≠] (1 : ℂ)) (𝓝 (1 - α + β)) := by
    have hc : ContinuousAt (fun t : ℂ => t - α + β) 1 := by fun_prop
    exact hc.continuousWithinAt.tendsto
  have hp : 1 - α + β ≠ 1 := by
    intro he
    apply hne
    linear_combination -he
  have hs : Tendsto (fun s : ℂ => s + α) (𝓝[≠] (1 - α)) (𝓝[≠] (1 : ℂ)) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨?_, ?_⟩
    · have hc : ContinuousAt (fun s : ℂ => s + α) (1 - α) := by fun_prop
      simpa using hc.continuousWithinAt.tendsto
    · filter_upwards [self_mem_nhdsWithin] with s hs
      change s ≠ 1 - α at hs
      change s + α ≠ 1
      intro he
      apply hs
      exact eq_sub_of_add_eq he
  have h := (estermann_residue_left h hg hp).comp hs
  simpa only [Function.comp_def, add_sub_cancel_right, sub_sub_eq_add_sub, add_comm α] using h

/-- The residue at the right shifted pole, with the other zeta factor evaluated there. -/
theorem estermann_shifted_residue_right {K : ℕ} [NeZero K] (h : (ZMod K)ˣ)
    {α β : ℂ} (hne : α ≠ β) :
    Tendsto (fun s : ℂ => (s - (1 - β)) * estermann (h : ZMod K) (s + α) (s + β))
      (𝓝[≠] (1 - β)) (𝓝 ((K : ℂ) ^ (-(1 - β + α)) * riemannZeta (1 - β + α))) := by
  have he : (fun s : ℂ => (s - (1 - β)) * estermann (h : ZMod K) (s + α) (s + β)) =
      fun s : ℂ => (s - (1 - β)) * estermann (h : ZMod K) (s + β) (s + α) := by
    funext s
    rw [estermann_swap (h : ZMod K) (s + α) (s + β)]
  rw [he]
  exact estermann_shifted_residue_left h hne.symm

end RiemannResearch.Analysis.ConreyBaluyot
