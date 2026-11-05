/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.RH.QDisplacementTailTests
import RiemannResearch.RH.QSquarefreeFiniteDisplacement
import RiemannResearch.RH.QPhysicalTailEnergy
import RiemannResearch.RH.QSquarefreeCapacity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! # One signed Gram entry for the matched finite displacement

The squarefree dictionary is that of Bagchi (2006), Remark 8. The test uses
the two finite normal equations and the exact remainder in Euclidean division.
Its limit is the squared Pareto approximation distance divided by zeta(2).
-/
noncomputable section
open Filter
open scoped Topology
namespace RiemannResearch.RH.QSquarefreeFiniteDisplacement
open ZetaTwoHilbert ZetaTwoProbability ZetaTwoParetoTransfer QParetoEquivalence
open QParetoClosedProjectionComparison QSquarefreeMeasureRigidity QShiftedReciprocal
open QSquarefreeDisplacementRigidity QSquarefreeDisplacementRegularity
open QAnnihilatorTailEscape ZetaTwoOptimizerStage ArithmeticCumulative

def residueRemainder (m : ℕ) : QHilbert :=
  qOne - B qOne - (m : ℝ) • B (qResidue m)

theorem residueRemainder_value {m : ℕ} (hm : 0 < m) (n : ℕ) :
    qSequence (residueRemainder m) n = ((n : ℝ) - ((n % m : ℕ) : ℝ)) / ((n : ℝ) + 1) := by
  have sub (x y : QHilbert) : qSequence (x-y) n = qSequence x n - qSequence y n :=
    congrFun (qSequenceLinear.map_sub x y) n
  have sm (a : ℝ) (x : QHilbert) : qSequence (a • x) n = a * qSequence x n :=
    congrFun (qSequenceLinear.map_smul a x) n
  by_cases hn : n = 0
  · subst n
    simp
  simp only [residueRemainder, sub, sm, qSequence_B, qSequence_qResidue, qSequence_qOne,
    qOneSequence, if_neg hn, residueFraction]
  have hm' : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  have hn' : (n : ℝ) + 1 ≠ 0 := by positivity
  field_simp [hm', hn']
  ring

theorem residueRemainder_bound {m : ℕ} (hm : 0 < m) :
    zetaTwo * ‖residueRemainder m‖ ^ 2 ≤ 2 / (m : ℝ) := by
  have hhead (n : ℕ) (hn : n ≤ m-1) : qSequence (residueRemainder m) n = 0 := by
    rw [residueRemainder_value hm, Nat.mod_eq_of_lt (by omega : n < m), sub_self, zero_div]
  have hb (n : ℕ) : |qSequence (residueRemainder m) n| ≤ 1 := by
    rw [residueRemainder_value hm]
    have ht : ((n % m : ℕ) : ℝ) ≤ n := by exact_mod_cast Nat.mod_le n m
    have hn : 0 < (n : ℝ) + 1 := by positivity
    rw [abs_of_nonneg (div_nonneg (sub_nonneg.mpr ht) hn.le)]
    apply (div_le_iff₀ hn).mpr
    linarith [Nat.cast_nonneg (α := ℝ) (n % m)]
  have h := zeta_mul_tail_energy_le_of_bounded (residueRemainder m) (m-1) 1 zero_le_one hb
  rw [tail_eq_self_of_head _ _ hhead] at h
  have he : ((m-1 : ℕ) : ℝ) + 1 = m := by
    exact_mod_cast (show m-1+1=m by omega)
  simpa only [one_pow, mul_one, he] using h

theorem finite_single_residue_exact (M m : ℕ) (hg : qResidue m ∈ stage M) :
    zetaTwo * ((m : ℝ) * inner ℝ (qResidue m) (finiteDisplacement M) +
      inner ℝ (residueRemainder m) (qOne - finitePFit M)) =
      ‖toPareto (qOne - finitePFit M)‖ ^ 2 := by
  let u := qOne - finitePFit M
  have h := Submodule.inner_right_of_mem_orthogonal hg (finite_witness_mem_orthogonal M)
  change inner ℝ (qResidue m) (B u - finiteDisplacement M) = 0 at h
  rw [inner_sub_right, ← B_symmetric] at h
  have hp : inner ℝ (toPareto (finitePFit M)) (toPareto u) = 0 := by
    dsimp only [u, finitePFit]
    rw [toPareto_sub, toPareto_pFit]
    exact Submodule.inner_right_of_mem_orthogonal ((paretoStage M).starProjection_apply_mem _)
      (Submodule.sub_starProjection_mem_orthogonal _)
  have he : inner ℝ (toPareto qOne) (toPareto u) = ‖toPareto u‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq]
    have hi := congrArg (fun v => inner ℝ v (toPareto u)) (toPareto_sub qOne (finitePFit M))
    change inner ℝ (toPareto u) (toPareto u) =
      inner ℝ (toPareto qOne - toPareto (finitePFit M)) (toPareto u) at hi
    rw [inner_sub_left, hp, sub_zero] at hi
    exact hi.symm
  rw [pareto_inner_identity, ← B_symmetric] at he
  change zetaTwo * (_ + inner ℝ (residueRemainder m) u) = ‖toPareto u‖ ^ 2
  rw [residueRemainder, inner_sub_left, inner_sub_left, real_inner_smul_left,
    sub_eq_zero.mp h]
  linarith

theorem residueRemainder_tendsto : Tendsto residueRemainder atTop (𝓝 0) := by
  have hs : Tendsto (fun m : ℕ => ‖residueRemainder m‖ ^ 2) atTop (𝓝 0) := by
    have ht : Tendsto (fun m : ℕ => (2 / zetaTwo) / (m : ℝ)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
    apply squeeze_zero' (Eventually.of_forall fun _ => sq_nonneg _) _ ht
    filter_upwards [eventually_ge_atTop 1] with m hm
    have h := residueRemainder_bound (by omega : 0 < m)
    apply (le_div_iff₀ (by exact_mod_cast (show 0 < m by omega) : 0 < (m : ℝ))).mpr
    apply (le_div_iff₀ zetaTwo_pos).mpr
    have h' := (le_div_iff₀ (by exact_mod_cast (show 0 < m by omega) : 0 < (m : ℝ))).mp h
    nlinarith
  apply tendsto_zero_iff_norm_tendsto_zero.mpr
  simpa only [Real.sqrt_sq (norm_nonneg _), Real.sqrt_zero] using hs.sqrt

theorem finite_single_residue_limit (M m : ℕ → ℕ)
    (hM : Tendsto M atTop atTop) (hm : Tendsto m atTop atTop)
    (hg : ∀ j, qResidue (m j) ∈ stage (M j)) :
    Tendsto (fun j => zetaTwo * ((m j : ℝ) *
      inner ℝ (qResidue (m j)) (finiteDisplacement (M j)))) atTop
      (𝓝 (‖toPareto pResidual‖ ^ 2)) := by
  have hu : Tendsto (fun j => qOne - finitePFit (M j)) atTop (𝓝 pResidual) :=
    tendsto_const_nhds.sub (finitePFit_tendsto.comp hM)
  have he : Tendsto (fun j => inner ℝ (residueRemainder (m j)) (qOne - finitePFit (M j))) atTop
      (𝓝 (inner ℝ (0 : QHilbert) pResidual)) := (residueRemainder_tendsto.comp hm).inner hu
  have hn := ((paretoEquiv.continuous.continuousAt.tendsto.comp hu).norm.pow 2)
  have ht := hn.sub (he.const_mul zetaTwo)
  simp only [inner_zero_left, mul_zero, sub_zero] at ht
  apply ht.congr'
  apply Eventually.of_forall
  intro j
  have h := finite_single_residue_exact (M j) (m j) (hg j)
  change ‖toPareto (qOne - finitePFit (M j))‖ ^ 2 -
    zetaTwo * inner ℝ (residueRemainder (m j)) (qOne - finitePFit (M j)) = _
  linarith

theorem riemannHypothesis_of_finite_single_residue (M m : ℕ → ℕ)
    (hM : Tendsto M atTop atTop) (hm : Tendsto m atTop atTop)
    (hg : ∀ j, qResidue (m j) ∈ stage (M j))
    (hsmall : Tendsto (fun j => (m j : ℝ) *
      inner ℝ (qResidue (m j)) (finiteDisplacement (M j))) atTop (𝓝 0)) :
    RiemannHypothesis := by
  have hz : ‖toPareto pResidual‖ ^ 2 = 0 := tendsto_nhds_unique
    (finite_single_residue_limit M m hM hm hg) (by simpa using hsmall.const_mul zetaTwo)
  have hp : pResidual = 0 := by
    apply paretoEquiv.injective
    change toPareto pResidual = paretoEquiv 0
    rw [map_zero]
    apply norm_eq_zero.mp
    nlinarith [norm_nonneg (toPareto pResidual)]
  have hmem := pFit_mem closure paretoSquarefreeClosure
    toPareto_mem_paretoSquarefreeClosure_iff qOne
  have he : qOne = pFit paretoSquarefreeClosure qOne := sub_eq_zero.mp hp
  apply QSquarefreeCapacity.riemannHypothesis_of_capacity_tendsto
  apply QSquarefreeCapacity.capacity_tendsto_iff_optimizer_closure.mpr
  rw [he]
  exact hmem

/-- A row evaluation against the Pareto residual needs only the Pareto Gram solve. -/
theorem finite_pareto_entry (M m : ℕ) (hg : qResidue m ∈ stage M) :
    inner ℝ (qResidue m) (qOne - finitePFit M) =
      inner ℝ (qResidue m) (finiteDisplacement M) := by
  rw [finitePResidual_eq, inner_add_right,
    Submodule.inner_right_of_mem_orthogonal hg (residual_mem_orthogonal _), zero_add]

theorem finite_pareto_entry_limit (M m : ℕ → ℕ)
    (hM : Tendsto M atTop atTop) (hm : Tendsto m atTop atTop)
    (hg : ∀ j, qResidue (m j) ∈ stage (M j)) :
    Tendsto (fun j => zetaTwo * ((m j : ℝ) *
      inner ℝ (qResidue (m j)) (qOne - finitePFit (M j)))) atTop
      (𝓝 (‖toPareto pResidual‖ ^ 2)) := by
  apply (finite_single_residue_limit M m hM hm hg).congr'
  exact Eventually.of_forall fun j => by
    dsimp only
    rw [finite_pareto_entry _ _ (hg j)]

theorem riemannHypothesis_of_finite_pareto_entry (M m : ℕ → ℕ)
    (hM : Tendsto M atTop atTop) (hm : Tendsto m atTop atTop)
    (hg : ∀ j, qResidue (m j) ∈ stage (M j))
    (hsmall : Tendsto (fun j => (m j : ℝ) *
      inner ℝ (qResidue (m j)) (qOne - finitePFit (M j))) atTop (𝓝 0)) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_finite_single_residue M m hM hm hg
  exact hsmall.congr' (Eventually.of_forall fun j => by rw [finite_pareto_entry _ _ (hg j)])

/-- One finite Pareto fit and one signed Q pairing per prime. -/
theorem riemannHypothesis_of_frequently_nonpositive_prime_entry
    (h : ∃ᶠ p : ℕ in atTop, p.Prime ∧
        inner ℝ (qResidue p) (qOne - finitePFit p) ≤ 0) : RiemannHypothesis := by
  have hex (j : ℕ) : ∃ p : ℕ, j ≤ p ∧ p.Prime ∧
      inner ℝ (qResidue p) (qOne - finitePFit p) ≤ 0 := by
    obtain ⟨p, hgood, hp⟩ := (h.and_eventually (eventually_ge_atTop j)).exists
    exact ⟨p, hp, hgood⟩
  choose m hge hprime hPsign using hex
  have hm : Tendsto m atTop atTop := tendsto_atTop.2 (fun b =>
    (eventually_ge_atTop b).mono (fun j hj => le_trans hj (hge j)))
  have hstage (j : ℕ) : qResidue (m j) ∈ stage (m j) := by
    have h₂ := (hprime j).two_le
    change qResidue (m j) ∈ Submodule.span ℝ
      (Set.range (fun i : Fin (m j) => squarefreeAtom i))
    apply Submodule.subset_span
    refine ⟨⟨m j - 2, by omega⟩, ?_⟩
    change squarefreeAtom (m j - 2) = qResidue (m j)
    simp [squarefreeAtom, show m j - 2 + 2 = m j by omega, (hprime j).squarefree]
  have hsign (j : ℕ) : inner ℝ (qResidue (m j)) (finiteDisplacement (m j)) ≤ 0 := by
    have h := hPsign j
    rw [finitePResidual_eq, inner_add_right,
      Submodule.inner_right_of_mem_orthogonal (hstage j) (residual_mem_orthogonal _), zero_add] at h
    exact h
  have hle : ‖toPareto pResidual‖ ^ 2 ≤ 0 := by
    apply le_of_tendsto (finite_single_residue_limit m m hm hm hstage)
    exact Eventually.of_forall (fun j => mul_nonpos_of_nonneg_of_nonpos zetaTwo_pos.le
      (mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg _) (hsign j)))
  have hp : pResidual = 0 := by
    apply paretoEquiv.injective
    change toPareto pResidual = paretoEquiv 0
    rw [map_zero]
    apply norm_eq_zero.mp
    nlinarith [norm_nonneg (toPareto pResidual)]
  have hmem := pFit_mem closure paretoSquarefreeClosure
    toPareto_mem_paretoSquarefreeClosure_iff qOne
  have he : qOne = pFit paretoSquarefreeClosure qOne := sub_eq_zero.mp hp
  apply QSquarefreeCapacity.riemannHypothesis_of_capacity_tendsto
  apply QSquarefreeCapacity.capacity_tendsto_iff_optimizer_closure.mpr
  rw [he]
  exact hmem

/-- A uniform finite relative error estimate, squared to avoid a choice of root. -/
theorem finite_single_residue_error_sq (M m : ℕ) (hm : 0 < m) (hg : qResidue m ∈ stage M) :
    (m : ℝ) * (zetaTwo * ((m : ℝ) * inner ℝ (qResidue m) (qOne - finitePFit M)) -
      ‖toPareto (qOne - finitePFit M)‖ ^ 2) ^ 2 ≤ 4 * ‖toPareto (qOne - finitePFit M)‖ ^ 2 := by
  let u := qOne - finitePFit M
  let T := residueRemainder m
  have he := finite_single_residue_exact M m hg
  have hpair : inner ℝ (qResidue m) u = inner ℝ (qResidue m) (finiteDisplacement M) := by
    dsimp only [u]
    rw [finitePResidual_eq, inner_add_right,
      Submodule.inner_right_of_mem_orthogonal hg (residual_mem_orthogonal _), zero_add]
  change (m : ℝ) * (zetaTwo * ((m : ℝ) * inner ℝ (qResidue m) u) - ‖toPareto u‖ ^ 2)^2 ≤ _
  rw [hpair]
  have hE : ‖toPareto u‖ ^ 2 = zetaTwo * ((m : ℝ) * inner ℝ (qResidue m)
      (finiteDisplacement M) + inner ℝ T u) := he.symm
  have hdiff : zetaTwo * ((m : ℝ) * inner ℝ (qResidue m) (finiteDisplacement M)) -
      ‖toPareto u‖ ^ 2 = -(zetaTwo * inner ℝ T u) := by rw [hE]; ring
  rw [hdiff]
  have hsq := (sq_le_sq₀ (abs_nonneg _) (mul_nonneg (norm_nonneg T) (norm_nonneg u))).mpr
    (abs_real_inner_le_norm T u)
  rw [sq_abs, mul_pow] at hsq
  have hT : zetaTwo * ‖T‖ ^ 2 * (m : ℝ) ≤ 2 := (le_div_iff₀
    (show 0 < (m : ℝ) by exact_mod_cast hm)).mp (residueRemainder_bound hm)
  have hu := zetaTwo_mul_norm_sq_le_two_toPareto_norm_sq u
  calc
    _ = ((m : ℝ) * zetaTwo ^ 2) * (inner ℝ T u)^2 := by ring
    _ ≤ ((m : ℝ) * zetaTwo ^ 2) * (‖T‖ ^ 2 * ‖u‖ ^ 2) :=
      mul_le_mul_of_nonneg_left hsq (by positivity)
    _ = (zetaTwo * ‖T‖ ^ 2 * (m : ℝ)) * (zetaTwo * ‖u‖ ^ 2) := by ring
    _ ≤ 2 * (2 * ‖toPareto u‖ ^ 2) := mul_le_mul hT hu
      (mul_nonneg zetaTwo_pos.le (sq_nonneg _)) (by norm_num)
    _ = _ := by dsimp only [u]; ring

/-- In particular, Burnol's transferred lower bound E ≫ 1/log M eventually makes
the diagonal prime sign strictly positive. This lemma isolates the required finite inequality. -/
theorem finite_single_residue_pos_of_distance (M m : ℕ) (hm : 0 < m)
    (hg : qResidue m ∈ stage M) (hgap : 4 / (m : ℝ) < ‖toPareto (qOne - finitePFit M)‖ ^ 2) :
    0 < inner ℝ (qResidue m) (qOne - finitePFit M) := by
  let E := ‖toPareto (qOne - finitePFit M)‖ ^ 2
  let x := zetaTwo * ((m : ℝ) * inner ℝ (qResidue m) (qOne - finitePFit M))
  have hm' : 0 < (m : ℝ) := by exact_mod_cast hm
  have hE : 0 < E := lt_trans (by positivity : 0 < 4 / (m : ℝ)) hgap
  have h4 : 4 < E * (m : ℝ) := (div_lt_iff₀ hm').mp hgap
  by_contra! hn
  have hx : x ≤ 0 := mul_nonpos_of_nonneg_of_nonpos zetaTwo_pos.le
    (mul_nonpos_of_nonneg_of_nonpos hm'.le hn)
  have hsq := (sq_le_sq₀ hE.le (show 0 ≤ E-x by linarith)).mpr (show E ≤ E-x by linarith)
  have he := finite_single_residue_error_sq M m hm hg
  change (m : ℝ) * (x-E)^2 ≤ 4 * E at he
  have hc := mul_le_mul_of_nonneg_left hsq hm'.le
  nlinarith [mul_pos (sub_pos.mpr h4) hE]

end RiemannResearch.RH.QSquarefreeFiniteDisplacement
