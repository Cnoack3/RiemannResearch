import RiemannResearch.RH.QDensityLeakageQuantitative
import RiemannResearch.RH.QFullTargetTotality
import RiemannResearch.RH.QDensityLeakage
import RiemannResearch.RH.QFullResidueProjection
import RiemannResearch.RH.QOptimizerParityRH
import RiemannResearch.RH.ZetaTwoHilbertSpace
import RiemannResearch.RH.ZetaTwoProbability
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Analysis.PSeries
import Mathlib.Tactic.Abel
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import RiemannResearch.RH.ZetaTwoParitySignal
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Tactic.Ring
import Lean.Elab.Tactic.Omega

/-!
# Signed leakage partial sums detect full residue totality

Source: Christian Noack's V-space continuation request, 14 November 2026,
and the exact harmonic centering in QDensityLeakageQuantitative.
Write r = 1 - projection_V(1), h_k = projection_(V-orthogonal)(B g_k),
H_N = sum_{k=2}^{N+1} 1/(zeta(2) k), and E_N for the centered sum.
The complete signed identity is S_N = H_N r + E_N, with uniformly bounded
E_N. If r is nonzero, the vector partial sums themselves escape to infinity.
Thus conditional convergence cannot rescue this particular leakage series:
vector summability and absolute norm summability are equivalent to 1 in V.

Cofinal boundedness of the actual sums is a conditional RH reduction.
No cofinal uniform bound, vanishing of r, or unconditional RH proof is asserted.
The bounds below allow harmonic growth. No RH-to-density analytic converse is used.
-/

noncomputable section
open Filter
open scoped Topology BigOperators
namespace RiemannResearch.RH.QDensityLeakageSeries
open ZetaTwoHilbert ZetaTwoProbability QFullResidueProjection QDensityLeakage

def residual : QHilbert := qOne - closure.starProjection qOne

def partialLeakage (N : ℕ) : QHilbert :=
  ∑ n ∈ Finset.range N, leakage (qResidue (n + 2))

def harmonicMass (N : ℕ) : ℝ :=
  ∑ n ∈ Finset.range N, 1 / (zetaTwo * ((n + 2 : ℕ) : ℝ))

def centeredPartial (N : ℕ) : QHilbert :=
  ∑ n ∈ Finset.range N, centeredLeakage (n + 2)

def centeredBudget : ℝ := ∑' n : ℕ, ‖centeredLeakage (n + 2)‖

theorem partialLeakage_exact (N : ℕ) :
    partialLeakage N = harmonicMass N • residual + centeredPartial N := by
  simp only [partialLeakage, harmonicMass, residual, centeredPartial,
    centeredLeakage, Finset.sum_sub_distrib, Finset.sum_smul]
  abel

theorem centeredPartial_norm_le (N : ℕ) :
    ‖centeredPartial N‖ ≤ centeredBudget := by
  exact (norm_sum_le _ _).trans
    (summable_centeredLeakage_norm.sum_le_tsum (Finset.range N)
      (fun n _ => norm_nonneg _))

theorem harmonicMass_nonneg (N : ℕ) : 0 ≤ harmonicMass N := by
  unfold harmonicMass
  exact Finset.sum_nonneg (fun n _ => by have hZ := zetaTwo_pos; positivity)

theorem harmonicMass_tendsto_atTop : Tendsto harmonicMass atTop atTop := by
  have hpos : ∀ n : ℕ, 0 ≤ 1 / (zetaTwo * ((n + 2 : ℕ) : ℝ)) := by
    intro n
    have hZ := zetaTwo_pos
    positivity
  apply (not_summable_iff_tendsto_nat_atTop_of_nonneg hpos).mp
  intro hs
  have hh : Summable (fun n : ℕ => 1 / ((n + 2 : ℕ) : ℝ)) := by
    apply (hs.mul_left zetaTwo).congr
    intro n
    have hZ := zetaTwo_pos.ne'
    have hn : ((n + 2 : ℕ) : ℝ) ≠ 0 := by positivity
    field_simp
  have ht : Summable (fun n : ℕ => 1 / (n : ℝ)) :=
    (summable_nat_add_iff (f := fun n : ℕ => 1 / (n : ℝ)) 2).mp hh
  have hb : 1 < (1 : ℕ) := (Real.summable_one_div_nat_pow (p := 1)).mp
    (by simpa only [pow_one] using ht)
  norm_num at hb

theorem partialLeakage_lower (N : ℕ) :
    harmonicMass N * ‖residual‖ ≤ ‖partialLeakage N‖ + centeredBudget := by
  have he : harmonicMass N • residual = partialLeakage N - centeredPartial N := by
    rw [partialLeakage_exact]
    abel
  have h := norm_sub_le (partialLeakage N) (centeredPartial N)
  rw [← he, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (harmonicMass_nonneg N)] at h
  linarith [centeredPartial_norm_le N]

theorem partialLeakage_norm_tendsto_atTop (hne : qOne ∉ closure) :
    Tendsto (fun N => ‖partialLeakage N‖) atTop atTop := by
  have hr : 0 < ‖residual‖ := by
    apply norm_pos_iff.mpr
    intro he
    exact hne (Submodule.starProjection_eq_self_iff.mp (sub_eq_zero.mp he).symm)
  apply tendsto_atTop.2
  intro b
  filter_upwards [harmonicMass_tendsto_atTop.eventually
    (eventually_ge_atTop ((b + centeredBudget) / ‖residual‖))] with N hN
  have h := (div_le_iff₀ hr).mp hN
  nlinarith [partialLeakage_lower N]

theorem frequently_bounded_partialLeakage_iff :
    (∃ C : ℝ, ∀ J : ℕ, ∃ N : ℕ, J ≤ N ∧ ‖partialLeakage N‖ ≤ C) ↔
      qOne ∈ closure := by
  constructor
  · rintro ⟨C, hC⟩
    by_contra hne
    obtain ⟨J, hJ⟩ := eventually_atTop.1
      ((partialLeakage_norm_tendsto_atTop hne).eventually
        (eventually_ge_atTop (C + 1)))
    obtain ⟨N, hJN, hN⟩ := hC J
    have h := hJ N hJN
    linarith
  · intro hmem
    have hz := residue_leakage_vanishes_iff_one_mem.mpr hmem
    refine ⟨0, fun J => ⟨J, le_rfl, ?_⟩⟩
    have hn (n : ℕ) : leakage (qResidue (n + 2)) = 0 := hz _ (by omega)
    simp only [partialLeakage, hn, Finset.sum_const_zero, norm_zero, le_refl]

theorem summable_residue_leakage_iff :
    Summable (fun n : ℕ => leakage (qResidue (n + 2))) ↔ qOne ∈ closure := by
  constructor
  · intro hs
    obtain ⟨C, hC⟩ := hs.hasSum.tendsto_sum_nat.norm.bddAbove_range
    apply frequently_bounded_partialLeakage_iff.mp
    exact ⟨C, fun J => ⟨J, le_rfl, hC ⟨J, rfl⟩⟩⟩
  · intro hmem
    exact (summable_residue_leakage_norm_iff.mpr hmem).of_norm

theorem summable_residue_leakage_iff_summable_norm :
    Summable (fun n : ℕ => leakage (qResidue (n + 2))) ↔
      Summable (fun n : ℕ => ‖leakage (qResidue (n + 2))‖) :=
  summable_residue_leakage_iff.trans summable_residue_leakage_norm_iff.symm

theorem frequently_bounded_partialLeakage_iff_totality :
    (∃ C : ℝ, ∀ J : ℕ, ∃ N : ℕ, J ≤ N ∧ ‖partialLeakage N‖ ≤ C) ↔
      closure = ⊤ :=
  frequently_bounded_partialLeakage_iff.trans
    QFullTargetTotality.closure_eq_top_iff_one_mem.symm

theorem riemannHypothesis_of_frequently_bounded_partialLeakage
    (h : ∃ C : ℝ, ∀ J : ℕ, ∃ N : ℕ, J ≤ N ∧ ‖partialLeakage N‖ ≤ C) :
    RiemannHypothesis :=
  riemannHypothesis_of_qOne_mem_full_closure
    (frequently_bounded_partialLeakage_iff.mp h)

/-! ## Cofinal subharmonic leakage

Source: user-requested proof-obligation triage continuation, 15 November 2026.
The exact signed identity above gives a two-sided norm error at every stage.
The conditional provider can therefore allow unbounded sums: for every positive
slope, cofinally many sums lie below that slope times harmonic mass. This
criterion is equivalent to constant-target membership; the arithmetic provider
remains open. No analytic RH converse is used.
-/

theorem partialLeakage_norm_gap_le (N : ℕ) :
    |‖partialLeakage N‖ - harmonicMass N * ‖residual‖| ≤ centeredBudget := by
  apply abs_le.mpr
  constructor
  · linarith [partialLeakage_lower N]
  · have h := norm_add_le (harmonicMass N • residual) (centeredPartial N)
    rw [← partialLeakage_exact, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (harmonicMass_nonneg N)] at h
    linarith [centeredPartial_norm_le N]

theorem cofinal_subharmonic_partialLeakage_iff :
    (∀ ε : ℝ, 0 < ε → ∀ J : ℕ,
      ∃ N : ℕ, J ≤ N ∧ ‖partialLeakage N‖ ≤ ε * harmonicMass N) ↔
      qOne ∈ closure := by
  constructor
  · intro h
    by_contra hne
    have hr : 0 < ‖residual‖ := by
      apply norm_pos_iff.mpr
      intro he
      exact hne (Submodule.starProjection_eq_self_iff.mp (sub_eq_zero.mp he).symm)
    obtain ⟨J, hJ⟩ := eventually_atTop.1
      (harmonicMass_tendsto_atTop.eventually
        (eventually_ge_atTop ((2 * centeredBudget + 1) / ‖residual‖)))
    obtain ⟨N, hJN, hN⟩ := h (‖residual‖ / 2) (by positivity) J
    have ht := (div_le_iff₀ hr).mp (hJ N hJN)
    nlinarith [partialLeakage_lower N]
  · intro hmem ε hε J
    have hz := residue_leakage_vanishes_iff_one_mem.mpr hmem
    refine ⟨J, le_rfl, ?_⟩
    have hn (n : ℕ) : leakage (qResidue (n + 2)) = 0 := hz _ (by omega)
    simp only [partialLeakage, hn, Finset.sum_const_zero, norm_zero]
    exact mul_nonneg hε.le (harmonicMass_nonneg J)

theorem cofinal_subharmonic_partialLeakage_iff_totality :
    (∀ ε : ℝ, 0 < ε → ∀ J : ℕ,
      ∃ N : ℕ, J ≤ N ∧ ‖partialLeakage N‖ ≤ ε * harmonicMass N) ↔
      closure = ⊤ :=
  cofinal_subharmonic_partialLeakage_iff.trans
    QFullTargetTotality.closure_eq_top_iff_one_mem.symm

theorem riemannHypothesis_of_cofinal_subharmonic_partialLeakage
    (h : ∀ ε : ℝ, 0 < ε → ∀ J : ℕ,
      ∃ N : ℕ, J ≤ N ∧ ‖partialLeakage N‖ ≤ ε * harmonicMass N) :
    RiemannHypothesis :=
  riemannHypothesis_of_qOne_mem_full_closure
    (cofinal_subharmonic_partialLeakage_iff.mp h)

/-! ## Normalized sum asymptotics and unconditional partial progress

Source: Christian Noack's cofinal-subharmonic obligation, 16 November 2026.
These deductions use the exact centered identity above and the repository's
complete parity mass calculation. They prove the normalized vector limit r,
the normalized norm limit ||r||, and the signed mean limit ||r||^2, with the
full signed norm-square expansion retained.

A concrete finite legal competitor gives ||S_N|| <= H_N/2 + centeredBudget.
Thus slopes greater than 1/2 are unconditional. Arbitrarily small positive
slopes are NOT supplied. The one-sided scalar mean criterion below is an
equivalent conditional reduction, with its arithmetic provider still open.

For the classical RH interpretation, see Bagchi, arXiv:math/0607733,
Theorem 1 and the equivalent-weight observation. This reference supports the
density interpretation, not an unconditional zero-residual estimate.
-/

/-- The normalizing mass is strictly positive at every nonempty stage. -/
theorem harmonicMass_pos (N : ℕ) (hN : 0 < N) : 0 < harmonicMass N := by
  unfold harmonicMass
  apply Finset.sum_pos
  · intro n hn
    exact one_div_pos.mpr (mul_pos zetaTwo_pos (by positivity))
  · exact ⟨0, Finset.mem_range.mpr hN⟩

/-- The full normalized vector error, with its sign retained. -/
theorem normalized_partialLeakage_error_eq (N : ℕ) (hN : 0 < N) :
    (harmonicMass N)⁻¹ • partialLeakage N - residual =
      (harmonicMass N)⁻¹ • centeredPartial N := by
  rw [partialLeakage_exact, smul_add, smul_smul,
    inv_mul_cancel₀ (harmonicMass_pos N hN).ne', one_smul, add_sub_cancel_left]

/-- An unconditional complete-Q error estimate of order 1/H_N. -/
theorem normalized_partialLeakage_error_norm_le (N : ℕ) (hN : 0 < N) :
    ‖(harmonicMass N)⁻¹ • partialLeakage N - residual‖ ≤
      centeredBudget / harmonicMass N := by
  rw [normalized_partialLeakage_error_eq N hN, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.mpr (harmonicMass_nonneg N)), div_eq_mul_inv, mul_comm]
  exact mul_le_mul_of_nonneg_right (centeredPartial_norm_le N)
    (inv_nonneg.mpr (harmonicMass_nonneg N))

/-- The normalized actual signed sums converge to the actual constant residual. -/
theorem normalized_partialLeakage_tendsto :
    Tendsto (fun N => (harmonicMass N)⁻¹ • partialLeakage N) atTop (𝓝 residual) := by
  have hc : Tendsto centeredPartial atTop
      (𝓝 (∑' n : ℕ, centeredLeakage (n + 2))) :=
    summable_centeredLeakage_norm.of_norm.hasSum.tendsto_sum_nat
  have hi : Tendsto (fun N => (harmonicMass N)⁻¹) atTop (𝓝 (0 : ℝ)) :=
    tendsto_inv_atTop_zero.comp harmonicMass_tendsto_atTop
  have he : Tendsto (fun N => (harmonicMass N)⁻¹ • centeredPartial N)
      atTop (𝓝 (0 : QHilbert)) := by
    simpa only [zero_smul] using hi.smul hc
  have ht := (tendsto_const_nhds (x := residual)).add he
  apply (show Tendsto (fun N => residual + (harmonicMass N)⁻¹ • centeredPartial N)
    atTop (𝓝 residual) from by simpa only [add_zero] using ht).congr'
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with N hN
  have hh := normalized_partialLeakage_error_eq N (by omega)
  exact (add_comm _ _).trans (eq_add_of_sub_eq hh).symm

/-- The limiting slope of the norm is the norm of the residual, not yet zero. -/
theorem normalized_partialLeakage_norm_tendsto :
    Tendsto (fun N => ‖partialLeakage N‖ / harmonicMass N)
      atTop (𝓝 ‖residual‖) := by
  convert normalized_partialLeakage_tendsto.norm using 1
  funext N
  rw [norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.mpr (harmonicMass_nonneg N)), div_eq_mul_inv, mul_comm]

/-- Exact energy expansion; the signed cross term and centered square are retained. -/
theorem partialLeakage_norm_sq_exact (N : ℕ) :
    ‖partialLeakage N‖ ^ 2 =
      (harmonicMass N) ^ 2 * ‖residual‖ ^ 2 +
        2 * harmonicMass N * inner ℝ residual (centeredPartial N) +
          ‖centeredPartial N‖ ^ 2 := by
  rw [partialLeakage_exact, norm_add_sq_real, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (harmonicMass_nonneg N), real_inner_smul_left]
  ring

/-- The constant-residual pairing is its complete squared norm. -/
theorem qOne_inner_residual : inner ℝ qOne residual = ‖residual‖ ^ 2 := by
  have ho := Submodule.inner_right_of_mem_orthogonal
    (closure.starProjection_apply_mem qOne)
    (Submodule.sub_starProjection_mem_orthogonal (K := closure) qOne)
  rw [← real_inner_self_eq_norm_sq, residual, inner_sub_left, ho, sub_zero]

/-- Exact signed mean identity for the actual leakage sum. -/
theorem partialLeakage_mean_exact (N : ℕ) :
    inner ℝ qOne (partialLeakage N) =
      harmonicMass N * ‖residual‖ ^ 2 + inner ℝ qOne (centeredPartial N) := by
  rw [partialLeakage_exact, inner_add_right, inner_smul_right, qOne_inner_residual]

/-- A complete bounded error for the signed mean; no absolute value is dropped. -/
theorem partialLeakage_mean_gap_le (N : ℕ) :
    |inner ℝ qOne (partialLeakage N) - harmonicMass N * ‖residual‖ ^ 2| ≤
      centeredBudget := by
  rw [partialLeakage_mean_exact, add_sub_cancel_left]
  have h := abs_real_inner_le_norm qOne (centeredPartial N)
  rw [qOne_norm, one_mul] at h
  exact h.trans (centeredPartial_norm_le N)

/-- The normalized signed mean converges unconditionally to residual energy. -/
theorem normalized_partialLeakage_mean_tendsto :
    Tendsto (fun N => inner ℝ qOne (partialLeakage N) / harmonicMass N)
      atTop (𝓝 (‖residual‖ ^ 2)) := by
  have hcont : Continuous (fun f : QHilbert => inner ℝ qOne f) :=
    continuous_const.inner continuous_id
  have ht := (hcont.tendsto residual).comp normalized_partialLeakage_tendsto
  simpa only [Function.comp_def, inner_smul_right, qOne_inner_residual,
    div_eq_mul_inv, mul_comm] using ht

/-- Conditional criterion using only a one-sided signed mean. Its smallness is open. -/
theorem cofinal_subharmonic_partialLeakage_mean_iff :
    (∀ ε : ℝ, 0 < ε → ∀ J : ℕ,
      ∃ N : ℕ, J ≤ N ∧ inner ℝ qOne (partialLeakage N) ≤ ε * harmonicMass N) ↔
      qOne ∈ closure := by
  constructor
  · intro h
    by_contra hne
    have hr : 0 < ‖residual‖ ^ 2 := by
      apply pow_pos
      apply norm_pos_iff.mpr
      intro he
      exact hne (Submodule.starProjection_eq_self_iff.mp (sub_eq_zero.mp he).symm)
    have hlim := normalized_partialLeakage_mean_tendsto.eventually
      (lt_mem_nhds (show ‖residual‖ ^ 2 / 2 < ‖residual‖ ^ 2 by linarith))
    have hmass := harmonicMass_tendsto_atTop.eventually (eventually_ge_atTop (1 : ℝ))
    obtain ⟨J, hJ⟩ := eventually_atTop.1 (hlim.and hmass)
    obtain ⟨N, hJN, hN⟩ := h (‖residual‖ ^ 2 / 2) (by positivity) J
    obtain ⟨hl, hm⟩ := hJ N hJN
    have hu := (div_le_iff₀ (show 0 < harmonicMass N by linarith)).mpr hN
    linarith
  · intro hmem ε hε J
    have hz := residue_leakage_vanishes_iff_one_mem.mpr hmem
    refine ⟨J, le_rfl, ?_⟩
    have hn (n : ℕ) : leakage (qResidue (n + 2)) = 0 := hz _ (by omega)
    simp only [partialLeakage, hn, Finset.sum_const_zero, inner_zero_right]
    exact mul_nonneg hε.le (harmonicMass_nonneg J)

/-- The requested vector criterion is equivalent to the one-sided scalar criterion. -/
theorem cofinal_subharmonic_partialLeakage_iff_mean :
    (∀ ε : ℝ, 0 < ε → ∀ J : ℕ,
      ∃ N : ℕ, J ≤ N ∧ ‖partialLeakage N‖ ≤ ε * harmonicMass N) ↔
    (∀ ε : ℝ, 0 < ε → ∀ J : ℕ,
      ∃ N : ℕ, J ≤ N ∧ inner ℝ qOne (partialLeakage N) ≤ ε * harmonicMass N) :=
  cofinal_subharmonic_partialLeakage_iff.trans
    cofinal_subharmonic_partialLeakage_mean_iff.symm

theorem partialLeakage_norm_le_legal_certificate
    (N : ℕ) (f : QHilbert) (hf : f ∈ closure) :
    ‖partialLeakage N‖ ≤ harmonicMass N * ‖qOne - f‖ + centeredBudget := by
  have hp := closureᗮ.norm_starProjection_apply_le (qOne - f)
  rw [map_sub, Submodule.starProjection_orthogonal_apply_eq_zero hf,
    sub_zero, Submodule.starProjection_orthogonal_val] at hp
  have hres : ‖residual‖ ≤ ‖qOne - f‖ := hp
  have hupper := (abs_le.mp (partialLeakage_norm_gap_le N)).2
  have hm := mul_le_mul_of_nonneg_left hres (harmonicMass_nonneg N)
  linarith

/-- A genuine unconditional arithmetic bound from the complete parity competitor.
It gives the coefficient 1/2, not arbitrarily small positive coefficients. -/
theorem partialLeakage_norm_le_half_harmonic_add_budget (N : ℕ) :
    ‖partialLeakage N‖ ≤ harmonicMass N / 2 + centeredBudget := by
  have hg : qResidue 2 ∈ closure :=
    legalSpan.le_topologicalClosure (Submodule.subset_span ⟨0, rfl⟩)
  have hf : ZetaTwoParitySignal.qOdd ∈ closure := closure.smul_mem 2 hg
  have hn : ‖qOne - ZetaTwoParitySignal.qOdd‖ = (1 / 2 : ℝ) := by
    change ‖ZetaTwoParitySignal.qEven‖ = _
    nlinarith [ZetaTwoParitySignal.qEven_norm_sq,
      norm_nonneg ZetaTwoParitySignal.qEven]
  have h := partialLeakage_norm_le_legal_certificate N _ hf
  simpa only [hn, mul_one_div] using h

/-- The requested eventual bound is unconditional for slopes strictly above 1/2.
No assertion is made here for every positive slope. -/
theorem eventually_partialLeakage_norm_le_of_half_lt (ε : ℝ) (hε : 1 / 2 < ε) :
    ∀ᶠ N : ℕ in atTop, ‖partialLeakage N‖ ≤ ε * harmonicMass N := by
  filter_upwards [harmonicMass_tendsto_atTop.eventually
    (eventually_ge_atTop (centeredBudget / (ε - 1 / 2)))] with N hN
  have ht := (div_le_iff₀ (show 0 < ε - 1 / 2 by linarith)).mp hN
  nlinarith [partialLeakage_norm_le_half_harmonic_add_budget N]


/--
info: 'RiemannResearch.RH.QDensityLeakageSeries.harmonicMass_pos' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms harmonicMass_pos

/--
info: 'RiemannResearch.RH.QDensityLeakageSeries.normalized_partialLeakage_error_eq' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms normalized_partialLeakage_error_eq

/--
info: 'RiemannResearch.RH.QDensityLeakageSeries.normalized_partialLeakage_error_norm_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms normalized_partialLeakage_error_norm_le

/--
info: 'RiemannResearch.RH.QDensityLeakageSeries.normalized_partialLeakage_tendsto' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms normalized_partialLeakage_tendsto

/--
info: 'RiemannResearch.RH.QDensityLeakageSeries.normalized_partialLeakage_norm_tendsto' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms normalized_partialLeakage_norm_tendsto

/--
info: 'RiemannResearch.RH.QDensityLeakageSeries.partialLeakage_norm_sq_exact' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms partialLeakage_norm_sq_exact

/--
info: 'RiemannResearch.RH.QDensityLeakageSeries.qOne_inner_residual' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms qOne_inner_residual

/--
info: 'RiemannResearch.RH.QDensityLeakageSeries.partialLeakage_mean_exact' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms partialLeakage_mean_exact

/--
info: 'RiemannResearch.RH.QDensityLeakageSeries.partialLeakage_mean_gap_le' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms partialLeakage_mean_gap_le

/--
info: 'RiemannResearch.RH.QDensityLeakageSeries.normalized_partialLeakage_mean_tendsto' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms normalized_partialLeakage_mean_tendsto

/--
info: 'RiemannResearch.RH.QDensityLeakageSeries.cofinal_subharmonic_partialLeakage_mean_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms cofinal_subharmonic_partialLeakage_mean_iff

/--
info: 'RiemannResearch.RH.QDensityLeakageSeries.cofinal_subharmonic_partialLeakage_iff_mean' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms cofinal_subharmonic_partialLeakage_iff_mean

/--
info: 'RiemannResearch.RH.QDensityLeakageSeries.partialLeakage_norm_le_legal_certificate' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms partialLeakage_norm_le_legal_certificate

/--
info: 'RiemannResearch.RH.QDensityLeakageSeries.partialLeakage_norm_le_half_harmonic_add_budget' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms partialLeakage_norm_le_half_harmonic_add_budget

/--
info: 'RiemannResearch.RH.QDensityLeakageSeries.eventually_partialLeakage_norm_le_of_half_lt' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms eventually_partialLeakage_norm_le_of_half_lt

end RiemannResearch.RH.QDensityLeakageSeries
