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
No bound on these actual sums, vanishing of r, or unconditional RH proof is
asserted. No RH-to-density analytic converse is used.
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

end RiemannResearch.RH.QDensityLeakageSeries
