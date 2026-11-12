import RiemannResearch.RH.QReciprocalCostEquivalence
import RiemannResearch.RH.QCanonicalMobiusCost
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Cofinal complete-cost and canonical-energy criteria

A fixed complete-cost bound is needed only at cofinally many indices. The closure equivalence and conditional RH consumers leave their arithmetic bounds as explicit hypotheses. Failure of RH forces the actual canonical source energies to tend to infinity.

Research agenda: D_Residue_Density_PQ_Nyman_Beurling_2026-11-11.pdf, Section 9.
-/

noncomputable section
open Filter
open scoped Topology
namespace RiemannResearch.RH.QReciprocalCofinalCost
open ZetaTwoHilbert ZetaTwoProbability QReciprocalCostEquivalence

theorem mem_closure_of_cofinal_cost (S : Submodule ℝ QHilbert) (x : QHilbert)
    (reg : ℕ → ℝ) (hr : ∀ j, 0 < reg j) (hr0 : Tendsto reg atTop (𝓝 0))
    (F : ℕ → QHilbert) (hm : ∀ j, F j ∈ S)
    (C : ℝ) (hC : 0 ≤ C)
    (hc : ∀ N, ∃ j, N ≤ j ∧ cost (reg j) x (F j) ≤ C * reg j) :
    x ∈ S.topologicalClosure := by
  choose φ hφge hφbound using hc
  have hφ : Tendsto φ atTop atTop := tendsto_atTop_mono hφge tendsto_id
  exact mem_closure_of_cost_bound S x (reg ∘ φ) (fun j => hr (φ j))
    (hr0.comp hφ) C hC (F ∘ φ) (fun j => hm (φ j)) hφbound

theorem mem_closure_iff_cofinal_cost (S : Submodule ℝ QHilbert) (x : QHilbert)
    (reg : ℕ → ℝ) (hr : ∀ j, 0 < reg j) (hr0 : Tendsto reg atTop (𝓝 0)) :
    x ∈ S.topologicalClosure ↔
    ∃ C : ℝ, 0 ≤ C ∧ ∃ F : ℕ → QHilbert, (∀ j, F j ∈ S) ∧
      ∀ N, ∃ j, N ≤ j ∧ cost (reg j) x (F j) ≤ C * reg j := by
  constructor
  · intro hx
    obtain ⟨C,hC,F,hm,hb⟩ :=
      (mem_closure_iff_regularized_cost S x reg hr hr0).mp hx
    exact ⟨C,hC,F,hm,fun N => ⟨N,le_rfl,hb N⟩⟩
  · rintro ⟨C,hC,F,hm,hb⟩
    exact mem_closure_of_cofinal_cost S x reg hr hr0 F hm C hC hb

theorem riemannHypothesis_of_cofinal_cost
    (reg : ℕ → ℝ) (hr : ∀ j, 0 < reg j) (hr0 : Tendsto reg atTop (𝓝 0))
    (F : ℕ → QHilbert) (hm : ∀ j, F j ∈ QFullResidueProjection.legalSpan)
    (C : ℝ) (hC : 0 ≤ C)
    (hc : ∀ N, ∃ j, N ≤ j ∧ cost (reg j) qOne (F j) ≤ C * reg j) :
    RiemannHypothesis := by
  exact QFullResidueProjection.riemannHypothesis_of_qOne_mem_full_closure
    (mem_closure_of_cofinal_cost _ qOne reg hr hr0 F hm C hC hc)

theorem riemannHypothesis_of_cofinal_canonical_energy
    (C : ℝ) (hC : 0 ≤ C)
    (hE : ∀ N : ℕ, ∃ H : ℕ, N ≤ H ∧ 0 < H ∧
      ‖Pareto.canonicalMobiusHilbert H‖^2 ≤ C) : RiemannHypothesis := by
  choose H hHge hHpos hHb using hE
  have hHt : Tendsto H atTop atTop := tendsto_atTop_mono hHge tendsto_id
  have hHR : ∀ j, (0 : ℝ) < H j := fun j => by exact_mod_cast hHpos j
  have hr0 : Tendsto (fun j => ((H j : ℝ)^2)⁻¹) atTop (𝓝 0) := by
    have ht := (tendsto_inv_atTop_zero.comp
      ((tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop).comp hHt)).pow 2
    simpa only [Function.comp_def, inv_pow, zero_pow (by decide : 2 ≠ 0)] using ht
  apply QFullResidueProjection.riemannHypothesis_of_qOne_mem_full_closure
  apply mem_closure_of_cost_bound QFullResidueProjection.legalSpan qOne
    (fun j => ((H j : ℝ)^2)⁻¹) (fun j => inv_pos.mpr (sq_pos_of_pos (hHR j))) hr0
    ((4/zetaTwo)*C) (by positivity [zetaTwo_pos]) (fun j => QMobiusExactHead.exactHead (H j))
    (fun j => QMobiusExactHead.exactHead_mem_legalSpan _)
  intro j
  calc
    _ ≤ (4/zetaTwo)*((H j : ℝ)^2)⁻¹*‖Pareto.canonicalMobiusHilbert (H j)‖^2 :=
      QCanonicalMobiusCost.balanced_cost_source_upper (H j) (hHpos j)
    _ ≤ (4/zetaTwo)*((H j : ℝ)^2)⁻¹*C :=
      mul_le_mul_of_nonneg_left (hHb j) (by positivity [zetaTwo_pos])
    _ = _ := by ring

theorem canonical_energy_diverges_of_not_RH (hRH : ¬RiemannHypothesis) :
    Tendsto (fun H : ℕ => ‖Pareto.canonicalMobiusHilbert H‖^2) atTop atTop := by
  apply tendsto_atTop.mpr
  intro C
  by_contra h
  have hf : ∀ N : ℕ, ∃ H : ℕ, max N 1 ≤ H ∧
      ‖Pareto.canonicalMobiusHilbert H‖^2 < C := by
    intro N
    by_contra hn
    apply h
    apply eventually_atTop.mpr
    refine ⟨max N 1, fun H hH => ?_⟩
    by_contra hHC
    exact hn ⟨H,hH,lt_of_not_ge hHC⟩
  apply hRH
  apply riemannHypothesis_of_cofinal_canonical_energy (max C 0) (le_max_right _ _)
  intro N
  obtain ⟨H,hH,hE⟩ := hf N
  exact ⟨H,(le_max_left N 1).trans hH, by omega,hE.le.trans (le_max_left C 0)⟩

end RiemannResearch.RH.QReciprocalCofinalCost
