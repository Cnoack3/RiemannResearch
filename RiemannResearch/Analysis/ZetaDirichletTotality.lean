import RiemannResearch.Analysis.ZetaDirichletKernel
import Mathlib.NumberTheory.LSeries.Injectivity
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
/-!
# Totality of the actual zeta evaluation vectors
Source: V_vector_space_RH.pdf, Section 5, Dirichlet-series uniqueness argument.
Mathlib's proved L-series injectivity implies that the orthogonal complement
of the half-plane feature family is zero. Thus its closed span is all l2.
-/
noncomputable section
open Filter
open scoped Topology BigOperators
namespace RiemannResearch.Analysis.ZetaDirichletKernel
abbrev Space := lp (fun _ : ℕ => ℂ) 2

def shifted (a : Space) : ℕ → ℂ
  | 0 => 0
  | n + 1 => a n

theorem shifted_term (a : Space) (s : ℂ) (n : ℕ) :
    LSeries.term (shifted a) s (n+1) = a n * feature s n := by
  rw [LSeries.term_of_ne_zero (Nat.succ_ne_zero n), shifted, feature_eq_cpow]
  push_cast
  ring

theorem shifted_summable (a : Space) (s : ℂ) (hs : 1 / 2 < s.re) :
    LSeriesSummable (shifted a) s := by
  apply (summable_nat_add_iff 1).mp
  simpa only [shifted_term] using (dirichlet_series_hasSum a s hs).summable

theorem shifted_LSeries (a : Space) (s : ℂ) (hs : 1 / 2 < s.re) :
    LSeries (shifted a) s = ∑' n, a n * feature s n := by
  rw [LSeries, (shifted_summable a s hs).tsum_eq_zero_add]
  simp only [LSeries.term_zero, shifted_term, zero_add]

theorem eq_zero_of_orthogonal_features (a : Space)
    (h : ∀ (s : ℂ) (hs : 1 / 2 < s.re), inner ℂ (vector s hs) a = 0) : a = 0 := by
  have habs : LSeries.abscissaOfAbsConv (shifted a) < ⊤ :=
    (shifted_summable a 2 (by norm_num)).abscissaOfAbsConv_le.trans_lt (EReal.coe_lt_top _)
  have hz : (fun x : ℝ => LSeries (shifted a) x) =ᶠ[atTop] 0 := by
    filter_upwards [eventually_gt_atTop (1 / 2 : ℝ)] with x hx
    rw [shifted_LSeries a x (by simpa using hx),
      (dirichlet_series_hasSum a x (by simpa using hx)).tsum_eq]
    exact h _ _
  have hc := (LSeries_eventually_eq_zero_iff'.mp hz).resolve_right (ne_of_lt habs)
  apply lp.ext
  funext n
  exact hc (n+1) (Nat.succ_ne_zero n)

theorem span_features_dense :
    (Submodule.span ℂ (Set.range (fun s : {s : ℂ // 1 / 2 < s.re} =>
      vector s.val s.property))).topologicalClosure = ⊤ := by
  let S := Submodule.span ℂ (Set.range (fun s : {s : ℂ // 1 / 2 < s.re} =>
      vector s.val s.property))
  have ho : Sᗮ = ⊥ := by
    apply le_antisymm
    · intro a ha
      change a = 0
      apply eq_zero_of_orthogonal_features
      intro s hs
      exact ha _ (Submodule.subset_span ⟨⟨s,hs⟩,rfl⟩)
    · exact bot_le
  rw [← Submodule.orthogonal_orthogonal_eq_closure, ho, Submodule.bot_orthogonal_eq_top]
end RiemannResearch.Analysis.ZetaDirichletKernel
