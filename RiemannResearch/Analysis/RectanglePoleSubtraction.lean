/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.RH.WeilExplicitFormula.FromPNTPlus.ResidueCalcOnRectangles
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.FunProp
import Mathlib.Tactic.Ring
/-!
# Rectangle primitives and finite residue accounting

A primitive on the boundary suffices to make a rectangle integral vanish;
no holomorphy of the primitive inside the rectangle is assumed. In particular,
a pure inverse-square pole contributes zero. Finite residue limits give a
rectangle formula that includes removable candidate poles.

Source: standard fundamental theorem of calculus and the project's rectangle
residue theorem. The concrete consumer is the double pole in Baluyot,
*On the Zeros of Riemann's Zeta-function* (2017), Lemma 3.1.3, pp. 96–97.
-/

open Complex Set MeasureTheory
noncomputable section
namespace Complex

theorem integral_affine_hasDerivAt {f g : ℂ → ℂ} (u v : ℂ) {a b : ℝ}
    (hd : ∀ t ∈ uIcc a b, HasDerivAt g (f (u + (t : ℂ) * v)) (u + (t : ℂ) * v))
    (hc : ContinuousOn (fun t : ℝ => f (u + (t : ℂ) * v)) (uIcc a b)) :
    v * (∫ t in a..b, f (u + (t : ℂ) * v)) =
      g (u + (b : ℂ) * v) - g (u + (a : ℂ) * v) := by
  rw [← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro t ht
    simpa [Function.comp_def, mul_comm] using
      ((hd t ht).comp (t : ℂ) (((hasDerivAt_id (t : ℂ)).mul_const v).const_add u)).comp_ofReal
  · exact (continuousOn_const.mul hc).intervalIntegrable

theorem rectangleIntegral_eq_zero_of_primitive {f g : ℂ → ℂ} {z w : ℂ}
    (hd : ∀ s ∈ RectangleBorder z w, HasDerivAt g (f s) s)
    (hc : ContinuousOn f (RectangleBorder z w)) :
    RectangleIntegral f z w = 0 := by
  have hbot := integral_affine_hasDerivAt (z.im * I) 1
    (fun t ht => hd _ (by
      simpa [add_comm] using mapsTo_rectangleBorder_left_im z w ht))
    (hc.comp (by fun_prop) (fun t ht => by
      simpa [add_comm] using mapsTo_rectangleBorder_left_im z w ht))
  have htop := integral_affine_hasDerivAt (w.im * I) 1
    (fun t ht => hd _ (by
      simpa [add_comm] using mapsTo_rectangleBorder_right_im z w ht))
    (hc.comp (by fun_prop) (fun t ht => by
      simpa [add_comm] using mapsTo_rectangleBorder_right_im z w ht))
  have hright := integral_affine_hasDerivAt (w.re : ℂ) I
    (fun t ht => hd _ (mapsTo_rectangleBorder_right_re z w ht))
    (hc.comp (by fun_prop) (mapsTo_rectangleBorder_right_re z w))
  have hleft := integral_affine_hasDerivAt (z.re : ℂ) I
    (fun t ht => hd _ (mapsTo_rectangleBorder_left_re z w ht))
    (hc.comp (by fun_prop) (mapsTo_rectangleBorder_left_re z w))
  simp only [mul_one, one_mul, add_comm (↑z.im * I), add_comm (↑w.im * I)] at hbot htop
  simp only [RectangleIntegral, HIntegral, VIntegral, smul_eq_mul,
    hbot, htop, hright, hleft]
  ring

theorem rectangleIntegral_div_sub_sq_eq_zero (A p : ℂ) {z w : ℂ}
    (hp : p ∉ RectangleBorder z w) :
    RectangleIntegral (fun s : ℂ => A / (s - p) ^ 2) z w = 0 := by
  have hn (s : ℂ) (hs : s ∈ RectangleBorder z w) : s - p ≠ 0 := by
    intro he
    exact hp (sub_eq_zero.mp he ▸ hs)
  apply rectangleIntegral_eq_zero_of_primitive
    (g := fun s : ℂ => -A / (s - p))
  · intro s hs
    simpa using! (hasDerivAt_const s (-A)).div
      ((hasDerivAt_id s).sub_const p) (hn s hs)
  · exact continuousOn_const.div
      ((continuousOn_id.sub continuousOn_const).pow 2)
      (fun s hs => pow_ne_zero 2 (hn s hs))
end Complex

open Filter
open scoped Topology BigOperators

namespace Complex
/-- A finite simple-residue limit forces meromorphic order at least minus one. -/
theorem meromorphicOrderAt_ge_neg_one_of_residue_limit {f : ℂ → ℂ} {p c : ℂ}
    (hf : MeromorphicAt f p)
    (hc : Tendsto (fun z : ℂ => (z - p) * f z) (𝓝[≠] p) (𝓝 c)) :
    ((-1 : ℤ) : WithTop ℤ) ≤ meromorphicOrderAt f p := by
  have hs : MeromorphicAt (fun z : ℂ => z - p) p :=
    (analyticAt_id.sub analyticAt_const).meromorphicAt
  have ho := (tendsto_nhds_iff_meromorphicOrderAt_nonneg (hs.mul hf)).mp ⟨c, hc⟩
  rw [meromorphicOrderAt_mul hs hf, meromorphicOrderAt_id_sub_const] at ho
  apply (WithTop.add_le_add_iff_left (show (1 : WithTop ℤ) ≠ ⊤ by simp)).mp
  simpa using ho

/-- Finite rectangle accounting from actual residue limits, allowing removable candidates. -/
theorem rectangleIntegral'_eq_sum_of_residue_limits (f : ℂ → ℂ) {z w : ℂ}
    (hre : z.re ≤ w.re) (him : z.im ≤ w.im) (S : Finset ℂ) (c : ℂ → ℂ)
    (hmero : MeromorphicOn f (Rectangle z w))
    (hS : ∀ p ∈ S, Rectangle z w ∈ 𝓝 p)
    (hoff : ∀ p ∈ Rectangle z w, p ∉ S → AnalyticAt ℂ f p)
    (hlim : ∀ p ∈ S, Tendsto (fun s : ℂ => (s - p) * f s) (𝓝[≠] p) (𝓝 (c p))) :
    RectangleIntegral' f z w = ∑ p ∈ S, c p := by
  classical
  let R : Set ℂ := Rectangle z w
  let P : Set ℂ := {p | meromorphicOrderAt f p < 0}
  have hSIn {p : ℂ} (hp : p ∈ (S : Set ℂ)) : p ∈ R :=
    mem_of_mem_nhds (hS p hp)
  have hsub : R ∩ P ⊆ (S : Set ℂ) := by
    intro p hp
    by_contra hn
    exact not_lt_of_ge (hoff p hp.1 hn).meromorphicOrderAt_nonneg hp.2
  have hnobd : Disjoint (RectangleBorder z w) P := by
    apply Set.disjoint_left.mpr
    intro p hpb hpP
    have hpS := hsub ⟨rectangleBorder_subset_rectangle z w hpb, hpP⟩
    exact not_mem_rectangleBorder_of_rectangle_mem_nhds (hS p hpS) hpb
  have hsimple : HasSimplePolesOn f R := by
    intro p hp
    by_cases hpS : p ∈ S
    · exact meromorphicOrderAt_ge_neg_one_of_residue_limit (hmero p hp) (hlim p hpS)
    · exact le_trans (show ((-1 : ℤ) : WithTop ℤ) ≤ 0 by decide)
        (hoff p hp hpS).meromorphicOrderAt_nonneg
  have hrect := RectangleIntegral'_eq_sumResiduesIn hre him hmero hnobd
    (S.finite_toSet.subset hsub) hsimple
  have hset : R ∩ P = (S : Set ℂ) ∩ P :=
    Set.Subset.antisymm (fun p hp => ⟨hsub hp, hp.2⟩)
      (fun p hp => ⟨hSIn hp.1, hp.2⟩)
  have hsum := sumResiduesIn_inter_eq_of_set_eq (F := f) hset
    (fun p hp hnp => residue_eq_zero_of_not_pole_of_meromorphicAt
      (hmero p (hSIn hp)) (le_of_not_gt hnp))
  rw [hsum] at hrect
  calc
    RectangleIntegral' f z w = sumResiduesIn f (S : Set ℂ) := hrect
    _ = ∑ p ∈ S, residue f p := by
      unfold sumResiduesIn
      exact (tsum_fintype _).trans
        (Finset.sum_subtype (p := fun p : ℂ => p ∈ (S : Set ℂ))
          S (fun p => Iff.rfl) (residue f)).symm
    _ = ∑ p ∈ S, c p := by
      apply Finset.sum_congr rfl
      intro p hp
      apply residue_eq_of_tendsto
      simpa only [smul_eq_mul] using hlim p hp
end Complex
