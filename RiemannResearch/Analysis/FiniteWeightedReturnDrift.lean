import RiemannResearch.Analysis.FiniteWeightedSpan
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic

/-!
# Endpoint drift for weighted prefix/tail regression
Source: user-provided audited Exact-Head Green Profiles, sections 21--23,
especially (23.5)--(23.8) and Proposition 23.9.
The statements below use finite weighted normal equations directly. They
therefore do not require an invertible design or a choice of coordinates.
No asymptotic estimate for the arithmetic target is assumed or concluded.
PDF: https://drive.google.com/file/d/1DHIp4gGwApIL1V6nHwV4HDxuOAFdijwG/view
-/
noncomputable section
open scoped BigOperators
namespace RiemannResearch.Analysis.FiniteWeightedReturnDrift
open FiniteProfileEnergy
variable {ι κ : Type*}

theorem endpoint_covariance (L T : Finset ι) (w C u v : ι → ℝ)
    (V : Submodule ℝ (ι → ℝ))
    (hglobal : ∀ f ∈ V, pairing L w (C - u) f + pairing T w (C - u) f = 0)
    (htail : ∀ f ∈ V, pairing T w (C - v) f = 0)
    (f : ι → ℝ) (hf : f ∈ V) :
    pairing L w (C - u) f = pairing T w (u - v) f := by
  have he : pairing T w (C - u) f =
      pairing T w (C - v) f - pairing T w (u - v) f := by
    unfold pairing
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    simp only [Pi.sub_apply]
    ring
  have h := hglobal f hf
  rw [he, htail f hf] at h
  linarith

/-- The energy charged to returns is the extension energy minus its prefix part.
This holds even for singular designs and signed weights; nonnegativity is needed
only when turning the equality into an inequality. -/
theorem endpoint_energy (L T : Finset ι) (w C u v : ι → ℝ)
    (V : Submodule ℝ (ι → ℝ)) (hu : u ∈ V) (hv : v ∈ V)
    (htail : ∀ f ∈ V, pairing T w (C - v) f = 0) :
    energy L w (C - u) + energy T w (C - u) =
      energy T w (C - v) + energy L w (C - u) + energy T w (u - v) := by
  have he : C - u = (C - v) + (v - u) := by abel
  have hc := normal_completion_on_span T w (C - v) V htail (v - u) (V.sub_mem hv hu)
  have hn : energy T w (v - u) = energy T w (u - v) := by
    unfold energy
    apply Finset.sum_congr rfl
    intro i hi
    simp only [Pi.sub_apply]
    ring
  have ht : energy T w (C - u) = energy T w (C - v) + energy T w (u - v) := by
    conv_lhs => rw [he]
    exact hc.trans (by rw [hn])
  rw [ht]
  ring

/-- Every return covariance can be computed from the signed prefix moment. -/
theorem curvature_energy_eq_prefix (L T : Finset ι) (w C u v : ι → ℝ)
    (V : Submodule ℝ (ι → ℝ))
    (hglobal : ∀ f ∈ V, pairing L w (C - u) f + pairing T w (C - u) f = 0)
    (htail : ∀ f ∈ V, pairing T w (C - v) f = 0)
    (D : Finset κ) (a : κ → ℝ) (F : κ → ι → ℝ)
    (hF : ∀ j ∈ D, F j ∈ V) :
    (∑ j ∈ D, a j * pairing T w (u - v) (F j)^2) =
      ∑ j ∈ D, a j * pairing L w (C - u) (F j)^2 := by
  apply Finset.sum_congr rfl
  intro j hj
  rw [endpoint_covariance L T w C u v V hglobal htail (F j) (hF j hj)]

/-- Path independence of any verified sequence of coefficient increments. -/
theorem signed_update_telescope {E : Type*} [AddCommGroup E]
    (c step : ℕ → E) (N : ℕ)
    (hstep : ∀ k < N, step k = c k - c (k + 1)) :
    (∑ k ∈ Finset.range N, step k) = c 0 - c N := by
  calc
    _ = ∑ k ∈ Finset.range N, (c k - c (k + 1)) :=
      Finset.sum_congr rfl (fun k hk => hstep k (Finset.mem_range.mp hk))
    _ = _ := by
      clear hstep
      induction N with
      | zero => simp
      | succ n ih => rw [Finset.sum_range_succ, ih]; abel

/-- A zero-mean/independent-increment interpretation is not a consequence of
normal equations: every feasible prefix/return pair is realized by an actual
least-squares target with zero global fitted component. -/
theorem accessible_drift_realized
    (L T : Finset ι) (hLT : Disjoint L T) (w h d : ι → ℝ)
    (V : Submodule ℝ (ι → ℝ)) (hd : d ∈ V)
    (hcov : ∀ f ∈ V, pairing L w h f = pairing T w d f) :
    ∃ C : ι → ℝ,
      (∀ i ∈ L, C i = h i) ∧
      (∀ i ∈ T, C i = -d i) ∧
      (∀ f ∈ V, pairing L w C f + pairing T w C f = 0) ∧
      (-d ∈ V) ∧
      (∀ f ∈ V, pairing T w (C - (-d)) f = 0) ∧
      (0 : ι → ℝ) - (-d) = d := by
  classical
  let C : ι → ℝ := fun i => if i ∈ L then h i else -d i
  have hL : ∀ i ∈ L, C i = h i := by intro i hi; simp [C,hi]
  have hT : ∀ i ∈ T, C i = -d i := by
    intro i hi
    have hn : i ∉ L := fun hl => (Finset.disjoint_left.mp hLT) hl hi
    simp [C,hn]
  refine ⟨C,hL,hT,?_,V.neg_mem hd,?_,by simp⟩
  · intro f hf
    have heL : pairing L w C f = pairing L w h f :=
      Finset.sum_congr rfl (fun i hi => by rw [hL i hi])
    have heT : pairing T w C f = -pairing T w d f := by
      unfold pairing
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      rw [hT i hi]
      ring
    rw [heL,heT,hcov f hf]
    ring
  · intro f hf
    apply Finset.sum_eq_zero
    intro i hi
    simp [Pi.sub_apply, hT i hi]

/-- Sherman--Morrison at the level of the normal equation. No matrix inverse
or positive-definiteness hypothesis is needed for this exact update. -/
theorem rank_one_normal_update {E : Type*} [AddCommGroup E] [Module ℝ E]
    (A : E →ₗ[ℝ] E) (ell : E →ₗ[ℝ] ℝ) (u x v b : E) (w y : ℝ)
    (hu : A u = x) (hv : A v = b) (hden : 1 + w * ell u ≠ 0) :
    let c := w * (y - ell v) / (1 + w * ell u)
    A (v + c • u) + (w * ell (v + c • u)) • x = b + (w * y) • x := by
  dsimp only
  let c := w * (y - ell v) / (1 + w * ell u)
  have hc : c + w * (ell v + c * ell u) = w * y := by
    dsimp [c]
    field_simp
    <;> ring
  change A (v + c • u) + (w * ell (v + c • u)) • x = _
  simp only [map_add, map_smul, hu, hv, smul_eq_mul]
  calc
    _ = b + (c + w * (ell v + c * ell u)) • x := by module
    _ = _ := by rw [hc]

end RiemannResearch.Analysis.FiniteWeightedReturnDrift
