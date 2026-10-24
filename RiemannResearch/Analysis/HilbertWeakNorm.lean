import RiemannResearch.Analysis.NonnegativeErrorConvergence
import Mathlib.Analysis.InnerProductSpace.Projection.Submodule
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Hilbert weak convergence, target pairing, and strong convergence

Source: user-requested fifth Ramanujan transfer program, 24 October 2026.
The norm identity retains the signed target pairing. A one-sided asymptotic
norm bound is enough to upgrade weak convergence to strong convergence.
-/

noncomputable section
open Filter
open scoped Topology
namespace RiemannResearch.Analysis.HilbertWeakNorm
open NonnegativeErrorConvergence
variable {H α : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] {l : Filter α}

def InnerWeakTendsto (F : α → H) (l : Filter α) (x : H) : Prop :=
  ∀ v : H, Tendsto (fun i => inner ℝ v (F i)) l (𝓝 (inner ℝ v x))

theorem norm_error_pairing_identity (x y : H) :
    ‖y - x‖ ^ 2 = ‖y‖ ^ 2 + ‖x‖ ^ 2 - 2 * inner ℝ x y := by
  rw [norm_sub_sq_real, real_inner_comm] <;> ring

/-- One signed target moment and norm convergence already suffice. -/
theorem tendsto_iff_norm_sq_and_target_pairing (F : α → H) (x : H) :
    Tendsto F l (𝓝 x) ↔
      Tendsto (fun i => ‖F i‖ ^ 2) l (𝓝 (‖x‖ ^ 2)) ∧
      Tendsto (fun i => inner ℝ x (F i)) l (𝓝 (‖x‖ ^ 2)) := by
  constructor
  · intro h
    refine ⟨h.norm.pow 2, ?_⟩
    have hi : Tendsto (fun i => inner ℝ x (F i)) l (𝓝 (inner ℝ x x)) :=
      ((innerSL ℝ x).continuous.tendsto x).comp h
    simpa only [real_inner_self_eq_norm_sq] using hi
  · rintro ⟨hn, hp⟩
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    apply (norm_zero_iff_square (l := l) (fun i => F i - x)).mpr
    have h := (hn.add_const (‖x‖ ^ 2)).sub (hp.const_mul 2)
    convert h using 1
    · funext i
      exact norm_error_pairing_identity x (F i)
    · ring

theorem tendsto_iff_innerWeak_and_norm_sq (F : α → H) (x : H) :
    Tendsto F l (𝓝 x) ↔ InnerWeakTendsto F l x ∧
      Tendsto (fun i => ‖F i‖ ^ 2) l (𝓝 (‖x‖ ^ 2)) := by
  constructor
  · intro h
    refine ⟨?_, h.norm.pow 2⟩
    intro v
    exact ((innerSL ℝ v).continuous.tendsto x).comp h
  · rintro ⟨hw, hn⟩
    apply (tendsto_iff_norm_sq_and_target_pairing (l := l) F x).mpr
    exact ⟨hn, by simpa only [real_inner_self_eq_norm_sq] using hw x⟩

/-- A limsup norm bound suffices; no norm-limit hypothesis is required. -/
theorem tendsto_of_target_pairing_and_norm_upper (F : α → H) (x : H)
    (hp : Tendsto (fun i => inner ℝ x (F i)) l (𝓝 (‖x‖ ^ 2)))
    (hn : ∀ ε : ℝ, 0 < ε → ∀ᶠ i in l, ‖F i‖ ^ 2 < ‖x‖ ^ 2 + ε) :
    Tendsto F l (𝓝 x) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply (norm_zero_iff_square (l := l) (fun i => F i - x)).mpr
  apply tendsto_order.2
  constructor
  · intro b hb
    exact Eventually.of_forall (fun i => lt_of_lt_of_le hb (sq_nonneg _))
  · intro ε hε
    have hu := hn (ε / 4) (by linarith)
    have hl := Filter.Tendsto.eventually_const_lt
      (show ‖x‖ ^ 2 - ε / 4 < ‖x‖ ^ 2 by linarith) hp
    filter_upwards [hu, hl] with i hi hpi
    rw [norm_error_pairing_identity]
    linarith

theorem tendsto_of_innerWeak_and_norm_upper (F : α → H) (x : H)
    (hw : InnerWeakTendsto F l x)
    (hn : ∀ ε : ℝ, 0 < ε → ∀ᶠ i in l, ‖F i‖ ^ 2 < ‖x‖ ^ 2 + ε) :
    Tendsto F l (𝓝 x) :=
  tendsto_of_target_pairing_and_norm_upper (l := l) F x
    (by simpa only [real_inner_self_eq_norm_sq] using hw x) hn

/-- Weak limits of eventually legal vectors remain in the norm-closed legal span. -/
theorem mem_closure_of_innerWeak [CompleteSpace H] [NeBot l]
    (S : Submodule ℝ H) (F : α → H) (x : H)
    (hF : ∀ᶠ i in l, F i ∈ S) (hw : InnerWeakTendsto F l x) :
    x ∈ S.topologicalClosure := by
  rw [← Submodule.orthogonal_orthogonal_eq_closure]
  apply (Submodule.mem_orthogonal _ x).mpr
  intro v hv
  have he : (fun i => inner ℝ v (F i)) =ᶠ[l] (fun _ => (0 : ℝ)) := by
    filter_upwards [hF] with i hi
    exact (Submodule.mem_orthogonal' _ v).mp hv (F i) hi
  have hz : Tendsto (fun i => inner ℝ v (F i)) l (𝓝 0) :=
    tendsto_const_nhds.congr' he.symm
  exact tendsto_nhds_unique (hw v) hz

end RiemannResearch.Analysis.HilbertWeakNorm
