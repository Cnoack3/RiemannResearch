import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Abel

/-!
# Bounded exact interpolation and Pythagorean convergence

Source: user-provided request, September 9, 2026, to use exact Pythagoras
for the Nyman-Pareto legal span. This is a standard Hilbert-space argument:
minimum-norm exact interpolants converge strongly when their norms stay
bounded. Its concrete consumer is RH.ThresholdBoundedInterpolation.

The uniform interpolation bound is an explicit hypothesis, not a proved
arithmetic estimate. All projections below are onto actual closed subspaces.
-/

open Filter
open scoped Topology

namespace RiemannResearch.Analysis.BoundedInterpolation

/-- Exact increments and a bounded monotone energy force a Cauchy sequence. -/
theorem cauchySeq_of_bounded_exact_energy {X : Type*} [PseudoMetricSpace X]
    (u : ℕ → X) (E : ℕ → ℝ)
    (hpyth : ∀ n m, n ≤ m → dist (u m) (u n)^2 = E m - E n)
    (hbdd : BddAbove (Set.range E)) : CauchySeq u := by
  have hmono : Monotone E := by
    intro n m hnm
    have he := hpyth n m hnm
    nlinarith [sq_nonneg (dist (u m) (u n))]
  have hcE : CauchySeq E := (tendsto_atTop_ciSup hmono hbdd).cauchySeq
  rw [Metric.cauchySeq_iff'] at hcE ⊢
  intro ε hε
  obtain ⟨N, hN⟩ := hcE (ε^2) (sq_pos_of_pos hε)
  refine ⟨N, fun n hn => ?_⟩
  have hsq : dist (u n) (u N)^2 < ε^2 := by
    rw [hpyth N n hn]
    exact (le_abs_self _).trans_lt (by simpa [Real.dist_eq] using hN n hn)
  exact (sq_lt_sq₀ dist_nonneg hε.le).mp hsq

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]


/-- Legal directions that leave the first finitely many observations unchanged. -/
def headNull (V : Submodule ℝ H) (ℓ : ℕ → H →L[ℝ] ℝ) (N : ℕ) :
    Submodule ℝ H where
  carrier := {v | v ∈ V ∧ ∀ k ≤ N, ℓ k v = 0}
  zero_mem' := ⟨V.zero_mem, by simp⟩
  add_mem' := by
    rintro x y ⟨hxV, hx⟩ ⟨hyV, hy⟩
    exact ⟨V.add_mem hxV hyV, by intro k hk; simp [map_add, hx k hk, hy k hk]⟩
  smul_mem' := by
    rintro c x ⟨hxV, hx⟩
    exact ⟨V.smul_mem c hxV, by intro k hk; simp [map_smul, hx k hk]⟩

/-- Continuous observations cut out a closed subspace of a closed legal space. -/
theorem headNull_isClosed (V : Submodule ℝ H) (hV : IsClosed (V : Set H))
    (ℓ : ℕ → H →L[ℝ] ℝ) (N : ℕ) :
    IsClosed (headNull V ℓ N : Set H) := by
  have hs : (headNull V ℓ N : Set H) =
      (V : Set H) ∩ ⋂ k, ⋂ (_ : k ≤ N), {v | ℓ k v = 0} := by
    ext v
    simp [headNull]
  rw [hs]
  exact hV.inter (isClosed_iInter fun k =>
    isClosed_iInter fun _ => isClosed_eq (ℓ k).continuous continuous_const)

/-- Remove the projection onto zero-head legal directions. The result has the
same head, no larger norm, and is orthogonal to every admissible correction. -/
theorem exists_minimum_head [CompleteSpace H] (V : Submodule ℝ H) (hV : IsClosed (V : Set H))
    (ℓ : ℕ → H →L[ℝ] ℝ) (N : ℕ) (f : H) (hf : f ∈ V) :
    ∃ v : H, v ∈ V ∧ (∀ k ≤ N, ℓ k v = ℓ k f) ∧ ‖v‖ ≤ ‖f‖ ∧
      ∀ t ∈ headNull V ℓ N, inner ℝ v t = 0 := by
  let K := headNull V ℓ N
  have : IsClosed (K : Set H) := headNull_isClosed V hV ℓ N
  have : CompleteSpace K := inferInstance
  have hP : K.starProjection f ∈ K := by
    rw [Submodule.starProjection_apply]
    exact (K.orthogonalProjectionOnto f).property
  refine ⟨f - K.starProjection f, V.sub_mem hf hP.1, ?_, ?_, ?_⟩
  · intro k hk
    simp only [map_sub, hP.2 k hk, sub_zero]
  · rw [← Submodule.starProjection_orthogonal_val]
    exact Kᗮ.norm_starProjection_apply_le f
  · intro t ht
    rw [real_inner_comm]
    exact (K.mem_orthogonal _).1
      (Submodule.sub_starProjection_mem_orthogonal f) t ht

/-- Exact completion of the norm at a minimum-head interpolant. -/
theorem minimum_head_pythagoras (V : Submodule ℝ H) (ℓ : ℕ → H →L[ℝ] ℝ)
    (N : ℕ) (v f : H) (hv : v ∈ V) (hf : f ∈ V)
    (hhead : ∀ k ≤ N, ℓ k f = ℓ k v)
    (horth : ∀ t ∈ headNull V ℓ N, inner ℝ v t = 0) :
    ‖f‖^2 = ‖v‖^2 + ‖f - v‖^2 := by
  have ht : f - v ∈ headNull V ℓ N :=
    ⟨V.sub_mem hf hv, by intro k hk; simp [map_sub, hhead k hk]⟩
  have he := norm_add_sq_eq_norm_sq_add_norm_sq_real (horth (f-v) ht)
  have hvf : v + (f-v) = f := by abel
  simpa only [hvf, ← pow_two] using he

/-- Bounded exact interpolation gives strong approximation, with an exact
squared-error identity. The bound on interpolants remains an explicit input. -/
theorem exists_exact_heads_tendsto_of_bounded [CompleteSpace H]
    (V : Submodule ℝ H) (hV : IsClosed (V : Set H))
    (ℓ : ℕ → H →L[ℝ] ℝ)
    (hsep : Function.Injective (fun x : H => fun k => ℓ k x))
    (z : H) (C : ℝ)
    (hbounded : ∀ N, ∃ f : H, f ∈ V ∧
      (∀ k ≤ N, ℓ k f = ℓ k z) ∧ ‖f‖^2 ≤ C) :
    ∃ v : ℕ → H, (∀ N, v N ∈ V ∧ ∀ k ≤ N, ℓ k (v N) = ℓ k z) ∧
      Tendsto v atTop (𝓝 z) ∧
      ∀ N, ‖z - v N‖^2 = ‖z‖^2 - ‖v N‖^2 := by
  choose f hfV hfhead hfbound using hbounded
  choose v hvV hvhead hvnorm hvorth using
    fun N => exists_minimum_head V hV ℓ N (f N) (hfV N)
  have hvheadz : ∀ N k, k ≤ N → ℓ k (v N) = ℓ k z := by
    intro N k hk
    exact (hvhead N k hk).trans (hfhead N k hk)
  have henergy : ∀ n m, n ≤ m →
      dist (v m) (v n)^2 = ‖v m‖^2 - ‖v n‖^2 := by
    intro n m hnm
    have he := minimum_head_pythagoras V ℓ n (v n) (v m) (hvV n) (hvV m)
      (by intro k hk; rw [hvheadz m k (hk.trans hnm), hvheadz n k hk]) (hvorth n)
    rw [dist_eq_norm]
    linarith
  have hb : BddAbove (Set.range (fun N => ‖v N‖^2)) := by
    refine ⟨C, ?_⟩
    rintro _ ⟨N, rfl⟩
    exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).2 (hvnorm N) |>.trans (hfbound N)
  obtain ⟨w, hw⟩ := cauchySeq_tendsto_of_complete
    (cauchySeq_of_bounded_exact_energy v (fun N => ‖v N‖^2) henergy hb)
  have hwV : w ∈ V := hV.mem_of_tendsto hw (Eventually.of_forall hvV)
  have hwz : w = z := by
    apply hsep
    funext k
    have hcoord := ((ℓ k).continuous.tendsto w).comp hw
    have hevent : (fun N => ℓ k (v N)) =ᶠ[atTop] (fun _ => ℓ k z) :=
      eventually_atTop.2 ⟨k, fun N hN => hvheadz N k hN⟩
    exact tendsto_nhds_unique hcoord (tendsto_const_nhds.congr' hevent.symm)
  have hzV : z ∈ V := by simpa only [hwz] using hwV
  refine ⟨v, fun N => ⟨hvV N, hvheadz N⟩, ?_, ?_⟩
  · simpa only [hwz] using hw
  · intro N
    have he := minimum_head_pythagoras V ℓ N (v N) z (hvV N) hzV
      (by intro k hk; exact (hvheadz N k hk).symm) (hvorth N)
    linarith

/-- Closed-space membership follows from bounded exact interpolation for
continuous observations that separate points. -/
theorem mem_of_bounded_exact_interpolation [CompleteSpace H]
    (V : Submodule ℝ H) (hV : IsClosed (V : Set H))
    (ℓ : ℕ → H →L[ℝ] ℝ)
    (hsep : Function.Injective (fun x : H => fun k => ℓ k x))
    (z : H) (C : ℝ)
    (hbounded : ∀ N, ∃ f : H, f ∈ V ∧
      (∀ k ≤ N, ℓ k f = ℓ k z) ∧ ‖f‖^2 ≤ C) : z ∈ V := by
  obtain ⟨v, hv, htend, _⟩ :=
    exists_exact_heads_tendsto_of_bounded V hV ℓ hsep z C hbounded
  exact hV.mem_of_tendsto htend (Eventually.of_forall fun N => (hv N).1)

end RiemannResearch.Analysis.BoundedInterpolation
