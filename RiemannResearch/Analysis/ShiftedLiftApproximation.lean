import RiemannResearch.Analysis.ShiftedLift
import RiemannResearch.Analysis.ExhaustiveProjectionWalk

/-!
# Finite regularized shifted approximation

Source: the user-requested continuation of the shifted-lift program in
RH/ActualResidualRegularityRoutes20260924.md, Route 3, and commit 8a7abbde.
The arguments are elementary Hilbert-space and finite-dimensional
minimization arguments; no novelty is asserted. The concrete arithmetic
consumer is RH/NoorRegularizedApproximation.

Density of the differenced dictionary implies vanishing unscaled finite
minima for any parameter sequence tending to zero. It supplies no rate
relative to that parameter. Positive regularization also gives attainment
without an external normal-equation provider.
-/

noncomputable section
open Filter
open scoped Topology

namespace RiemannResearch.Analysis.ShiftedLift
open ExhaustiveWalk
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- The infimum over the complete lift norm; finite-dimensional attainment is
proved below for positive regularization. -/
def regularizedInf (S : H →ₗ[ℝ] H) (a : H) (t : ℝ)
    (V : Submodule ℝ H) : ℝ :=
  sInf {E : ℝ | ∃ v ∈ V, regularizedEnergy S a t v = E}

theorem regularizedEnergy_nonneg (S : H →ₗ[ℝ] H) (a : H) (t : ℝ) (v : H) :
    0 ≤ regularizedEnergy S a t v := by
  unfold regularizedEnergy
  positivity

theorem regularizedInf_nonneg (S : H →ₗ[ℝ] H) (a : H) (t : ℝ) (V : Submodule ℝ H) :
    0 ≤ regularizedInf S a t V := by
  apply le_csInf
  · exact ⟨_, 0, V.zero_mem, rfl⟩
  · rintro E ⟨v, hv, rfl⟩
    exact regularizedEnergy_nonneg S a t v

theorem regularizedInf_le (S : H →ₗ[ℝ] H) (a : H) (t : ℝ)
    (V : Submodule ℝ H) (v : H) (hv : v ∈ V) :
    regularizedInf S a t V ≤ regularizedEnergy S a t v := by
  apply csInf_le
  · exact ⟨0, by rintro E ⟨w, hw, rfl⟩; exact regularizedEnergy_nonneg S a t w⟩
  · exact ⟨v, hv, rfl⟩

/-- Dense differenced finite spaces give vanishing unscaled infima for every
vanishing parameter schedule and every convergent target sequence. No bound
on the norms of the approximating lifts is assumed or obtained. -/
theorem regularizedInf_tendsto_zero
    (S : H →ₗ[ℝ] H) (V : ℕ → Submodule ℝ H) (hV : Monotone V)
    (a : H) (hdense : ∀ ε : ℝ, 0 < ε →
      ∃ N, ∃ v ∈ V N, ‖difference S v - a‖ < ε)
    (aN : ℕ → H) (ha : Tendsto aN atTop (𝓝 a))
    (t : ℕ → ℝ) (ht : Tendsto t atTop (𝓝 0)) :
    Tendsto (fun N => regularizedInf S (aN N) (t N) (V N)) atTop (𝓝 0) := by
  apply tendsto_order.mpr
  constructor
  · intro b hb
    exact Filter.Eventually.of_forall (fun N =>
      lt_of_lt_of_le hb (regularizedInf_nonneg S (aN N) (t N) (V N)))
  · intro ε hε
    obtain ⟨M, v, hv, he⟩ := hdense (Real.sqrt (ε / 2)) (Real.sqrt_pos.2 (by linarith))
    have he2 : ‖difference S v - a‖ ^ 2 < ε := by
      have hs := Real.sq_sqrt (show 0 ≤ ε / 2 by linarith)
      nlinarith [norm_nonneg (difference S v - a), Real.sqrt_nonneg (ε / 2)]
    have hlim : Tendsto (fun N => regularizedEnergy S (aN N) (t N) v)
        atTop (𝓝 (‖difference S v - a‖ ^ 2)) := by
      simpa only [regularizedEnergy, zero_pow (by decide : 2 ≠ 0), zero_mul, add_zero] using
        ((tendsto_const_nhds.sub ha).norm.pow 2).add ((ht.pow 2).mul_const (‖v‖ ^ 2))
    filter_upwards [eventually_ge_atTop M, (tendsto_order.mp hlim).2 ε he2] with N hN hE
    exact lt_of_le_of_lt (regularizedInf_le S (aN N) (t N) (V N) v (hV hN hv)) hE
/-- Every algebraic combination of differenced atoms lifts at a finite stage. -/
theorem span_difference_has_finite_lift (S : H →ₗ[ℝ] H) (u : ℕ → H)
    (w : H) (hw : w ∈ Submodule.span ℝ (Set.range (fun i => difference S (u i)))) :
    ∃ N, ∃ v ∈ walkSpan u id N, difference S v = w := by
  induction hw using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨i, rfl⟩ := hw
    exact ⟨i+1, u i, Submodule.subset_span ⟨⟨i, Nat.lt_succ_self i⟩, rfl⟩, rfl⟩
  | zero =>
    exact ⟨0, 0, (walkSpan u id 0).zero_mem, map_zero _⟩
  | add x y hx hy ihx ihy =>
    obtain ⟨M, v, hv, rfl⟩ := ihx
    obtain ⟨N, z, hz, rfl⟩ := ihy
    exact ⟨M+N, v+z, (walkSpan u id (M+N)).add_mem
      (walkSpan_mono u id (Nat.le_add_right M N) hv)
      (walkSpan_mono u id (Nat.le_add_left N M) hz), map_add _ _ _⟩
  | smul c x hx ih =>
    obtain ⟨N, v, hv, rfl⟩ := ih
    exact ⟨N, c • v, (walkSpan u id N).smul_mem c hv, map_smul _ _ _⟩

/-- Shifted density provides approximation by lifts with finite support. -/
theorem finite_lift_approximation_of_dense (S : H →ₗ[ℝ] H) (u : ℕ → H)
    (hdense : (Submodule.span ℝ (Set.range (fun i =>
      difference S (u i)))).topologicalClosure = ⊤)
    (a : H) (ε : ℝ) (hε : 0 < ε) :
    ∃ N, ∃ v ∈ walkSpan u id N, ‖difference S v - a‖ < ε := by
  have ha : a ∈ (Submodule.span ℝ (Set.range (fun i =>
      difference S (u i)))).topologicalClosure := by rw [hdense]; trivial
  obtain ⟨w, hw, hdist⟩ := Metric.mem_closure_iff.mp ha ε hε
  obtain ⟨N, v, hv, rfl⟩ := span_difference_has_finite_lift S u w hw
  exact ⟨N, v, hv, by simpa only [dist_eq_norm, norm_sub_rev] using hdist⟩

/-- Positive regularization makes the finite-dimensional problem coercive.
A minimum is attained without supplying normal equations as a hypothesis. -/
theorem exists_regularizedEnergy_minimizer
    (S : H →ₗ[ℝ] H) (a : H) (t : ℝ) (ht : 0 < t)
    (V : Submodule ℝ H) [FiniteDimensional ℝ V] :
    ∃ v ∈ V, regularizedEnergy S a t v = regularizedInf S a t V := by
  let f : V → ℝ := fun v => regularizedEnergy S a t v
  have hcont : Continuous f := by
    exact ((((difference S).comp V.subtype).continuous_of_finiteDimensional.sub
      continuous_const).norm.pow 2).add (continuous_const.mul
        (V.subtype.continuous_of_finiteDimensional.norm.pow 2))
  let R : ℝ := ‖a‖ / t
  have hR : 0 ≤ R := div_nonneg (norm_nonneg a) (le_of_lt ht)
  have hzero : (0 : V) ∈ Metric.closedBall 0 R := by
    simpa using hR
  obtain ⟨v, hv, hmin⟩ := (isCompact_closedBall (0 : V) R).exists_isMinOn
    ⟨0, hzero⟩ hcont.continuousOn
  have hbound : f v ≤ ‖a‖ ^ 2 := by
    simpa [f, regularizedEnergy] using hmin hzero
  have hglobal (w : V) : f v ≤ f w := by
    by_cases hw : w ∈ Metric.closedBall 0 R
    · exact hmin hw
    · have hn : R < ‖w‖ := by
        simpa only [Metric.mem_closedBall, dist_zero_right, not_le] using hw
      have hn' : ‖a‖ < t * ‖(w : H)‖ := by
        have h := (div_lt_iff₀ ht).mp hn
        simpa only [mul_comm, Submodule.norm_coe] using h
      have he : t ^ 2 * ‖(w : H)‖ ^ 2 ≤ f w := by
        dsimp [f, regularizedEnergy]
        nlinarith [sq_nonneg ‖difference S w - a‖]
      have hsq : ‖a‖ ^ 2 ≤ t ^ 2 * ‖(w : H)‖ ^ 2 := by
        nlinarith [norm_nonneg a, norm_nonneg (w : H)]
      exact hbound.trans (hsq.trans he)
  refine ⟨v, v.property, le_antisymm ?_ (regularizedInf_le S a t V v v.property)⟩
  apply le_csInf
  · exact ⟨_, 0, V.zero_mem, rfl⟩
  · rintro E ⟨w, hw, rfl⟩
    exact hglobal ⟨w, hw⟩

/-- Identify the new infimum with the exact normal-solution formula. -/
theorem regularizedInf_eq_norm_sq_sub_pairing
    (S : H →ₗ[ℝ] H) (a : H) (t : ℝ) (V : Submodule ℝ H)
    (v₀ : H) (hv₀ : v₀ ∈ V)
    (hnormal : ∀ w ∈ V,
      inner ℝ (difference S v₀ - a) (difference S w) +
        t ^ 2 * inner ℝ v₀ w = 0) :
    regularizedInf S a t V = ‖a‖ ^ 2 - inner ℝ (difference S v₀) a := by
  have hmin := regularizedEnergy_isLeast S a t V v₀ hv₀ hnormal
  have he : regularizedInf S a t V = regularizedEnergy S a t v₀ := by
    apply le_antisymm (regularizedInf_le S a t V v₀ hv₀)
    apply le_csInf
    · exact ⟨_, hmin.1⟩
    · exact hmin.2
  rw [he, regularizedEnergy_eq_norm_sq_sub_pairing S a t V v₀ hv₀ hnormal]

end RiemannResearch.Analysis.ShiftedLift
