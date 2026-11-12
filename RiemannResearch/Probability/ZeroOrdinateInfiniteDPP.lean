import RiemannResearch.Analysis.ActualZeroOrdinate
import RiemannResearch.Analysis.ExhaustiveProjectionWalk
import RiemannResearch.Analysis.ProjectionDPPKernel
import RiemannResearch.Probability.DeterminantalExistence
import RiemannResearch.Probability.DeterminantalEntry
import RiemannResearch.Probability.DeterminantalPairTransfer
import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Tactic.Ring
import Mathlib.Topology.Instances.Matrix
import Mathlib.Logic.Encodable.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

/-!
# Infinite Fourier-projection DPP on actual zeta-zero copies

Sources: Ford--Meng--Zaharescu, https://arxiv.org/abs/1511.06814, motivates
prime-log Fourier features; Lyons, https://arxiv.org/abs/math/0204325,
supplies the discrete projection-DPP framework. The implementation uses
the repository's proved contractionDPP construction and Hilbert projection
convergence, not an external existence or convergence axiom.

All positive zeros and analytic multiplicities are retained as labels.
Cutoff features are finitely supported in one fixed l2 space. Their closed
span gives the infinite law; recomputed finite-height laws are not assumed
projectively consistent. Finite feature-prefix inclusion probabilities converge.
Every selected configuration is locally finite, and almost surely no two
selected labels have the same ordinate. No RH or Selberg premise is used.
This is an auxiliary thinning, not an assertion of Montgomery pair correlation.
-/

noncomputable section
open MeasureTheory Filter
open scoped BigOperators Topology
namespace RiemannResearch.Probability.DPP.ZeroOrdinateInfinite
open RiemannResearch.Analysis ActualZeroOrdinate ProjectionDPP ExhaustiveWalk

abbrev Site := PositiveCopies
abbrev Space := lp (fun _ : Site => ℝ) 2

def ordinate (i : Site) : ℝ := i.1.1.im
open Classical in
def coordinate (i : Site) : Space := lp.single 2 i 1

open Classical in
theorem coordinate_inner (i j : Site) :
    inner ℝ (coordinate i) (coordinate j) = if i = j then 1 else 0 := by
  by_cases h : i = j
  · subst j
    simp [coordinate]
  · simp [coordinate, lp.inner_single_left, h]

def liftCopy (T : ℝ) : Copies T ↪ Site where
  toFun c := ⟨⟨c.1.1, (mem_cutoff_iff_zeta.mp c.1.property).1,
    (mem_cutoff_iff_zeta.mp c.1.property).2.1⟩, c.2⟩
  inj' := by
    rintro ⟨⟨ρ, hρ⟩, a⟩ ⟨⟨σ, hσ⟩, b⟩ hab
    have hz : ρ = σ := congrArg (fun c : Site => c.1.1) hab
    subst σ
    have hi : a.val = b.val := congrArg (fun c : Site => c.2.val) hab
    have hi' : a = b := Fin.ext hi
    subst b
    rfl

theorem bounded_sites_finite (T : ℝ) : Set.Finite {i : Site | ordinate i ≤ T} := by
  apply (Set.finite_range (liftCopy T)).subset
  intro i hi
  refine ⟨⟨⟨i.1.1, mem_cutoff_iff_zeta.mpr ⟨i.1.property.1, i.1.property.2, hi⟩⟩, i.2⟩, ?_⟩
  rfl

theorem selected_sites_locally_finite (x : Site → Bool) (T : ℝ) :
    Set.Finite {i : Site | x i = true ∧ ordinate i ≤ T} :=
  (bounded_sites_finite T).subset (fun _ hi => hi.2)

def cutoffVector (T : ℝ) (f : ℝ → ℝ) : Space :=
  ∑ c : Copies T, f c.1.1.im • coordinate (liftCopy T c)

abbrev FeatureIndex := ℕ × (ℕ × Bool)
def feature (q : ℕ → ℝ) (a : FeatureIndex) : Space :=
  cutoffVector (a.1 : ℝ) (fun t =>
    if a.2.2 then Real.sin (q a.2.1 * t) else Real.cos (q a.2.1 * t))

def enumeration (n : ℕ) : FeatureIndex :=
  (Encodable.decode (α := FeatureIndex) n).getD (0, 0, false)

theorem enumeration_surjective : Function.Surjective enumeration := by
  intro a
  refine ⟨Encodable.encode a, ?_⟩
  simp [enumeration, Encodable.encodek]

def finiteSpace (q : ℕ → ℝ) (n : ℕ) : Submodule ℝ Space :=
  walkSpan (feature q) enumeration n
instance finiteSpace_finiteDimensional (q : ℕ → ℝ) (n : ℕ) :
    FiniteDimensional ℝ (finiteSpace q n) :=
  walkSpan_finiteDimensional _ _ _

def closedSpace (q : ℕ → ℝ) : Submodule ℝ Space := dictionaryClosure (feature q)
instance closedSpace_hasOrthogonalProjection (q : ℕ → ℝ) :
    (closedSpace q).HasOrthogonalProjection := by
  unfold closedSpace
  infer_instance

def kernelOfSpace (S : Submodule ℝ Space) [S.HasOrthogonalProjection] : Site → Site → ℝ :=
  kernel S coordinate

open Classical in
def lawOfSpace (S : Submodule ℝ Space) [S.HasOrthogonalProjection] : Measure (Site → Bool) :=
  contractionDPP (kernelOfSpace S)
    (fun I => principal_posSemidef S coordinate (fun i : I => i.1))
    (fun I => by
      have h := identity_sub_principal_posSemidef S coordinate
        (fun i : I => i.1) (by intro i j; simp [coordinate_inner])
      convert h using 1
      ext i j
      simp [Matrix.sub_apply, Matrix.one_apply, kernelOfSpace])

instance lawOfSpace_probability (S : Submodule ℝ Space) [S.HasOrthogonalProjection] :
    IsProbabilityMeasure (lawOfSpace S) := by
  unfold lawOfSpace
  exact contractionDPP_probability _ _ _

theorem lawOfSpace_isDPP (S : Submodule ℝ Space) [S.HasOrthogonalProjection] :
    IsDPP (lawOfSpace S) (fun x => {i | x i = true}) (kernelOfSpace S) :=
  contractionDPP_isDPP _ _ _

def finiteKernel (q : ℕ → ℝ) (n : ℕ) := kernelOfSpace (finiteSpace q n)
def limitingKernel (q : ℕ → ℝ) := kernelOfSpace (closedSpace q)
def finiteLaw (q : ℕ → ℝ) (n : ℕ) := lawOfSpace (finiteSpace q n)
def limitingLaw (q : ℕ → ℝ) := lawOfSpace (closedSpace q)

instance finiteLaw_probability (q : ℕ → ℝ) (n : ℕ) :
    IsProbabilityMeasure (finiteLaw q n) := lawOfSpace_probability _
instance limitingLaw_probability (q : ℕ → ℝ) :
    IsProbabilityMeasure (limitingLaw q) := lawOfSpace_probability _

theorem finiteLaw_isDPP (q : ℕ → ℝ) (n : ℕ) :
    IsDPP (finiteLaw q n) (fun x => {i | x i = true}) (finiteKernel q n) :=
  lawOfSpace_isDPP _
theorem limitingLaw_isDPP (q : ℕ → ℝ) :
    IsDPP (limitingLaw q) (fun x => {i | x i = true}) (limitingKernel q) :=
  lawOfSpace_isDPP _

theorem kernel_tendsto (q : ℕ → ℝ) (i j : Site) :
    Tendsto (fun n => finiteKernel q n i j) atTop (𝓝 (limitingKernel q i j)) :=
  (walkProjection_tendsto (feature q) enumeration enumeration_surjective (coordinate i)).inner
    (walkProjection_tendsto (feature q) enumeration enumeration_surjective (coordinate j))

theorem inclusion_tendsto (q : ℕ → ℝ) (m : ℕ) (e : Fin m ↪ Site) :
    Tendsto (fun n => (finiteLaw q n).real {x | ∀ i, x (e i) = true}) atTop
      (𝓝 ((limitingLaw q).real {x | ∀ i, x (e i) = true})) := by
  have hf (n : ℕ) :
      (finiteLaw q n).real {x | ∀ i, x (e i) = true} =
        Matrix.det (Matrix.of (fun i j => finiteKernel q n (e i) (e j))) :=
    (finiteLaw_isDPP q n).correlation m e
  have hl :
      (limitingLaw q).real {x | ∀ i, x (e i) = true} =
        Matrix.det (Matrix.of (fun i j => limitingKernel q (e i) (e j))) :=
    (limitingLaw_isDPP q).correlation m e
  simp_rw [hf, hl]
  exact (continuous_id.matrix_det.tendsto _).comp
    (tendsto_pi_nhds.mpr fun i => tendsto_pi_nhds.mpr fun j =>
      kernel_tendsto q (e i) (e j))

theorem vacancy_eq_projection_residual (q : ℕ → ℝ) (i : Site) :
    1 - limitingKernel q i i =
      ‖coordinate i - (closedSpace q).starProjection (coordinate i)‖^2 := by
  have h := holeKernel_eq (closedSpace q) coordinate i i
  rw [coordinate_inner, if_pos rfl, holeKernel_diagonal] at h
  exact h.symm

theorem limitingLaw_two_point (q : ℕ → ℝ) {i j : Site} (hij : i ≠ j) :
    (limitingLaw q).real {x | x i = true ∧ x j = true} =
      limitingKernel q i i * limitingKernel q j j - (limitingKernel q i j)^2 := by
  have h := (limitingLaw_isDPP q).two_point hij
  have hs : limitingKernel q j i = limitingKernel q i j :=
    kernel_symmetric _ _ _ _
  simpa only [Set.mem_ofPred_eq, hs, pow_two] using h


theorem cutoffVector_coordinate (T : ℝ) (f : ℝ → ℝ) (i : Site) :
    inner ℝ (coordinate i) (cutoffVector T f) =
      if ordinate i ≤ T then f (ordinate i) else 0 := by
  classical
  unfold cutoffVector
  rw [inner_sum]
  simp_rw [inner_smul_right, coordinate_inner]
  by_cases hi : ordinate i ≤ T
  · let c : Copies T :=
      ⟨⟨i.1.1, mem_cutoff_iff_zeta.mpr ⟨i.1.property.1, i.1.property.2, hi⟩⟩, i.2⟩
    have hc : liftCopy T c = i := rfl
    rw [if_pos hi, Finset.sum_eq_single c]
    · simp [hc, c, ordinate]
    · intro b hb hbc
      have hn : i ≠ liftCopy T b := by
        intro he
        apply hbc
        exact (liftCopy T).injective (he.symm.trans hc.symm)
      simp [hn]
    · simp
  · rw [if_neg hi]
    apply Finset.sum_eq_zero
    intro b hb
    have hn : i ≠ liftCopy T b := by
      intro he
      apply hi
      rw [he]
      exact (mem_cutoff.mp b.1.property).2.2
    simp [hn]

theorem collision_projection_eq (q : ℕ → ℝ) {i j : Site}
    (hij : ordinate i = ordinate j) :
    (closedSpace q).starProjection (coordinate i) =
      (closedSpace q).starProjection (coordinate j) := by
  let L : Space →L[ℝ] ℝ := innerSL ℝ (coordinate i - coordinate j)
  have hspan : Submodule.span ℝ (Set.range (feature q)) ≤ L.ker := by
    apply Submodule.span_le.mpr
    rintro _ ⟨a, rfl⟩
    change inner ℝ (coordinate i - coordinate j) (feature q a) = 0
    rw [inner_sub_left]
    unfold feature
    rw [cutoffVector_coordinate, cutoffVector_coordinate, hij, sub_self]
  have hclosed : closedSpace q ≤ L.ker :=
    Submodule.topologicalClosure_minimal _ hspan L.isClosed_ker
  have horth : coordinate i - coordinate j ∈ (closedSpace q)ᗮ := by
    apply (Submodule.mem_orthogonal _ _).mpr
    intro x hx
    rw [real_inner_comm]
    exact hclosed hx
  have hz : (closedSpace q).starProjection (coordinate i - coordinate j) = 0 :=
    ((closedSpace q).starProjection_apply_eq_zero_iff).mpr horth
  simpa only [map_sub, sub_eq_zero] using hz

theorem collision_pair_probability_zero (q : ℕ → ℝ) {i j : Site}
    (hne : i ≠ j) (hij : ordinate i = ordinate j) :
    (limitingLaw q).real {x | x i = true ∧ x j = true} = 0 := by
  rw [limitingLaw_two_point q hne]
  simp only [limitingKernel, kernelOfSpace, kernel, collision_projection_eq q hij]
  ring

theorem zero_pair_transfer_bound (q : ℕ → ℝ) (T : ℝ)
    (w : Copies T → Copies T → ℝ) (hw : ∀ i, w i i = 0) :
    |pairMass w -
      ∫ x, pairStatistic (fun x : Site → Bool => {i | x i = true}) (liftCopy T) w x
        ∂limitingLaw q| ≤
      ∑ i, ‖coordinate (liftCopy T i) -
        (closedSpace q).starProjection (coordinate (liftCopy T i))‖^2 *
          (∑ j, (|w i j|+|w j i|)) := by
  have h := (limitingLaw_isDPP q).pairStatistic_error_le (liftCopy T) w hw
  rw [pairVacancyBudget_eq_degrees] at h
  simpa only [vacancy_eq_projection_residual] using h


theorem ordinate_injective_ae (q : ℕ → ℝ) :
    ∀ᵐ x ∂limitingLaw q, Set.InjOn ordinate {i | x i = true} := by
  have h (i j : Site) : ∀ᵐ x ∂limitingLaw q,
      x i = true → x j = true → ordinate i = ordinate j → i = j := by
    by_cases hne : i = j
    · simp [hne]
    by_cases hij : ordinate i = ordinate j
    · have hz : (limitingLaw q) {x | x i = true ∧ x j = true} = 0 :=
        (measureReal_eq_zero_iff (measure_ne_top _ _)).mp
          (collision_pair_probability_zero q hne hij)
      have ha : ∀ᵐ x ∂limitingLaw q, ¬ (x i = true ∧ x j = true) :=
        ae_iff.mpr (by simpa only [not_not] using hz)
      filter_upwards [ha] with x hx
      exact fun hi hj _ => (hx ⟨hi, hj⟩).elim
    · filter_upwards with x
      exact fun _ _ he => (hij he).elim
  filter_upwards [ae_all_iff.mpr (fun i => ae_all_iff.mpr (h i))] with x hx
  intro i hi j hj hij
  exact hx i j hi hj hij

theorem collision_vacancy_lower (q : ℕ → ℝ) {i j : Site}
    (hne : i ≠ j) (hij : ordinate i = ordinate j) :
    1 ≤ (1-limitingKernel q i i)+(1-limitingKernel q j j) := by
  have hb := (limitingLaw_isDPP q).pairDefect_bounds hne
  have hz : limitingKernel q i i * limitingKernel q j j -
      limitingKernel q i j * limitingKernel q j i = 0 :=
    ((limitingLaw_isDPP q).two_point hne).symm.trans
      (collision_pair_probability_zero q hne hij)
  simpa only [pairDefect, hz, sub_zero] using hb.2

end RiemannResearch.Probability.DPP.ZeroOrdinateInfinite
