import RiemannResearch.Probability.ZeroOrdinateFiberDPP
import RiemannResearch.Probability.ZeroOrdinateDPPSampling
import RiemannResearch.Probability.DeterminantalProcess
import Mathlib.Data.Fintype.BigOperators
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# The determinantal process on distinct actual ordinates

Passing from multiplicity labels to distinct ordinates gives a determinantal
law even for an incomplete Fourier dictionary. Its principal determinants
sum the disjoint alternatives for the selected representatives. The quotient
kernel is the compression to normalized fibre indicators. The scalar vacancy
identity retains the exact norm-square loss of the Fourier approximation.

The finite-inclusion definition follows Lyons, *Determinantal probability
measures*, §2, https://doi.org/10.1007/s10240-003-0016-0.
-/

noncomputable section
open MeasureTheory
open scoped BigOperators
namespace RiemannResearch.Probability.DPP.ZeroOrdinateInfinite
open RiemannResearch.Analysis ProjectionDPP

/-- The countable set of represented positive ordinates. -/
abbrev OrdinateSite := {τ : ℝ // τ ∈ Set.range ordinate}

/-- A representative whose choice leaves every kernel entry unchanged. -/
def representative (τ : OrdinateSite) : Site := τ.property.choose

private theorem ordinate_representative (τ : OrdinateSite) :
    ordinate (representative τ) = τ.val := τ.property.choose_spec

def ordinateLabels (τ : OrdinateSite) : Finset Site := ordinateFiber (representative τ)

@[simp] theorem mem_ordinateLabels {τ : OrdinateSite} {i : Site} :
    i ∈ ordinateLabels τ ↔ ordinate i = τ.val := by
  rw [ordinateLabels, mem_ordinateFiber, ordinate_representative]

/-- Image of a selected configuration in the distinct-ordinate ground set. -/
def selectedOrdinates (x : Site → Bool) : Set OrdinateSite :=
  {τ | ∃ i : Site, ordinate i = τ.val ∧ x i = true}

/-- Symmetric kernel for the image process on distinct ordinates. -/
def ordinateQuotientKernel (q : ℕ → ℝ) (τ σ : OrdinateSite) : ℝ :=
  Real.sqrt (ordinateLabels τ).card * limitingKernel q (representative τ) (representative σ) *
    Real.sqrt (ordinateLabels σ).card

private theorem kernel_eq_of_ordinates (q : ℕ → ℝ) {i j k l : Site}
    (hi : ordinate i = ordinate k) (hj : ordinate j = ordinate l) :
    limitingKernel q i j = limitingKernel q k l := by
  simp only [limitingKernel, kernelOfSpace, kernel, collision_projection_eq q hi,
    collision_projection_eq q hj]

private theorem measurable_ordinate_occupancy (q : ℕ → ℝ) (τ : OrdinateSite) :
    MeasurableSet {x | τ ∈ selectedOrdinates x} := by
  have he : {x | τ ∈ selectedOrdinates x} =
      ⋃ i : ↥(ordinateLabels τ), {x : Site → Bool | x i.val = true} := by
    ext x
    constructor
    · rintro ⟨i, hi, hx⟩
      exact Set.mem_iUnion.mpr ⟨⟨i, mem_ordinateLabels.mpr hi⟩, hx⟩
    · intro hx
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
      exact ⟨i, mem_ordinateLabels.mp i.property, hi⟩
  rw [he]
  exact MeasurableSet.iUnion fun i => (limitingLaw_isDPP q).measurable_occupancy i.val

/-- The finite inclusion probability on ordinates is the inclusion probability
of any specified representatives times the product of the fibre sizes. -/
theorem ordinate_inclusion_mass (q : ℕ → ℝ) (m : ℕ) (e : Fin m ↪ OrdinateSite)
    (a : (k : Fin m) → ↥(ordinateLabels (e k))) :
    (limitingLaw q).real {x | ∀ k, e k ∈ selectedOrdinates x} =
      (∏ k, ((ordinateLabels (e k)).card : ℝ)) *
        (limitingLaw q).real {x | ∀ k, x (a k).val = true} := by
  classical
  let μ := limitingLaw q
  let A := (k : Fin m) → ↥(ordinateLabels (e k))
  let F := fun u : A => {x : Site → Bool | ∀ k, x (u k).val = true}
  let B := {x : Site → Bool | ∀ k, e k ∈ selectedOrdinates x}
  have hF (u : A) : MeasurableSet (F u) := by
    simp only [F, Set.ofPred_forall]
    exact MeasurableSet.iInter fun k => (limitingLaw_isDPP q).measurable_occupancy (u k).val
  have hB : MeasurableSet B := by
    simp only [B, Set.ofPred_forall]
    exact MeasurableSet.iInter fun k => measurable_ordinate_occupancy q (e k)
  have hsum : B.indicator (1 : (Site → Bool) → ℝ) =ᵐ[μ]
      fun x => ∑ u : A, (F u).indicator (1 : (Site → Bool) → ℝ) x := by
    filter_upwards [ordinate_injective_ae q] with x hx
    by_cases hbx : x ∈ B
    · have hrep : ∀ k, ∃ i : ↥(ordinateLabels (e k)), x i.val = true := by
        intro k
        obtain ⟨i, hi, hsel⟩ := hbx k
        exact ⟨⟨i, mem_ordinateLabels.mpr hi⟩, hsel⟩
      choose u hu using hrep
      have hgood : x ∈ F u := hu
      rw [Set.indicator_of_mem hbx, Finset.sum_eq_single u, Set.indicator_of_mem hgood]
      · intro v _ hv
        apply Set.indicator_of_notMem
        intro hsel
        apply hv
        funext k
        apply Subtype.ext
        exact hx (hsel k) (hu k) ((mem_ordinateLabels.mp (v k).property).trans
          (mem_ordinateLabels.mp (u k).property).symm)
      · simp
    · rw [Set.indicator_of_notMem hbx]
      symm
      apply Finset.sum_eq_zero
      intro v _
      apply Set.indicator_of_notMem
      intro hv
      apply hbx
      intro k
      exact ⟨(v k).val, mem_ordinateLabels.mp (v k).property, hv k⟩
  let lift := fun u : A => (⟨fun k => (u k).val, by
    intro i j hij
    apply e.injective
    apply Subtype.ext
    exact (mem_ordinateLabels.mp (u i).property).symm.trans
      ((congrArg ordinate hij).trans (mem_ordinateLabels.mp (u j).property))⟩ : Fin m ↪ Site)
  have hprob (u : A) : μ.real (F u) = μ.real (F a) := by
    have h (v : A) : μ.real (F v) =
        Matrix.det (Matrix.of (fun k l => limitingKernel q ((lift v) k) ((lift v) l))) :=
      (limitingLaw_isDPP q).correlation m (lift v)
    rw [h u, h a]
    congr 1
    ext k l
    exact kernel_eq_of_ordinates q
      ((mem_ordinateLabels.mp (u k).property).trans (mem_ordinateLabels.mp (a k).property).symm)
      ((mem_ordinateLabels.mp (u l).property).trans (mem_ordinateLabels.mp (a l).property).symm)
  change μ.real B = _ * μ.real (F a)
  rw [← integral_indicator_one hB, integral_congr_ae hsum, integral_finsetSum]
  · simp_rw [integral_indicator_one (hF _), hprob]
    simp [A, Fintype.card_pi, nsmul_eq_mul]
  · intro u _
    exact (integrable_const (1 : ℝ)).indicator (hF u)

/-- The image of the zero-label DPP is itself determinantal on the distinct
actual ordinates for every frequency dictionary. -/
theorem selectedOrdinates_isDPP (q : ℕ → ℝ) :
    IsDPP (limitingLaw q) selectedOrdinates (ordinateQuotientKernel q) := by
  classical
  refine ⟨measurable_ordinate_occupancy q, ?_⟩
  intro m e
  let a := fun k : Fin m => (⟨representative (e k), mem_ordinateLabels.mpr
    (ordinate_representative (e k))⟩ : ↥(ordinateLabels (e k)))
  let l : Fin m ↪ Site := ⟨fun k => representative (e k), by
    intro i j hij
    apply e.injective
    apply Subtype.ext
    exact (ordinate_representative (e i)).symm.trans
      ((congrArg ordinate hij).trans (ordinate_representative (e j)))⟩
  let K := Matrix.of (fun k l' : Fin m => limitingKernel q (l k) (l l'))
  let v := fun k : Fin m => Real.sqrt (ordinateLabels (e k)).card
  have hp : (limitingLaw q).real {x | ∀ k, x (a k).val = true} = K.det :=
    (limitingLaw_isDPP q).correlation m l
  rw [ordinate_inclusion_mass q m e a, hp]
  let C := Matrix.of (fun k l' : Fin m => v k * K k l')
  have hC : C.det = (∏ k, v k) * K.det := Matrix.det_mul_column v K
  have hM : Matrix.of (fun k l' : Fin m => ordinateQuotientKernel q (e k) (e l')) =
      Matrix.of (fun k l' => v l' * C k l') := by
    ext k l'
    change v k * K k l' * v l' = v l' * (v k * K k l')
    ring
  rw [hM, Matrix.det_mul_row, hC, ← mul_assoc, ← Finset.prod_mul_distrib]
  congr 1
  apply Finset.prod_congr rfl
  intro k _
  dsimp [v]
  rw [← pow_two, Real.sq_sqrt (Nat.cast_nonneg _)]

/-- The generic label vacancy is its unavoidable multiplicity loss plus
the remaining projection residual of its entire ordinate fibre. -/
theorem vacancy_eq_fiber_residual (q : ℕ → ℝ) (i : Site) :
    1 - limitingKernel q i i =
      1 - ((ordinateFiber i).card : ℝ)⁻¹ +
        ‖fiberVector i - (closedSpace q).starProjection (fiberVector i)‖ ^ 2 /
          ((ordinateFiber i).card : ℝ) ^ 2 := by
  let S := closedSpace q
  let m : ℝ := (ordinateFiber i).card
  have hm : m ≠ 0 := Nat.cast_ne_zero.mpr (ordinateFiber_card_pos i).ne'
  have hproj : S.starProjection (fiberVector i) = m • S.starProjection (coordinate i) := by
    rw [fiberVector, map_sum]
    calc
      _ = ∑ _j ∈ ordinateFiber i, S.starProjection (coordinate i) :=
        Finset.sum_congr rfl fun j hj => collision_projection_eq q (mem_ordinateFiber.mp hj)
      _ = _ := by simp only [Finset.sum_const, Nat.cast_smul_eq_nsmul, m]
  have hnorm : inner ℝ (fiberVector i) (fiberVector i) = m := by
    conv_lhs => lhs; rw [fiberVector]
    rw [sum_inner]
    calc
      _ = ∑ _j ∈ ordinateFiber i, (1 : ℝ) := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [inner_coordinate_fiberVector, if_pos (mem_ordinateFiber.mp hj)]
      _ = _ := by simp [m]
  have h := holeKernel_eq S (fun _ : Unit => fiberVector i) () ()
  rw [holeKernel_diagonal, hnorm] at h
  have hK : kernel S (fun _ : Unit => fiberVector i) () () = m * (m * limitingKernel q i i) := by
    change inner ℝ (S.starProjection (fiberVector i)) (S.starProjection (fiberVector i)) = _
    rw [hproj, real_inner_smul_left, real_inner_smul_right]
    rfl
  rw [hK] at h
  change 1 - limitingKernel q i i = 1 - m⁻¹ + _ / m ^ 2
  rw [h]
  field_simp [hm]
  ring

/-- Missing a represented ordinate has exactly the normalized fibre residual
as its probability, for every Fourier dictionary. -/
theorem ordinate_vacancy_eq_residual (q : ℕ → ℝ) (τ : OrdinateSite) :
    (limitingLaw q).real {x | τ ∉ selectedOrdinates x} =
      ‖fiberVector (representative τ) -
        (closedSpace q).starProjection (fiberVector (representative τ))‖ ^ 2 /
        (ordinateLabels τ).card := by
  let i := representative τ
  let m : ℝ := (ordinateLabels τ).card
  have hm : m ≠ 0 := Nat.cast_ne_zero.mpr (ordinateFiber_card_pos i).ne'
  have hres := vacancy_eq_fiber_residual q i
  change 1 - limitingKernel q i i = 1 - m⁻¹ + _ / m ^ 2 at hres
  rw [(selectedOrdinates_isDPP q).vacancy]
  change 1 - Real.sqrt m * limitingKernel q i i * Real.sqrt m = _
  rw [show Real.sqrt m * limitingKernel q i i * Real.sqrt m = m * limitingKernel q i i by
    calc
      _ = Real.sqrt m ^ 2 * limitingKernel q i i := by ring
      _ = _ := by rw [Real.sq_sqrt (Nat.cast_nonneg _)]]
  change 1 - m * limitingKernel q i i = _ / m
  field_simp [hm] at hres ⊢
  nlinarith only [hres]

/-- Finite-cutoff vacancy splits into the exact multiplicity excess and
the nonnegative residual caused by an incomplete Fourier dictionary. -/
theorem cutoffVacancy_eq_excess_add_residual (q : ℕ → ℝ) (T : ℝ) :
    cutoffVacancy q T = ((Zeta23.Ncount 0 T : ℝ) -
      (ActualZeroCollisionCertificate.actualOrdinateSupport T).card) +
      ∑ c : ActualZeroOrdinate.Copies T,
        ‖fiberVector (liftCopy T c) -
          (closedSpace q).starProjection (fiberVector (liftCopy T c))‖ ^ 2 /
          ((ordinateFiber (liftCopy T c)).card : ℝ) ^ 2 := by
  rw [← logarithmic_cutoff_vacancy]
  simp only [cutoffVacancy, logarithmic_limitingKernel]
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun c _ => vacancy_eq_fiber_residual q (liftCopy T c))

/-- Among all dictionaries the logarithmic one minimizes expected
deletions at every finite height. -/
theorem logarithmic_cutoffVacancy_minimal (q : ℕ → ℝ) (T : ℝ) :
    cutoffVacancy (fun k => Real.log ((k : ℝ) + 1)) T ≤ cutoffVacancy q T := by
  rw [logarithmic_cutoff_vacancy, cutoffVacancy_eq_excess_add_residual]
  exact le_add_of_nonneg_right (Finset.sum_nonneg
    (fun _ _ => div_nonneg (sq_nonneg _) (sq_nonneg _)))

end RiemannResearch.Probability.DPP.ZeroOrdinateInfinite
