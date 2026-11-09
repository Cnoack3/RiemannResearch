import RiemannResearch.RH.ParetoLCMTargetProbe
import RiemannResearch.RH.MellinCriticalPoint
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Tactic.Linarith

/-!
# Adding grouped Mellin zero rows to the LCM projection DPP

The grouped rows are embedded by giving them zero in the multiples class.
The augmented legal, zero, and multiples spaces are pairwise orthogonal.
Projection onto the zero span is defined even for a singular row Gram.
-/

noncomputable section

open MeasureTheory Filter
open scoped BigOperators Topology

namespace RiemannResearch.RH.Pareto.ResidueMellin

open RiemannResearch.Analysis.FiniteHilbertGram
open RiemannResearch.Probability.DPP
open MellinFrequency (criticalPoint criticalPoint_ne_one)

private def appendClass (N : ℕ) (x : EuclideanSpace ℝ (Fin N)) (a : ℝ) :
    EuclideanSpace ℝ (Fin (N + 1)) :=
  WithLp.toLp 2 (Fin.snoc (fun r => x r) a)

@[simp] private theorem appendClass_castSucc (N : ℕ) (x : EuclideanSpace ℝ (Fin N))
    (a : ℝ) (r : Fin N) : appendClass N x a r.castSucc = x r := by
  change Fin.snoc (α := fun _ : Fin (N + 1) => ℝ) (fun i => x i) a r.castSucc = x r
  exact Fin.snoc_castSucc (α := fun _ => ℝ) a (fun i => x i) r

@[simp] private theorem appendClass_last (N : ℕ) (x : EuclideanSpace ℝ (Fin N)) (a : ℝ) :
    appendClass N x a (Fin.last N) = a := by
  change Fin.snoc (α := fun _ : Fin (N + 1) => ℝ) (fun i => x i) a (Fin.last N) = a
  exact Fin.snoc_last (α := fun _ : Fin (N + 1) => ℝ) a (fun i => x i)

private theorem appendClass_inner (N : ℕ) (x y : EuclideanSpace ℝ (Fin N)) (a b : ℝ) :
    inner ℝ (appendClass N x a) (appendClass N y b) = inner ℝ x y + a * b := by
  simp only [EuclideanSpace.inner_eq_star_dotProduct, dotProduct, star_trivial]
  rw [Fin.sum_univ_castSucc]
  simp [mul_comm a b]

private theorem appendClass_norm_sq (N : ℕ) (x : EuclideanSpace ℝ (Fin N)) (a : ℝ) :
    ‖appendClass N x a‖ ^ 2 = ‖x‖ ^ 2 + a ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, appendClass_inner, real_inner_self_eq_norm_sq, pow_two a]

private theorem appendClass_add (N : ℕ) (x y : EuclideanSpace ℝ (Fin N)) (a b : ℝ) :
    appendClass N x a + appendClass N y b = appendClass N (x + y) (a + b) := by
  ext r
  refine Fin.lastCases ?_ (fun r => ?_) r <;> simp

private theorem appendClass_sub (N : ℕ) (x y : EuclideanSpace ℝ (Fin N)) (a b : ℝ) :
    appendClass N x a - appendClass N y b = appendClass N (x - y) (a - b) := by
  ext r
  refine Fin.lastCases ?_ (fun r => ?_) r <;> simp

private def embedNonzero (N : ℕ) :
    EuclideanSpace ℝ (Fin N) →ₗ[ℝ] EuclideanSpace ℝ (Fin (N + 1)) where
  toFun x := appendClass N x 0
  map_add' x y := by simpa only [add_zero] using (appendClass_add N x y 0 0).symm
  map_smul' a x := by
    ext r
    refine Fin.lastCases ?_ (fun r => ?_) r <;> simp

private theorem quotient_error_eq_append {N : ℕ} {f : ThresholdHilbert}
    (hf : f ∈ trialSpace (N + 1)) :
    quotientTarget N - quotientEval N f =
      appendClass N (errorVector N f) (Real.sqrt (classWeight N (Fin.last N))) := by
  rw [quotientTarget, ← map_sub]
  ext r
  refine Fin.lastCases ?_ (fun r => ?_) r
  · rw [appendClass_last]
    change Real.sqrt (classWeight N (Fin.last N)) * error N f (Fin.last N) = _
    rw [error_multiples hf, mul_one]
  · rw [appendClass_castSucc]
    rfl

private theorem quotientEval_last_of_legal {N : ℕ} {f : ThresholdHilbert}
    (hf : f ∈ trialSpace (N + 1)) : quotientEval N f (Fin.last N) = 0 := by
  change Real.sqrt (classWeight N (Fin.last N)) * hilbertSequence f (N + 1) = 0
  rw [← trial_sequence_mod hf (N + 1), Nat.mod_self, hilbertSequence_zero, mul_zero]

variable {ι : Type*}

/-- Grouped zero rows, extended by zero on the multiples class. -/
def quotientZeroSpace (N : ℕ) (z : ι → ℂ) :
    Submodule ℝ (EuclideanSpace ℝ (Fin (N + 1))) :=
  (synthesisSpan (rowVector N z)).map (embedNonzero N)

/-- The direction of the class consisting of multiples of the modulus. -/
def quotientMultiplesSpace (N : ℕ) : Submodule ℝ (EuclideanSpace ℝ (Fin (N + 1))) :=
  ℝ ∙ appendClass N 0 1

/-- The legal space with the grouped zero rows and the multiples direction adjoined. -/
def quotientAugmentedSpace (N : ℕ) (z : ι → ℂ) :
    Submodule ℝ (EuclideanSpace ℝ (Fin (N + 1))) :=
  quotientLegalSpace N ⊔ quotientZeroSpace N z ⊔ quotientMultiplesSpace N

theorem quotientZero_orthogonal_legal (N : ℕ) (z : ι → ℂ)
    (hs : ∀ i, 0 < (z i).re) (hs1 : ∀ i, z i ≠ 1) (hz : ∀ i, riemannZeta (z i) = 0) :
    quotientZeroSpace N z ≤ (quotientLegalSpace N)ᗮ := by
  intro w hw
  rw [Submodule.mem_orthogonal]
  rintro v ⟨f, hf, rfl⟩
  obtain ⟨u, hu, rfl⟩ := Submodule.mem_map.mp hw
  clear hw
  rw [real_inner_comm]
  change u ∈ Submodule.span ℝ (Set.range (rowVector N z)) at hu
  induction hu using Submodule.span_induction with
  | mem u hu =>
    obtain ⟨i, rfl⟩ := hu
    have hobs (g : ThresholdHilbert) (hg : g ∈ trialSpace (N + 1)) :
        inner ℝ (embedNonzero N (rowVector N z i))
          (quotientTarget N - quotientEval N g) = source N z i := by
      rw [quotient_error_eq_append hg]
      change inner ℝ (appendClass N (rowVector N z i) 0)
        (appendClass N (errorVector N g) (Real.sqrt (classWeight N (Fin.last N)))) = _
      rw [appendClass_inner, zero_mul, add_zero, error_observation hg z i (hs _) (hs1 _) (hz _)]
    have h := hobs f hf
    have h0 := hobs 0 ((trialSpace (N + 1)).zero_mem)
    rw [map_zero, sub_zero] at h0
    rw [inner_sub_right, h0] at h
    linarith
  | zero => simp
  | add u v _ _ hu hv => simp [inner_add_left, hu, hv]
  | smul a u _ hu => simp [real_inner_smul_left, hu]

private theorem inner_multiples_eq_zero {N : ℕ}
    {x m : EuclideanSpace ℝ (Fin (N + 1))} (hx : x (Fin.last N) = 0)
    (hm : m ∈ quotientMultiplesSpace N) : inner ℝ x m = 0 := by
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hm
  rw [real_inner_smul_right, EuclideanSpace.inner_eq_star_dotProduct]
  simp [dotProduct, star_trivial, Fin.sum_univ_castSucc, hx]

theorem quotientMultiples_orthogonal_legal (N : ℕ) :
    quotientMultiplesSpace N ≤ (quotientLegalSpace N)ᗮ := by
  intro m hm
  rw [Submodule.mem_orthogonal]
  rintro v ⟨f, hf, rfl⟩
  exact inner_multiples_eq_zero (quotientEval_last_of_legal hf) hm

theorem quotientMultiples_orthogonal_zero (N : ℕ) (z : ι → ℂ) :
    quotientMultiplesSpace N ≤ (quotientZeroSpace N z)ᗮ := by
  intro m hm
  rw [Submodule.mem_orthogonal]
  rintro v ⟨u, hu, rfl⟩
  exact inner_multiples_eq_zero (appendClass_last N u 0) hm

private theorem append_multiples_mem (N : ℕ) (a : ℝ) :
    appendClass N 0 a ∈ quotientMultiplesSpace N := by
  apply Submodule.mem_span_singleton.mpr
  refine ⟨a, ?_⟩
  ext r
  refine Fin.lastCases ?_ (fun r => ?_) r <;> simp

variable [Fintype ι]

private theorem augmented_projection_residual (M : ℕ) (z : ι → ℂ)
    (hs : ∀ i, 0 < (z i).re) (hs1 : ∀ i, z i ≠ 1) (hz : ∀ i, riemannZeta (z i) = 0) :
    let N := lcmResidueIndex M
    quotientTarget N - (quotientAugmentedSpace N z).starProjection (quotientTarget N) =
      appendClass N (errorVector N (lcmBest M) - certificateVector N z) 0 := by
  let N := lcmResidueIndex M
  let S := quotientLegalSpace N
  let Z := quotientZeroSpace N z
  let U := quotientMultiplesSpace N
  let t := quotientTarget N
  let v := quotientEval N (lcmBest M)
  let c := certificateVector N z
  let a := Real.sqrt (classWeight N (Fin.last N))
  let r := appendClass N (errorVector N (lcmBest M) - c) 0
  change t - (S ⊔ Z ⊔ U).starProjection t = r
  have hf : lcmBest M ∈ trialSpace (N + 1) := (lcmResidueIndex_succ M).symm ▸ lcmBest_mem M
  have hv : v ∈ S := Submodule.mem_map.mpr ⟨_, hf, rfl⟩
  have hc : appendClass N c 0 ∈ Z := Submodule.mem_map.mpr
    ⟨c, (synthesisSpan (rowVector N z)).starProjection_apply_mem _, rfl⟩
  have ha : appendClass N 0 a ∈ U := append_multiples_mem N a
  have hsplit : t - (v + appendClass N c 0 + appendClass N 0 a) = r := by
    rw [add_assoc, appendClass_add, add_zero, zero_add, ← sub_sub, show t - v =
      appendClass N (errorVector N (lcmBest M)) a from quotient_error_eq_append hf,
      appendClass_sub, sub_self]
  have hvorth : t - v ∈ Sᗮ := by
    have hbest : S.starProjection t = v := quotient_projection_eq_lcmBest M
    rw [← hbest]
    exact S.sub_starProjection_mem_orthogonal t
  have hrS : r ∈ Sᗮ := by
    rw [← hsplit, add_assoc, ← sub_sub]
    exact Submodule.sub_mem _ hvorth (Submodule.add_mem _
      (quotientZero_orthogonal_legal N z hs hs1 hz hc) (quotientMultiples_orthogonal_legal N ha))
  have hcproj : c = (synthesisSpan (rowVector N z)).starProjection (errorVector N (lcmBest M)) := by
    obtain ⟨coeff, hcoeff⟩ := exists_zero_normal N z hs hs1 hz
    have hzero := certificate_eq_projection ((trialSpace (N + 1)).zero_mem) z hs hs1 hz coeff hcoeff
    exact hzero.symm.trans (certificate_eq_projection hf z hs hs1 hz coeff hcoeff)
  have hrZ : r ∈ Zᗮ := by
    rw [Submodule.mem_orthogonal]
    rintro _ ⟨w, hw, rfl⟩
    change inner ℝ (appendClass N w 0) (appendClass N (errorVector N (lcmBest M) - c) 0) = 0
    rw [appendClass_inner, zero_mul, add_zero, hcproj]
    exact (Submodule.mem_orthogonal _ _).mp
      ((synthesisSpan (rowVector N z)).sub_starProjection_mem_orthogonal _) _ hw
  have hrU : r ∈ Uᗮ := by
    rw [Submodule.mem_orthogonal]
    intro m hm
    rw [real_inner_comm]
    exact inner_multiples_eq_zero (appendClass_last _ _ _) hm
  have hproj : v + appendClass N c 0 + appendClass N 0 a = (S ⊔ Z ⊔ U).starProjection t := by
    symm
    apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
    · exact Submodule.mem_sup.mpr
        ⟨_, Submodule.mem_sup.mpr ⟨_, hv, _, hc, rfl⟩, _, ha, rfl⟩
    · intro w hw
      rw [hsplit, real_inner_comm]
      obtain ⟨x, hx, u, hu, rfl⟩ := Submodule.mem_sup.mp hw
      obtain ⟨l, hl, q, hq, rfl⟩ := Submodule.mem_sup.mp hx
      simp only [inner_add_left, (Submodule.mem_orthogonal _ _).mp hrS _ hl,
        (Submodule.mem_orthogonal _ _).mp hrZ _ hq,
        (Submodule.mem_orthogonal _ _).mp hrU _ hu, add_zero]
  rwa [hproj] at hsplit

theorem lcm_augmented_probe_vacancy {κ : Type*} [Fintype κ] [DecidableEq κ] (M : ℕ)
    (z : ι → ℂ) (hs : ∀ i, 0 < (z i).re) (hs1 : ∀ i, z i ≠ 1)
    (hz : ∀ i, riemannZeta (z i) = 0)
    (e : κ → EuclideanSpace ℝ (Fin (lcmResidueIndex M + 1)))
    (he : ∀ i j, inner ℝ (e i) (e j) = if i = j then 1 else 0)
    (i : κ) (hi : e i = quotientTarget (lcmResidueIndex M)) :
    (projectionObservationLaw (quotientAugmentedSpace (lcmResidueIndex M) z) e he).real
        {x | x i = false} = lcmRemainder z M := by
  rw [projectionObservationLaw_vacancy, hi, augmented_projection_residual M z hs hs1 hz,
    appendClass_norm_sq, zero_pow (by decide : 2 ≠ 0), add_zero, lcmRemainder]

/-- The legal probe vacancy splits into the multiples mass, the zero energy,
and the vacancy after both orthogonal directions are added. -/
theorem lcm_probe_vacancy_split {κ : Type*} [Fintype κ] [DecidableEq κ] (M : ℕ)
    (z : ι → ℂ) (hs : ∀ i, 0 < (z i).re) (hs1 : ∀ i, z i ≠ 1)
    (hz : ∀ i, riemannZeta (z i) = 0)
    (e : κ → EuclideanSpace ℝ (Fin (lcmResidueIndex M + 1)))
    (he : ∀ i j, inner ℝ (e i) (e j) = if i = j then 1 else 0)
    (i : κ) (hi : e i = quotientTarget (lcmResidueIndex M)) :
    (projectionObservationLaw (quotientLegalSpace (lcmResidueIndex M)) e he).real
        {x | x i = false} =
      classWeight (lcmResidueIndex M) (Fin.last (lcmResidueIndex M)) +
        certificateEnergy (lcmResidueIndex M) z +
        (projectionObservationLaw (quotientAugmentedSpace (lcmResidueIndex M) z) e he).real
          {x | x i = false} := by
  rw [lcm_probe_vacancy M e he i hi, lcm_augmented_probe_vacancy M z hs hs1 hz e he i hi]
  exact lcm_best_error_eq M z hs hs1 hz

/-- An arbitrary legal shifted trial retains exactly the displacement from the optimizer. -/
theorem lcm_shifted_trial_norm_sq (M : ℕ) {f : ThresholdHilbert}
    (hf : f ∈ trialSpace (Nat.lcmUpto M)) (z : ι → ℂ)
    (hs : ∀ i, 0 < (z i).re) (hs1 : ∀ i, z i ≠ 1) (hz : ∀ i, riemannZeta (z i) = 0) :
    ‖errorVector (lcmResidueIndex M) f - certificateVector (lcmResidueIndex M) z‖ ^ 2 =
      lcmRemainder z M + ‖f - lcmBest M‖ ^ 2 := by
  have h := lcm_error_four_terms M hf z hs hs1 hz
  rw [legal_error_completion_canonical ((lcmResidueIndex_succ M).symm ▸ hf) z hs hs1 hz] at h
  linarith

/-- A cofinal, vanishing upper budget on the complete shifted trial proves RH. -/
theorem riemannHypothesis_of_lcm_shifted_trials (γ : ι → ℝ)
    (hγ : Function.Injective γ) (hpos : ∀ i, 0 < γ i)
    (hz : ∀ i, riemannZeta (criticalPoint (γ i)) = 0)
    (M : ℕ → ℕ) (hM : Tendsto M atTop atTop) (f : ℕ → ThresholdHilbert)
    (hf : ∀ j, f j ∈ trialSpace (Nat.lcmUpto (M j)))
    (B : ℕ → ℝ) (hB : Tendsto B atTop (𝓝 0))
    (hub : ∀ᶠ j in atTop, ‖errorVector (lcmResidueIndex (M j)) (f j) -
      certificateVector (lcmResidueIndex (M j)) (fun i => criticalPoint (γ i))‖ ^ 2 ≤ B j) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_cofinal_remainder_upper γ hγ hpos hz M hM B hB
  filter_upwards [hub] with j hj
  rw [lcm_shifted_trial_norm_sq (M j) (hf j) (fun i => criticalPoint (γ i))
    (fun i => by simp) (fun i => criticalPoint_ne_one (γ i)) hz] at hj
  linarith [sq_nonneg ‖f j - lcmBest (M j)‖]

/-- The moving-family version needs the certificate energy and the augmented
vacancy to vanish along the same cofinal schedule. -/
theorem riemannHypothesis_of_cofinal_augmented_vacancy
    (κ : ℕ → Type*) [∀ j, Fintype (κ j)]
    (M : ℕ → ℕ) (hM : Tendsto M atTop atTop) (z : ∀ j, κ j → ℂ)
    (hs : ∀ j i, 0 < (z j i).re) (hs1 : ∀ j i, z j i ≠ 1)
    (hz : ∀ j i, riemannZeta (z j i) = 0)
    (hcert : Tendsto (fun j => certificateEnergy (lcmResidueIndex (M j)) (z j)) atTop (𝓝 0))
    (hrem : Tendsto (fun j => lcmRemainder (z j) (M j)) atTop (𝓝 0)) :
    RiemannHypothesis := by
  let γ : Fin 0 → ℝ := Fin.elim0
  let z₀ := fun i => criticalPoint (γ i)
  have hc₀ (N : ℕ) : certificateEnergy N z₀ = 0 := by
    have hrange : Set.range (rowVector N z₀) = ∅ := by
      ext x
      constructor
      · rintro ⟨i, _⟩
        exact Fin.elim0 i.1
      · simp
    simp [certificateEnergy, certificateVector, synthesisSpan, hrange]
  have hsplit (j : ℕ) : lcmRemainder z₀ (M j) =
      certificateEnergy (lcmResidueIndex (M j)) (z j) + lcmRemainder (z j) (M j) := by
    have ha := lcm_best_error_eq (M j) (z j) (hs j) (hs1 j) (hz j)
    have hb := lcm_best_error_eq (M j) z₀
      (fun i => Fin.elim0 i) (fun i => Fin.elim0 i) (fun i => Fin.elim0 i)
    rw [hc₀, add_zero] at hb
    linarith only [ha, hb]
  have hγ : Function.Injective γ := by
    intro i
    exact Fin.elim0 i
  apply riemannHypothesis_of_cofinal_remainder_upper γ
    hγ (fun i => Fin.elim0 i) (fun i => Fin.elim0 i) M hM
    (fun j => certificateEnergy (lcmResidueIndex (M j)) (z j) + lcmRemainder (z j) (M j))
  · simpa only [zero_add] using hcert.add hrem
  · exact Eventually.of_forall (fun j => (hsplit j).le)

end RiemannResearch.RH.Pareto.ResidueMellin
