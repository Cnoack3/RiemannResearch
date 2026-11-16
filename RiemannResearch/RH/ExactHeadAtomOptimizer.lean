import RiemannResearch.RH.ExactHeadGcdAtoms
import RiemannResearch.RH.MobiusHeadGreenNormal
import RiemannResearch.Analysis.FiniteWeightedSpan
import Mathlib.Tactic

/-!
# Identification of the gcd-atom and Mobius floor optimizers
Source: user-provided "Exact-Head Green Profiles in the Nyman--Beurling Program",
27 July 2026, sections 2--4. Exact finite weighted normal equations determine
the residual, even when the chosen coefficient vector is not unique.
The period-endpoint atom vanishes on the nonterminal optimization domain.
-/
noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.Pareto.ExactHeadAtomOptimizer
open RiemannResearch.RH.ExactHeadGcdAtoms
open RiemannResearch.RH.ExactHeadGreenProfile
open RiemannResearch.Analysis.FiniteProfileEnergy
open RiemannResearch.Analysis.FiniteWeightedNormal
open MobiusHeadGreen

def target (P r : ℕ) : ℝ := atom P 1 r - 1

def atomNormalCoefficients (P x : ℕ) : ℕ → ℝ :=
  Classical.choose (exists_normal_finset (Finset.Icc 1 (P - 1)) (upperDivisors P x)
    (progressionWeight P) (fun r _ => progressionWeight_nonneg P r) (atom P) (target P))

def atomResidual (P x r : ℕ) : ℝ :=
  target P r - ∑ d ∈ upperDivisors P x, atomNormalCoefficients P x d * atom P d r

def atomEnergy (P x : ℕ) : ℝ :=
  energy (Finset.Icc 1 (P - 1)) (progressionWeight P) (atomResidual P x)

def atomProfile (P x d : ℕ) : ℝ :=
  (d : ℝ) * score (Finset.Icc 1 (P - 1)) (progressionWeight P) (atomResidual P x) d

theorem atomResidual_normal (P x : ℕ) :
    ∀ v ∈ upperSpan P x (atom P),
      pairing (Finset.Icc 1 (P - 1)) (progressionWeight P) (atomResidual P x) v = 0 := by
  apply pairing_eq_zero_on_span
  intro d hd
  have h := (Classical.choose_spec (exists_normal_finset
    (Finset.Icc 1 (P - 1)) (upperDivisors P x)
    (progressionWeight P) (fun r _ => progressionWeight_nonneg P r)
    (atom P) (target P))).2 d hd
  simpa only [pairing, atomResidual, atomNormalCoefficients, mul_comm, mul_left_comm,
    mul_assoc] using h

theorem atomResidual_sub_target_mem (P x : ℕ) :
    atomResidual P x - target P ∈ upperSpan P x (atom P) := by
  have heq : atomResidual P x - target P =
      -(∑ d ∈ upperDivisors P x, atomNormalCoefficients P x d • atom P d) := by
    funext r
    simp [atomResidual, Finset.sum_apply]
  rw [heq]
  apply Submodule.neg_mem
  apply Submodule.sum_mem
  intro d hd
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨d,hd,rfl⟩)

theorem floor_residual_sub_target_mem (P x : ℕ) (hP : 0 < P) (c : ℕ → ℝ)
    (hlow : ∀ d, 1 ≤ d → d ≤ x → c d = (ArithmeticFunction.moebius d : ℝ))
    (hdiv : ∀ d ∈ Finset.Icc 1 P, c d ≠ 0 → d ∣ P) :
    residual P c - target P ∈ upperSpan P x grid := by
  have hs (r : ℕ) : (∑ d ∈ Finset.Icc 1 P, c d * grid d r) =
      ∑ d ∈ P.divisors, c d * grid d r := by
    symm
    apply Finset.sum_subset
    · intro d hd
      exact Finset.mem_Icc.mpr ⟨Nat.pos_of_mem_divisors hd,
        Nat.le_of_dvd hP (Nat.dvd_of_mem_divisors hd)⟩
    · intro d hd hnd
      have hc : c d = 0 := by
        by_contra h
        exact hnd (Nat.mem_divisors.mpr ⟨hdiv d hd h, hP.ne'⟩)
      simp [hc]
  have heq : residual P c - target P =
      ∑ d ∈ P.divisors, (c d - (ArithmeticFunction.moebius d : ℝ)) • grid d := by
    funext r
    simp only [Pi.sub_apply, MobiusHeadGreen.residual, target, hs,
      atom_one_eq_moebius_grid P r hP.ne', Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    simp only [sub_mul, Finset.sum_sub_distrib]
    ring
  rw [heq]
  apply Submodule.sum_mem
  intro d hd
  by_cases hdx : d ≤ x
  · rw [hlow d (Nat.pos_of_mem_divisors hd) hdx, sub_self, zero_smul]
    exact Submodule.zero_mem _
  · apply Submodule.smul_mem
    exact Submodule.subset_span ⟨d, Finset.mem_filter.mpr ⟨hd, Nat.lt_of_not_ge hdx⟩,rfl⟩

theorem floor_residual_normal (P x : ℕ) (hP : 0 < P) (c : ℕ → ℝ)
    (hn : ∀ d ∈ Finset.Icc 1 P, x < d → d ∣ P →
      score (Finset.Icc 1 (P - 1)) (progressionWeight P) (residual P c) d = 0) :
    ∀ v ∈ upperSpan P x grid,
      pairing (Finset.Icc 1 (P - 1)) (progressionWeight P) (residual P c) v = 0 := by
  apply pairing_eq_zero_on_span
  intro d hd
  obtain ⟨hd,hxd⟩ := Finset.mem_filter.mp hd
  exact hn d (Finset.mem_Icc.mpr ⟨Nat.pos_of_mem_divisors hd,
    Nat.le_of_dvd hP (Nat.dvd_of_mem_divisors hd)⟩) hxd (Nat.dvd_of_mem_divisors hd)

/-- The paper's actual atom optimizer is exactly the floor-normal residual. -/
theorem floor_residual_eq_atomResidual (P x : ℕ) (hP : 0 < P) (c : ℕ → ℝ)
    (hlow : ∀ d, 1 ≤ d → d ≤ x → c d = (ArithmeticFunction.moebius d : ℝ))
    (hdiv : ∀ d ∈ Finset.Icc 1 P, c d ≠ 0 → d ∣ P)
    (hn : ∀ d ∈ Finset.Icc 1 P, x < d → d ∣ P →
      score (Finset.Icc 1 (P - 1)) (progressionWeight P) (residual P c) d = 0) :
    ∀ r ∈ Finset.Icc 1 (P - 1), residual P c r = atomResidual P x r := by
  have ha := atomResidual_sub_target_mem P x
  rw [upper_spans_eq P x hP.ne'] at ha
  have hd : residual P c - atomResidual P x ∈ upperSpan P x grid := by
    have hh := Submodule.sub_mem _ (floor_residual_sub_target_mem P x hP c hlow hdiv) ha
    convert hh using 1 <;> abel
  have han := atomResidual_normal P x
  rw [upper_spans_eq P x hP.ne'] at han
  exact normal_residual_unique _ _ _ _ (upperSpan P x grid)
    (fun r hr => progressionWeight_pos P r hP (Finset.mem_Icc.mp hr).1)
    (floor_residual_normal P x hP c hn) han hd

theorem primorial_residual_eq_atomResidual (x r : ℕ)
    (hr : r ∈ Finset.Icc 1 (greenPeriod x - 1)) :
    residual (greenPeriod x) (primorialNormalCoefficients x) r =
      atomResidual (greenPeriod x) x r :=
  floor_residual_eq_atomResidual (greenPeriod x) x
    (lt_of_le_of_lt (Nat.zero_le x) (greenPeriod_gt x)) (primorialNormalCoefficients x)
    (primorialNormalCoefficients_spec x).1 (primorialNormalCoefficients_spec x).2.1
    (primorialNormalCoefficients_spec x).2.2 r hr

theorem primorial_q_eq_atomEnergy (x : ℕ) :
    q (greenPeriod x) (primorialNormalCoefficients x) = atomEnergy (greenPeriod x) x := by
  unfold q atomEnergy energy
  apply Finset.sum_congr rfl
  intro r hr
  rw [primorial_residual_eq_atomResidual x r hr]

theorem primorial_profile_eq_atomProfile (x d : ℕ) :
    profile (greenPeriod x) (primorialNormalCoefficients x) d =
      atomProfile (greenPeriod x) x d := by
  unfold profile atomProfile score pairing
  congr 1
  apply Finset.sum_congr rfl
  intro r hr
  rw [primorial_residual_eq_atomResidual x r hr]

/-- The same two analytic obligations now refer to the actual gcd-atom fit. -/
theorem riemannHypothesis_of_atom_profile_deficit (h : ℕ → ℕ → ℝ)
    (δ C B : ℝ) (hδ : 0 < δ) (hC : 0 ≤ C)
    (hdata : ∀ J, ∃ x, J ≤ x ∧
      mass (Finset.Icc 1 x) MobiusAffineProfile.weight *
        energy (Finset.Icc 1 x) MobiusAffineProfile.weight
          (fun d => atomProfile (greenPeriod x) x d - h x d) ≤
            C * atomEnergy (greenPeriod x) x ∧
      MobiusAffineProfile.signedSum x (h x) ≤
        (1 - δ) * atomEnergy (greenPeriod x) x + B) : RiemannHypothesis := by
  apply riemannHypothesis_of_primorial_profile_deficit h δ C B hδ hC
  simpa only [primorial_q_eq_atomEnergy, primorial_profile_eq_atomProfile] using hdata

end RiemannResearch.RH.Pareto.ExactHeadAtomOptimizer
