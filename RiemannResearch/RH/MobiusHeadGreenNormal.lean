import RiemannResearch.Analysis.FiniteWeightedNormal
import RiemannResearch.RH.MobiusHeadGreen
import Mathlib.NumberTheory.Primorial

/-!
# Existence of actual upper-divisor normal coefficients
Finite nonnegative least squares provides the upper normal equations without
a Gram inverse or rank assumption. The period must cover the nonzero Mobius
coefficients below x. No energy or signed-moment estimate is supplied here.
-/
noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.Pareto.MobiusHeadGreen
open RiemannResearch.RH.ExactHeadGreenProfile
open RiemannResearch.Analysis.FiniteProfileEnergy
open RiemannResearch.Analysis.FiniteWeightedNormal

theorem exists_mobius_head_normal_coefficients (P x : ℕ) (hx : x ≤ P)
    (hcover : ∀ d, 1 ≤ d → d ≤ x → ArithmeticFunction.moebius d ≠ 0 → d ∣ P) :
    ∃ c : ℕ → ℝ,
      (∀ d, 1 ≤ d → d ≤ x → c d = (ArithmeticFunction.moebius d : ℝ)) ∧
      (∀ d ∈ Finset.Icc 1 P, c d ≠ 0 → d ∣ P) ∧
      (∀ d ∈ Finset.Icc 1 P, x < d → d ∣ P →
        score (Finset.Icc 1 (P - 1)) (progressionWeight P) (residual P c) d = 0) := by
  classical
  let D := (Finset.Icc 1 P).filter (fun d => x < d ∧ d ∣ P)
  let y : ℕ → ℝ := fun r => 1 -
    ∑ d ∈ Finset.Icc 1 x, (ArithmeticFunction.moebius d : ℝ) * grid d r
  obtain ⟨u,hu0,hun⟩ := exists_normal_finset (Finset.Icc 1 (P - 1)) D
    (progressionWeight P) (fun r _ => progressionWeight_nonneg P r) grid y
  let c : ℕ → ℝ := fun d => (if d ≤ x then (ArithmeticFunction.moebius d : ℝ) else 0) + u d
  have huhead (d : ℕ) (hd : d ≤ x) : u d = 0 := by
    apply hu0
    intro h
    have := (Finset.mem_filter.mp h).2.1
    omega
  have hufull (r : ℕ) :
      (∑ d ∈ Finset.Icc 1 P, u d * grid d r) = ∑ d ∈ D, u d * grid d r := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro d hd hnd
    rw [hu0 d hnd,zero_mul]
  have hlfilter : (Finset.Icc 1 P).filter (fun d => d ≤ x) = Finset.Icc 1 x := by
    ext d
    simp only [Finset.mem_filter, Finset.mem_Icc]
    omega
  have hres (r : ℕ) : residual P c r = -(y r - ∑ d ∈ D, u d * grid d r) := by
    unfold residual
    simp only [c, add_mul, Finset.sum_add_distrib, ite_mul, zero_mul]
    rw [← Finset.sum_filter,hlfilter,hufull]
    unfold y
    ring
  refine ⟨c,?_,?_,?_⟩
  · intro d hd hdx
    simp [c,hdx,huhead d hdx]
  · intro d hd hcd
    by_cases hdx : d ≤ x
    · apply hcover d (Finset.mem_Icc.mp hd).1 hdx
      intro hmu
      exact hcd (by simp [c,hdx,hmu,huhead d hdx])
    · have hu : u d ≠ 0 := by simpa [c,hdx] using hcd
      have hdD : d ∈ D := by
        by_contra h
        exact hu (hu0 d h)
      exact (Finset.mem_filter.mp hdD).2.2
  · intro d hd hxd hdiv
    have hdD : d ∈ D := Finset.mem_filter.mpr ⟨hd,hxd,hdiv⟩
    have hn := hun d hdD
    unfold score pairing
    calc
      _ = ∑ r ∈ Finset.Icc 1 (P - 1),
          -(progressionWeight P r * grid d r * (y r - ∑ k ∈ D, u k * grid k r)) := by
        apply Finset.sum_congr rfl
        intro r hr
        rw [hres]
        ring
      _ = -(∑ r ∈ Finset.Icc 1 (P - 1),
          progressionWeight P r * grid d r * (y r - ∑ k ∈ D, u k * grid k r)) :=
        Finset.sum_neg_distrib _
      _ = 0 := by rw [hn,neg_zero]


def greenPeriod (x : ℕ) : ℕ := primorial (x + 1)

theorem greenPeriod_gt (x : ℕ) : x < greenPeriod x :=
  (Nat.lt_succ_self x).trans_le le_primorial_self

theorem greenPeriod_covers (x d : ℕ) (hd : 1 ≤ d) (hdx : d ≤ x)
    (hmu : ArithmeticFunction.moebius d ≠ 0) : d ∣ greenPeriod x :=
  (ArithmeticFunction.moebius_ne_zero_iff_squarefree.mp hmu).dvd_primorial.trans
    (primorial_dvd_primorial (hdx.trans (Nat.le_succ x)))

theorem exists_primorial_normal_coefficients (x : ℕ) :
    ∃ c : ℕ → ℝ,
      (∀ d, 1 ≤ d → d ≤ x → c d = (ArithmeticFunction.moebius d : ℝ)) ∧
      (∀ d ∈ Finset.Icc 1 (greenPeriod x), c d ≠ 0 → d ∣ greenPeriod x) ∧
      (∀ d ∈ Finset.Icc 1 (greenPeriod x), x < d → d ∣ greenPeriod x →
        score (Finset.Icc 1 (greenPeriod x - 1)) (progressionWeight (greenPeriod x))
          (residual (greenPeriod x) c) d = 0) :=
  exists_mobius_head_normal_coefficients (greenPeriod x) x (greenPeriod_gt x).le
    (greenPeriod_covers x)

/-- An actual exact finite least-squares choice; no numeric oracle is used. -/
def primorialNormalCoefficients (x : ℕ) : ℕ → ℝ :=
  Classical.choose (exists_primorial_normal_coefficients x)

theorem primorialNormalCoefficients_spec (x : ℕ) :
    (∀ d, 1 ≤ d → d ≤ x →
      primorialNormalCoefficients x d = (ArithmeticFunction.moebius d : ℝ)) ∧
    (∀ d ∈ Finset.Icc 1 (greenPeriod x),
      primorialNormalCoefficients x d ≠ 0 → d ∣ greenPeriod x) ∧
    (∀ d ∈ Finset.Icc 1 (greenPeriod x), x < d → d ∣ greenPeriod x →
      score (Finset.Icc 1 (greenPeriod x - 1)) (progressionWeight (greenPeriod x))
        (residual (greenPeriod x) (primorialNormalCoefficients x)) d = 0) :=
  Classical.choose_spec (exists_primorial_normal_coefficients x)

/-- Only the two cofinal analytic estimates remain: all finite arithmetic,
normal equations, legality, heads, root, charge and norm split are provided. -/
theorem riemannHypothesis_of_primorial_profile_deficit (h : ℕ → ℕ → ℝ)
    (δ C B : ℝ) (hδ : 0 < δ) (hC : 0 ≤ C)
    (hdata : ∀ J, ∃ x, J ≤ x ∧
      mass (Finset.Icc 1 x) MobiusAffineProfile.weight *
        energy (Finset.Icc 1 x) MobiusAffineProfile.weight
          (fun d => profile (greenPeriod x) (primorialNormalCoefficients x) d - h x d) ≤
            C * q (greenPeriod x) (primorialNormalCoefficients x) ∧
      MobiusAffineProfile.signedSum x (h x) ≤
        (1 - δ) * q (greenPeriod x) (primorialNormalCoefficients x) + B) :
    RiemannHypothesis := by
  apply riemannHypothesis_of_cofinal_mobius_profile_deficit greenPeriod greenPeriod_gt
    primorialNormalCoefficients h
    (fun x => (primorialNormalCoefficients_spec x).1)
    (fun x => (primorialNormalCoefficients_spec x).2.1) _ δ C B hδ hC hdata
  intro x d hd hxd hc
  exact (primorialNormalCoefficients_spec x).2.2 d hd hxd
    ((primorialNormalCoefficients_spec x).2.1 d hd hc)

end RiemannResearch.RH.Pareto.MobiusHeadGreen
