/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.Analysis.RationalInterval
import Mathlib.Data.Finset.Max
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-!
# Sound rational Neumann certificates for finite real linear systems

Source: the exact-rational interval algorithms accompanying the user's
7 November 2026 canonical and reciprocal-head reviews. Rational centers
and preconditioners may be proposed by any external calculation. Only the
finite defect and residual endpoint checks enter the certificate. Actual
matrix and right-hand-side enclosures remain explicit proved inputs.
-/

noncomputable section
open scoped BigOperators

namespace RiemannResearch.Analysis.FiniteNeumannCertificate
variable {ι : Type*} [Fintype ι] [Nonempty ι] [DecidableEq ι]

/-- Finite-dimensional maximum-norm error bound, proved directly from the
exact fixed-point identity. No analytic Neumann series is trusted. -/
theorem coordinate_error_bound (E : ι → ι → ℝ) (r e : ι → ℝ) (θ ρ : ℝ)
    (hθ : θ < 1)
    (hrows : ∀ i, (∑ j, |E i j|) ≤ θ)
    (hres : ∀ i, |r i| ≤ ρ)
    (hfix : ∀ i, e i = (∑ j, E i j * e j) + r i) :
    ∀ i, |e i| ≤ ρ / (1 - θ) := by
  classical
  obtain ⟨m, _, hm⟩ := Finset.exists_max_image Finset.univ
    (fun i => |e i|) Finset.univ_nonempty
  have hmax : ∀ j, |e j| ≤ |e m| := fun j => hm j (Finset.mem_univ j)
  have hstep : |e m| ≤ θ * |e m| + ρ := by
    calc
      |e m| = |(∑ j, E m j * e j) + r m| := congrArg abs (hfix m)
      _ ≤ |∑ j, E m j * e j| + |r m| := abs_add_le _ _
      _ ≤ (∑ j, |E m j * e j|) + ρ :=
        add_le_add (Finset.abs_sum_le_sum_abs _ _) (hres m)
      _ = (∑ j, |E m j| * |e j|) + ρ := by simp_rw [abs_mul]
      _ ≤ (∑ j, |E m j| * |e m|) + ρ := by
        exact add_le_add (Finset.sum_le_sum (fun j _ =>
          mul_le_mul_of_nonneg_left (hmax j) (abs_nonneg _))) le_rfl
      _ = (∑ j, |E m j|) * |e m| + ρ := by rw [Finset.sum_mul]
      _ ≤ θ * |e m| + ρ :=
        add_le_add (mul_le_mul_of_nonneg_right (hrows m) (abs_nonneg _)) le_rfl
  have hb : |e m| ≤ ρ / (1 - θ) := by
    apply (le_div_iff₀ (sub_pos.mpr hθ)).2
    nlinarith
  exact fun i => (hmax i).trans hb

/-- The exact preconditioned error equation behind the endpoint checker. -/
theorem preconditioned_error_identity
    (A R : ι → ι → ℝ) (b c x : ι → ℝ)
    (hsol : ∀ i, (∑ j, A i j * x j) = b i) (i : ι) :
    x i - c i =
      (∑ j, ((if i = j then 1 else 0) - ∑ k, R i k * A k j) * (x j - c j)) +
        ∑ k, R i k * (b k - ∑ j, A k j * c j) := by
  classical
  have hprod : (∑ j, (∑ k, R i k * A k j) * (x j - c j)) =
      ∑ k, R i k * (b k - ∑ j, A k j * c j) := by
    calc
      _ = ∑ j, ∑ k, R i k * (A k j * (x j - c j)) := by
        apply Finset.sum_congr rfl
        intro j _
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro k _
        ring
      _ = ∑ k, ∑ j, R i k * (A k j * (x j - c j)) := Finset.sum_comm
      _ = ∑ k, R i k * (∑ j, A k j * (x j - c j)) := by
        apply Finset.sum_congr rfl
        intro k _
        rw [Finset.mul_sum]
      _ = _ := by
        apply Finset.sum_congr rfl
        intro k _
        congr 1
        simp_rw [mul_sub, Finset.sum_sub_distrib]
        rw [hsol k]
  have hdiag : (∑ j, (if i = j then (1 : ℝ) else 0) * (x j - c j)) =
      x i - c i := by simp
  simp_rw [sub_mul]
  rw [Finset.sum_sub_distrib, hdiag, hprod]
  ring

end RiemannResearch.Analysis.FiniteNeumannCertificate

namespace RiemannResearch.RatInterval

def absBound (I : RatInterval) : ℚ := max |I.lo| |I.hi|

theorem abs_le_absBound {I : RatInterval} {x : ℝ} (hx : I.Contains x) :
    |x| ≤ (absBound I : ℝ) := by
  have hlo : -(max |(I.lo : ℝ)| |(I.hi : ℝ)|) ≤ x :=
    (neg_le_neg (le_max_left _ _)).trans ((neg_abs_le (I.lo : ℝ)).trans hx.1)
  have hhi : x ≤ max |(I.lo : ℝ)| |(I.hi : ℝ)| :=
    hx.2.trans ((le_abs_self (I.hi : ℝ)).trans (le_max_right _ _))
  simpa only [absBound, Rat.cast_max, Rat.cast_abs] using abs_le.mpr ⟨hlo, hhi⟩

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The interval for one entry of `Id - R A`. -/
def linearDefect (A : ι → ι → RatInterval) (R : ι → ι → ℚ) (i j : ι) :
    RatInterval :=
  sub (point (if i = j then 1 else 0))
    (sum Finset.univ (fun k => mul (point (R i k)) (A k j)))

/-- The interval for one entry of the preconditioned residual `R(b-Ac)`. -/
def linearResidual (A : ι → ι → RatInterval) (b : ι → RatInterval)
    (R : ι → ι → ℚ) (c : ι → ℚ) (i : ι) : RatInterval :=
  sum Finset.univ (fun k => mul (point (R i k))
    (sub (b k) (sum Finset.univ (fun j => mul (A k j) (point (c j))))))

theorem linearDefect_contains
    (AI : ι → ι → RatInterval) (A : ι → ι → ℝ) (R : ι → ι → ℚ)
    (hA : ∀ i j, (AI i j).Contains (A i j)) (i j : ι) :
    (linearDefect AI R i j).Contains
      ((if i = j then 1 else 0) - ∑ k, (R i k : ℝ) * A k j) := by
  apply contains_sub
  · by_cases h : i = j <;> simp only [h, if_true, if_false]
    · simpa only [Rat.cast_one] using contains_point 1
    · simpa only [Rat.cast_zero] using contains_point 0
  · exact contains_sum _ _ _ (fun k _ => contains_mul (contains_point _) (hA k j))

theorem linearResidual_contains
    (AI : ι → ι → RatInterval) (bI : ι → RatInterval)
    (A : ι → ι → ℝ) (b : ι → ℝ) (R : ι → ι → ℚ) (c : ι → ℚ)
    (hA : ∀ i j, (AI i j).Contains (A i j)) (hb : ∀ i, (bI i).Contains (b i))
    (i : ι) :
    (linearResidual AI bI R c i).Contains
      (∑ k, (R i k : ℝ) * (b k - ∑ j, A k j * (c j : ℝ))) := by
  apply contains_sum
  intro k _
  apply contains_mul (contains_point _)
  apply contains_sub (hb k)
  exact contains_sum _ _ _ (fun j _ => contains_mul (hA k j) (contains_point _))

def linearSolution (c : ι → ℚ) (θ ρ : ℚ) (i : ι) : RatInterval :=
  ⟨c i - ρ / (1 - θ), c i + ρ / (1 - θ)⟩

/-- A checkable rational certificate for every coordinate of an actual real
solution. Centers and approximate inverses are untrusted rational witnesses;
all acceptance conditions are finite rational inequalities. -/
theorem linearSolution_contains [Nonempty ι]
    (AI : ι → ι → RatInterval) (bI : ι → RatInterval)
    (A : ι → ι → ℝ) (b x : ι → ℝ) (R : ι → ι → ℚ) (c : ι → ℚ)
    (θ ρ : ℚ)
    (hA : ∀ i j, (AI i j).Contains (A i j)) (hb : ∀ i, (bI i).Contains (b i))
    (hθ : θ < 1)
    (hrows : ∀ i, (∑ j, absBound (linearDefect AI R i j)) ≤ θ)
    (hres : ∀ i, absBound (linearResidual AI bI R c i) ≤ ρ)
    (hsol : ∀ i, (∑ j, A i j * x j) = b i) :
    ∀ i, (linearSolution c θ ρ i).Contains (x i) := by
  let E : ι → ι → ℝ := fun i j =>
    (if i = j then 1 else 0) - ∑ k, (R i k : ℝ) * A k j
  let r : ι → ℝ := fun i =>
    ∑ k, (R i k : ℝ) * (b k - ∑ j, A k j * (c j : ℝ))
  have hrowsR : ∀ i, (∑ j, |E i j|) ≤ (θ : ℝ) := by
    intro i
    calc
      _ ≤ ∑ j, (absBound (linearDefect AI R i j) : ℝ) :=
        Finset.sum_le_sum (fun j _ => abs_le_absBound (linearDefect_contains AI A R hA i j))
      _ = ((∑ j, absBound (linearDefect AI R i j) : ℚ) : ℝ) := by norm_cast
      _ ≤ _ := by exact_mod_cast hrows i
  have hresR : ∀ i, |r i| ≤ (ρ : ℝ) := by
    intro i
    exact (abs_le_absBound (linearResidual_contains AI bI A b R c hA hb i)).trans
      (by exact_mod_cast hres i)
  have hfix : ∀ i, x i - (c i : ℝ) =
      (∑ j, E i j * (x j - (c j : ℝ))) + r i :=
    RiemannResearch.Analysis.FiniteNeumannCertificate.preconditioned_error_identity
      A (fun i j => (R i j : ℝ)) b (fun i => (c i : ℝ)) x hsol
  have he := RiemannResearch.Analysis.FiniteNeumannCertificate.coordinate_error_bound
    E r (fun i => x i - (c i : ℝ)) (θ : ℝ) (ρ : ℝ)
    (by exact_mod_cast hθ) hrowsR hresR hfix
  intro i
  have h := abs_le.mp (he i)
  unfold Contains linearSolution
  push_cast
  constructor <;> linarith [h.1, h.2]

end RiemannResearch.RatInterval
