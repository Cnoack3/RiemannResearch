import RiemannResearch.RH.ExactHeadGcdAtoms
import RiemannResearch.Analysis.FiniteWeightedReturnDrift
import Mathlib.Tactic

/-!
# Activated gcd-atom moments for endpoint returns
Source: the audited Exact-Head Green Profiles supplement, (22.5) and
(23.21)--(23.24). These finite identities hold for any positive or signed
weights, arbitrary periods, and arbitrary divisor signals, not only primes.
They connect the basis-free endpoint theorem to the actual gcd-atom space.
No uniform inverse-Gram or signed-curvature estimate is inferred.
PDF: https://drive.google.com/file/d/1DHIp4gGwApIL1V6nHwV4HDxuOAFdijwG/view
-/
noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.ExactHeadAtomReturnMoments
open RiemannResearch.RH.ExactHeadGcdAtoms
open RiemannResearch.Analysis.FiniteProfileEnergy
open RiemannResearch.Analysis.FiniteWeightedReturnDrift

def prefixMoment (P Y : ℕ) (w h : ℕ → ℝ) (g : ℕ) : ℝ :=
  pairing (Finset.Icc 1 Y) w h (atom P g)

def upperDivisorSignal (P x p : ℕ) : ℕ → ℝ :=
  synthesis P (upperDivisors P x) (fun g => if p ∣ g then 1 else 0)

def activatedMoment (P x Y p : ℕ) (w h : ℕ → ℝ) : ℝ :=
  ∑ g ∈ (upperDivisors P x).filter (fun g => g ≤ Y),
    if p ∣ g then prefixMoment P Y w h g else 0

theorem prefixMoment_zero_above_cutoff (P Y g : ℕ) (w h : ℕ → ℝ)
    (hYg : Y < g) : prefixMoment P Y w h g = 0 := by
  unfold prefixMoment pairing
  apply Finset.sum_eq_zero
  intro r hr
  rw [atom_zero_of_lt P g r ((Finset.mem_Icc.mp hr).2.trans_lt hYg)]
  ring

theorem upperDivisorSignal_mem (P x p : ℕ) :
    upperDivisorSignal P x p ∈ upperSpan P x (atom P) := by
  have he : upperDivisorSignal P x p =
      ∑ g ∈ upperDivisors P x, (if p ∣ g then (1 : ℝ) else 0) • atom P g := by
    funext r
    simp [upperDivisorSignal,synthesis,Finset.sum_apply,ite_apply]
  rw [he]
  apply Submodule.sum_mem
  intro g hg
  apply Submodule.smul_mem
  exact Submodule.subset_span ⟨g,hg,rfl⟩

theorem prefix_pairing_synthesis (P Y : ℕ) (D : Finset ℕ)
    (w h c : ℕ → ℝ) :
    pairing (Finset.Icc 1 Y) w h (synthesis P D c) =
      ∑ g ∈ D, c g * prefixMoment P Y w h g := by
  unfold prefixMoment pairing synthesis
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro g hg
  apply Finset.sum_congr rfl
  intro r hr
  ring

/-- Only activated atoms x < g <= Y contribute, even though the return
profile itself runs through the complete upper-divisor family. -/
theorem upperDivisorSignal_prefix (P x Y p : ℕ) (w h : ℕ → ℝ) :
    pairing (Finset.Icc 1 Y) w h (upperDivisorSignal P x p) =
      activatedMoment P x Y p w h := by
  rw [upperDivisorSignal,prefix_pairing_synthesis]
  unfold activatedMoment
  calc
    _ = ∑ g ∈ upperDivisors P x,
        if p ∣ g then prefixMoment P Y w h g else 0 := by
      apply Finset.sum_congr rfl
      intro g hg
      split_ifs <;> simp
    _ = _ := by
      symm
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro g hg hng
      have hYg : Y < g := by
        by_contra! h
        exact hng (Finset.mem_filter.mpr ⟨hg,h⟩)
      simp [prefixMoment_zero_above_cutoff P Y g w h hYg]

/-- The full tail return is an exact activated-atom prefix moment. The
normal equations are the only assumptions; no matrix inverse is needed. -/
theorem endpoint_divisor_signal (P x Y p : ℕ) (T : Finset ℕ)
    (w C u v : ℕ → ℝ)
    (hglobal : ∀ f ∈ upperSpan P x (atom P),
      pairing (Finset.Icc 1 Y) w (C - u) f + pairing T w (C - u) f = 0)
    (htail : ∀ f ∈ upperSpan P x (atom P), pairing T w (C - v) f = 0) :
    pairing T w (u - v) (upperDivisorSignal P x p) =
      activatedMoment P x Y p w (C - u) := by
  rw [← endpoint_covariance (Finset.Icc 1 Y) T w C u v
    (upperSpan P x (atom P)) hglobal htail _ (upperDivisorSignal_mem P x p)]
  exact upperDivisorSignal_prefix P x Y p w (C - u)

/-- This is the complete p,q return difference from (22.5), for arbitrary
divisor labels. In particular, it covers the prime signals in (23.23). -/
theorem endpoint_signal_difference (P x Y p q : ℕ) (T : Finset ℕ)
    (w C u v : ℕ → ℝ)
    (hglobal : ∀ f ∈ upperSpan P x (atom P),
      pairing (Finset.Icc 1 Y) w (C - u) f + pairing T w (C - u) f = 0)
    (htail : ∀ f ∈ upperSpan P x (atom P), pairing T w (C - v) f = 0) :
    pairing T w (u - v) (upperDivisorSignal P x p - upperDivisorSignal P x q) =
      activatedMoment P x Y p w (C - u) - activatedMoment P x Y q w (C - u) := by
  have he : pairing T w (u-v) (upperDivisorSignal P x p - upperDivisorSignal P x q) =
      pairing T w (u-v) (upperDivisorSignal P x p) -
      pairing T w (u-v) (upperDivisorSignal P x q) := by
    simp [pairing,Pi.sub_apply,mul_sub,Finset.sum_sub_distrib]
  rw [he, endpoint_divisor_signal P x Y p T w C u v hglobal htail,
    endpoint_divisor_signal P x Y q T w C u v hglobal htail]

/-- The determinant numerator depends only on three activated moments.
The relation among coefficients makes reciprocal-affine cancellation explicit. -/
theorem triple_curvature_moment (P x Y p q r : ℕ) (T : Finset ℕ)
    (w C u v : ℕ → ℝ)
    (hglobal : ∀ f ∈ upperSpan P x (atom P),
      pairing (Finset.Icc 1 Y) w (C - u) f + pairing T w (C - u) f = 0)
    (htail : ∀ f ∈ upperSpan P x (atom P), pairing T w (C - v) f = 0) :
    (p : ℝ) * ((r : ℝ) - q) *
      pairing T w (u-v) (upperDivisorSignal P x p - upperDivisorSignal P x q) -
    (r : ℝ) * ((q : ℝ) - p) *
      pairing T w (u-v) (upperDivisorSignal P x q - upperDivisorSignal P x r) =
    (p : ℝ) * ((r : ℝ) - q) * activatedMoment P x Y p w (C-u) -
    (q : ℝ) * ((r : ℝ) - p) * activatedMoment P x Y q w (C-u) +
    (r : ℝ) * ((q : ℝ) - p) * activatedMoment P x Y r w (C-u) := by
  rw [endpoint_signal_difference P x Y p q T w C u v hglobal htail,
    endpoint_signal_difference P x Y q r T w C u v hglobal htail]
  ring

end RiemannResearch.RH.ExactHeadAtomReturnMoments
