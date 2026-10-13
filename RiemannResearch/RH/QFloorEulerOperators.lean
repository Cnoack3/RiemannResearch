import RiemannResearch.RH.QFloorDilation
import RiemannResearch.Analysis.ClosedInvariantCalculus
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Convergent local Euler operators on the actual Q legal closure

Source: user-provided prime convolution and exp/log proposal, 13 October 2026.
The multiplicative floor-dilation representation makes each prime Euler
factor a genuine bounded invertible operator. Both the factor and its
Neumann inverse preserve the legal closure. The exact membership equivalence
is important: this calculus cannot by itself insert a new target into it.
No convergence of an undamped product over all primes is asserted.
-/

noncomputable section
open scoped BigOperators Topology
namespace RiemannResearch.RH.QFloorEulerOperators
open ZetaTwoHilbert QFloorDilation QFullResidueProjection
open RiemannResearch.Analysis.ClosedInvariantCalculus

theorem floorDilation_pow (m : ℕ) (hm : 0 < m) (k : ℕ) :
    floorDilation m hm ^ k = floorDilation (m ^ k) (pow_pos hm k) := by
  induction k with
  | zero => simp; rfl
  | succ k ih =>
    rw [pow_succ, ih]
    change (floorDilation (m ^ k) _).comp (floorDilation m hm) = _
    rw [floorDilation_comp]
    simp only [pow_succ]

/-- A geometric majorant valid even for the prime two. -/
theorem floorDilation_pow_norm_le (m : ℕ) (hm : 0 < m) (k : ℕ) :
    ‖floorDilation m hm ^ k‖ ≤
      Real.sqrt 2 * (Real.sqrt (1 / (m : ℝ))) ^ k := by
  rw [floorDilation_pow]
  refine (floorDilation_opNorm_le _ _).trans_eq ?_
  apply (sq_eq_sq₀ (Real.sqrt_nonneg _)
    (mul_nonneg (Real.sqrt_nonneg _) (pow_nonneg (Real.sqrt_nonneg _) _))).mp
  have hr : (Real.sqrt (1 / (m : ℝ))) ^ 2 = 1 / (m : ℝ) :=
    Real.sq_sqrt (by positivity)
  have hp : ((Real.sqrt (1 / (m : ℝ))) ^ k) ^ 2 = (1 / (m : ℝ)) ^ k := by
    rw [← pow_mul, Nat.mul_comm k 2, pow_mul, hr]
  rw [Real.sq_sqrt (by positivity), mul_pow, Real.sq_sqrt (by norm_num), hp]
  simp only [Nat.cast_pow, div_pow, one_pow]
  ring

/-- Every nontrivial integer floor dilation has a convergent Neumann series. -/
theorem floorDilation_powers_summable (m : ℕ) (hm : 1 < m) :
    Summable (fun k : ℕ => floorDilation m (by omega) ^ k) := by
  have hmR : (1 : ℝ) < m := by exact_mod_cast hm
  have hlt : Real.sqrt (1 / (m : ℝ)) < 1 := by
    have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 1 / (m : ℝ) by positivity)
    have hd : (1 : ℝ) / m < 1 := (div_lt_one (by positivity)).mpr hmR
    nlinarith [Real.sqrt_nonneg (1 / (m : ℝ))]
  have hg : Summable (fun k : ℕ => (Real.sqrt (1 / (m : ℝ))) ^ k) :=
    summable_geometric_of_norm_lt_one (by
      simpa only [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)] using hlt)
  exact (hg.mul_left (Real.sqrt 2)).of_norm_bounded
    (floorDilation_pow_norm_le m (by omega))

theorem floorDilation_invariant (m : ℕ) (hm : 0 < m) :
    floorDilation m hm ∈ invariantAlgebra closure :=
  floorDilation_mem_legalClosure m hm

/-- The actual local Euler inverse, including all prime-power terms. -/
def eulerInverse (m : ℕ) (hm : 1 < m) : QHilbert →L[ℝ] QHilbert :=
  neumann (floorDilation m (by omega))

theorem eulerInverse_left (m : ℕ) (hm : 1 < m) :
    eulerInverse m hm * (1 - floorDilation m (by omega)) = 1 :=
  neumann_mul_one_sub (floorDilation_powers_summable m hm)

theorem eulerInverse_right (m : ℕ) (hm : 1 < m) :
    (1 - floorDilation m (by omega)) * eulerInverse m hm = 1 :=
  one_sub_mul_neumann (floorDilation_powers_summable m hm)

/-- Applying a prime Euler factor does not alter membership in the legal closure. -/
theorem eulerFactor_mem_iff (m : ℕ) (hm : 1 < m) (f : QHilbert) :
    (1 - floorDilation m (by omega)) f ∈ closure ↔ f ∈ closure := by
  constructor
  · intro hf
    have h := neumann_apply_mem closure (by exact isClosed_closure)
      (floorDilation_mem_legalClosure m (by omega)) hf
    have he : neumann (floorDilation m (by omega))
        ((1 - floorDilation m (by omega)) f) = f := by
      change (neumann (floorDilation m (by omega)) *
        (1 - floorDilation m (by omega))) f = f
      rw [neumann_mul_one_sub (floorDilation_powers_summable m hm)]
      rfl
    rwa [he] at h
  · intro hf
    exact closure.sub_mem hf (floorDilation_mem_legalClosure m (by omega) f hf)

/-- Ordered finite prime products are actual operators; primality also gives
the strict contraction of prime-power iterates needed by their inverses. -/
def primeEulerProduct (ps : List {p : ℕ // p.Prime}) : QHilbert →L[ℝ] QHilbert :=
  (ps.map (fun p => 1 - floorDilation p.val p.property.pos)).prod

theorem primeEulerProduct_mem_iff (ps : List {p : ℕ // p.Prime}) (f : QHilbert) :
    primeEulerProduct ps f ∈ closure ↔ f ∈ closure := by
  induction ps with
  | nil => simp [primeEulerProduct]
  | cons p ps ih =>
    change (1 - floorDilation p.val p.property.pos) (primeEulerProduct ps f) ∈
      closure ↔ f ∈ closure
    rw [eulerFactor_mem_iff p.val p.property.one_lt, ih]

/-- The exact two-prime expansion retains the mixed conductor. -/
theorem two_euler_factors (p q : ℕ) (hp : 0 < p) (hq : 0 < q)
    (f : QHilbert) :
    (1 - floorDilation p hp) ((1 - floorDilation q hq) f) =
      f - floorDilation p hp f - floorDilation q hq f +
        floorDilation (p * q) (Nat.mul_pos hp hq) f := by
  change (f - floorDilation q hq f) -
    floorDilation p hp (f - floorDilation q hq f) = _
  rw [map_sub]
  have hc := congrArg (fun T : QHilbert →L[ℝ] QHilbert => T f)
    (floorDilation_comp p q hp hq)
  simp only [ContinuousLinearMap.comp_apply] at hc
  rw [hc]
  abel

end RiemannResearch.RH.QFloorEulerOperators
