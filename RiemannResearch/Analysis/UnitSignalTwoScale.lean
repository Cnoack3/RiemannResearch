import Mathlib.Data.Real.Basic
import Mathlib.Topology.Algebra.GroupWithZero
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Unit-signal two-scale algebra

Source: user-provided `Final_Limit_Unit_Signal_Residues_2026-10-11 (1).md`,
Sections 4--6, for the dilation/scalar strategy; the relaxed constants and
polynomial detector are the algebraic continuation described in
`RH/UnitSignalLimit20261013.md`.

The lemmas are abstract real algebra. They do not define the actual residue
atoms, the zeta(2) measure, orthogonal projections, or the optimized coefficients.
In particular, their hypotheses are NOT assertions that the required arithmetic
bounds hold for the actual optimizers, and this file does not prove RH.

Intended application of the two-scale hypotheses:

* `x = δ_(2M)` and `y = δ_M`;
* `z = (1 - 4*x) * ℓ_(2M) / κ`;
* the projection/dilation argument must separately supply
  `(x + z)^2 ≤ x*y/2`;
* a scalar allowance `ℓ_(2M) ≥ -κ*e_(2M)/4 - ε` corresponds to
  `z ≥ -x/4 - b`, where `b = (1 - 4*x)*ε/κ`.

The detector hypothesis `2*(κ*e + ℓ)^2 ≤ (κ*e)^2` likewise has to be
proved for the actual limiting projection. It is kept explicit here.

The all-dyadic fixed-relative allowance yields a power-law rate in the conductor.
It is an algebraic consequence, not a recommended arithmetic conjecture:
independent Nyman--Beurling logarithmic lower bounds obstruct such a uniform
rate for the actual residue approximation errors. Those external lower bounds
are not formalized in this module. A hypothesis on a sparse cofinal subsequence
is different from requiring a uniform allowance at every dyadic stage.

-/

namespace RiemannResearch.Analysis.UnitSignalTwoScale

open Filter

/-- A squared two-scale estimate tolerates an additive lower-bound error. -/
theorem two_scale_additive (x y z b : ℝ)
    (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hsq : (x + z) ^ 2 ≤ x * y / 2) (hz : -b ≤ z) :
    x ≤ y / 2 + 2 * b := by
  have hu : x + z ≤ x / 2 + y / 4 := by
    by_contra hnot
    have hbad : x / 2 + y / 4 < x + z := lt_of_not_ge hnot
    have hp :
        0 < ((x + z) - (x / 2 + y / 4)) *
          ((x + z) + (x / 2 + y / 4)) :=
      mul_pos (by linarith) (by linarith)
    nlinarith [sq_nonneg (2 * x - y)]
  linarith

/-- A negative allowance of one quarter of the defect still permits contraction. -/
theorem two_scale_quarter_relaxed (x y z b : ℝ)
    (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hsq : (x + z) ^ 2 ≤ x * y / 2) (hz : -x / 4 - b ≤ z) :
    x ≤ (8 / 9 : ℝ) * y + (8 / 3 : ℝ) * b := by
  have hu : x + z ≤ 3 * x / 8 + y / 3 := by
    by_contra hnot
    have hbad : 3 * x / 8 + y / 3 < x + z := lt_of_not_ge hnot
    have hp :
        0 < ((x + z) - (3 * x / 8 + y / 3)) *
          ((x + z) + (3 * x / 8 + y / 3)) :=
      mul_pos (by linarith) (by linarith)
    nlinarith [sq_nonneg (9 * x - 8 * y)]
  linarith

/-- The error-free quarter allowance gives the explicit contraction factor 8/9. -/
theorem two_scale_quarter_contraction (x y z : ℝ)
    (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hsq : (x + z) ^ 2 ≤ x * y / 2) (hz : -x / 4 ≤ z) :
    x ≤ (8 / 9 : ℝ) * y := by
  have h := two_scale_quarter_relaxed x y z 0 hx hy hsq (by simpa using hz)
  simpa using h

/-- A nonnegative scalar gives the stronger contraction factor 1/2. -/
theorem two_scale_nonnegative_contraction (x y z : ℝ)
    (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hsq : (x + z) ^ 2 ≤ x * y / 2) (hz : 0 ≤ z) :
    x ≤ y / 2 := by
  have h := two_scale_additive x y z 0 hx hy hsq (by simpa using hz)
  simpa using h

/-- The same 8/9 contraction survives the optimizer-error transform. -/
theorem quarter_contraction_error_transform (x y : ℝ)
    (hx : 0 ≤ x) (hy : 0 ≤ y)
    (hxden : 0 < 1 - 4 * x) (hyden : 0 < 1 - 4 * y)
    (hxy : x ≤ (8 / 9 : ℝ) * y) :
    x / (1 - 4 * x) ≤ (8 / 9 : ℝ) * (y / (1 - 4 * y)) := by
  have hcross :
      x * (1 - 4 * y) ≤ ((8 / 9 : ℝ) * y) * (1 - 4 * x) := by
    nlinarith [mul_nonneg hx hy]
  calc
    x / (1 - 4 * x) ≤ ((8 / 9 : ℝ) * y) / (1 - 4 * y) :=
      (div_le_div_iff₀ hxden hyden).2 hcross
    _ = (8 / 9 : ℝ) * (y / (1 - 4 * y)) := by ring

/-- An elementary recurrence bound; no claim of convergence is implicit. -/
theorem geometric_upper_bound (u : ℕ → ℝ) (q : ℝ)
    (hq : 0 ≤ q) (hstep : ∀ n : ℕ, u (n + 1) ≤ q * u n) :
    ∀ n : ℕ, u n ≤ q ^ n * u 0 := by
  intro n
  induction n with
  | zero => simp
  | succ n ih =>
      calc
        u (n + 1) ≤ q * u n := hstep n
        _ ≤ q * (q ^ n * u 0) := mul_le_mul_of_nonneg_left ih hq
        _ = q ^ (n + 1) * u 0 := by rw [pow_succ]; ring

/-- Iterating the quarter contraction produces a geometric upper bound. -/
theorem quarter_geometric_upper_bound (u : ℕ → ℝ)
    (hstep : ∀ n : ℕ, u (n + 1) ≤ (8 / 9 : ℝ) * u n) :
    ∀ n : ℕ, u n ≤ (8 / 9 : ℝ) ^ n * u 0 :=
  geometric_upper_bound u (8 / 9 : ℝ) (by norm_num) hstep

/-- The polynomial detector forces its scalar coordinate to be nonpositive. -/
theorem detector_nonpositive (κ e ell : ℝ)
    (hk : 0 < κ) (he : 0 ≤ e)
    (hdet : 2 * (κ * e + ell) ^ 2 ≤ (κ * e) ^ 2) :
    ell ≤ 0 := by
  have ha : 0 ≤ κ * e := mul_nonneg (le_of_lt hk) he
  by_contra hnot
  have hell : 0 < ell := lt_of_not_ge hnot
  have hs : 0 < ell * ell := mul_pos hell hell
  nlinarith [mul_nonneg ha (le_of_lt hell), sq_nonneg (κ * e)]

/-- Vanishing of the detector coordinate is exactly vanishing of the energy. -/
theorem detector_zero_iff (κ e ell : ℝ)
    (hk : 0 < κ)
    (hdet : 2 * (κ * e + ell) ^ 2 ≤ (κ * e) ^ 2) :
    ell = 0 ↔ e = 0 := by
  constructor
  · intro hell
    have ha : κ * e = 0 := by
      rw [hell] at hdet
      have hs : (κ * e) * (κ * e) = 0 := by
        nlinarith [sq_nonneg (κ * e)]
      exact (mul_eq_zero.mp hs).elim id id
    exact (mul_eq_zero.mp ha).resolve_left (ne_of_gt hk)
  · intro he
    rw [he] at hdet
    nlinarith [sq_nonneg ell]

/-- A fixed negative quarter allowance already forces the energy to vanish. -/
theorem detector_zero_of_quarter_lower_bound (κ e ell : ℝ)
    (hk : 0 < κ) (he : 0 ≤ e)
    (hdet : 2 * (κ * e + ell) ^ 2 ≤ (κ * e) ^ 2)
    (hlower : -(κ * e) / 4 ≤ ell) :
    e = 0 := by
  have ha : 0 ≤ κ * e := mul_nonneg (le_of_lt hk) he
  have hp :
      0 ≤ ((κ * e + ell) - 3 * (κ * e) / 4) *
        ((κ * e + ell) + 3 * (κ * e) / 4) :=
    mul_nonneg (by linarith) (by linarith)
  have hazero : κ * e = 0 := by
    have hs : (κ * e) * (κ * e) = 0 := by
      nlinarith [sq_nonneg (κ * e)]
    exact (mul_eq_zero.mp hs).elim id id
  exact (mul_eq_zero.mp hazero).resolve_left (ne_of_gt hk)

/--
An eventual quarter allowance with a vanishing additive error forces the
limiting energy to be zero. This is also applicable to a convergent subsequence;
the theorem does not assert that the actual optimizers satisfy its allowance.
-/
theorem limit_zero_of_eventual_quarter_allowance
    (energy scalar allowance : ℕ → ℝ) (κ e ell : ℝ)
    (hk : 0 < κ) (he : 0 ≤ e)
    (henergy : Filter.Tendsto energy Filter.atTop (nhds e))
    (hscalar : Filter.Tendsto scalar Filter.atTop (nhds ell))
    (hallowance : Filter.Tendsto allowance Filter.atTop (nhds 0))
    (hlower : ∀ᶠ n in Filter.atTop,
      -(κ * energy n) / 4 - allowance n ≤ scalar n)
    (hdet : 2 * (κ * e + ell) ^ 2 ≤ (κ * e) ^ 2) :
    e = 0 := by
  have hmul :
      Filter.Tendsto (fun n => κ * energy n) Filter.atTop (nhds (κ * e)) :=
    tendsto_const_nhds.mul henergy
  have hdiv :
      Filter.Tendsto (fun n => -(κ * energy n) / 4) Filter.atTop
        (nhds (-(κ * e) / 4)) :=
    hmul.neg.div_const 4
  have hleft :
      Filter.Tendsto (fun n => -(κ * energy n) / 4 - allowance n)
        Filter.atTop (nhds (-(κ * e) / 4)) := by
    simpa using hdiv.sub hallowance
  have hlimit : -(κ * e) / 4 ≤ ell :=
    le_of_tendsto_of_tendsto hleft hscalar hlower
  exact detector_zero_of_quarter_lower_bound κ e ell hk he hdet hlimit

end RiemannResearch.Analysis.UnitSignalTwoScale
