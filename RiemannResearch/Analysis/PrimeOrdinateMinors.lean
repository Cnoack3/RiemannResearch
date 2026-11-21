/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import RiemannResearch.Analysis.PrimePhaseTorus
import RiemannResearch.Analysis.OrdinateLagPhase
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Prime phase determinants at two and three ordinates

Ford, Meng and Zaharescu, *Simultaneous distribution of the fractional parts
of Riemann zeta zeros*, Bull. Lond. Math. Soc. 49 (2017), 1–9,
https://doi.org/10.1112/blms.12001, supplies the one-ordinate prime-phase
setting. Here two fixed columns are sampled at different times. Their three
quadratic monomials give a signed three-row determinant. Its leading term in
norm retains both neighboring gaps, with an explicit fifth-order error.
-/

noncomputable section

namespace RiemannResearch.Analysis.PrimeOrdinateMinors

/-- The first Fourier character of the prime coordinate, in radians. -/
def atom (p : ℕ) (t : ℝ) : ℂ := OrdinateLagPhase.phase (Real.log p) t

theorem atom_eq_fourier (p : ℕ) (t : ℝ) :
    atom p t = fourier 1 (PrimePhaseTorus.primePhase p t) := by
  rw [PrimePhaseTorus.fourier_primePhase]
  simp only [atom, OrdinateLagPhase.phase, Int.cast_one, one_mul]

/-- The absolute angular frequency of the ratio of two columns. -/
def logDistance (p q : ℕ) : ℝ := |Real.log (q : ℝ) - Real.log (p : ℝ)|

theorem logDistance_nonneg (p q : ℕ) : 0 ≤ logDistance p q := abs_nonneg _

/-- The signed determinant of the two prime columns at times s and t. -/
def pairMinor (p q : ℕ) (s t : ℝ) : ℂ := atom p s * atom q t - atom q s * atom p t

/-- The three columns are the characters of p², pq, q², in that order. -/
def tripleMinor (p q : ℕ) (s t u : ℝ) : ℂ :=
  Matrix.det !![atom p s ^ 2, atom p s * atom q s, atom q s ^ 2;
                atom p t ^ 2, atom p t * atom q t, atom q t ^ 2;
                atom p u ^ 2, atom p u * atom q u, atom q u ^ 2]

/-- All orientation signs are retained, including the nonadjacent pair (s,u). -/
theorem tripleMinor_factor (p q : ℕ) (s t u : ℝ) :
    tripleMinor p q s t u = pairMinor p q s t * pairMinor p q s u * pairMinor p q t u := by
  simp [tripleMinor, Matrix.det_fin_three, pairMinor]
  ring

theorem pairMinor_factor (p q : ℕ) (s t : ℝ) :
    pairMinor p q s t = atom q s * atom p t *
      (Complex.exp (Complex.I * (((Real.log q - Real.log p) * (t-s) : ℝ) : ℂ)) - 1) := by
  have he : atom p s * atom q t = atom q s * atom p t *
      Complex.exp (Complex.I * (((Real.log q - Real.log p) * (t-s) : ℝ) : ℂ)) := by
    simp only [atom, OrdinateLagPhase.phase, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [pairMinor, he]
  ring

/-- Chord length for a real angular displacement (in radians). -/
def chord (x : ℝ) : ℝ := 2 * |Real.sin (x / 2)|

theorem chord_nonneg (x : ℝ) : 0 ≤ chord x := by unfold chord; positivity

private theorem chord_abs (x : ℝ) : chord |x| = chord x := by
  rcases le_total 0 x with h | h
  · rw [abs_of_nonneg h]
  · simp [chord, abs_of_nonpos h, neg_div]

theorem pairMinor_norm (p q : ℕ) (s t : ℝ) :
    ‖pairMinor p q s t‖ = chord (logDistance p q * |t-s|) := by
  rw [logDistance, ← abs_mul, chord_abs, pairMinor_factor, norm_mul, norm_mul]
  rw [Complex.norm_exp_I_mul_ofReal_sub_one]
  simp [atom, chord]

theorem chord_le {x : ℝ} (hx : 0 ≤ x) : chord x ≤ x := by
  have h : |Real.sin (x / 2)| ≤ |x / 2| := Real.abs_sin_le_abs
  rw [abs_of_nonneg (by positivity : 0 ≤ x / 2)] at h
  unfold chord
  linarith

/-- The constant 1/24 is the cubic coefficient of the chord deficit. -/
theorem chord_defect_le {x : ℝ} (hx : 0 ≤ x) : x - chord x ≤ x^3 / 24 := by
  have h := Real.sin_ge_sub_cube (show 0 ≤ x / 2 by positivity)
  have ha := le_abs_self (Real.sin (x/2))
  unfold chord
  linarith

private theorem product_chord_bounds {x y z : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (hz : 0 ≤ z) :
    0 ≤ x*y*z - chord x*chord y*chord z ∧
    x*y*z - chord x*chord y*chord z ≤ x*y*z*(x^2+y^2+z^2)/24 := by
  have cx := chord_nonneg x
  have cy := chord_nonneg y
  have cz := chord_nonneg z
  have lx := chord_le hx
  have ly := chord_le hy
  have lz := chord_le hz
  refine ⟨sub_nonneg.mpr ?_, ?_⟩
  · gcongr
  · have h₁ : (x-chord x)*y*z ≤ (x^3/24)*y*z := by
      gcongr; exact chord_defect_le hx
    have h₂ : chord x*(y-chord y)*z ≤ x*(y^3/24)*z := by
      have h := mul_le_mul lx (chord_defect_le hy) (sub_nonneg.mpr ly) hx
      exact mul_le_mul_of_nonneg_right h hz
    have h₃ : (chord x*chord y)*(z-chord z) ≤ (x*y)*(z^3/24) := by
      have hxy : chord x*chord y ≤ x*y := mul_le_mul lx ly cy hx
      exact mul_le_mul hxy (chord_defect_le hz) (sub_nonneg.mpr lz) (mul_nonneg hx hy)
    linarith only [h₁, h₂, h₃]

theorem tripleMinor_norm_gaps (p q : ℕ) (s : ℝ) {g h : ℝ} (hg : 0 ≤ g) (hh : 0 ≤ h) :
    ‖tripleMinor p q s (s+g) (s+g+h)‖ =
      chord (logDistance p q*g) * chord (logDistance p q*h) * chord (logDistance p q*(g+h)) := by
  rw [tripleMinor_factor, norm_mul, norm_mul, pairMinor_norm, pairMinor_norm, pairMinor_norm]
  rw [show s+g-s=g by ring, show s+g+h-s=g+h by ring, show s+g+h-(s+g)=h by ring,
    abs_of_nonneg hg, abs_of_nonneg hh, abs_of_nonneg (add_nonneg hg hh)]
  ring

/-- Pointwise mixed-gap main term and explicit one-sided fifth-order remainder. -/
theorem tripleMinor_defect (p q : ℕ) (s : ℝ) {g h : ℝ} (hg : 0 ≤ g) (hh : 0 ≤ h) :
    let d := logDistance p q
    0 ≤ d^3*g*h*(g+h) - ‖tripleMinor p q s (s+g) (s+g+h)‖ ∧
      d^3*g*h*(g+h) - ‖tripleMinor p q s (s+g) (s+g+h)‖ ≤
        d^5*g*h*(g+h)*(g^2+g*h+h^2)/12 := by
  dsimp only
  rw [tripleMinor_norm_gaps p q s hg hh]
  have hd := logDistance_nonneg p q
  have hb := product_chord_bounds (mul_nonneg hd hg) (mul_nonneg hd hh)
    (mul_nonneg hd (add_nonneg hg hh))
  constructor <;> linarith only [hb.1, hb.2]

/-- Each of the two remaining chord factors has length at most two. -/
theorem tripleMinor_norm_le_four_pair (p q : ℕ) (s t u : ℝ) :
    ‖tripleMinor p q s t u‖ ≤ 4 * ‖pairMinor p q s t‖ := by
  have h (v w : ℝ) : ‖pairMinor p q v w‖ ≤ 2 := by
    rw [pairMinor_norm, chord]
    have hs : |Real.sin (logDistance p q * |w-v| / 2)| ≤ 1 :=
      abs_le.mpr ⟨Real.neg_one_le_sin _, Real.sin_le_one _⟩
    linarith
  rw [tripleMinor_factor, norm_mul, norm_mul]
  calc
    _ ≤ ‖pairMinor p q s t‖ * 2 * 2 := by gcongr <;> apply h
    _ = _ := by ring

/-- Uniform arithmetic separation for a fixed additive shift, including shift two. -/
theorem logDistance_add_le (p k : ℕ) (hp : 0 < p) :
    logDistance p (p+k) ≤ (k : ℝ) / p := by
  have hp' : (0 : ℝ) < p := by exact_mod_cast hp
  have hk' : (0 : ℝ) ≤ k := Nat.cast_nonneg _
  rw [logDistance, Nat.cast_add, abs_of_nonneg (sub_nonneg.mpr (Real.log_le_log hp' (by linarith)))]
  rw [← Real.log_div (by positivity) hp'.ne']
  calc
    _ ≤ ((p : ℝ) + k) / p - 1 := Real.log_le_sub_one_of_pos (by positivity)
    _ = _ := by field_simp; ring

end RiemannResearch.Analysis.PrimeOrdinateMinors
