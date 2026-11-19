/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.Analysis.ConreyHorizontalStopLoss
import RiemannResearch.RH.WeilExplicitFormula.ThmD.Functional
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Two-neighbor isolation in the full zeta zero array

Cheolmin Kim, Hexagon 2611.00318v1, Proposition 4.2 and Sections 5–6.
<https://hexagonmath.org/pdf/2611.00318v1>
The analytic transfer and the new strict numerical majorant are separate
inputs. The finite reflection identity fixes the factor 4π between the
physical and normalized ordinate scales. The reproducible interval evaluation
is recorded in RiemannResearch/RH/BoundCertificateReplays20261119.md.
-/

noncomputable section
open Filter Set Zeta23
open scoped BigOperators Topology

namespace RiemannResearch.Analysis.ActualZeroOrdinate
open ZeroOrdinate

/-- The first zero is excluded and every other positive zero in the infinite
array is tested, including ordinates above the height cutoff. -/
def KimIsolatedCopy (T c : ℝ) (j : Copies T) : Prop :=
  zeroMult j.1.1 = 1 ∧
    (∃ w : ℂ, IsNontrivialZero w ∧ 0 < w.im ∧ w.im < j.1.1.im) ∧
    ∀ w : ℂ, IsNontrivialZero w → 0 < w.im → w ≠ j.1.1 →
      2 * Real.pi * c / Real.log T < |w.im - j.1.1.im|

/-- The denominator counts every occurrence, including off-line copies. -/
def kimIsolatedProportion (T c : ℝ) : ℝ := by
  classical
  exact (∑ j : Copies T, if KimIsolatedCopy T c j then (1 : ℝ) else 0) / (Ncount 0 T : ℝ)

def KimIsolationLower (c b : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ T : ℝ in atTop, b - ε ≤ kimIsolatedProportion T c

/-- The positive part vanishes on the entire closed left half-plane when
T ≥ 1 and the threshold is nonnegative. -/
def kimRightExcess (T a : ℝ) : ℝ :=
  realSum T (fun z => max ((z.re - 1 / 2) * Real.log T / (2 * Real.pi) - a) 0) /
    (Ncount 0 T : ℝ)

private theorem abs_excess_from_two_sides (y a L d : ℝ) (ha : 0 ≤ a) (hL : 0 ≤ L)
    (hd : 0 < d) :
    max (|y| * L - d * a) 0 =
      (max (y * L / d - a) 0 + max (-y * L / d - a) 0) * d := by
  have hscale (v : ℝ) : max (v - d * a) 0 = max (v / d - a) 0 * d := by
    by_cases hv : v / d ≤ a
    · have h := (div_le_iff₀ hd).mp hv
      rw [max_eq_right (by linarith only [h]), max_eq_right (sub_nonpos.mpr hv), zero_mul]
    · have h := (lt_div_iff₀ hd).mp (lt_of_not_ge hv)
      rw [max_eq_left (by linarith only [h]), max_eq_left (by linarith)]
      field_simp
  by_cases hy : 0 ≤ y
  · have hneg := div_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hy) hL) hd.le
    rw [abs_of_nonneg hy, max_eq_right (sub_nonpos.mpr (hneg.trans ha)), add_zero, hscale]
  · have hpos := div_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonpos_of_nonneg (le_of_lt (lt_of_not_ge hy)) hL) hd.le
    rw [abs_of_neg (lt_of_not_ge hy), max_eq_right (sub_nonpos.mpr (hpos.trans ha)),
      zero_add, hscale]

/-- Exact finite-height conversion between Conrey's absolute stop-loss mean
and the right-sided Kim positive part. -/
theorem microscopicExcess_eq_four_pi_kimRightExcess {T a : ℝ} (hT : 1 ≤ T) (ha : 0 ≤ a) :
    microscopicExcess T (2 * Real.pi * a) = 4 * Real.pi * kimRightExcess T a := by
  let f (z : ℂ) := max ((z.re - 1 / 2) * Real.log T / (2 * Real.pi) - a) 0
  have hind (z : ℂ) : max (|z.re - 1 / 2| * Real.log T - 2 * Real.pi * a) 0 =
      (f z + f (reflect z)) * (2 * Real.pi) := by
    dsimp only [f]
    rw [reflect_re, show 1 - z.re - 1 / 2 = -(z.re - 1 / 2) by ring]
    exact abs_excess_from_two_sides _ _ _ _ ha (Real.log_nonneg hT) (by positivity)
  have hsum : (∑ j : Copies T, max (copyDisplacement T j * Real.log T - 2 * Real.pi * a) 0) =
      (realSum T f + realSum T f) * (2 * Real.pi) := by
    calc
      _ = ∑ j : Copies T, ((f j.1.1 + f (reflect j.1.1)) * (2 * Real.pi)) :=
        Finset.sum_congr rfl fun j _ => hind j.1.1
      _ = realSum T (fun z => (f z + f (reflect z)) * (2 * Real.pi)) :=
        (realSum_eq_copies T (fun z : ℂ => (f z + f (reflect z)) * (2 * Real.pi))).symm
      _ = _ := by rw [realSum_mul_const, realSum_add, realSum_reflect]
  unfold microscopicExcess kimRightExcess
  rw [hsum]
  change (realSum T f + realSum T f) * (2 * Real.pi) / _ =
    4 * Real.pi * (realSum T f / _)
  ring

def kimMTTransform (y : ℝ) : ℝ :=
  let t := Real.pi * y
  (Real.cosh t + Real.sqrt 2 * t *
    (Real.cos (Real.sqrt 2)⁻¹ / Real.sin (Real.sqrt 2)⁻¹) * Real.sinh t) / (1 + 2 * t ^ 2)

def kimMTDefect (y : ℝ) : ℝ :=
  1 - 4 * kimMTTransform y ^ 2 / (1 + kimMTTransform (2 * y))

/-- A finite strict margin and an automatic large-y bound survive the
smoothing in Sections 5–6 of Kim's preprint. -/
def KimStrictMajorant (a ℓ : ℝ) : Prop :=
  ∃ b : ℝ, a < b ∧ 1 < ℓ * (b - a) ∧
    ∀ y ∈ Icc (0 : ℝ) b, kimMTDefect y < ℓ * max (y - a) 0

/-- Proposition 4.2 followed by the admissible smoothing limit at the
Montgomery–Taylor density. This explicit outside input includes the
two-boundary correction for Kim's full infinite-neighbor convention. -/
def KimIsolationTransfer : Prop :=
  ∀ a ℓ D c : ℝ, 0 < a → 0 < ℓ → 0 ≤ D → KimStrictMajorant a ℓ →
    (∀ ε : ℝ, 0 < ε → ∀ᶠ T : ℝ in atTop, kimRightExcess T a ≤ D + ε) →
    0 < c → c ≤ 1 / (4 * Real.pi) →
    KimIsolationLower c (ThmD.HD 1 - ℓ * D - 6 * Real.pi ^ 2 * c ^ 2)

/-- The fixed-strike Conrey upper input in the right-sided normalization. -/
theorem kimRightExcess_eventually (hC : ConreyStopLossHypothesis) {a δ : ℝ}
    (ha : 0 < a) (hδ : 0 < δ) :
    ∀ᶠ T : ℝ in atTop, kimRightExcess T a ≤ conreyStopLossProfile (2 * Real.pi * a) /
      (4 * Real.pi) + δ := by
  let u := 2 * Real.pi * a
  let F := conreyStopLossProfile u
  have hu : 0 < u := by dsimp [u]; positivity
  have hp : 0 < 4 * Real.pi := by positivity
  have hB : F < F + 4 * Real.pi * δ := by linarith only [mul_pos hp hδ]
  filter_upwards [hC u hu.le _ hB, eventually_ge_atTop (1 : ℝ)] with T hT ht
  change microscopicExcess T (2 * Real.pi * a) ≤ _ at hT
  rw [microscopicExcess_eq_four_pi_kimRightExcess ht ha.le] at hT
  have hdiv : kimRightExcess T a ≤ (F + 4 * Real.pi * δ) / (4 * Real.pi) :=
    (le_div_iff₀ hp).mpr (by linarith only [hT])
  change kimRightExcess T a ≤ F / (4 * Real.pi) + δ
  exact hdiv.trans_eq (by rw [add_div]; field_simp)

theorem kimIsolationLower_of_conrey (hC : ConreyStopLossHypothesis)
    (hK : KimIsolationTransfer) {a ℓ c : ℝ} (ha : 0 < a) (hℓ : 0 < ℓ)
    (hmaj : KimStrictMajorant a ℓ) (hc : 0 < c) (hc1 : c ≤ 1 / (4 * Real.pi)) :
    KimIsolationLower c (ThmD.HD 1 - ℓ * (conreyStopLossProfile (2 * Real.pi * a) /
      (4 * Real.pi)) - 6 * Real.pi ^ 2 * c ^ 2) := by
  let u := 2 * Real.pi * a
  have hu : 0 < u := by dsimp [u]; positivity
  have hF : 0 ≤ conreyStopLossProfile u := by
    rw [conreyStopLossProfile, if_neg hu.ne']
    have hden : 0 < 1 - Real.exp (-(8 / 7) * u) := sub_pos.mpr
      (Real.exp_lt_one_iff.mpr (by linarith))
    apply Real.log_nonneg ((one_le_div hden).mpr _)
    have h := Real.exp_le_exp.mpr (by linarith : -(22 / 7) * u ≤ -(8 / 7) * u)
    linarith only [h]
  apply hK a ℓ _ c ha hℓ (div_nonneg hF (by positivity)) hmaj _ hc hc1
  exact fun ε hε => kimRightExcess_eventually hC ha hε

/-- The rational cover and the directed final coefficient calculation are
external numerical inputs. See RiemannResearch/RH/BoundCertificateReplays20261119.md. -/
def IsolationIntervalCertificate : Prop :=
  KimStrictMajorant (303 / 250) (7061 / 10000) ∧
    (6724913656 / 10 ^ 10 : ℝ) ≤ ThmD.HD 1 -
      (7061 / 10000) * (conreyStopLossProfile (2 * Real.pi * (303 / 250)) / (4 * Real.pi)) -
      6 * Real.pi ^ 2 * (1 / 100000 : ℝ) ^ 2

/-- The certified two-sided isolation proportion for every positive gap
parameter up to 10⁻⁵. -/
theorem kimIsolationLower_6724913656 (hC : ConreyStopLossHypothesis)
    (hK : KimIsolationTransfer) (hI : IsolationIntervalCertificate) {c : ℝ}
    (hc : 0 < c) (hc1 : c ≤ 1 / 100000) : KimIsolationLower c (6724913656 / 10 ^ 10) := by
  have hc' : c ≤ 1 / (4 * Real.pi) := hc1.trans <|
    (le_div_iff₀ (by positivity)).mpr (by linarith only [Real.pi_lt_four])
  have h := kimIsolationLower_of_conrey hC hK (by norm_num) (by norm_num) hI.1 hc hc'
  have hsq : c ^ 2 ≤ (1 / 100000 : ℝ) ^ 2 := pow_le_pow_left₀ hc.le hc1 2
  have hcost := mul_le_mul_of_nonneg_left hsq (show 0 ≤ 6 * Real.pi ^ 2 by positivity)
  intro ε hε
  filter_upwards [h ε hε] with T ht
  linarith only [hI.2, ht, hcost]

end RiemannResearch.Analysis.ActualZeroOrdinate
