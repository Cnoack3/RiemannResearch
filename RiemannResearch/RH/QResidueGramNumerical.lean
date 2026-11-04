/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import RiemannResearch.RH.QResidueMoments
import RiemannResearch.RH.ReciprocalSquareTailBounds
import RiemannResearch.Analysis.RationalInterval
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Certified numerical residue Gram entries for conductors 2, 3, 5, 6

Source: the user's request to verify the triangular matrix numerics,
4 November 2026. Each certificate controls the complete infinite Q sum.
The trigamma function is enclosed by a sixteen-term rational head and
proved reciprocal-square tail bounds. All displayed interval endpoints
are exact rationals, checked by kernel-producing arithmetic tactics.
-/

set_option maxRecDepth 4096
set_option maxHeartbeats 2000000
noncomputable section
open scoped BigOperators

namespace RiemannResearch.RH.QResidueGramNumerical
open CRTBlock ZetaTwoHilbert ZetaTwoProbability ArithmeticCumulative
open ReciprocalSquareTailBounds RiemannResearch.RatInterval

private theorem trigamma_certified (x : ℝ) (hx : 0 < x) (I : RatInterval)
    (hl : (I.lo : ℝ) ≤ head x 16 + lower ((16 : ℝ) + x))
    (hu : head x 16 + upper ((16 : ℝ) + x) ≤ (I.hi : ℝ)) :
    I.Contains (trigamma x) := by
  have h := trigamma_head_sandwich x hx 16
  exact ⟨hl.trans h.1, h.2.trans hu⟩

def tg_1_30 : RatInterval := ⟨(225392064276341 / 250000000000 : ℚ), (450784128552683 / 500000000000 : ℚ)⟩

theorem tg_1_30_contains : tg_1_30.Contains (trigamma (1 / 30 : ℝ)) := by
  apply trigamma_certified (1 / 30 : ℝ) (by norm_num) tg_1_30
  · norm_num [tg_1_30, head, Finset.sum_range_succ, lower, upper]
  · norm_num [tg_1_30, head, Finset.sum_range_succ, lower, upper]

def tg_1_15 : RatInterval := ⟨(45299590984531 / 200000000000 : ℚ), (7078061091333 / 31250000000 : ℚ)⟩

theorem tg_1_15_contains : tg_1_15.Contains (trigamma (1 / 15 : ℝ)) := by
  apply trigamma_certified (1 / 15 : ℝ) (by norm_num) tg_1_15
  · norm_num [tg_1_15, head, Finset.sum_range_succ, lower, upper]
  · norm_num [tg_1_15, head, Finset.sum_range_succ, lower, upper]

def tg_1_10 : RatInterval := ⟨(12679162393849 / 125000000000 : ℚ), (50716649575397 / 500000000000 : ℚ)⟩

theorem tg_1_10_contains : tg_1_10.Contains (trigamma (1 / 10 : ℝ)) := by
  apply trigamma_certified (1 / 10 : ℝ) (by norm_num) tg_1_10
  · norm_num [tg_1_10, head, Finset.sum_range_succ, lower, upper]
  · norm_num [tg_1_10, head, Finset.sum_range_succ, lower, upper]

def tg_2_15 : RatInterval := ⟨(576236648259 / 10000000000 : ℚ), (57623664825901 / 1000000000000 : ℚ)⟩

theorem tg_2_15_contains : tg_2_15.Contains (trigamma (2 / 15 : ℝ)) := by
  apply trigamma_certified (2 / 15 : ℝ) (by norm_num) tg_2_15
  · norm_num [tg_2_15, head, Finset.sum_range_succ, lower, upper]
  · norm_num [tg_2_15, head, Finset.sum_range_succ, lower, upper]

def tg_1_6 : RatInterval := ⟨(37318513092349 / 1000000000000 : ℚ), (37318513092351 / 1000000000000 : ℚ)⟩

theorem tg_1_6_contains : tg_1_6.Contains (trigamma (1 / 6 : ℝ)) := by
  apply trigamma_certified (1 / 6 : ℝ) (by norm_num) tg_1_6
  · norm_num [tg_1_6, head, Finset.sum_range_succ, lower, upper]
  · norm_num [tg_1_6, head, Finset.sum_range_succ, lower, upper]

def tg_1_5 : RatInterval := ⟨(26267377205423 / 1000000000000 : ℚ), (1050695088217 / 40000000000 : ℚ)⟩

theorem tg_1_5_contains : tg_1_5.Contains (trigamma (1 / 5 : ℝ)) := by
  apply trigamma_certified (1 / 5 : ℝ) (by norm_num) tg_1_5
  · norm_num [tg_1_5, head, Finset.sum_range_succ, lower, upper]
  · norm_num [tg_1_5, head, Finset.sum_range_succ, lower, upper]

def tg_7_30 : RatInterval := ⟨(4896799517457 / 250000000000 : ℚ), (19587198069829 / 1000000000000 : ℚ)⟩

theorem tg_7_30_contains : tg_7_30.Contains (trigamma (7 / 30 : ℝ)) := by
  apply trigamma_certified (7 / 30 : ℝ) (by norm_num) tg_7_30
  · norm_num [tg_7_30, head, Finset.sum_range_succ, lower, upper]
  · norm_num [tg_7_30, head, Finset.sum_range_succ, lower, upper]

def tg_4_15 : RatInterval := ⟨(15238080204857 / 1000000000000 : ℚ), (7619040102429 / 500000000000 : ℚ)⟩

theorem tg_4_15_contains : tg_4_15.Contains (trigamma (4 / 15 : ℝ)) := by
  apply trigamma_certified (4 / 15 : ℝ) (by norm_num) tg_4_15
  · norm_num [tg_4_15, head, Finset.sum_range_succ, lower, upper]
  · norm_num [tg_4_15, head, Finset.sum_range_succ, lower, upper]

def tg_3_10 : RatInterval := ⟨(12245364546107 / 1000000000000 : ℚ), (12245364546109 / 1000000000000 : ℚ)⟩

theorem tg_3_10_contains : tg_3_10.Contains (trigamma (3 / 10 : ℝ)) := by
  apply trigamma_certified (3 / 10 : ℝ) (by norm_num) tg_3_10
  · norm_num [tg_3_10, head, Finset.sum_range_succ, lower, upper]
  · norm_num [tg_3_10, head, Finset.sum_range_succ, lower, upper]

def tg_1_3 : RatInterval := ⟨(10095597125427 / 1000000000000 : ℚ), (2523899281357 / 250000000000 : ℚ)⟩

theorem tg_1_3_contains : tg_1_3.Contains (trigamma (1 / 3 : ℝ)) := by
  apply trigamma_certified (1 / 3 : ℝ) (by norm_num) tg_1_3
  · norm_num [tg_1_3, head, Finset.sum_range_succ, lower, upper]
  · norm_num [tg_1_3, head, Finset.sum_range_succ, lower, upper]

def tg_11_30 : RatInterval := ⟨(339895443803 / 40000000000 : ℚ), (2124346523769 / 250000000000 : ℚ)⟩

theorem tg_11_30_contains : tg_11_30.Contains (trigamma (11 / 30 : ℝ)) := by
  apply trigamma_certified (11 / 30 : ℝ) (by norm_num) tg_11_30
  · norm_num [tg_11_30, head, Finset.sum_range_succ, lower, upper]
  · norm_num [tg_11_30, head, Finset.sum_range_succ, lower, upper]

def tg_2_5 : RatInterval := ⟨(7275356590529 / 1000000000000 : ℚ), (727535659053 / 100000000000 : ℚ)⟩

theorem tg_2_5_contains : tg_2_5.Contains (trigamma (2 / 5 : ℝ)) := by
  apply trigamma_certified (2 / 5 : ℝ) (by norm_num) tg_2_5
  · norm_num [tg_2_5, head, Finset.sum_range_succ, lower, upper]
  · norm_num [tg_2_5, head, Finset.sum_range_succ, lower, upper]

def tg_13_30 : RatInterval := ⟨(631881162801 / 100000000000 : ℚ), (1579702907003 / 250000000000 : ℚ)⟩

theorem tg_13_30_contains : tg_13_30.Contains (trigamma (13 / 30 : ℝ)) := by
  apply trigamma_certified (13 / 30 : ℝ) (by norm_num) tg_13_30
  · norm_num [tg_13_30, head, Finset.sum_range_succ, lower, upper]
  · norm_num [tg_13_30, head, Finset.sum_range_succ, lower, upper]

def tg_7_15 : RatInterval := ⟨(1388767587841 / 250000000000 : ℚ), (1111014070273 / 200000000000 : ℚ)⟩

theorem tg_7_15_contains : tg_7_15.Contains (trigamma (7 / 15 : ℝ)) := by
  apply trigamma_certified (7 / 15 : ℝ) (by norm_num) tg_7_15
  · norm_num [tg_7_15, head, Finset.sum_range_succ, lower, upper]
  · norm_num [tg_7_15, head, Finset.sum_range_succ, lower, upper]

def tg_1_2 : RatInterval := ⟨(154212568767 / 31250000000 : ℚ), (2467401100273 / 500000000000 : ℚ)⟩

theorem tg_1_2_contains : tg_1_2.Contains (trigamma (1 / 2 : ℝ)) := by
  apply trigamma_certified (1 / 2 : ℝ) (by norm_num) tg_1_2
  · norm_num [tg_1_2, head, Finset.sum_range_succ, lower, upper]
  · norm_num [tg_1_2, head, Finset.sum_range_succ, lower, upper]

def tg_8_15 : RatInterval := ⟨(884712517051 / 200000000000 : ℚ), (4423562585257 / 1000000000000 : ℚ)⟩

theorem tg_8_15_contains : tg_8_15.Contains (trigamma (8 / 15 : ℝ)) := by
  apply trigamma_certified (8 / 15 : ℝ) (by norm_num) tg_8_15
  · norm_num [tg_8_15, head, Finset.sum_range_succ, lower, upper]
  · norm_num [tg_8_15, head, Finset.sum_range_succ, lower, upper]

def tg_17_30 : RatInterval := ⟨(1998352190473 / 500000000000 : ℚ), (3996704380947 / 1000000000000 : ℚ)⟩

theorem tg_17_30_contains : tg_17_30.Contains (trigamma (17 / 30 : ℝ)) := by
  apply trigamma_certified (17 / 30 : ℝ) (by norm_num) tg_17_30
  · norm_num [tg_17_30, head, Finset.sum_range_succ, lower, upper]
  · norm_num [tg_17_30, head, Finset.sum_range_succ, lower, upper]

def tg_3_5 : RatInterval := ⟨(1818104835451 / 500000000000 : ℚ), (3636209670903 / 1000000000000 : ℚ)⟩

theorem tg_3_5_contains : tg_3_5.Contains (trigamma (3 / 5 : ℝ)) := by
  apply trigamma_certified (3 / 5 : ℝ) (by norm_num) tg_3_5
  · norm_num [tg_3_5, head, Finset.sum_range_succ, lower, upper]
  · norm_num [tg_3_5, head, Finset.sum_range_succ, lower, upper]

def tg_19_30 : RatInterval := ⟨(3328655993529 / 1000000000000 : ℚ), (3328655993531 / 1000000000000 : ℚ)⟩

theorem tg_19_30_contains : tg_19_30.Contains (trigamma (19 / 30 : ℝ)) := by
  apply trigamma_certified (19 / 30 : ℝ) (by norm_num) tg_19_30
  · norm_num [tg_19_30, head, Finset.sum_range_succ, lower, upper]
  · norm_num [tg_19_30, head, Finset.sum_range_succ, lower, upper]

def tg_2_3 : RatInterval := ⟨(1531937704679 / 500000000000 : ℚ), (38298442617 / 12500000000 : ℚ)⟩

theorem tg_2_3_contains : tg_2_3.Contains (trigamma (2 / 3 : ℝ)) := by
  apply trigamma_certified (2 / 3 : ℝ) (by norm_num) tg_2_3
  · norm_num [tg_2_3, head, Finset.sum_range_succ, lower, upper]
  · norm_num [tg_2_3, head, Finset.sum_range_succ, lower, upper]

def tg_7_10 : RatInterval := ⟨(1417024578347 / 500000000000 : ℚ), (566809831339 / 200000000000 : ℚ)⟩

theorem tg_7_10_contains : tg_7_10.Contains (trigamma (7 / 10 : ℝ)) := by
  apply trigamma_certified (7 / 10 : ℝ) (by norm_num) tg_7_10
  · norm_num [tg_7_10, head, Finset.sum_range_succ, lower, upper]
  · norm_num [tg_7_10, head, Finset.sum_range_succ, lower, upper]

def tg_11_15 : RatInterval := ⟨(2633083335629 / 1000000000000 : ℚ), (263308333563 / 100000000000 : ℚ)⟩

theorem tg_11_15_contains : tg_11_15.Contains (trigamma (11 / 15 : ℝ)) := by
  apply trigamma_certified (11 / 15 : ℝ) (by norm_num) tg_11_15
  · norm_num [tg_11_15, head, Finset.sum_range_succ, lower, upper]
  · norm_num [tg_11_15, head, Finset.sum_range_succ, lower, upper]

def tg_23_30 : RatInterval := ⟨(1228085068083 / 500000000000 : ℚ), (2456170136167 / 1000000000000 : ℚ)⟩

theorem tg_23_30_contains : tg_23_30.Contains (trigamma (23 / 30 : ℝ)) := by
  apply trigamma_certified (23 / 30 : ℝ) (by norm_num) tg_23_30
  · norm_num [tg_23_30, head, Finset.sum_range_succ, lower, upper]
  · norm_num [tg_23_30, head, Finset.sum_range_succ, lower, upper]

def tg_4_5 : RatInterval := ⟨(2299474137501 / 1000000000000 : ℚ), (2299474137503 / 1000000000000 : ℚ)⟩

theorem tg_4_5_contains : tg_4_5.Contains (trigamma (4 / 5 : ℝ)) := by
  apply trigamma_certified (4 / 5 : ℝ) (by norm_num) tg_4_5
  · norm_num [tg_4_5, head, Finset.sum_range_succ, lower, upper]
  · norm_num [tg_4_5, head, Finset.sum_range_succ, lower, upper]

def tg_5_6 : RatInterval := ⟨(2159904512007 / 1000000000000 : ℚ), (2159904512009 / 1000000000000 : ℚ)⟩

theorem tg_5_6_contains : tg_5_6.Contains (trigamma (5 / 6 : ℝ)) := by
  apply trigamma_certified (5 / 6 : ℝ) (by norm_num) tg_5_6
  · norm_num [tg_5_6, head, Finset.sum_range_succ, lower, upper]
  · norm_num [tg_5_6, head, Finset.sum_range_succ, lower, upper]

def tg_13_15 : RatInterval := ⟨(2034947247441 / 1000000000000 : ℚ), (1017473623721 / 500000000000 : ℚ)⟩

theorem tg_13_15_contains : tg_13_15.Contains (trigamma (13 / 15 : ℝ)) := by
  apply trigamma_certified (13 / 15 : ℝ) (by norm_num) tg_13_15
  · norm_num [tg_13_15, head, Finset.sum_range_succ, lower, upper]
  · norm_num [tg_13_15, head, Finset.sum_range_succ, lower, upper]

def tg_9_10 : RatInterval := ⟨(1922539959477 / 1000000000000 : ℚ), (961269979739 / 500000000000 : ℚ)⟩

theorem tg_9_10_contains : tg_9_10.Contains (trigamma (9 / 10 : ℝ)) := by
  apply trigamma_certified (9 / 10 : ℝ) (by norm_num) tg_9_10
  · norm_num [tg_9_10, head, Finset.sum_range_succ, lower, upper]
  · norm_num [tg_9_10, head, Finset.sum_range_succ, lower, upper]

def tg_14_15 : RatInterval := ⟨(364195472351 / 200000000000 : ℚ), (455244340439 / 250000000000 : ℚ)⟩

theorem tg_14_15_contains : tg_14_15.Contains (trigamma (14 / 15 : ℝ)) := by
  apply trigamma_certified (14 / 15 : ℝ) (by norm_num) tg_14_15
  · norm_num [tg_14_15, head, Finset.sum_range_succ, lower, upper]
  · norm_num [tg_14_15, head, Finset.sum_range_succ, lower, upper]

def tg_29_30 : RatInterval := ⟨(1728839095657 / 1000000000000 : ℚ), (864419547829 / 500000000000 : ℚ)⟩

theorem tg_29_30_contains : tg_29_30.Contains (trigamma (29 / 30 : ℝ)) := by
  apply trigamma_certified (29 / 30 : ℝ) (by norm_num) tg_29_30
  · norm_num [tg_29_30, head, Finset.sum_range_succ, lower, upper]
  · norm_num [tg_29_30, head, Finset.sum_range_succ, lower, upper]

def tg_1_1 : RatInterval := ⟨(51404189589 / 31250000000 : ℚ), (1644934066849 / 1000000000000 : ℚ)⟩

theorem tg_1_1_contains : tg_1_1.Contains (trigamma (1 / 1 : ℝ)) := by
  apply trigamma_certified (1 / 1 : ℝ) (by norm_num) tg_1_1
  · norm_num [tg_1_1, head, Finset.sum_range_succ, lower, upper]
  · norm_num [tg_1_1, head, Finset.sum_range_succ, lower, upper]

theorem zeta_bounds : tg_1_1.Contains zetaTwo := by
  rw [zetaTwo_eq_trigamma_one]
  simpa only [div_one] using tg_1_1_contains

/-- Complete Q Gram entry for conductors 2 and 2; outward rational enclosure. -/
def gram_2_2_interval : RatInterval := ⟨(187499999999 / 1000000000000 : ℚ), (187500000001 / 1000000000000 : ℚ)⟩

theorem gram_2_2_bounds : gram_2_2_interval.Contains
    (inner ℝ (qResidue 2) (qResidue 2)) := by
  have heq : inner ℝ (qResidue 2) (qResidue 2) =
      (((1 / 16 : ℚ) : ℝ) * trigamma (1 / 2 : ℝ)) / zetaTwo := by
    rw [qResidue_gram_eq_trigamma 2 2 (by norm_num) (by norm_num)]
    rw [show Nat.lcm 2 2 = 2 by decide]
    norm_num [Fin.sum_univ_succ, residueFraction]
    field_simp [ne_of_gt zetaTwo_pos]
    <;> ring
  have hn := (contains_mul (contains_point (1 / 16 : ℚ)) tg_1_2_contains)
  have hq := contains_div_pos hn zeta_bounds (by norm_num [tg_1_1])
  rw [heq]
  exact contains_weaken hq
    (by norm_num [gram_2_2_interval, tg_1_2, tg_1_1, RatInterval.div, RatInterval.mul, RatInterval.inv, RatInterval.point, RatInterval.add])
    (by norm_num [gram_2_2_interval, tg_1_2, tg_1_1, RatInterval.div, RatInterval.mul, RatInterval.inv, RatInterval.point, RatInterval.add])

/-- Complete Q Gram entry for conductors 2 and 3; outward rational enclosure. -/
def gram_2_3_interval : RatInterval := ⟨(5859505669 / 50000000000 : ℚ), (117190113381 / 1000000000000 : ℚ)⟩

theorem gram_2_3_bounds : gram_2_3_interval.Contains
    (inner ℝ (qResidue 2) (qResidue 3)) := by
  have heq : inner ℝ (qResidue 2) (qResidue 3) =
      ((((1 / 216 : ℚ) : ℝ) * trigamma (1 / 6 : ℝ)) + (((1 / 108 : ℚ) : ℝ) * trigamma (5 / 6 : ℝ))) / zetaTwo := by
    rw [qResidue_gram_eq_trigamma 2 3 (by norm_num) (by norm_num)]
    rw [show Nat.lcm 2 3 = 6 by decide]
    norm_num [Fin.sum_univ_succ, residueFraction]
    field_simp [ne_of_gt zetaTwo_pos]
    <;> ring
  have hn := (contains_add (contains_mul (contains_point (1 / 216 : ℚ)) tg_1_6_contains)
      (contains_mul (contains_point (1 / 108 : ℚ)) tg_5_6_contains))
  have hq := contains_div_pos hn zeta_bounds (by norm_num [tg_1_1])
  rw [heq]
  exact contains_weaken hq
    (by norm_num [gram_2_3_interval, tg_1_6, tg_5_6, tg_1_1, RatInterval.div, RatInterval.mul, RatInterval.inv, RatInterval.point, RatInterval.add])
    (by norm_num [gram_2_3_interval, tg_1_6, tg_5_6, tg_1_1, RatInterval.div, RatInterval.mul, RatInterval.inv, RatInterval.point, RatInterval.add])

/-- Complete Q Gram entry for conductors 2 and 5; outward rational enclosure. -/
def gram_2_5_interval : RatInterval := ⟨(46058882843 / 500000000000 : ℚ), (92117765687 / 1000000000000 : ℚ)⟩

theorem gram_2_5_bounds : gram_2_5_interval.Contains
    (inner ℝ (qResidue 2) (qResidue 5)) := by
  have heq : inner ℝ (qResidue 2) (qResidue 5) =
      ((((((1 / 1000 : ℚ) : ℝ) * trigamma (1 / 10 : ℝ)) + (((3 / 1000 : ℚ) : ℝ) * trigamma (3 / 10 : ℝ))) + (((1 / 500 : ℚ) : ℝ) * trigamma (7 / 10 : ℝ))) + (((1 / 250 : ℚ) : ℝ) * trigamma (9 / 10 : ℝ))) / zetaTwo := by
    rw [qResidue_gram_eq_trigamma 2 5 (by norm_num) (by norm_num)]
    rw [show Nat.lcm 2 5 = 10 by decide]
    norm_num [Fin.sum_univ_succ, residueFraction]
    field_simp [ne_of_gt zetaTwo_pos]
    <;> ring
  have hn := (contains_add (contains_add (contains_add (contains_mul (contains_point (1 / 1000 : ℚ)) tg_1_10_contains)
      (contains_mul (contains_point (3 / 1000 : ℚ)) tg_3_10_contains))
      (contains_mul (contains_point (1 / 500 : ℚ)) tg_7_10_contains))
      (contains_mul (contains_point (1 / 250 : ℚ)) tg_9_10_contains))
  have hq := contains_div_pos hn zeta_bounds (by norm_num [tg_1_1])
  rw [heq]
  exact contains_weaken hq
    (by norm_num [gram_2_5_interval, tg_1_10, tg_3_10, tg_7_10, tg_9_10, tg_1_1, RatInterval.div, RatInterval.mul, RatInterval.inv, RatInterval.point, RatInterval.add])
    (by norm_num [gram_2_5_interval, tg_1_10, tg_3_10, tg_7_10, tg_9_10, tg_1_1, RatInterval.div, RatInterval.mul, RatInterval.inv, RatInterval.point, RatInterval.add])

/-- Complete Q Gram entry for conductors 2 and 6; outward rational enclosure. -/
def gram_2_6_interval : RatInterval := ⟨(22136723357 / 250000000000 : ℚ), (88546893429 / 1000000000000 : ℚ)⟩

theorem gram_2_6_bounds : gram_2_6_interval.Contains
    (inner ℝ (qResidue 2) (qResidue 6)) := by
  have heq : inner ℝ (qResidue 2) (qResidue 6) =
      (((((1 / 432 : ℚ) : ℝ) * trigamma (1 / 6 : ℝ)) + (((1 / 144 : ℚ) : ℝ) * trigamma (1 / 2 : ℝ))) + (((5 / 432 : ℚ) : ℝ) * trigamma (5 / 6 : ℝ))) / zetaTwo := by
    rw [qResidue_gram_eq_trigamma 2 6 (by norm_num) (by norm_num)]
    rw [show Nat.lcm 2 6 = 6 by decide]
    norm_num [Fin.sum_univ_succ, residueFraction]
    field_simp [ne_of_gt zetaTwo_pos]
    <;> ring
  have hn := (contains_add (contains_add (contains_mul (contains_point (1 / 432 : ℚ)) tg_1_6_contains)
      (contains_mul (contains_point (1 / 144 : ℚ)) tg_1_2_contains))
      (contains_mul (contains_point (5 / 432 : ℚ)) tg_5_6_contains))
  have hq := contains_div_pos hn zeta_bounds (by norm_num [tg_1_1])
  rw [heq]
  exact contains_weaken hq
    (by norm_num [gram_2_6_interval, tg_1_6, tg_1_2, tg_5_6, tg_1_1, RatInterval.div, RatInterval.mul, RatInterval.inv, RatInterval.point, RatInterval.add])
    (by norm_num [gram_2_6_interval, tg_1_6, tg_1_2, tg_5_6, tg_1_1, RatInterval.div, RatInterval.mul, RatInterval.inv, RatInterval.point, RatInterval.add])

/-- Complete Q Gram entry for conductors 3 and 3; outward rational enclosure. -/
def gram_3_3_interval : RatInterval := ⟨(167751094989 / 1000000000000 : ℚ), (16775109499 / 100000000000 : ℚ)⟩

theorem gram_3_3_bounds : gram_3_3_interval.Contains
    (inner ℝ (qResidue 3) (qResidue 3)) := by
  have heq : inner ℝ (qResidue 3) (qResidue 3) =
      ((((1 / 81 : ℚ) : ℝ) * trigamma (1 / 3 : ℝ)) + (((4 / 81 : ℚ) : ℝ) * trigamma (2 / 3 : ℝ))) / zetaTwo := by
    rw [qResidue_gram_eq_trigamma 3 3 (by norm_num) (by norm_num)]
    rw [show Nat.lcm 3 3 = 3 by decide]
    norm_num [Fin.sum_univ_succ, residueFraction]
    field_simp [ne_of_gt zetaTwo_pos]
    <;> ring
  have hn := (contains_add (contains_mul (contains_point (1 / 81 : ℚ)) tg_1_3_contains)
      (contains_mul (contains_point (4 / 81 : ℚ)) tg_2_3_contains))
  have hq := contains_div_pos hn zeta_bounds (by norm_num [tg_1_1])
  rw [heq]
  exact contains_weaken hq
    (by norm_num [gram_3_3_interval, tg_1_3, tg_2_3, tg_1_1, RatInterval.div, RatInterval.mul, RatInterval.inv, RatInterval.point, RatInterval.add])
    (by norm_num [gram_3_3_interval, tg_1_3, tg_2_3, tg_1_1, RatInterval.div, RatInterval.mul, RatInterval.inv, RatInterval.point, RatInterval.add])

/-- Complete Q Gram entry for conductors 3 and 5; outward rational enclosure. -/
def gram_3_5_interval : RatInterval := ⟨(52374971337 / 500000000000 : ℚ), (4189997707 / 40000000000 : ℚ)⟩

theorem gram_3_5_bounds : gram_3_5_interval.Contains
    (inner ℝ (qResidue 3) (qResidue 5)) := by
  have heq : inner ℝ (qResidue 3) (qResidue 5) =
      ((((((((((1 / 3375 : ℚ) : ℝ) * trigamma (1 / 15 : ℝ)) + (((4 / 3375 : ℚ) : ℝ) * trigamma (2 / 15 : ℝ))) + (((4 / 3375 : ℚ) : ℝ) * trigamma (4 / 15 : ℝ))) + (((2 / 3375 : ℚ) : ℝ) * trigamma (7 / 15 : ℝ))) + (((2 / 1125 : ℚ) : ℝ) * trigamma (8 / 15 : ℝ))) + (((2 / 3375 : ℚ) : ℝ) * trigamma (11 / 15 : ℝ))) + (((1 / 1125 : ℚ) : ℝ) * trigamma (13 / 15 : ℝ))) + (((8 / 3375 : ℚ) : ℝ) * trigamma (14 / 15 : ℝ))) / zetaTwo := by
    rw [qResidue_gram_eq_trigamma 3 5 (by norm_num) (by norm_num)]
    rw [show Nat.lcm 3 5 = 15 by decide]
    norm_num [Fin.sum_univ_succ, residueFraction]
    field_simp [ne_of_gt zetaTwo_pos]
    <;> ring
  have hn := (contains_add (contains_add (contains_add (contains_add (contains_add (contains_add (contains_add (contains_mul (contains_point (1 / 3375 : ℚ)) tg_1_15_contains)
      (contains_mul (contains_point (4 / 3375 : ℚ)) tg_2_15_contains))
      (contains_mul (contains_point (4 / 3375 : ℚ)) tg_4_15_contains))
      (contains_mul (contains_point (2 / 3375 : ℚ)) tg_7_15_contains))
      (contains_mul (contains_point (2 / 1125 : ℚ)) tg_8_15_contains))
      (contains_mul (contains_point (2 / 3375 : ℚ)) tg_11_15_contains))
      (contains_mul (contains_point (1 / 1125 : ℚ)) tg_13_15_contains))
      (contains_mul (contains_point (8 / 3375 : ℚ)) tg_14_15_contains))
  have hq := contains_div_pos hn zeta_bounds (by norm_num [tg_1_1])
  rw [heq]
  exact contains_weaken hq
    (by norm_num [gram_3_5_interval, tg_1_15, tg_2_15, tg_4_15, tg_7_15, tg_8_15, tg_11_15, tg_13_15, tg_14_15, tg_1_1, RatInterval.div, RatInterval.mul, RatInterval.inv, RatInterval.point, RatInterval.add])
    (by norm_num [gram_3_5_interval, tg_1_15, tg_2_15, tg_4_15, tg_7_15, tg_8_15, tg_11_15, tg_13_15, tg_14_15, tg_1_1, RatInterval.div, RatInterval.mul, RatInterval.inv, RatInterval.point, RatInterval.add])

/-- Complete Q Gram entry for conductors 3 and 6; outward rational enclosure. -/
def gram_3_6_interval : RatInterval := ⟨(20931351979 / 200000000000 : ℚ), (13082094987 / 125000000000 : ℚ)⟩

theorem gram_3_6_bounds : gram_3_6_interval.Contains
    (inner ℝ (qResidue 3) (qResidue 6)) := by
  have heq : inner ℝ (qResidue 3) (qResidue 6) =
      ((((((1 / 648 : ℚ) : ℝ) * trigamma (1 / 6 : ℝ)) + (((1 / 162 : ℚ) : ℝ) * trigamma (1 / 3 : ℝ))) + (((1 / 162 : ℚ) : ℝ) * trigamma (2 / 3 : ℝ))) + (((5 / 324 : ℚ) : ℝ) * trigamma (5 / 6 : ℝ))) / zetaTwo := by
    rw [qResidue_gram_eq_trigamma 3 6 (by norm_num) (by norm_num)]
    rw [show Nat.lcm 3 6 = 6 by decide]
    norm_num [Fin.sum_univ_succ, residueFraction]
    field_simp [ne_of_gt zetaTwo_pos]
    <;> ring
  have hn := (contains_add (contains_add (contains_add (contains_mul (contains_point (1 / 648 : ℚ)) tg_1_6_contains)
      (contains_mul (contains_point (1 / 162 : ℚ)) tg_1_3_contains))
      (contains_mul (contains_point (1 / 162 : ℚ)) tg_2_3_contains))
      (contains_mul (contains_point (5 / 324 : ℚ)) tg_5_6_contains))
  have hq := contains_div_pos hn zeta_bounds (by norm_num [tg_1_1])
  rw [heq]
  exact contains_weaken hq
    (by norm_num [gram_3_6_interval, tg_1_6, tg_1_3, tg_2_3, tg_5_6, tg_1_1, RatInterval.div, RatInterval.mul, RatInterval.inv, RatInterval.point, RatInterval.add])
    (by norm_num [gram_3_6_interval, tg_1_6, tg_1_3, tg_2_3, tg_5_6, tg_1_1, RatInterval.div, RatInterval.mul, RatInterval.inv, RatInterval.point, RatInterval.add])

/-- Complete Q Gram entry for conductors 5 and 5; outward rational enclosure. -/
def gram_5_5_interval : RatInterval := ⟨(121474803711 / 1000000000000 : ℚ), (59313869 / 488281250 : ℚ)⟩

theorem gram_5_5_bounds : gram_5_5_interval.Contains
    (inner ℝ (qResidue 5) (qResidue 5)) := by
  have heq : inner ℝ (qResidue 5) (qResidue 5) =
      ((((((1 / 625 : ℚ) : ℝ) * trigamma (1 / 5 : ℝ)) + (((4 / 625 : ℚ) : ℝ) * trigamma (2 / 5 : ℝ))) + (((9 / 625 : ℚ) : ℝ) * trigamma (3 / 5 : ℝ))) + (((16 / 625 : ℚ) : ℝ) * trigamma (4 / 5 : ℝ))) / zetaTwo := by
    rw [qResidue_gram_eq_trigamma 5 5 (by norm_num) (by norm_num)]
    rw [show Nat.lcm 5 5 = 5 by decide]
    norm_num [Fin.sum_univ_succ, residueFraction]
    field_simp [ne_of_gt zetaTwo_pos]
    <;> ring
  have hn := (contains_add (contains_add (contains_add (contains_mul (contains_point (1 / 625 : ℚ)) tg_1_5_contains)
      (contains_mul (contains_point (4 / 625 : ℚ)) tg_2_5_contains))
      (contains_mul (contains_point (9 / 625 : ℚ)) tg_3_5_contains))
      (contains_mul (contains_point (16 / 625 : ℚ)) tg_4_5_contains))
  have hq := contains_div_pos hn zeta_bounds (by norm_num [tg_1_1])
  rw [heq]
  exact contains_weaken hq
    (by norm_num [gram_5_5_interval, tg_1_5, tg_2_5, tg_3_5, tg_4_5, tg_1_1, RatInterval.div, RatInterval.mul, RatInterval.inv, RatInterval.point, RatInterval.add])
    (by norm_num [gram_5_5_interval, tg_1_5, tg_2_5, tg_3_5, tg_4_5, tg_1_1, RatInterval.div, RatInterval.mul, RatInterval.inv, RatInterval.point, RatInterval.add])

/-- Complete Q Gram entry for conductors 5 and 6; outward rational enclosure. -/
def gram_5_6_interval : RatInterval := ⟨(47680493937 / 500000000000 : ℚ), (762887903 / 8000000000 : ℚ)⟩

theorem gram_5_6_bounds : gram_5_6_interval.Contains
    (inner ℝ (qResidue 5) (qResidue 6)) := by
  have heq : inner ℝ (qResidue 5) (qResidue 6) =
      ((((((((((((((((((((((1 / 27000 : ℚ) : ℝ) * trigamma (1 / 30 : ℝ)) + (((1 / 6750 : ℚ) : ℝ) * trigamma (1 / 15 : ℝ))) + (((1 / 3000 : ℚ) : ℝ) * trigamma (1 / 10 : ℝ))) + (((2 / 3375 : ℚ) : ℝ) * trigamma (2 / 15 : ℝ))) + (((1 / 13500 : ℚ) : ℝ) * trigamma (7 / 30 : ℝ))) + (((1 / 4500 : ℚ) : ℝ) * trigamma (4 / 15 : ℝ))) + (((1 / 2250 : ℚ) : ℝ) * trigamma (3 / 10 : ℝ))) + (((1 / 5400 : ℚ) : ℝ) * trigamma (11 / 30 : ℝ))) + (((1 / 9000 : ℚ) : ℝ) * trigamma (13 / 30 : ℝ))) + (((1 / 3375 : ℚ) : ℝ) * trigamma (7 / 15 : ℝ))) + (((1 / 6750 : ℚ) : ℝ) * trigamma (8 / 15 : ℝ))) + (((1 / 2700 : ℚ) : ℝ) * trigamma (17 / 30 : ℝ))) + (((1 / 6750 : ℚ) : ℝ) * trigamma (19 / 30 : ℝ))) + (((1 / 9000 : ℚ) : ℝ) * trigamma (7 / 10 : ℝ))) + (((1 / 3375 : ℚ) : ℝ) * trigamma (11 / 15 : ℝ))) + (((1 / 1800 : ℚ) : ℝ) * trigamma (23 / 30 : ℝ))) + (((1 / 13500 : ℚ) : ℝ) * trigamma (13 / 15 : ℝ))) + (((1 / 4500 : ℚ) : ℝ) * trigamma (9 / 10 : ℝ))) + (((1 / 2250 : ℚ) : ℝ) * trigamma (14 / 15 : ℝ))) + (((1 / 1350 : ℚ) : ℝ) * trigamma (29 / 30 : ℝ))) / zetaTwo := by
    rw [qResidue_gram_eq_trigamma 5 6 (by norm_num) (by norm_num)]
    rw [show Nat.lcm 5 6 = 30 by decide]
    norm_num [Fin.sum_univ_succ, residueFraction]
    field_simp [ne_of_gt zetaTwo_pos]
    <;> ring
  have hn := (contains_add (contains_add (contains_add (contains_add (contains_add (contains_add (contains_add (contains_add (contains_add (contains_add (contains_add (contains_add (contains_add (contains_add (contains_add (contains_add (contains_add (contains_add (contains_add (contains_mul (contains_point (1 / 27000 : ℚ)) tg_1_30_contains)
      (contains_mul (contains_point (1 / 6750 : ℚ)) tg_1_15_contains))
      (contains_mul (contains_point (1 / 3000 : ℚ)) tg_1_10_contains))
      (contains_mul (contains_point (2 / 3375 : ℚ)) tg_2_15_contains))
      (contains_mul (contains_point (1 / 13500 : ℚ)) tg_7_30_contains))
      (contains_mul (contains_point (1 / 4500 : ℚ)) tg_4_15_contains))
      (contains_mul (contains_point (1 / 2250 : ℚ)) tg_3_10_contains))
      (contains_mul (contains_point (1 / 5400 : ℚ)) tg_11_30_contains))
      (contains_mul (contains_point (1 / 9000 : ℚ)) tg_13_30_contains))
      (contains_mul (contains_point (1 / 3375 : ℚ)) tg_7_15_contains))
      (contains_mul (contains_point (1 / 6750 : ℚ)) tg_8_15_contains))
      (contains_mul (contains_point (1 / 2700 : ℚ)) tg_17_30_contains))
      (contains_mul (contains_point (1 / 6750 : ℚ)) tg_19_30_contains))
      (contains_mul (contains_point (1 / 9000 : ℚ)) tg_7_10_contains))
      (contains_mul (contains_point (1 / 3375 : ℚ)) tg_11_15_contains))
      (contains_mul (contains_point (1 / 1800 : ℚ)) tg_23_30_contains))
      (contains_mul (contains_point (1 / 13500 : ℚ)) tg_13_15_contains))
      (contains_mul (contains_point (1 / 4500 : ℚ)) tg_9_10_contains))
      (contains_mul (contains_point (1 / 2250 : ℚ)) tg_14_15_contains))
      (contains_mul (contains_point (1 / 1350 : ℚ)) tg_29_30_contains))
  have hq := contains_div_pos hn zeta_bounds (by norm_num [tg_1_1])
  rw [heq]
  exact contains_weaken hq
    (by norm_num [gram_5_6_interval, tg_1_30, tg_1_15, tg_1_10, tg_2_15, tg_7_30, tg_4_15, tg_3_10, tg_11_30, tg_13_30, tg_7_15, tg_8_15, tg_17_30, tg_19_30, tg_7_10, tg_11_15, tg_23_30, tg_13_15, tg_9_10, tg_14_15, tg_29_30, tg_1_1, RatInterval.div, RatInterval.mul, RatInterval.inv, RatInterval.point, RatInterval.add])
    (by norm_num [gram_5_6_interval, tg_1_30, tg_1_15, tg_1_10, tg_2_15, tg_7_30, tg_4_15, tg_3_10, tg_11_30, tg_13_30, tg_7_15, tg_8_15, tg_17_30, tg_19_30, tg_7_10, tg_11_15, tg_23_30, tg_13_15, tg_9_10, tg_14_15, tg_29_30, tg_1_1, RatInterval.div, RatInterval.mul, RatInterval.inv, RatInterval.point, RatInterval.add])

/-- Complete Q Gram entry for conductors 6 and 6; outward rational enclosure. -/
def gram_6_6_interval : RatInterval := ⟨(52802817339 / 500000000000 : ℚ), (105605634679 / 1000000000000 : ℚ)⟩

theorem gram_6_6_bounds : gram_6_6_interval.Contains
    (inner ℝ (qResidue 6) (qResidue 6)) := by
  have heq : inner ℝ (qResidue 6) (qResidue 6) =
      (((((((1 / 1296 : ℚ) : ℝ) * trigamma (1 / 6 : ℝ)) + (((1 / 324 : ℚ) : ℝ) * trigamma (1 / 3 : ℝ))) + (((1 / 144 : ℚ) : ℝ) * trigamma (1 / 2 : ℝ))) + (((1 / 81 : ℚ) : ℝ) * trigamma (2 / 3 : ℝ))) + (((25 / 1296 : ℚ) : ℝ) * trigamma (5 / 6 : ℝ))) / zetaTwo := by
    rw [qResidue_gram_eq_trigamma 6 6 (by norm_num) (by norm_num)]
    rw [show Nat.lcm 6 6 = 6 by decide]
    norm_num [Fin.sum_univ_succ, residueFraction]
    field_simp [ne_of_gt zetaTwo_pos]
    <;> ring
  have hn := (contains_add (contains_add (contains_add (contains_add (contains_mul (contains_point (1 / 1296 : ℚ)) tg_1_6_contains)
      (contains_mul (contains_point (1 / 324 : ℚ)) tg_1_3_contains))
      (contains_mul (contains_point (1 / 144 : ℚ)) tg_1_2_contains))
      (contains_mul (contains_point (1 / 81 : ℚ)) tg_2_3_contains))
      (contains_mul (contains_point (25 / 1296 : ℚ)) tg_5_6_contains))
  have hq := contains_div_pos hn zeta_bounds (by norm_num [tg_1_1])
  rw [heq]
  exact contains_weaken hq
    (by norm_num [gram_6_6_interval, tg_1_6, tg_1_3, tg_1_2, tg_2_3, tg_5_6, tg_1_1, RatInterval.div, RatInterval.mul, RatInterval.inv, RatInterval.point, RatInterval.add])
    (by norm_num [gram_6_6_interval, tg_1_6, tg_1_3, tg_1_2, tg_2_3, tg_5_6, tg_1_1, RatInterval.div, RatInterval.mul, RatInterval.inv, RatInterval.point, RatInterval.add])

end RiemannResearch.RH.QResidueGramNumerical
