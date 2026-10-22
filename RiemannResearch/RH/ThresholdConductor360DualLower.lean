import Mathlib.Algebra.BigOperators.Field
import RiemannResearch.Analysis.PeriodicSquareBound
import RiemannResearch.LinearAlgebra.WeightedDualCertificate
import RiemannResearch.RH.ThresholdInfiniteCertificate
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.IntervalCases

/-!
# A rational dual obstruction for the full conductor-360 generator span

All 34 allowed generators (a in {2,3}, a*m dividing 360) occur below.
The dual annihilates them all, with no numerical optimality assumption.
The two retained progression masses give an exact rational lower enclosure;
the full positive remainder is present in the actual infinite error.
-/

open scoped BigOperators
namespace RiemannResearch.RH.TwoSeedThreshold
open Pareto
open RiemannResearch.LinearAlgebra
noncomputable section
set_option maxRecDepth 8192
set_option maxHeartbeats 20000000

/-- Two exact positive masses give a lower enclosure of each residue weight. -/
def residueLower360 (r : ℕ) : ℝ :=
  1 / ((r : ℝ) * (r + 1)) +
  1 / (((r : ℝ) + 360) * (r + 361))

def conductor360Generator (j : Fin 34) (k : ℕ) : ℝ :=
  certificateGenerator
    ((![(2 : ℕ), 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3]) j)
    ((![(1 : ℕ), 2, 3, 4, 5, 6, 9, 10, 12, 15, 18, 20, 30, 36, 45, 60, 90, 180, 1, 2, 3, 4, 5, 6, 8, 10, 12, 15, 20, 24, 30, 40, 60, 120]) j) k

/-- The 34 indexed generators exhaust every legal conductor-360 pair. -/
theorem conductor360Generator_exhaustive (a m : ℕ)
    (ha : a = 2 ∨ a = 3) (hm : 0 < m) (hd : a*m ∣ 360) :
    ∃ j : Fin 34, certificateGenerator a m = conductor360Generator j := by
  have ham : a*m ≤ 360 := Nat.le_of_dvd (by norm_num) hd
  rcases ha with rfl | rfl
  · have hmle : m ≤ 180 := by omega
    interval_cases m <;> norm_num at hd
    all_goals first
      | exact ⟨(0 : Fin 34), rfl⟩
      | exact ⟨(1 : Fin 34), rfl⟩
      | exact ⟨(2 : Fin 34), rfl⟩
      | exact ⟨(3 : Fin 34), rfl⟩
      | exact ⟨(4 : Fin 34), rfl⟩
      | exact ⟨(5 : Fin 34), rfl⟩
      | exact ⟨(6 : Fin 34), rfl⟩
      | exact ⟨(7 : Fin 34), rfl⟩
      | exact ⟨(8 : Fin 34), rfl⟩
      | exact ⟨(9 : Fin 34), rfl⟩
      | exact ⟨(10 : Fin 34), rfl⟩
      | exact ⟨(11 : Fin 34), rfl⟩
      | exact ⟨(12 : Fin 34), rfl⟩
      | exact ⟨(13 : Fin 34), rfl⟩
      | exact ⟨(14 : Fin 34), rfl⟩
      | exact ⟨(15 : Fin 34), rfl⟩
      | exact ⟨(16 : Fin 34), rfl⟩
      | exact ⟨(17 : Fin 34), rfl⟩
  · have hmle : m ≤ 120 := by omega
    interval_cases m <;> norm_num at hd
    all_goals first
      | exact ⟨(18 : Fin 34), rfl⟩
      | exact ⟨(19 : Fin 34), rfl⟩
      | exact ⟨(20 : Fin 34), rfl⟩
      | exact ⟨(21 : Fin 34), rfl⟩
      | exact ⟨(22 : Fin 34), rfl⟩
      | exact ⟨(23 : Fin 34), rfl⟩
      | exact ⟨(24 : Fin 34), rfl⟩
      | exact ⟨(25 : Fin 34), rfl⟩
      | exact ⟨(26 : Fin 34), rfl⟩
      | exact ⟨(27 : Fin 34), rfl⟩
      | exact ⟨(28 : Fin 34), rfl⟩
      | exact ⟨(29 : Fin 34), rfl⟩
      | exact ⟨(30 : Fin 34), rfl⟩
      | exact ⟨(31 : Fin 34), rfl⟩
      | exact ⟨(32 : Fin 34), rfl⟩
      | exact ⟨(33 : Fin 34), rfl⟩

def conductor360Combination (c : Fin 34 → ℝ) (k : ℕ) : ℝ :=
  ∑ j : Fin 34, c j * conductor360Generator j k

private def dualNumeratorInt360 (r : Fin 360) : ℤ :=
  let blocks : Fin 12 → Fin 30 → ℤ :=
    ![![28889, 5316, 1393, 11346, -9401, 9698, -9552, 1345, 4581, 2571, -5004, 4632, -1216, -1178, -1277, 1202, -2017, 2395, -333, -211, -223, -255, -1947, 1149, 274, 217, 622, 840, -305, 166],
    ![-805, -155, -159, -172, -570, 968, 248, 218, 197, 408, -163, 231, -283, -163, 10, -7, -430, 346, -58, -108, -110, -28, -362, 142, -32, 171, 160, 147, -129, 95],
    ![-164, -166, -80, 77, -46, 115, -101, -52, -54, -79, -266, 294, 107, 100, 87, 121, -43, 73, -83, -23, 27, 22, -118, 85, 11, 7, 5, 88, -36, 82],
    ![-36, -10, -11, -14, -72, 127, 20, 17, 50, 53, -43, 26, -67, -5, -10, -12, -98, 83, -1, -13, -14, 39, -39, 18, -23, -6, 18, 16, -55, 30],
    ![-41, -42, -42, -27, -61, 35, -27, 14, 13, 4, -54, 31, -26, -27, -7, 29, -25, 14, -38, -36, -36, -37, -86, 62, 35, 33, 32, 42, -4, 16],
    ![-29, 1, 15, 14, -9, 52, 10, 9, 8, 23, -16, 43, 4, 13, 10, 9, -28, 40, 4, -1, 11, 18, -16, 9, -10, 13, 12, 11, -21, 27],
    ![-10, -11, -11, 10, -7, 15, -15, -8, 2, -2, -31, 23, -6, -7, -8, -2, -29, 12, -15, -5, -5, -6, -31, 6, -7, -8, 0, 17, -8, 3],
    ![-21, -15, -16, -16, -29, 41, 17, 17, 16, 17, -5, 11, -11, 4, 11, 10, -11, 20, -1, -4, -4, 10, -11, 20, 9, 13, 13, 12, -7, 15],
    ![-4, -4, 2, 6, -4, 10, -8, 4, 3, 1, -17, 20, 3, 2, 1, 13, -4, 8, -8, -8, -2, -3, -19, 11, 3, 2, 2, 5, -10, 5],
    ![-10, 0, 0, -1, -9, 13, -2, -2, 3, 8, -6, 4, -10, -7, -7, -8, -21, 20, 6, 4, 4, 7, -6, 3, -4, 5, 9, 9, -4, 6],
    ![-6, -6, -7, 2, -5, 14, 1, 4, 4, 2, -10, 12, 1, 0, 4, 7, -5, 4, -8, -3, -3, -4, -15, 9, 3, 2, 2, 9, -1, 3],
    ![-7, -5, -1, -2, -7, 12, 2, 1, 1, 2, -8, 7, -3, 4, 3, 3, -7, 7, -3, -4, -1, 6, -4, 3, -2, 0, 0, 0, -9, 10]]
  blocks
    ⟨r.val / 30, by have hr := r.isLt; omega⟩
    ⟨r.val % 30, Nat.mod_lt _ (by norm_num)⟩

private def dualNumerator360 (r : Fin 360) : ℝ :=
  (dualNumeratorInt360 r : ℝ)

private def dual360 (r : Fin 360) : ℝ :=
  dualNumerator360 r / 1000000

private def dualLowerNumeratorInt360 (r : Fin 360) : ℤ :=
  let blocks : Fin 12 → Fin 30 → ℤ :=
    ![![5610887, 1046244, 276271, 2011775, -2145277, 1544708, -2421137, 255981, 727454, 441547, -1331013, 592071, -270077, -264698, -294471, 201176, -527623, 283295, -70803, -44065, -46891, -54279, -597871, 150908, 49941, 40109, 95298, 111011, -69048, 30652],
    ![-224871, -33520, -34617, -37894, -154611, 69837, 41028, 36622, 33404, 54576, -37127, 36669, -71579, -37798, 1979, -1411, -127155, 41434, -12413, -24530, -25160, -5813, -109288, 22513, -6710, 25034, 23694, 22147, -31575, 15763],
    ![-42761, -43733, -18524, 12989, -10087, 17290, -24735, -11638, -12173, -18821, -88404, 14610, 15388, 14608, 13211, 15887, -9677, 11418, -20816, -4932, 4931, 4081, -32976, 12021, 2114, 1364, 981, 11762, -8199, 11106],
    ![-8243, -2083, -2302, -2968, -18929, 11023, 3636, 3131, 7635, 7891, -10417, 4523, -17981, -1026, -2106, -2556, -30142, 8903, -202, -2796, -3031, 5978, -9653, 3198, -5267, -1247, 3178, 2861, -15068, 4770],
    ![-10533, -10887, -10926, -6460, -17694, 5163, -6510, 2497, 2335, 774, -15506, 4626, -6323, -6628, -1484, 4343, -6098, 2450, -10207, -9572, -9604, -9973, -31286, 4982, 4605, 4443, 4345, 4815, -833, 2666],
    ![-7575, 197, 2513, 2370, -1980, 4334, 1772, 1613, 1451, 3355, -3810, 4148, 761, 2183, 1750, 1595, -7599, 3876, 758, -203, 1877, 2727, -3897, 1577, -2279, 2124, 1990, 1852, -5480, 3263],
    ![-2297, -2563, -2566, 1694, -1552, 2299, -3708, -1804, 387, -413, -9345, 2851, -1321, -1566, -1818, -414, -8715, 1896, -3795, -1090, -1090, -1331, -9721, 1066, -1583, -1841, 0, 2292, -1848, 564],
    ![-5936, -3893, -4225, -4234, -9226, 1294, 2202, 2192, 2121, 2172, -1108, 1677, -2728, 729, 1664, 1553, -2745, 2185, -205, -874, -875, 1531, -2772, 2096, 1411, 1783, 1776, 1693, -1643, 1878],
    ![-881, -881, 379, 1015, -883, 1478, -1937, 715, 552, 194, -4964, 1820, 550, 377, 194, 1652, -891, 1235, -1967, -1970, -424, -653, -5927, 1482, 546, 375, 375, 847, -2614, 845],
    ![-2623, 0, 0, -207, -2318, 1513, -426, -427, 540, 1177, -1440, 692, -2674, -1732, -1735, -2040, -7245, 1220, 948, 687, 686, 1050, -1459, 535, -917, 817, 1204, 1201, -919, 930],
    ![-1471, -1473, -1774, 369, -1193, 1280, 192, 674, 673, 368, -2799, 1243, 191, 0, 669, 997, -1207, 666, -2136, -676, -677, -937, -4924, 1103, 522, 365, 365, 1087, -209, 520],
    ![-1838, -1225, -210, -437, -1848, 1078, 363, 190, 190, 362, -2204, 935, -686, 646, 513, 512, -1877, 920, -689, -959, -210, 840, -961, 509, -441, 0, 0, 0, -2638, 960]]
  blocks
    ⟨r.val / 30, by have hr := r.isLt; omega⟩
    ⟨r.val % 30, Nat.mod_lt _ (by norm_num)⟩

private def dualLowerCap360 (r : Fin 360) : ℝ :=
  (dualLowerNumeratorInt360 r : ℝ) / 100000000

/-- Integer values of the unchanged real generators. -/
private def conductor360GeneratorInt (j : Fin 34) (k : ℕ) : ℤ :=
  let a : ℕ := ((![(2 : ℕ), 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3, 3]) j)
  let m : ℕ := ((![(1 : ℕ), 2, 3, 4, 5, 6, 9, 10, 12, 15, 18, 20, 30, 36, 45, 60, 90, 180, 1, 2, 3, 4, 5, 6, 8, 10, 12, 15, 20, 24, 30, 40, 60, 120]) j)
  ((k % (a*m) : ℕ) : ℤ) - ((k % m : ℕ) : ℤ)

private theorem conductor360Generator_eq_int (j : Fin 34) (k : ℕ) :
    conductor360Generator j k = (conductor360GeneratorInt j k : ℝ) := by
  simp only [conductor360Generator, certificateGenerator, conductor360GeneratorInt,
    Int.cast_sub, Int.cast_natCast]

/-- A finite integer identity, checked by kernel reduction of decidable equality. -/
private theorem dualNumeratorInt360_annihilates_generator (j : Fin 34) :
    (∑ r : Fin 360, dualNumeratorInt360 r * conductor360GeneratorInt j (r.val+1)) = 0 := by
  fin_cases j <;> decide

private theorem dualNumerator360_annihilates_generator (j : Fin 34) :
    (∑ r : Fin 360, dualNumerator360 r * conductor360Generator j (r.val+1)) = 0 := by
  simp only [dualNumerator360, conductor360Generator_eq_int]
  exact_mod_cast (dualNumeratorInt360_annihilates_generator j)

private theorem dual360_annihilates_generator (j : Fin 34) :
    (∑ r : Fin 360, dual360 r * conductor360Generator j (r.val+1)) = 0 := by
  simp only [dual360, div_mul_eq_mul_div]
  rw [← Finset.sum_div, dualNumerator360_annihilates_generator, zero_div]

private theorem dual360_annihilates_combination (c : Fin 34 → ℝ) :
    (∑ r : Fin 360, dual360 r * conductor360Combination c (r.val+1)) = 0 := by
  unfold conductor360Combination
  calc
    _ = ∑ r : Fin 360, ∑ j : Fin 34,
        c j * (dual360 r * conductor360Generator j (r.val+1)) := by
      apply Finset.sum_congr rfl
      intro r _
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = ∑ j : Fin 34, ∑ r : Fin 360,
        c j * (dual360 r * conductor360Generator j (r.val+1)) := by
      rw [Finset.sum_comm]
    _ = ∑ j : Fin 34, c j *
        (∑ r : Fin 360, dual360 r * conductor360Generator j (r.val+1)) := by
      simp only [Finset.mul_sum]
    _ = 0 := by simp only [dual360_annihilates_generator, mul_zero, Finset.sum_const_zero]

private def dualLowerNumeratorNat360 (k : ℕ) : ℤ :=
  dualLowerNumeratorInt360 ⟨k % 360, Nat.mod_lt _ (by norm_num)⟩

private theorem dualLowerNumeratorNat360_sum_split (offset n m : ℕ) :
    (∑ r : Fin (n+m), dualLowerNumeratorNat360 (offset+r.val)) =
      (∑ r : Fin n, dualLowerNumeratorNat360 (offset+r.val)) +
        ∑ r : Fin m, dualLowerNumeratorNat360 ((offset+n)+r.val) := by
  rw [Fin.sum_univ_add]
  simp only [Fin.val_natAdd, Fin.val_castAdd, Nat.add_assoc]

private theorem dualLowerNumeratorNat360_row0 :
    (∑ r : Fin 30, dualLowerNumeratorNat360 (0+r.val)) = (5332075 : ℤ) := by
  decide

private theorem dualLowerNumeratorNat360_row1 :
    (∑ r : Fin 30, dualLowerNumeratorNat360 (30+r.val)) = (-551372 : ℤ) := by
  decide

private theorem dualLowerNumeratorNat360_row2 :
    (∑ r : Fin 30, dualLowerNumeratorNat360 (60+r.val)) = (-183715 : ℤ) := by
  decide

private theorem dualLowerNumeratorNat360_row3 :
    (∑ r : Fin 30, dualLowerNumeratorNat360 (90+r.val)) = (-69290 : ℤ) := by
  decide

private theorem dualLowerNumeratorNat360_row4 :
    (∑ r : Fin 30, dualLowerNumeratorNat360 (120+r.val)) = (-122480 : ℤ) := by
  decide

private theorem dualLowerNumeratorNat360_row5 :
    (∑ r : Fin 30, dualLowerNumeratorNat360 (150+r.val)) = (15263 : ℤ) := by
  decide

private theorem dualLowerNumeratorNat360_row6 :
    (∑ r : Fin 30, dualLowerNumeratorNat360 (180+r.val)) = (-47332 : ℤ) := by
  decide

private theorem dualLowerNumeratorNat360_row7 :
    (∑ r : Fin 30, dualLowerNumeratorNat360 (210+r.val)) = (-10507 : ℤ) := by
  decide

private theorem dualLowerNumeratorNat360_row8 :
    (∑ r : Fin 30, dualLowerNumeratorNat360 (240+r.val)) = (-9361 : ℤ) := by
  decide

private theorem dualLowerNumeratorNat360_row9 :
    (∑ r : Fin 30, dualLowerNumeratorNat360 (270+r.val)) = (-12962 : ℤ) := by
  decide

private theorem dualLowerNumeratorNat360_row10 :
    (∑ r : Fin 30, dualLowerNumeratorNat360 (300+r.val)) = (-8192 : ℤ) := by
  decide

private theorem dualLowerNumeratorNat360_row11 :
    (∑ r : Fin 30, dualLowerNumeratorNat360 (330+r.val)) = (-8205 : ℤ) := by
  decide

private theorem dualLowerNumeratorInt360_sum :
    (∑ r : Fin 360, dualLowerNumeratorInt360 r) = (4323922 : ℤ) := by
  have he : (∑ r : Fin 360, dualLowerNumeratorInt360 r) =
      ∑ r : Fin 360, dualLowerNumeratorNat360 (0+r.val) := by
    apply Finset.sum_congr rfl
    intro r _
    unfold dualLowerNumeratorNat360
    congr 1
    apply Fin.ext
    simp [Nat.mod_eq_of_lt r.isLt]
  rw [he]
  rw [dualLowerNumeratorNat360_sum_split 0 30 330, dualLowerNumeratorNat360_row0]
  rw [dualLowerNumeratorNat360_sum_split 30 30 300, dualLowerNumeratorNat360_row1]
  rw [dualLowerNumeratorNat360_sum_split 60 30 270, dualLowerNumeratorNat360_row2]
  rw [dualLowerNumeratorNat360_sum_split 90 30 240, dualLowerNumeratorNat360_row3]
  rw [dualLowerNumeratorNat360_sum_split 120 30 210, dualLowerNumeratorNat360_row4]
  rw [dualLowerNumeratorNat360_sum_split 150 30 180, dualLowerNumeratorNat360_row5]
  rw [dualLowerNumeratorNat360_sum_split 180 30 150, dualLowerNumeratorNat360_row6]
  rw [dualLowerNumeratorNat360_sum_split 210 30 120, dualLowerNumeratorNat360_row7]
  rw [dualLowerNumeratorNat360_sum_split 240 30 90, dualLowerNumeratorNat360_row8]
  rw [dualLowerNumeratorNat360_sum_split 270 30 60, dualLowerNumeratorNat360_row9]
  rw [dualLowerNumeratorNat360_sum_split 300 30 30, dualLowerNumeratorNat360_row10]
  rw [dualLowerNumeratorNat360_row11]
  norm_num

private def dualQ360 (r : Fin 360) : ℚ :=
  (dualNumeratorInt360 r : ℚ) / 1000000

private def residueLowerQ360 (r : ℕ) : ℚ :=
  1 / ((r : ℚ) * (r + 1)) +
  1 / (((r : ℚ) + 360) * (r + 361))

private def dualLowerCapQ360 (r : Fin 360) : ℚ :=
  (dualLowerNumeratorInt360 r : ℚ) / 100000000

private theorem dualQ360_cast (r : Fin 360) :
    (dualQ360 r : ℝ) = dual360 r := by
  simp only [dualQ360, dual360, dualNumerator360]
  push_cast <;> rfl

private theorem residueLowerQ360_cast (r : ℕ) :
    (residueLowerQ360 r : ℝ) = residueLower360 r := by
  simp only [residueLowerQ360, residueLower360]
  push_cast <;> rfl

private theorem dualLowerCapQ360_cast (r : Fin 360) :
    (dualLowerCapQ360 r : ℝ) = dualLowerCap360 r := by
  simp only [dualLowerCapQ360, dualLowerCap360]
  push_cast <;> rfl

private theorem dualLowerCapQ360_block0 (r : Fin 360)
    (hlo : 0 ≤ r.val) (hhi : r.val < 30) :
    dualLowerCapQ360 r ≤ 2 * dualQ360 r - (dualQ360 r)^2 / residueLowerQ360 (r.val+1) := by
  rcases r with ⟨r, hr⟩
  dsimp only at hlo hhi ⊢
  interval_cases r <;>
    norm_num [dualLowerCapQ360, dualLowerNumeratorInt360, dualQ360,
      dualNumeratorInt360, residueLowerQ360]

private theorem dualLowerCapQ360_block1 (r : Fin 360)
    (hlo : 30 ≤ r.val) (hhi : r.val < 60) :
    dualLowerCapQ360 r ≤ 2 * dualQ360 r - (dualQ360 r)^2 / residueLowerQ360 (r.val+1) := by
  rcases r with ⟨r, hr⟩
  dsimp only at hlo hhi ⊢
  interval_cases r <;>
    norm_num [dualLowerCapQ360, dualLowerNumeratorInt360, dualQ360,
      dualNumeratorInt360, residueLowerQ360]

private theorem dualLowerCapQ360_block2 (r : Fin 360)
    (hlo : 60 ≤ r.val) (hhi : r.val < 90) :
    dualLowerCapQ360 r ≤ 2 * dualQ360 r - (dualQ360 r)^2 / residueLowerQ360 (r.val+1) := by
  rcases r with ⟨r, hr⟩
  dsimp only at hlo hhi ⊢
  interval_cases r <;>
    norm_num [dualLowerCapQ360, dualLowerNumeratorInt360, dualQ360,
      dualNumeratorInt360, residueLowerQ360]

private theorem dualLowerCapQ360_block3 (r : Fin 360)
    (hlo : 90 ≤ r.val) (hhi : r.val < 120) :
    dualLowerCapQ360 r ≤ 2 * dualQ360 r - (dualQ360 r)^2 / residueLowerQ360 (r.val+1) := by
  rcases r with ⟨r, hr⟩
  dsimp only at hlo hhi ⊢
  interval_cases r <;>
    norm_num [dualLowerCapQ360, dualLowerNumeratorInt360, dualQ360,
      dualNumeratorInt360, residueLowerQ360]

private theorem dualLowerCapQ360_block4 (r : Fin 360)
    (hlo : 120 ≤ r.val) (hhi : r.val < 150) :
    dualLowerCapQ360 r ≤ 2 * dualQ360 r - (dualQ360 r)^2 / residueLowerQ360 (r.val+1) := by
  rcases r with ⟨r, hr⟩
  dsimp only at hlo hhi ⊢
  interval_cases r <;>
    norm_num [dualLowerCapQ360, dualLowerNumeratorInt360, dualQ360,
      dualNumeratorInt360, residueLowerQ360]

private theorem dualLowerCapQ360_block5 (r : Fin 360)
    (hlo : 150 ≤ r.val) (hhi : r.val < 180) :
    dualLowerCapQ360 r ≤ 2 * dualQ360 r - (dualQ360 r)^2 / residueLowerQ360 (r.val+1) := by
  rcases r with ⟨r, hr⟩
  dsimp only at hlo hhi ⊢
  interval_cases r <;>
    norm_num [dualLowerCapQ360, dualLowerNumeratorInt360, dualQ360,
      dualNumeratorInt360, residueLowerQ360]

private theorem dualLowerCapQ360_block6 (r : Fin 360)
    (hlo : 180 ≤ r.val) (hhi : r.val < 210) :
    dualLowerCapQ360 r ≤ 2 * dualQ360 r - (dualQ360 r)^2 / residueLowerQ360 (r.val+1) := by
  rcases r with ⟨r, hr⟩
  dsimp only at hlo hhi ⊢
  interval_cases r <;>
    norm_num [dualLowerCapQ360, dualLowerNumeratorInt360, dualQ360,
      dualNumeratorInt360, residueLowerQ360]

private theorem dualLowerCapQ360_block7 (r : Fin 360)
    (hlo : 210 ≤ r.val) (hhi : r.val < 240) :
    dualLowerCapQ360 r ≤ 2 * dualQ360 r - (dualQ360 r)^2 / residueLowerQ360 (r.val+1) := by
  rcases r with ⟨r, hr⟩
  dsimp only at hlo hhi ⊢
  interval_cases r <;>
    norm_num [dualLowerCapQ360, dualLowerNumeratorInt360, dualQ360,
      dualNumeratorInt360, residueLowerQ360]

private theorem dualLowerCapQ360_block8 (r : Fin 360)
    (hlo : 240 ≤ r.val) (hhi : r.val < 270) :
    dualLowerCapQ360 r ≤ 2 * dualQ360 r - (dualQ360 r)^2 / residueLowerQ360 (r.val+1) := by
  rcases r with ⟨r, hr⟩
  dsimp only at hlo hhi ⊢
  interval_cases r <;>
    norm_num [dualLowerCapQ360, dualLowerNumeratorInt360, dualQ360,
      dualNumeratorInt360, residueLowerQ360]

private theorem dualLowerCapQ360_block9 (r : Fin 360)
    (hlo : 270 ≤ r.val) (hhi : r.val < 300) :
    dualLowerCapQ360 r ≤ 2 * dualQ360 r - (dualQ360 r)^2 / residueLowerQ360 (r.val+1) := by
  rcases r with ⟨r, hr⟩
  dsimp only at hlo hhi ⊢
  interval_cases r <;>
    norm_num [dualLowerCapQ360, dualLowerNumeratorInt360, dualQ360,
      dualNumeratorInt360, residueLowerQ360]

private theorem dualLowerCapQ360_block10 (r : Fin 360)
    (hlo : 300 ≤ r.val) (hhi : r.val < 330) :
    dualLowerCapQ360 r ≤ 2 * dualQ360 r - (dualQ360 r)^2 / residueLowerQ360 (r.val+1) := by
  rcases r with ⟨r, hr⟩
  dsimp only at hlo hhi ⊢
  interval_cases r <;>
    norm_num [dualLowerCapQ360, dualLowerNumeratorInt360, dualQ360,
      dualNumeratorInt360, residueLowerQ360]

private theorem dualLowerCapQ360_block11 (r : Fin 360)
    (hlo : 330 ≤ r.val) (hhi : r.val < 360) :
    dualLowerCapQ360 r ≤ 2 * dualQ360 r - (dualQ360 r)^2 / residueLowerQ360 (r.val+1) := by
  rcases r with ⟨r, hr⟩
  dsimp only at hlo hhi ⊢
  interval_cases r <;>
    norm_num [dualLowerCapQ360, dualLowerNumeratorInt360, dualQ360,
      dualNumeratorInt360, residueLowerQ360]

private theorem dualLowerCapQ360_pointwise (r : Fin 360) :
    dualLowerCapQ360 r ≤ 2 * dualQ360 r - (dualQ360 r)^2 / residueLowerQ360 (r.val+1) := by
  by_cases h0 : r.val < 30
  · exact dualLowerCapQ360_block0 r (by omega) h0
  by_cases h1 : r.val < 60
  · exact dualLowerCapQ360_block1 r (by omega) h1
  by_cases h2 : r.val < 90
  · exact dualLowerCapQ360_block2 r (by omega) h2
  by_cases h3 : r.val < 120
  · exact dualLowerCapQ360_block3 r (by omega) h3
  by_cases h4 : r.val < 150
  · exact dualLowerCapQ360_block4 r (by omega) h4
  by_cases h5 : r.val < 180
  · exact dualLowerCapQ360_block5 r (by omega) h5
  by_cases h6 : r.val < 210
  · exact dualLowerCapQ360_block6 r (by omega) h6
  by_cases h7 : r.val < 240
  · exact dualLowerCapQ360_block7 r (by omega) h7
  by_cases h8 : r.val < 270
  · exact dualLowerCapQ360_block8 r (by omega) h8
  by_cases h9 : r.val < 300
  · exact dualLowerCapQ360_block9 r (by omega) h9
  by_cases h10 : r.val < 330
  · exact dualLowerCapQ360_block10 r (by omega) h10
  exact dualLowerCapQ360_block11 r (by omega) r.isLt

private theorem dualLowerCap360_pointwise (r : Fin 360) :
    dualLowerCap360 r ≤ 2 * dual360 r - (dual360 r)^2 / residueLower360 (r.val+1) := by
  have h : (dualLowerCapQ360 r : ℝ) ≤
      2 * (dualQ360 r : ℝ) - (dualQ360 r : ℝ)^2 / (residueLowerQ360 (r.val+1) : ℝ) := by
    exact_mod_cast (dualLowerCapQ360_pointwise r)
  simpa only [dualLowerCapQ360_cast, dualQ360_cast, residueLowerQ360_cast] using h

private theorem dual360_lower_certificate :
    (27 : ℝ) / 625 <
      ∑ r : Fin 360, (2 * dual360 r - (dual360 r)^2 / residueLower360 (r.val+1)) := by
  apply lt_of_lt_of_le _ (Finset.sum_le_sum (fun r _ => dualLowerCap360_pointwise r))
  have hs : (∑ r : Fin 360, (dualLowerNumeratorInt360 r : ℝ)) = 4323922 := by
    exact_mod_cast dualLowerNumeratorInt360_sum
  simp only [dualLowerCap360]
  rw [← Finset.sum_div, hs]
  norm_num

/-- Every combination of all 34 conductor-360 legal generators has error > .0432
for every true weight vector dominating the two retained progression terms. -/
theorem conductor360_error_gt_of_weights (c : Fin 34 → ℝ)
    (w : Fin 360 → ℝ) (hw : ∀ r, residueLower360 (r.val+1) ≤ w r) :
    (27 : ℝ) / 625 <
      ∑ r : Fin 360, w r * (1-conductor360Combination c (r.val+1))^2 := by
  apply lt_of_lt_of_le dual360_lower_certificate
  apply le_trans (weighted_error_lower_of_dual
    (fun r => residueLower360 (r.val+1)) dual360
    (fun r => conductor360Combination c (r.val+1))
    (by intro r; unfold residueLower360; positivity)
    (dual360_annihilates_combination c))
  exact Finset.sum_le_sum fun r _ => mul_le_mul_of_nonneg_right (hw r) (sq_nonneg _)

theorem residueLower360_le_progressionWeight (r : ℕ) :
    residueLower360 r ≤ progressionWeight 360 r := by
  have he : residueLower360 r = positiveWeight r + positiveWeight (r+360) := by
    simp only [residueLower360, positiveWeight, Nat.cast_add, Nat.cast_ofNat]
    congr 1 <;> congr 1 <;> ring
  rw [he, progressionWeight_split 360 r (by norm_num),
    progressionWeight_split 360 (r+360) (by norm_num)]
  have hn := progressionWeight_nonneg 360 (r+360+360)
  linarith

theorem conductor360Generator_periodic (j : Fin 34) (k : ℕ) :
    conductor360Generator j (k+360) = conductor360Generator j k := by
  have h1 : (k+360)%1 = k%1 := by omega
  have h2 : (k+360)%2 = k%2 := by omega
  have h3 : (k+360)%3 = k%3 := by omega
  have h4 : (k+360)%4 = k%4 := by omega
  have h5 : (k+360)%5 = k%5 := by omega
  have h6 : (k+360)%6 = k%6 := by omega
  have h8 : (k+360)%8 = k%8 := by omega
  have h9 : (k+360)%9 = k%9 := by omega
  have h10 : (k+360)%10 = k%10 := by omega
  have h12 : (k+360)%12 = k%12 := by omega
  have h15 : (k+360)%15 = k%15 := by omega
  have h18 : (k+360)%18 = k%18 := by omega
  have h20 : (k+360)%20 = k%20 := by omega
  have h24 : (k+360)%24 = k%24 := by omega
  have h30 : (k+360)%30 = k%30 := by omega
  have h36 : (k+360)%36 = k%36 := by omega
  have h40 : (k+360)%40 = k%40 := by omega
  have h45 : (k+360)%45 = k%45 := by omega
  have h60 : (k+360)%60 = k%60 := by omega
  have h72 : (k+360)%72 = k%72 := by omega
  have h90 : (k+360)%90 = k%90 := by omega
  have h120 : (k+360)%120 = k%120 := by omega
  have h180 : (k+360)%180 = k%180 := by omega
  have h360 : (k+360)%360 = k%360 := by omega
  fin_cases j <;>
    simp [conductor360Generator, certificateGenerator, h1, h2, h3, h4, h5, h6, h8, h9, h10, h12, h15, h18, h20, h24, h30, h36, h40, h45, h60, h72, h90, h120, h180, h360]

theorem conductor360Combination_periodic (c : Fin 34 → ℝ) :
    Function.Periodic (conductor360Combination c) 360 := by
  intro k
  simp only [conductor360Combination, conductor360Generator_periodic]

theorem conductor360Combination_error_bound (c : Fin 34 → ℝ) (k : ℕ) :
    (1-conductor360Combination c k)^2 ≤
      ∑ r : Fin 360, (1-conductor360Combination c r.val)^2 := by
  exact RiemannResearch.Analysis.periodic_square_error_bound
    (conductor360Combination c) 360 (by norm_num) (conductor360Combination_periodic c) k

theorem conductor360Combination_error_summable (c : Fin 34 → ℝ) :
    Summable (fun k : ℕ => positiveWeight (k+1) *
      (1-conductor360Combination c (k+1))^2) := by
  have hw : Summable (fun k : ℕ => positiveWeight (k+1)) :=
    positiveWeight_summable.comp_injective (by intro a b h; exact Nat.add_right_cancel h)
  apply Summable.of_nonneg_of_le
    (fun k => mul_nonneg (positiveWeight_nonneg _) (sq_nonneg _))
    (fun k => mul_le_mul_of_nonneg_left (conductor360Combination_error_bound c _)
      (positiveWeight_nonneg _))
    (hw.mul_right _)

theorem conductor360Combination_add_multiple (c : Fin 34 → ℝ) (r j : ℕ) :
    conductor360Combination c (r+360*j) = conductor360Combination c r := by
  induction j with
  | zero => simp
  | succ j ih =>
    have h : r+360*(j+1) = (r+360*j)+360 := by omega
    rw [h, conductor360Combination_periodic c, ih]

theorem conductor360Combination_exact_error (c : Fin 34 → ℝ) :
    (∑' k : ℕ, positiveWeight (k+1) * (1-conductor360Combination c (k+1))^2) =
      ∑ r : Fin 360, progressionWeight 360 (r.val+1) *
        (1-conductor360Combination c (r.val+1))^2 := by
  rw [Nat.sumByResidueClasses (conductor360Combination_error_summable c) 360]
  apply Finset.sum_congr rfl
  intro r _
  calc
    _ = ∑' j : ℕ, positiveWeight ((r.val+1)+360*j) *
        (1-conductor360Combination c (r.val+1))^2 := by
      apply tsum_congr
      intro j
      have h : r.val+360*j+1 = (r.val+1)+360*j := by omega
      rw [h, conductor360Combination_add_multiple]
    _ = _ := by rw [tsum_mul_right]; rfl

/-- Unconditional full infinite-error lower bound for the conductor-360 legal span. -/
theorem conductor360Combination_full_error_gt (c : Fin 34 → ℝ) :
    (27 : ℝ) / 625 <
      ∑' k : ℕ, positiveWeight (k+1) * (1-conductor360Combination c (k+1))^2 := by
  rw [conductor360Combination_exact_error]
  exact conductor360_error_gt_of_weights c _ fun r =>
    residueLower360_le_progressionWeight (r.val+1)

end
end RiemannResearch.RH.TwoSeedThreshold
