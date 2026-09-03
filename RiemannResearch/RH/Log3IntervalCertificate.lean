/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/
import RiemannResearch.RH.StrictDiagonalDominance
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# Rational proof kernel for the localized `L = log 3` interval certificate

The original numerical experiment used interval LDL pivots after a floating
orthogonal preconditioner. This repaired interface removes that trust point.
It records exact rational unit-upper-triangular preconditioners and exact
rational diagonal/radius bounds. Lean verifies that the rational row margins
are positive, that each preconditioner is invertible, and that any real
Hermitian matrix satisfying the displayed enclosure hypotheses is positive
definite.

The remaining analytic obligation is explicit: establish the `hdiag` and
`hrow` inequalities for the finite Schur-complement matrices constructed from
the localized Weil operator. No floating-point eigenvalue or floating-point
matrix invertibility is used in the theorem below.
-/

namespace RiemannResearch.RH.Log3IntervalCertificate

open scoped BigOperators
open Matrix
open RiemannResearch.RH.StrictDiagonalDominance

variable {n : Type*} [Fintype n] [LinearOrder n] [DecidableEq n]

/-- The unit-upper-triangular matrix with prescribed strict upper entries. -/
def unitUpper (c : Matrix n n ℝ) : Matrix n n ℝ := fun i j =>
  if i = j then 1 else if i < j then c i j else 0

/-- `unitUpper c` is upper triangular. -/
theorem unitUpper_isUpperTriangular (c : Matrix n n ℝ) :
    (unitUpper c).IsUpperTriangular := by
  intro i j hji
  simp [unitUpper, (ne_of_gt hji).symm, not_lt_of_ge hji.le]

/-- Every diagonal entry of `unitUpper c` is one. -/
@[simp] theorem unitUpper_apply_self (c : Matrix n n ℝ) (i : n) :
    unitUpper c i i = 1 := by
  simp [unitUpper]

/-- The determinant of a unit-upper-triangular matrix is one. -/
theorem unitUpper_det (c : Matrix n n ℝ) :
    (unitUpper c).det = 1 := by
  rw [Matrix.det_of_isUpperTriangular _ (unitUpper_isUpperTriangular c)]
  simp

/-- A unit-upper-triangular real matrix acts surjectively on column vectors. -/
theorem unitUpper_mulVec_surjective (c : Matrix n n ℝ) :
    Function.Surjective (unitUpper c).mulVec := by
  rw [Matrix.mulVec_surjective_iff_isUnit, Matrix.isUnit_iff_isUnit_det,
    unitUpper_det]
  exact isUnit_one

/-- Congruence transform used by the exact rational certificate. -/
def congruence (Q A : Matrix n n ℝ) : Matrix n n ℝ :=
  Qᴴ * A * Q

/-- Positivity of an invertible congruence transform implies positivity of the
original Hermitian matrix. -/
theorem posDef_of_congruence_posDef
    {A Q : Matrix n n ℝ}
    (_hA : A.IsHermitian)
    (hQ : Function.Surjective Q.mulVec)
    (hcong : (congruence Q A).PosDef) :
    A.PosDef := by
  have hunit : IsUnit Q :=
    Matrix.mulVec_surjective_iff_isUnit.mp hQ
  apply (hunit.posDef_star_left_conjugate_iff (x := A)).mp
  simpa [congruence, star_eq_conjTranspose] using hcong

abbrev Log3Index := Fin 20

def evenPreconditionerCoefficientsQ : Matrix Log3Index Log3Index ℚ := ![
  ![1, -1.53120603, 13.09041586, 83.17163855, 739.87354880, 1252.37190581, 608.80100760, 106.78110954, -649.01308617, -1386.20744105, -1032.45640141, -1527.73262786, -1642.13314578, -1478.48976228, -1777.09126732, -1624.42384992, -1676.63756653, -1660.95901006, -1662.51138591, -1628.48363161],
  ![0, 1, -10.12469716, -68.09069249, -612.53874288, -1041.98796958, -517.82386118, -99.65198281, 527.82042289, 1139.42052085, 846.93103712, 1257.15374669, 1352.03105540, 1216.37180108, 1463.87398385, 1337.59771217, 1380.54387811, 1368.56536492, 1368.99051478, 1341.45240326],
  ![0, 0, 1, 8.52980202, 79.73103759, 137.76119234, 73.40084773, 17.79284261, -64.58250721, -144.64969023, -106.84148437, -160.24310281, -172.65398334, -154.97015775, -187.24833650, -170.89639449, -176.36923003, -175.21030108, -174.93108726, -171.60400882],
  ![0, 0, 0, 1, 10.00029899, 17.75867598, 10.77971455, 3.45772325, -7.01463484, -17.11581460, -12.49962887, -19.15311152, -20.71885245, -18.52278307, -22.55106740, -20.54153436, -21.19898903, -21.14139315, -21.03801237, -20.67987909],
  ![0, 0, 0, 0, 1, 1.48279988, 1.13195376, 0.46955887, -0.38506095, -1.19237935, -0.85576997, -1.37289576, -1.49880826, -1.33236324, -1.64479587, -1.49428482, -1.54280175, -1.54876952, -1.53350610, -1.51258556],
  ![0, 0, 0, 0, 0, 1, 0.91230396, 0.43190232, 0.01177124, -0.35938702, -0.25292445, -0.47262809, -0.53261892, -0.47064538, -0.60082492, -0.54464224, -0.56408440, -0.57413128, -0.56409012, -0.56036656],
  ![0, 0, 0, 0, 0, 0, 1, 0.10742586, 0.12462890, 0.13429128, 0.08594479, 0.10159009, 0.09864323, 0.08431798, 0.09580633, 0.08500591, 0.08569417, 0.08349985, 0.08221794, 0.07982034],
  ![0, 0, 0, 0, 0, 0, 0, 1, 0.12667917, 0.16151632, 0.09362916, 0.12908593, 0.13090516, 0.11033732, 0.13358429, 0.11812215, 0.11997190, 0.12035765, 0.11681898, 0.11517907],
  ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0.31733469, 0.14243329, 0.23850100, 0.24797966, 0.20346758, 0.25906412, 0.22688291, 0.23085207, 0.23654022, 0.22615012, 0.22539412],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0.01186488, 0.14646114, 0.16301337, 0.12829822, 0.17750957, 0.15337461, 0.15650574, 0.16484966, 0.15458056, 0.15616031],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0.20771491, 0.18642293, 0.13194302, 0.18178112, 0.15207265, 0.15296188, 0.16194751, 0.14891695, 0.15084893],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0.18795428, 0.10956944, 0.19442830, 0.15712332, 0.15892058, 0.17669407, 0.15708515, 0.16270601],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0.02095594, 0.11468184, 0.08648820, 0.08791430, 0.10382527, 0.08825468, 0.09374356],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0.22887022, 0.13349883, 0.12613514, 0.14874237, 0.12011312, 0.12787792],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0.03828975, 0.06034374, 0.10407792, 0.07394598, 0.08770649],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0.05697253, 0.09932139, 0.06077169, 0.07279055],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0.18378071, 0.07630609, 0.09992425],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -0.03744430, 0.03054387],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0.10388212],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]
]

/-- Exact rational unit-upper preconditioner for the even block. -/
def evenPreconditioner : Matrix Log3Index Log3Index ℝ :=
  unitUpper fun i j => (evenPreconditionerCoefficientsQ i j : ℝ)

def evenDiagLowerQ : Log3Index → ℚ := ![
  0.112447720870, 0.001477393749, 0.003026860213, 0.010435134292,
  0.294787867620, 0.289997422524, 1.046095279843, 1.898005678596,
  1.370675125494, 1.815946590769, 2.075449142320, 1.612019583562,
  2.400002482643, 2.102481985152, 2.039107786307, 2.739470557284,
  2.159631060912, 2.567188545601, 2.805253318714, 2.312310445565
]

def evenRowRadiusQ : Log3Index → ℚ := ![
  0.000063416545, 0.000097853353, 0.000837540002, 0.005306817418,
  0.045699659244, 0.075358256899, 0.037864809983, 0.006816855853,
  0.040263047206, 0.082821754138, 0.062823266528, 0.090604640099,
  0.096804343597, 0.087910951599, 0.104013092303, 0.095850156706,
  0.098658132158, 0.097817502796, 0.097900175651, 0.096069528280
]

/-- The rational row bounds for the even block are strictly separated. -/
theorem evenRationalMarginsPositive :
    ∀ i, evenRowRadiusQ i < evenDiagLowerQ i := by
  intro i
  fin_cases i <;> norm_num [evenRowRadiusQ, evenDiagLowerQ]

/-- Exact Lean-checkable endpoint for the even finite block. The two
hypotheses are the remaining analytic interval-enclosure obligations. -/
theorem evenBlock_posDef
    (A : Matrix Log3Index Log3Index ℝ)
    (hA : A.IsHermitian)
    (hdiag : ∀ i,
      (evenDiagLowerQ i : ℝ) ≤ congruence evenPreconditioner A i i)
    (hrow : ∀ i,
      offDiagonalRowSum (congruence evenPreconditioner A) i ≤
        (evenRowRadiusQ i : ℝ)) :
    A.PosDef := by
  have hsep : ∀ i,
      (evenRowRadiusQ i : ℝ) < (evenDiagLowerQ i : ℝ) := by
    intro i
    exact_mod_cast evenRationalMarginsPositive i
  have htransformed : (congruence evenPreconditioner A).PosDef := by
    apply posDef_of_row_interval_certificate
      (Matrix.isHermitian_conjTranspose_mul_mul evenPreconditioner hA)
      (fun i => (evenDiagLowerQ i : ℝ))
      (fun i => (evenRowRadiusQ i : ℝ))
    · exact hdiag
    · exact hrow
    · exact hsep
  apply posDef_of_congruence_posDef hA ?_ htransformed
  simpa [evenPreconditioner] using
    unitUpper_mulVec_surjective
      (fun i j => (evenPreconditionerCoefficientsQ i j : ℝ))

def oddPreconditionerCoefficientsQ : Matrix Log3Index Log3Index ℚ := ![
  ![1, -1.05548225, -33.37692792, 48.22854013, -80.73883733, -27.58009067, -39.84772679, -80.13875041, -52.22195118, -61.39027547, -56.34447245, -55.86213053, -47.20166500, -43.43255629, -48.53304430, -30.79945899, -39.91698375, -35.94356880, -20.29719702, -39.94026746],
  ![0, 1, 31.64899271, -45.72090632, 76.51393263, 26.14425172, 37.77532242, 75.95036784, 49.49781390, 58.19111171, 53.41035638, 52.95049724, 44.73829131, 41.16534164, 46.00053409, 29.19454831, 37.83705161, 34.07394508, 19.23931196, 37.86169478],
  ![0, 0, 1, -1.44309082, 2.40706807, 0.81748582, 1.18146857, 2.39104963, 1.55236548, 1.83065647, 1.68111700, 1.66630808, 1.40637572, 1.29380001, 1.44745293, 0.91776410, 1.19007829, 1.07148589, 0.60432269, 1.19061105],
  ![0, 0, 0, 1, -1.49508985, -0.47202249, -0.70221869, -1.47115296, -0.93665388, -1.10311344, -1.01252871, -1.00169127, -0.84350492, -0.77544838, -0.86825453, -0.55012518, -0.71350651, -0.64245553, -0.36240061, -0.71366529],
  ![0, 0, 0, 0, 1, 0.38907516, 0.53203282, 0.97620573, 0.66079218, 0.78108171, 0.71504454, 0.70654027, 0.59448157, 0.54620779, 0.61159117, 0.38733938, 0.50226447, 0.45218636, 0.25495508, 0.50267933],
  ![0, 0, 0, 0, 0, 1, 0.06922425, -0.01779075, 0.03256420, 0.03968930, 0.03589233, 0.03505502, 0.02928215, 0.02700397, 0.03031367, 0.01920098, 0.02497244, 0.02264476, 0.01289996, 0.02571566],
  ![0, 0, 0, 0, 0, 0, 1, 0.27428167, 0.27408796, 0.32593824, 0.29614067, 0.29132204, 0.24396339, 0.22497912, 0.25247868, 0.15999650, 0.20773508, 0.18785107, 0.10660993, 0.21164667],
  ![0, 0, 0, 0, 0, 0, 0, 1, 0.23834529, 0.27928520, 0.25432911, 0.25065667, 0.21006221, 0.19359612, 0.21729688, 0.13770306, 0.17882403, 0.16160552, 0.09134052, 0.18138084],
  ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0.28643253, 0.25472524, 0.25000744, 0.20910604, 0.19278206, 0.21629749, 0.13698257, 0.17782401, 0.16072794, 0.09111005, 0.18154235],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0.24027814, 0.23541930, 0.19669997, 0.18131802, 0.20345560, 0.12879373, 0.16721743, 0.15113452, 0.08558575, 0.17078344],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0.22410250, 0.18687167, 0.17221246, 0.19328453, 0.12232593, 0.15884024, 0.14367259, 0.08137124, 0.16250422],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0.17764723, 0.16370515, 0.18375256, 0.11625949, 0.15095556, 0.13653595, 0.07733252, 0.15455214],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0.15555478, 0.17465286, 0.11049621, 0.14347351, 0.12978594, 0.07349343, 0.14694997],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0.16631164, 0.10515664, 0.13652938, 0.12354248, 0.06995409, 0.13995630],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0.09969506, 0.12943275, 0.11711157, 0.06631218, 0.13278379],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0.12289318, 0.11124882, 0.06298867, 0.12613890],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0.10585953, 0.05994268, 0.12003576],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0.05682998, 0.11380610],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0.10791987],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]
]

/-- Exact rational unit-upper preconditioner for the odd block. -/
def oddPreconditioner : Matrix Log3Index Log3Index ℝ :=
  unitUpper fun i j => (oddPreconditionerCoefficientsQ i j : ℝ)

def oddDiagLowerQ : Log3Index → ℚ := ![
  0.073157443436, 0.000370488589, 0.790231564297, 0.113303087872,
  0.863974189017, 1.855065179501, 1.353981860710, 1.719599627339,
  2.123352317677, 1.676569198558, 2.416800591970, 2.227376055263,
  2.071957630713, 2.816375510185, 2.288969553207, 2.513878468374,
  2.952644552189, 2.382730422078, 2.953581114355, 2.899481165027
]

def oddRowRadiusQ : Log3Index → ℚ := ![
  0.000000076932, 0.000000097781, 0.000002932808, 0.000004205100,
  0.000006726518, 0.000002441304, 0.000003480968, 0.000006684191,
  0.000004502165, 0.000005240416, 0.000004846003, 0.000004797985,
  0.000004107072, 0.000003795262, 0.000004209972, 0.000002739238,
  0.000003501920, 0.000003170421, 0.000001831342, 0.000003503085
]

/-- The rational row bounds for the odd block are strictly separated. -/
theorem oddRationalMarginsPositive :
    ∀ i, oddRowRadiusQ i < oddDiagLowerQ i := by
  intro i
  fin_cases i <;> norm_num [oddRowRadiusQ, oddDiagLowerQ]

/-- Exact Lean-checkable endpoint for the odd finite block. The two
hypotheses are the remaining analytic interval-enclosure obligations. -/
theorem oddBlock_posDef
    (A : Matrix Log3Index Log3Index ℝ)
    (hA : A.IsHermitian)
    (hdiag : ∀ i,
      (oddDiagLowerQ i : ℝ) ≤ congruence oddPreconditioner A i i)
    (hrow : ∀ i,
      offDiagonalRowSum (congruence oddPreconditioner A) i ≤
        (oddRowRadiusQ i : ℝ)) :
    A.PosDef := by
  have hsep : ∀ i,
      (oddRowRadiusQ i : ℝ) < (oddDiagLowerQ i : ℝ) := by
    intro i
    exact_mod_cast oddRationalMarginsPositive i
  have htransformed : (congruence oddPreconditioner A).PosDef := by
    apply posDef_of_row_interval_certificate
      (Matrix.isHermitian_conjTranspose_mul_mul oddPreconditioner hA)
      (fun i => (oddDiagLowerQ i : ℝ))
      (fun i => (oddRowRadiusQ i : ℝ))
    · exact hdiag
    · exact hrow
    · exact hsep
  apply posDef_of_congruence_posDef hA ?_ htransformed
  simpa [oddPreconditioner] using
    unitUpper_mulVec_surjective
      (fun i j => (oddPreconditionerCoefficientsQ i j : ℝ))

end RiemannResearch.RH.Log3IntervalCertificate
