/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Cnoack3
-/
import RiemannResearch.RH.Log3Parameters
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
  change j < i at hji
  simp only [unitUpper]
  rw [if_neg (ne_of_gt hji), if_neg (not_lt_of_ge hji.le)]

/-- Every diagonal entry of `unitUpper c` is one. -/
@[simp] theorem unitUpper_apply_self (c : Matrix n n ℝ) (i : n) :
    unitUpper c i i = 1 := by
  simp [unitUpper]

/-- The determinant of a unit-upper-triangular matrix is one. -/
theorem unitUpper_det (c : Matrix n n ℝ) :
    (unitUpper c).det = 1 := by
  rw [Matrix.det_of_isUpperTriangular (unitUpper_isUpperTriangular c)]
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

abbrev Log3Index :=
  RiemannResearch.RH.Log3Parameters.LowIndex

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

/-- Exact eight-decimal rational rounding of the regenerated midpoint
nonpivoted-LDL preconditioner `L⁻ᵀ` for the odd block. -/
def oddPreconditionerCoefficientsQ : Matrix Log3Index Log3Index ℚ := ![
  ![1, -1.05548225, -33.37692792, 48.22854013, -80.73883733, -27.58009067, -39.84772679, -80.13875041, -52.22195118, -61.39027547, -56.34447245, -55.86213053, -47.20166500, -43.43255629, -48.53304430, -30.79945899, -39.91698375, -35.94356880, -20.29719702, -39.94026746],
  ![0, 1, 30.83048123, -47.55747741, 77.88910570, 25.47187823, 37.32110424, 77.47865363, 49.57655440, 58.89802329, 54.35401074, 53.29752802, 45.48077403, 41.73108447, 46.43330050, 29.76385878, 38.23139055, 34.47985945, 19.63304245, 38.22698224],
  ![0, 0, 1, -0.60633747, 0.92311913, 0.26803480, 0.41243203, 0.92804867, 0.56975685, 0.69393696, 0.64830413, 0.62071737, 0.54121660, 0.49367058, 0.54436961, 0.35642277, 0.44933366, 0.40661471, 0.23556578, 0.44869467],
  ![0, 0, 0, 1, -0.98256252, -0.19562390, -0.40047022, -1.12793564, -0.63736196, -0.82196675, -0.78783072, -0.72213568, -0.65625478, -0.59274103, -0.64347870, -0.43758641, -0.53412345, -0.48642552, -0.29033679, -0.53265779],
  ![0, 0, 0, 0, 1, -0.01524271, 0.05237209, 0.22937783, 0.11374700, 0.15815937, 0.15570101, 0.13482366, 0.12859296, 0.11461587, 0.12198957, 0.08656994, 0.10176256, 0.09330670, 0.05754806, 0.10116906],
  ![0, 0, 0, 0, 0, 1, 0.02911510, 0.08550528, 0.03764877, 0.05006571, 0.04800897, 0.04016551, 0.03829713, 0.03366129, 0.03533683, 0.02529317, 0.02921948, 0.02676023, 0.01665032, 0.02874913],
  ![0, 0, 0, 0, 0, 0, 1, 0.24074022, 0.06704684, 0.10225300, 0.10083857, 0.07556475, 0.07801052, 0.06689172, 0.06784864, 0.05182503, 0.05645972, 0.05223568, 0.03408213, 0.05520813],
  ![0, 0, 0, 0, 0, 0, 0, 1, -0.07760870, 0.02723888, 0.05234934, 0.02117451, 0.04250978, 0.03442799, 0.03092681, 0.03191549, 0.02826816, 0.02779521, 0.02168234, 0.02826540],
  ![0, 0, 0, 0, 0, 0, 0, 0, 1, 0.10811603, 0.09524991, 0.04711504, 0.06086198, 0.04807617, 0.04402097, 0.03929018, 0.03697271, 0.03500754, 0.02536568, 0.03537227],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0.11513208, 0.00900645, 0.05935693, 0.04238559, 0.03246210, 0.04088601, 0.03048329, 0.03088138, 0.02664183, 0.02966078],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -0.07780793, 0.01366956, 0.00662289, -0.00110469, 0.01540364, 0.00475364, 0.00732247, 0.01059276, 0.00597584],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0.13723439, 0.06451980, 0.03835807, 0.05201527, 0.03293549, 0.03322278, 0.03004080, 0.02951217],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -0.01135587, -0.02681543, 0.02310847, -0.00241269, 0.00438187, 0.01418127, 0.00168534],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -0.03033498, 0.02971996, 0.00060236, 0.00645715, 0.01421023, 0.00340337],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0.12907315, 0.02236249, 0.02827735, 0.03680433, 0.01729857],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -0.08252164, -0.02956521, 0.00393615, -0.02188629],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0.02920477, 0.04344823, 0.00641595],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0.08145784, -0.01252000],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, -0.09430238],
  ![0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1]
]

/-- Exact rational unit-upper preconditioner for the odd block. -/
def oddPreconditioner : Matrix Log3Index Log3Index ℝ :=
  unitUpper fun i j => (oddPreconditionerCoefficientsQ i j : ℝ)

/-- Regenerated interval diagonal lower endpoints, relaxed downward by
`10⁻¹²` so the certificate does not depend on last-bit endpoint tightness. -/
def oddDiagLowerQ : Log3Index → ℚ := ![
  0.073157443435, 0.000370488588, 0.790231564296, 0.113303087871,
  0.863974189016, 1.855065179500, 1.353981860709, 1.719599627338,
  2.123352317676, 1.676569198557, 2.416800591969, 2.227376055262,
  2.071957630712, 2.816375510184, 2.288969553206, 2.513878468373,
  2.952644552188, 2.382730422077, 2.953581114354, 2.899481165026
]

/-- Conservative exact row-radius bound for the regenerated odd preconditioner.
The external interval audit gives a maximum below `6.77 · 10⁻⁶`; proving the
corresponding analytic enclosure remains an explicit theorem hypothesis. -/
def oddRowRadiusQ : Log3Index → ℚ := fun _ => 0.000010000000

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
