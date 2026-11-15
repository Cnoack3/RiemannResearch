/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.QPeriodicCertifiedWeights
import RiemannResearch.LinearAlgebra.RationalLinearSolveCertificate
import RiemannResearch.LinearAlgebra.RationalQuadraticCertificate
import Mathlib.Data.Rat.Cast.Order
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases

/-!
# Kernel checked rational canonical collocation witnesses

Source: the 7 November 2026 canonical prime-power review. These tables
are untrusted rational proposals. Every source weight is attached to its
actual complete inverse-square series; every preconditioner is accepted
only after its exact finite defect and residual checks.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.CanonicalReviewCertificates
open RiemannResearch RatInterval ZetaTwoProbability
open RiemannResearch.Analysis.InverseSquareTailCertificates

def collocationMatrix {L n : ℕ} (W : Fin L → RatInterval)
    (rows cols : Fin n → ℕ) (i j : Fin n) : RatInterval :=
  RatInterval.sum Finset.univ (fun r =>
    if Nat.gcd (r.val+1) L = rows i then
      RatInterval.mul (W r) (RatInterval.point (((r.val+1) % cols j : ℕ) / (cols j : ℚ)))
    else RatInterval.point 0)

def collocationRhs {L n : ℕ} (W : Fin L → RatInterval)
    (rows : Fin n → ℕ) (i : Fin n) : RatInterval :=
  RatInterval.sum Finset.univ (fun r =>
    if Nat.gcd (r.val+1) L = rows i then W r else RatInterval.point 0)

def valueInterval {n : ℕ} (cols : Fin n → ℕ) (c : Fin n → RatInterval)
    (a : ℕ) : RatInterval :=
  RatInterval.sum Finset.univ (fun j =>
    RatInterval.mul (RatInterval.point ((a % cols j : ℕ)/(cols j : ℚ))) (c j))

def periodicEnergyInterval {L n : ℕ} (W : Fin L → RatInterval)
    (cols : Fin n → ℕ) (c : Fin n → RatInterval) (Z : RatInterval) : RatInterval :=
  RatInterval.div (RatInterval.sum Finset.univ (fun r =>
    RatInterval.mul (W r) (RatInterval.mul
      (valueInterval cols c (r.val+1)) (valueInterval cols c (r.val+1))))) Z

def realCollocationMatrix {L n : ℕ} (W : Fin L → ℝ)
    (rows cols : Fin n → ℕ) (i j : Fin n) : ℝ :=
  ∑ r : Fin L, if Nat.gcd (r.val+1) L = rows i then
    W r * (((r.val+1) % cols j : ℕ)/(cols j : ℚ) : ℚ) else 0

def realCollocationRhs {L n : ℕ} (W : Fin L → ℝ)
    (rows : Fin n → ℕ) (i : Fin n) : ℝ :=
  ∑ r : Fin L, if Nat.gcd (r.val+1) L = rows i then W r else 0

def realValue {n : ℕ} (cols : Fin n → ℕ) (c : Fin n → ℝ) (a : ℕ) : ℝ :=
  ∑ j, (((a % cols j : ℕ)/(cols j : ℚ) : ℚ) : ℝ) * c j

theorem collocationMatrix_contains {L n : ℕ} (WI : Fin L → RatInterval)
    (W : Fin L → ℝ) (rows cols : Fin n → ℕ)
    (hW : ∀ r, (WI r).Contains (W r)) (i j : Fin n) :
    (collocationMatrix WI rows cols i j).Contains (realCollocationMatrix W rows cols i j) := by
  apply contains_sum
  intro r hr
  by_cases h : Nat.gcd (r.val+1) L = rows i
  · simp only [h, if_true]
    exact contains_mul (hW r) (contains_point _)
  · simp only [h, if_false]
    simpa only [Rat.cast_zero] using contains_point 0

theorem collocationRhs_contains {L n : ℕ} (WI : Fin L → RatInterval)
    (W : Fin L → ℝ) (rows : Fin n → ℕ)
    (hW : ∀ r, (WI r).Contains (W r)) (i : Fin n) :
    (collocationRhs WI rows i).Contains (realCollocationRhs W rows i) := by
  apply contains_sum
  intro r hr
  by_cases h : Nat.gcd (r.val+1) L = rows i
  · simp only [h, if_true]
    exact hW r
  · simp only [h, if_false]
    simpa only [Rat.cast_zero] using contains_point 0

theorem valueInterval_contains {n : ℕ} (cols : Fin n → ℕ)
    (cI : Fin n → RatInterval) (c : Fin n → ℝ)
    (hc : ∀ j, (cI j).Contains (c j)) (a : ℕ) :
    (valueInterval cols cI a).Contains (realValue cols c a) := by
  exact contains_sum _ _ _ (fun j _ => contains_mul (contains_point _) (hc j))

theorem periodicEnergyInterval_contains {L n : ℕ}
    (WI : Fin L → RatInterval) (cols : Fin n → ℕ) (cI : Fin n → RatInterval)
    (ZI : RatInterval) (W : Fin L → ℝ) (c : Fin n → ℝ) (Z : ℝ)
    (hW : ∀ r, (WI r).Contains (W r)) (hc : ∀ j, (cI j).Contains (c j))
    (hZ : ZI.Contains Z) (hZpos : 0 < ZI.lo) :
    (periodicEnergyInterval WI cols cI ZI).Contains
      ((∑ r : Fin L, W r * (realValue cols c (r.val+1))^2)/Z) := by
  apply contains_div_pos _ hZ hZpos
  apply contains_sum
  intro r hr
  apply contains_mul (hW r)
  simpa only [pow_two] using contains_mul
    (valueInterval_contains cols cI c hc (r.val+1))
    (valueInterval_contains cols cI c hc (r.val+1))

def zetaInterval : RatInterval :=
  ⟨164493406684822643647/10^20, 164493406684822643648/10^20⟩

theorem zetaInterval_contains : zetaInterval.Contains zetaTwo := by
  have h := zetaTwoInterval_contains 32 (by norm_num)
  apply contains_weaken h <;> decide +kernel

theorem zetaInterval_pos : 0 < zetaInterval.lo := by decide +kernel

def weights2 : Fin 2 → RatInterval :=
  ![⟨(24674011002723396547/20000000000000000000), (7710628438351061421/6250000000000000000)⟩, ⟨(41123351671205660911/100000000000000000000), (2570209479450353807/6250000000000000000)⟩]

theorem weights2_refines : ∀ r : Fin 2,
    (weights2 r).lo ≤ (rawResidueSquareInterval 2 (r.val+1) 32).lo ∧
      (rawResidueSquareInterval 2 (r.val+1) 32).hi ≤ (weights2 r).hi := by
  decide +kernel

theorem weights2_contains (r : Fin 2) :
    (weights2 r).Contains (rawResidueSquareWeight 2 (r.val+1)) := by
  have h := rawResidueSquareInterval_contains 2 (r.val+1) 32
    (by norm_num) (by positivity) (by norm_num)
  simp only [Rat.cast_add, Rat.cast_natCast, Rat.cast_one, Rat.cast_ofNat] at h
  exact contains_weaken h (weights2_refines r).1 (weights2_refines r).2

def rows2 : Fin 1 → ℕ := ![1]
def cols2 : Fin 1 → ℕ := ![2]
def matrix2 := collocationMatrix weights2 rows2 cols2
def rhs2 := collocationRhs weights2 rows2
def inverse2 : Fin 1 → Fin 1 → ℚ :=
  ![![(16211389382774043431/10000000000000000000)]]
def center2 : Fin 1 → ℚ := ![2]

def solution2 : Fin 1 → RatInterval :=
  linearSolution center2 (1/10^15) (1/10^15)

def energy2 : RatInterval :=
  periodicEnergyInterval weights2 cols2 solution2 zetaInterval

def actualWeights2 (r : Fin 2) : ℝ := rawResidueSquareWeight 2 (r.val+1)

def actualMatrix2 := realCollocationMatrix actualWeights2 rows2 cols2
def actualRhs2 := realCollocationRhs actualWeights2 rows2
def actualEnergy2 (c : Fin 1 → ℝ) : ℝ :=
  (∑ r : Fin 2, actualWeights2 r * (realValue cols2 c (r.val+1))^2)/zetaTwo

theorem defect2_checked : ∀ i : Fin 1,
    (∑ j, absBound (linearDefect matrix2 inverse2 i j)) ≤ (1/10^15 : ℚ) := by
  decide +kernel

theorem residual2_checked : ∀ i : Fin 1,
    absBound (linearResidual matrix2 rhs2 inverse2 center2 i) ≤ (1/10^15 : ℚ) := by
  decide +kernel

theorem solution2_contains (x : Fin 1 → ℝ)
    (hsol : ∀ i, (∑ j, actualMatrix2 i j * x j) = actualRhs2 i) :
    ∀ i, (solution2 i).Contains (x i) := by
  apply linearSolution_contains matrix2 rhs2 actualMatrix2 actualRhs2 x
    inverse2 center2 (1/10^15) (1/10^15)
  · exact collocationMatrix_contains weights2 actualWeights2 rows2 cols2
      weights2_contains
  · exact collocationRhs_contains weights2 actualWeights2 rows2 weights2_contains
  · decide +kernel
  · exact defect2_checked
  · exact residual2_checked
  · exact hsol

theorem energy2_contains (x : Fin 1 → ℝ)
    (hsol : ∀ i, (∑ j, actualMatrix2 i j * x j) = actualRhs2 i) :
    energy2.Contains (actualEnergy2 x) := by
  exact periodicEnergyInterval_contains weights2 cols2 solution2 zetaInterval
    actualWeights2 x zetaTwo weights2_contains (solution2_contains x hsol)
    zetaInterval_contains zetaInterval_pos

theorem energy2_checked :
    ((749999999999/1000000000000) : ℚ) < energy2.lo ∧ energy2.hi < ((750000000001/1000000000000) : ℚ) := by
  decide +kernel

theorem actualEnergy2_bounds (x : Fin 1 → ℝ)
    (hsol : ∀ i, (∑ j, actualMatrix2 i j * x j) = actualRhs2 i) :
    ((749999999999/1000000000000) : ℝ) < actualEnergy2 x ∧
      actualEnergy2 x < ((750000000001/1000000000000) : ℝ) := by
  have h := energy2_contains x hsol
  have hlo : ((749999999999/1000000000000) : ℝ) < (energy2.lo : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat] using
      (Rat.cast_lt (K := ℝ)).mpr energy2_checked.1
  have hhi : (energy2.hi : ℝ) < ((750000000001/1000000000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat] using
      (Rat.cast_lt (K := ℝ)).mpr energy2_checked.2
  exact ⟨hlo.trans_le h.1, h.2.trans_lt hhi⟩

def weights6 : Fin 6 → RatInterval :=
  ![⟨(25915634091909485359/25000000000000000000), (103662536367637941437/100000000000000000000)⟩, ⟨(28043325348408594671/100000000000000000000), (1752707834275537167/6250000000000000000)⟩, ⟨(1370778389040188697/10000000000000000000), (13707783890401886971/100000000000000000000)⟩, ⟨(8510765025996437249/100000000000000000000), (34043060103985749/400000000000000000)⟩, ⟨(749966844447144291/12500000000000000000), (5999734755577154329/100000000000000000000)⟩, ⟨(456926129680062899/10000000000000000000), (4569261296800628991/100000000000000000000)⟩]

theorem weights6_refines : ∀ r : Fin 6,
    (weights6 r).lo ≤ (rawResidueSquareInterval 6 (r.val+1) 32).lo ∧
      (rawResidueSquareInterval 6 (r.val+1) 32).hi ≤ (weights6 r).hi := by
  decide +kernel

theorem weights6_contains (r : Fin 6) :
    (weights6 r).Contains (rawResidueSquareWeight 6 (r.val+1)) := by
  have h := rawResidueSquareInterval_contains 6 (r.val+1) 32
    (by norm_num) (by positivity) (by norm_num)
  simp only [Rat.cast_add, Rat.cast_natCast, Rat.cast_one, Rat.cast_ofNat] at h
  exact contains_weaken h (weights6_refines r).1 (weights6_refines r).2

def rows6 : Fin 3 → ℕ := ![1, 2, 3]
def cols6 : Fin 3 → ℕ := ![2, 3, 6]
def matrix6 := collocationMatrix weights6 rows6 cols6
def rhs6 := collocationRhs weights6 rows6
def inverse6 : Fin 3 → Fin 3 → ℚ :=
  ![![(84103507684316265919/50000000000000000000), (-75293882049022776227/25000000000000000000), (113368921500603654089/100000000000000000000)], ![(916762780399850853/781250000000000000), (15894181086703632079/6250000000000000000), (-23469127178236181837/2500000000000000000)], ![(-84103507684316265919/50000000000000000000), (75293882049022776227/25000000000000000000), (672828061474530127357/50000000000000000000)]]
def center6 : Fin 3 → ℚ := ![(89908025237609148549/100000000000000000000), (18591914619856759919/20000000000000000000), (110091974762390851451/100000000000000000000)]

def solution6 : Fin 3 → RatInterval :=
  linearSolution center6 (1/10^15) (1/10^15)

def energy6 : RatInterval :=
  periodicEnergyInterval weights6 cols6 solution6 zetaInterval

def actualWeights6 (r : Fin 6) : ℝ := rawResidueSquareWeight 6 (r.val+1)

def actualMatrix6 := realCollocationMatrix actualWeights6 rows6 cols6
def actualRhs6 := realCollocationRhs actualWeights6 rows6
def actualEnergy6 (c : Fin 3 → ℝ) : ℝ :=
  (∑ r : Fin 6, actualWeights6 r * (realValue cols6 c (r.val+1))^2)/zetaTwo

theorem defect6_checked : ∀ i : Fin 3,
    (∑ j, absBound (linearDefect matrix6 inverse6 i j)) ≤ (1/10^15 : ℚ) := by
  decide +kernel

theorem residual6_checked : ∀ i : Fin 3,
    absBound (linearResidual matrix6 rhs6 inverse6 center6 i) ≤ (1/10^15 : ℚ) := by
  decide +kernel

theorem solution6_contains (x : Fin 3 → ℝ)
    (hsol : ∀ i, (∑ j, actualMatrix6 i j * x j) = actualRhs6 i) :
    ∀ i, (solution6 i).Contains (x i) := by
  apply linearSolution_contains matrix6 rhs6 actualMatrix6 actualRhs6 x
    inverse6 center6 (1/10^15) (1/10^15)
  · exact collocationMatrix_contains weights6 actualWeights6 rows6 cols6
      weights6_contains
  · exact collocationRhs_contains weights6 actualWeights6 rows6 weights6_contains
  · decide +kernel
  · exact defect6_checked
  · exact residual6_checked
  · exact hsol

theorem energy6_contains (x : Fin 3 → ℝ)
    (hsol : ∀ i, (∑ j, actualMatrix6 i j * x j) = actualRhs6 i) :
    energy6.Contains (actualEnergy6 x) := by
  exact periodicEnergyInterval_contains weights6 cols6 solution6 zetaInterval
    actualWeights6 x zetaTwo weights6_contains (solution6_contains x hsol)
    zetaInterval_contains zetaInterval_pos

theorem energy6_checked :
    ((1009917/1000000) : ℚ) < energy6.lo ∧ energy6.hi < ((504959/500000) : ℚ) := by
  decide +kernel

theorem actualEnergy6_bounds (x : Fin 3 → ℝ)
    (hsol : ∀ i, (∑ j, actualMatrix6 i j * x j) = actualRhs6 i) :
    ((1009917/1000000) : ℝ) < actualEnergy6 x ∧
      actualEnergy6 x < ((504959/500000) : ℝ) := by
  have h := energy6_contains x hsol
  have hlo : ((1009917/1000000) : ℝ) < (energy6.lo : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat] using
      (Rat.cast_lt (K := ℝ)).mpr energy6_checked.1
  have hhi : (energy6.hi : ℝ) < ((504959/500000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat] using
      (Rat.cast_lt (K := ℝ)).mpr energy6_checked.2
  exact ⟨hlo.trans_le h.1, h.2.trans_lt hhi⟩

def weights12 : Fin 12 → RatInterval :=
  ![⟨(315679172088481807/312500000000000000), (101017335068314178241/100000000000000000000)⟩, ⟨(25915634091909485359/100000000000000000000), (323945426148868567/1250000000000000000)⟩, ⟨(11942589690629938013/100000000000000000000), (5971294845314969007/50000000000000000000)⟩, ⟨(7010831337102148667/100000000000000000000), (1752707834275537167/25000000000000000000)⟩, ⟨(2350388973791657461/50000000000000000000), (4700777947583314923/100000000000000000000)⟩, ⟨(1713472986300235871/50000000000000000000), (3426945972600471743/100000000000000000000)⟩, ⟨(661300324830940799/25000000000000000000), (2645201299323763197/100000000000000000000)⟩, ⟨(33245175882798583/1562500000000000000), (2127691256499109313/100000000000000000000)⟩, ⟨(1765194199771948957/100000000000000000000), (882597099885974479/50000000000000000000)⟩, ⟨(749966844447144291/50000000000000000000), (1499933688894288583/100000000000000000000)⟩, ⟨(259791361598767881/20000000000000000000), (649478403996919703/50000000000000000000)⟩, ⟨(1142315324200157247/100000000000000000000), (17848676940627457/1562500000000000000)⟩]

theorem weights12_refines : ∀ r : Fin 12,
    (weights12 r).lo ≤ (rawResidueSquareInterval 12 (r.val+1) 32).lo ∧
      (rawResidueSquareInterval 12 (r.val+1) 32).hi ≤ (weights12 r).hi := by
  decide +kernel

theorem weights12_contains (r : Fin 12) :
    (weights12 r).Contains (rawResidueSquareWeight 12 (r.val+1)) := by
  have h := rawResidueSquareInterval_contains 12 (r.val+1) 32
    (by norm_num) (by positivity) (by norm_num)
  simp only [Rat.cast_add, Rat.cast_natCast, Rat.cast_one, Rat.cast_ofNat] at h
  exact contains_weaken h (weights12_refines r).1 (weights12_refines r).2

def rows12 : Fin 5 → ℕ := ![1, 2, 3, 4, 6]
def cols12 : Fin 5 → ℕ := ![2, 3, 4, 6, 12]
def matrix12 := collocationMatrix weights12 rows12 cols12
def rhs12 := collocationRhs weights12 rows12
def inverse12 : Fin 5 → Fin 5 → ℚ :=
  ![![(183607456756974837443/100000000000000000000), (-48317166195448486769/12500000000000000000), (-2458652401533697689/25000000000000000000), (-1104020209086615421/2000000000000000000), (-279717668548144297/10000000000000000000)], ![(1297703859547549919/1250000000000000000), (82324364524148199513/25000000000000000000), (-415265235055215974067/50000000000000000000), (38217654773331809413/100000000000000000000), (140457397218185383357/100000000000000000000)], ![(-9650719743426654687/12500000000000000000), (106984313113955407637/25000000000000000000), (123529212715861179991/20000000000000000000), (-154140460970630283229/12500000000000000000), (349020808530102255199/100000000000000000000)], ![(-63142876300404358507/50000000000000000000), (2150428552261192403/3125000000000000000), (1010286020806469736083/100000000000000000000), (24268457775087834377/2500000000000000000), (-245369849362839248417/6250000000000000000)], ![(9650719743426654687/12500000000000000000), (-106984313113955407637/25000000000000000000), (-123529212715861179991/20000000000000000000), (154140460970630283229/12500000000000000000), (2743539684634276690113/50000000000000000000)]]
def center12 : Fin 5 → ℚ := ![(44444090934675430367/50000000000000000000), (98584695958328811649/100000000000000000000), (829644761716883299/5000000000000000000), (-26962264541317721683/100000000000000000000), (9170355238283116701/5000000000000000000)]

def solution12 : Fin 5 → RatInterval :=
  linearSolution center12 (1/10^15) (1/10^15)

def energy12 : RatInterval :=
  periodicEnergyInterval weights12 cols12 solution12 zetaInterval

def actualWeights12 (r : Fin 12) : ℝ := rawResidueSquareWeight 12 (r.val+1)

def actualMatrix12 := realCollocationMatrix actualWeights12 rows12 cols12
def actualRhs12 := realCollocationRhs actualWeights12 rows12
def actualEnergy12 (c : Fin 5 → ℝ) : ℝ :=
  (∑ r : Fin 12, actualWeights12 r * (realValue cols12 c (r.val+1))^2)/zetaTwo

theorem defect12_checked : ∀ i : Fin 5,
    (∑ j, absBound (linearDefect matrix12 inverse12 i j)) ≤ (1/10^15 : ℚ) := by
  decide +kernel

theorem residual12_checked : ∀ i : Fin 5,
    absBound (linearResidual matrix12 rhs12 inverse12 center12 i) ≤ (1/10^15 : ℚ) := by
  decide +kernel

theorem solution12_contains (x : Fin 5 → ℝ)
    (hsol : ∀ i, (∑ j, actualMatrix12 i j * x j) = actualRhs12 i) :
    ∀ i, (solution12 i).Contains (x i) := by
  apply linearSolution_contains matrix12 rhs12 actualMatrix12 actualRhs12 x
    inverse12 center12 (1/10^15) (1/10^15)
  · exact collocationMatrix_contains weights12 actualWeights12 rows12 cols12
      weights12_contains
  · exact collocationRhs_contains weights12 actualWeights12 rows12 weights12_contains
  · decide +kernel
  · exact defect12_checked
  · exact residual12_checked
  · exact hsol

theorem energy12_contains (x : Fin 5 → ℝ)
    (hsol : ∀ i, (∑ j, actualMatrix12 i j * x j) = actualRhs12 i) :
    energy12.Contains (actualEnergy12 x) := by
  exact periodicEnergyInterval_contains weights12 cols12 solution12 zetaInterval
    actualWeights12 x zetaTwo weights12_contains (solution12_contains x hsol)
    zetaInterval_contains zetaInterval_pos

theorem energy12_checked :
    ((133589/125000) : ℚ) < energy12.lo ∧ energy12.hi < ((1068713/1000000) : ℚ) := by
  decide +kernel

theorem actualEnergy12_bounds (x : Fin 5 → ℝ)
    (hsol : ∀ i, (∑ j, actualMatrix12 i j * x j) = actualRhs12 i) :
    ((133589/125000) : ℝ) < actualEnergy12 x ∧
      actualEnergy12 x < ((1068713/1000000) : ℝ) := by
  have h := energy12_contains x hsol
  have hlo : ((133589/125000) : ℝ) < (energy12.lo : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat] using
      (Rat.cast_lt (K := ℝ)).mpr energy12_checked.1
  have hhi : (energy12.hi : ℝ) < ((1068713/1000000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat] using
      (Rat.cast_lt (K := ℝ)).mpr energy12_checked.2
  exact ⟨hlo.trans_le h.1, h.2.trans_lt hhi⟩

def weights60 : Fin 60 → RatInterval :=
  ![⟨(12505575516048377283/12500000000000000000), (20008920825677403653/20000000000000000000)⟩, ⟨(6260890674342812301/25000000000000000000), (5008712539474249841/20000000000000000000)⟩, ⟨(11153676592836531091/100000000000000000000), (2788419148209132773/25000000000000000000)⟩, ⟨(6291609858962645031/100000000000000000000), (786451232370330629/12500000000000000000)⟩, ⟨(4040693402732567129/100000000000000000000), (404069340273256713/10000000000000000000)⟩, ⟨(2817591643077576633/100000000000000000000), (1408795821538788317/50000000000000000000)⟩, ⟨(2079785488360898151/100000000000000000000), (259973186045112269/12500000000000000000)⟩, ⟨(160065735627500887/10000000000000000000), (1600657356275008871/100000000000000000000)⟩, ⟨(317986137475559391/25000000000000000000), (254388909980447513/20000000000000000000)⟩, ⟨(518312681838189707/50000000000000000000), (207325072735275883/20000000000000000000)⟩, ⟨(172469644252241027/20000000000000000000), (53896763828825321/6250000000000000000)⟩, ⟨(729649366817327197/100000000000000000000), (364824683408663599/50000000000000000000)⟩, ⟨(626248926742938549/100000000000000000000), (12524978534858771/2000000000000000000)⟩, ⟨(544088835273006551/100000000000000000000), (68011104409125819/12500000000000000000)⟩, ⟨(5971294845314969/1250000000000000000), (477703587625197521/100000000000000000000)⟩, ⟨(16931200227619477/4000000000000000000), (211640002845243463/50000000000000000000)⟩, ⟨(378092058846021981/100000000000000000000), (189046029423010991/50000000000000000000)⟩, ⟨(340149015169659179/100000000000000000000), (17007450758482959/5000000000000000000)⟩, ⟨(76992405849498637/25000000000000000000), (307969623397994549/100000000000000000000)⟩, ⟨(140216626742042973/50000000000000000000), (280433253484085947/100000000000000000000)⟩, ⟨(64169854459762581/25000000000000000000), (10267176713562013/4000000000000000000)⟩, ⟨(236038502640979093/100000000000000000000), (118019251320489547/50000000000000000000)⟩, ⟨(13623943883529289/6250000000000000000), (1743864817091749/800000000000000000)⟩, ⟨(202093238625822151/100000000000000000000), (25261654828227769/12500000000000000000)⟩, ⟨(47007779475833149/25000000000000000000), (188031117903332597/100000000000000000000)⟩, ⟨(43880636305629807/25000000000000000000), (175522545222519229/100000000000000000000)⟩, ⟨(82171533243507473/50000000000000000000), (164343066487014947/100000000000000000000)⟩, ⟨(154307509760121037/100000000000000000000), (77153754880060519/50000000000000000000)⟩, ⟨(145262005931136183/100000000000000000000), (18157750741392023/12500000000000000000)⟩, ⟨(137077838904018869/100000000000000000000), (13707783890401887/10000000000000000000)⟩, ⟨(129646661097978553/100000000000000000000), (64823330548989277/50000000000000000000)⟩, ⟨(122876738479330919/100000000000000000000), (3071918461983273/2500000000000000000)⟩, ⟨(116689979473775443/100000000000000000000), (29172494868443861/25000000000000000000)⟩, ⟨(111019566137390451/100000000000000000000), (27754891534347613/25000000000000000000)⟩, ⟨(105808051972950527/100000000000000000000), (206656351509669/195312500000000000)⟩, ⟨(101005824191732157/100000000000000000000), (50502912095866079/50000000000000000000)⟩, ⟨(48284926365564027/50000000000000000000), (19313970546225611/20000000000000000000)⟩, ⟨(9246266648693883/10000000000000000000), (92462666486938831/100000000000000000000)⟩, ⟨(88651510776399153/100000000000000000000), (44325755388199577/50000000000000000000)⟩, ⟨(21276912564991093/25000000000000000000), (85107650259964373/100000000000000000000)⟩, ⟨(81805789302711237/100000000000000000000), (40902894651355619/50000000000000000000)⟩, ⟨(39361793842980703/50000000000000000000), (78723587685961407/100000000000000000000)⟩, ⟨(15168250829427673/20000000000000000000), (37920627073569183/50000000000000000000)⟩, ⟨(36570601883738799/50000000000000000000), (73141203767477599/100000000000000000000)⟩, ⟨(35303883995438979/50000000000000000000), (70607767990877959/100000000000000000000)⟩, ⟨(68226948226836753/100000000000000000000), (34113474113418377/50000000000000000000)⟩, ⟨(2639448228141593/4000000000000000000), (32993102851769913/50000000000000000000)⟩, ⟨(63874281597269451/100000000000000000000), (15968570399317363/25000000000000000000)⟩, ⟨(61881042549760773/100000000000000000000), (30940521274880387/50000000000000000000)⟩, ⟨(59997347555771543/100000000000000000000), (7499668444471443/12500000000000000000)⟩, ⟨(582149329047953/1000000000000000000), (58214932904795301/100000000000000000000)⟩, ⟨(56526312428931301/100000000000000000000), (28263156214465651/50000000000000000000)⟩, ⟨(5492469077087839/10000000000000000000), (54924690770878391/100000000000000000000)⟩, ⟨(53403887763255653/100000000000000000000), (26701943881627827/50000000000000000000)⟩, ⟨(6494784039969197/12500000000000000000), (51958272319753577/100000000000000000000)⟩, ⟨(6322838061650747/12500000000000000000), (50582704493205977/100000000000000000000)⟩, ⟨(24636242283003833/50000000000000000000), (49272484566007667/100000000000000000000)⟩, ⟨(12005827053175717/25000000000000000000), (48023308212702869/100000000000000000000)⟩, ⟨(46831226919675291/100000000000000000000), (11707806729918823/25000000000000000000)⟩, ⟨(45692612968006289/100000000000000000000), (4569261296800629/10000000000000000000)⟩]

theorem weights60_refines : ∀ r : Fin 60,
    (weights60 r).lo ≤ (rawResidueSquareInterval 60 (r.val+1) 32).lo ∧
      (rawResidueSquareInterval 60 (r.val+1) 32).hi ≤ (weights60 r).hi := by
  decide +kernel

theorem weights60_contains (r : Fin 60) :
    (weights60 r).Contains (rawResidueSquareWeight 60 (r.val+1)) := by
  have h := rawResidueSquareInterval_contains 60 (r.val+1) 32
    (by norm_num) (by positivity) (by norm_num)
  simp only [Rat.cast_add, Rat.cast_natCast, Rat.cast_one, Rat.cast_ofNat] at h
  exact contains_weaken h (weights60_refines r).1 (weights60_refines r).2

def rows60 : Fin 11 → ℕ := ![1, 2, 3, 4, 5, 6, 10, 12, 15, 20, 30]
def cols60 : Fin 11 → ℕ := ![2, 3, 4, 5, 6, 10, 12, 15, 20, 30, 60]
def matrix60 := collocationMatrix weights60 rows60 cols60
def rhs60 := collocationRhs weights60 rows60
def inverse60 : Fin 11 → Fin 11 → ℚ :=
  ![![(94792668097578123307/50000000000000000000), (-193123903615548558227/50000000000000000000), (1346499698639389401/20000000000000000000), (-10911780210176943163/100000000000000000000), (1505924611928416001/100000000000000000000), (-130365194940951244439/100000000000000000000), (-5903596981123219909/4000000000000000000), (26989156705939336227/25000000000000000000), (-98385798960555685011/100000000000000000000), (224407020089597031/125000000000000000), (59087325624790374149/100000000000000000000)], ![(5205410796378094501/5000000000000000000), (166010558705482424707/50000000000000000000), (-416361904147447863821/50000000000000000000), (109631619511652449263/100000000000000000000), (26069395916591610601/100000000000000000000), (50797628038200723269/25000000000000000000), (-89220438228045857851/50000000000000000000), (-97367062250315835263/50000000000000000000), (-2649515329338978821/1250000000000000000), (531833710859390027767/100000000000000000000), (141516912898439711697/50000000000000000000)], ![(-84026090515060974049/100000000000000000000), (429657303166919469743/100000000000000000000), (62544263300851784067/10000000000000000000), (-319817979415315747161/25000000000000000000), (10212792794831149769/20000000000000000000), (433411250617283164199/100000000000000000000), (2014302062170511067/10000000000000000000), (-91016328892397194837/100000000000000000000), (356937237447016425423/50000000000000000000), (-446472596724259213623/100000000000000000000), (309083211986267879411/100000000000000000000)], ![(15618035867738499611/20000000000000000000), (12789616038520580329/100000000000000000000), (207176787209213178479/100000000000000000000), (138209832109430420309/12500000000000000000), (-1219190430471153117877/50000000000000000000), (-2675341989809113591/400000000000000000), (-3119693244488523809/1562500000000000000), (11688044359221274611/12500000000000000000), (-5731380481395325323/1250000000000000000), (405631065539317915903/100000000000000000000), (113159550570772634099/100000000000000000000)], ![(-9561209107008309117/5000000000000000000), (54727392864977981479/100000000000000000000), (387236726342748460751/50000000000000000000), (57612717371528590879/100000000000000000000), (2043038025551309747507/100000000000000000000), (-677007795302709135009/20000000000000000000), (388697295723483986431/100000000000000000000), (-64363330509888877219/100000000000000000000), (1783375902049502914721/100000000000000000000), (-669055037597155270769/50000000000000000000), (-87158636681261912043/20000000000000000000)], ![(-53675576125578780307/50000000000000000000), (20030250230011253967/100000000000000000000), (37911644668566458331/100000000000000000000), (-3640419566708743711/4000000000000000000), (1331499795206362617799/50000000000000000000), (3078145927152349469981/100000000000000000000), (-4723509509392201252569/50000000000000000000), (-68935424422664752583/25000000000000000000), (-400613740781286311013/25000000000000000000), (-580266214134402779591/100000000000000000000), (168765557482970503579/100000000000000000000)], ![(151308068335319059989/100000000000000000000), (-217589439481920093111/50000000000000000000), (-455414932801939917049/100000000000000000000), (1196356083645369928207/100000000000000000000), (-416228404942230956531/20000000000000000000), (2947403189334892063461/100000000000000000000), (78367748234444871031/1250000000000000000), (-9915935040074450529861/100000000000000000000), (-36801363386136581223/2500000000000000000), (332616685059463767691/5000000000000000000), (4096953600461070542909/100000000000000000000)], ![(-32953062701569751257/50000000000000000000), (-12797733049427275831/50000000000000000000), (285391636736643981971/50000000000000000000), (-1225027687439991743469/100000000000000000000), (2483367253673751301747/100000000000000000000), (361252269132680760253/100000000000000000000), (635427797785994391423/25000000000000000000), (4498910707661924302309/50000000000000000000), (-2091176051534613705601/10000000000000000000), (-4217458477679969647611/100000000000000000000), (2348319601489203429/25000000000000000000)], ![(13920978321050941207/10000000000000000000), (-30030649322636465781/50000000000000000000), (-30410599701759878351/2500000000000000000), (267957741505982863331/25000000000000000000), (-1546131886615209969037/100000000000000000000), (-834643882247281401947/100000000000000000000), (1123071343976769160753/12500000000000000000), (2362634108350253870923/100000000000000000000), (3708738107548338961097/25000000000000000000), (-3940064479731011504991/12500000000000000000), (7661422486105685226351/100000000000000000000)], ![(4251166179265017911/6250000000000000000), (37082226286173376839/100000000000000000000), (-95085318826817496777/25000000000000000000), (49581215875828295311/25000000000000000000), (-56211324402367265687/1562500000000000000), (36757745722059121721/5000000000000000000), (504065636159006437303/20000000000000000000), (-145442272714786680019/10000000000000000000), (12424403099342192343861/50000000000000000000), (12736430483176233963479/50000000000000000000), (-974493655073455656727/1000000000000000000)], ![(-20649176103076749801/10000000000000000000), (65582874442193648041/100000000000000000000), (1046396287863817210419/100000000000000000000), (-988915132008038392887/100000000000000000000), (3576209947352209002847/100000000000000000000), (-2546170557704893825713/100000000000000000000), (-15274133631191448079173/100000000000000000000), (305772690424663754151/4000000000000000000), (-14076772369641925446313/100000000000000000000), (25314654733383075899731/100000000000000000000), (133835045146413367449813/100000000000000000000)]]
def center60 : Fin 11 → ℚ := ![(46700063870695013593/50000000000000000000), (101926841918559051047/100000000000000000000), (6562034478791189791/50000000000000000000), (39418502711229375027/50000000000000000000), (-93837288606435896669/100000000000000000000), (-2489353347254570123/25000000000000000000), (19332947723312701927/25000000000000000000), (8818287508066663569/100000000000000000000), (70483110586483254511/100000000000000000000), (11282742599797763927/50000000000000000000), (39061029562683558199/100000000000000000000)]

def solution60 : Fin 11 → RatInterval :=
  linearSolution center60 (1/10^15) (1/10^15)

def energy60 : RatInterval :=
  periodicEnergyInterval weights60 cols60 solution60 zetaInterval

def actualWeights60 (r : Fin 60) : ℝ := rawResidueSquareWeight 60 (r.val+1)

def actualMatrix60 := realCollocationMatrix actualWeights60 rows60 cols60
def actualRhs60 := realCollocationRhs actualWeights60 rows60
def actualEnergy60 (c : Fin 11 → ℝ) : ℝ :=
  (∑ r : Fin 60, actualWeights60 r * (realValue cols60 c (r.val+1))^2)/zetaTwo

theorem defect60_checked : ∀ i : Fin 11,
    (∑ j, absBound (linearDefect matrix60 inverse60 i j)) ≤ (1/10^15 : ℚ) := by
  decide +kernel

theorem residual60_checked : ∀ i : Fin 11,
    absBound (linearResidual matrix60 rhs60 inverse60 center60 i) ≤ (1/10^15 : ℚ) := by
  decide +kernel

theorem solution60_contains (x : Fin 11 → ℝ)
    (hsol : ∀ i, (∑ j, actualMatrix60 i j * x j) = actualRhs60 i) :
    ∀ i, (solution60 i).Contains (x i) := by
  apply linearSolution_contains matrix60 rhs60 actualMatrix60 actualRhs60 x
    inverse60 center60 (1/10^15) (1/10^15)
  · exact collocationMatrix_contains weights60 actualWeights60 rows60 cols60
      weights60_contains
  · exact collocationRhs_contains weights60 actualWeights60 rows60 weights60_contains
  · decide +kernel
  · exact defect60_checked
  · exact residual60_checked
  · exact hsol

theorem energy60_contains (x : Fin 11 → ℝ)
    (hsol : ∀ i, (∑ j, actualMatrix60 i j * x j) = actualRhs60 i) :
    energy60.Contains (actualEnergy60 x) := by
  exact periodicEnergyInterval_contains weights60 cols60 solution60 zetaInterval
    actualWeights60 x zetaTwo weights60_contains (solution60_contains x hsol)
    zetaInterval_contains zetaInterval_pos

theorem energy60_checked :
    ((1053173/1000000) : ℚ) < energy60.lo ∧ energy60.hi < ((42127/40000) : ℚ) := by
  decide +kernel

theorem actualEnergy60_bounds (x : Fin 11 → ℝ)
    (hsol : ∀ i, (∑ j, actualMatrix60 i j * x j) = actualRhs60 i) :
    ((1053173/1000000) : ℝ) < actualEnergy60 x ∧
      actualEnergy60 x < ((42127/40000) : ℝ) := by
  have h := energy60_contains x hsol
  have hlo : ((1053173/1000000) : ℝ) < (energy60.lo : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat] using
      (Rat.cast_lt (K := ℝ)).mpr energy60_checked.1
  have hhi : (energy60.hi : ℝ) < ((42127/40000) : ℝ) := by
    simpa only [Rat.cast_div, Rat.cast_ofNat] using
      (Rat.cast_lt (K := ℝ)).mpr energy60_checked.2
  exact ⟨hlo.trans_le h.1, h.2.trans_lt hhi⟩

end RiemannResearch.RH.CanonicalReviewCertificates
