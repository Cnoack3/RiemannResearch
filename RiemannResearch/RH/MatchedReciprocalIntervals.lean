/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.LinearAlgebra.RationalQuadraticCertificate
import Mathlib.Tactic.Ring

/-! Signed finite interval evaluation for the reciprocal-head review tables. -/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.MatchedReciprocalIntervals
open RiemannResearch RatInterval
variable {ι κ : Type*} [Fintype ι] [Fintype κ]

def vectorSub (x y : ι → RatInterval) (i : ι) : RatInterval := sub (x i) (y i)
def realVectorSub (x y : ι → ℝ) (i : ι) : ℝ := x i-y i

theorem vectorSub_contains (xI yI : ι → RatInterval) (x y : ι → ℝ)
    (hx : ∀ i, (xI i).Contains (x i)) (hy : ∀ i, (yI i).Contains (y i)) (i : ι) :
    (vectorSub xI yI i).Contains (realVectorSub x y i) := contains_sub (hx i) (hy i)

def matvec (A : ι → κ → RatInterval) (x : κ → RatInterval) (i : ι) : RatInterval :=
  linearForm (A i) x
def realMatvec (A : ι → κ → ℝ) (x : κ → ℝ) (i : ι) : ℝ := ∑ j, A i j*x j

theorem matvec_contains (AI : ι → κ → RatInterval) (xI : κ → RatInterval)
    (A : ι → κ → ℝ) (x : κ → ℝ) (hA : ∀ i j, (AI i j).Contains (A i j))
    (hx : ∀ j, (xI j).Contains (x j)) (i : ι) :
    (matvec AI xI i).Contains (realMatvec A x i) := linearForm_contains _ _ _ _ (hA i) hx

def crossVector (G P : ι → ι → RatInterval) (d : ι → RatInterval) (i : ι) : RatInterval :=
  linearForm (fun j => sub (G i j) (P i j)) d
def realCrossVector (G P : ι → ι → ℝ) (d : ι → ℝ) (i : ι) : ℝ :=
  ∑ j, (G i j-P i j)*d j

theorem crossVector_contains (GI PI : ι → ι → RatInterval) (dI : ι → RatInterval)
    (G P : ι → ι → ℝ) (d : ι → ℝ)
    (hG : ∀ i j, (GI i j).Contains (G i j))
    (hP : ∀ i j, (PI i j).Contains (P i j))
    (hd : ∀ i, (dI i).Contains (d i)) (i : ι) :
    (crossVector GI PI dI i).Contains (realCrossVector G P d i) :=
  linearForm_contains _ _ _ _ (fun j => contains_sub (hG i j) (hP i j)) hd

/-- A weighted physical head sum; the caller retains the exact weight and all
signs. It is used both for the finite head energy and the signed residual head. -/
def headPair (w : κ → ℚ) (x y : κ → RatInterval) : RatInterval :=
  RatInterval.sum Finset.univ (fun i => mul (point (w i)) (mul (x i) (y i)))
def realHeadPair (w : κ → ℚ) (x y : κ → ℝ) : ℝ :=
  ∑ i, (w i : ℝ)*(x i*y i)

theorem headPair_contains (w : κ → ℚ) (xI yI : κ → RatInterval) (x y : κ → ℝ)
    (hx : ∀ i, (xI i).Contains (x i)) (hy : ∀ i, (yI i).Contains (y i)) :
    (headPair w xI yI).Contains (realHeadPair w x y) :=
  contains_sum _ _ _ (fun i _ => contains_mul (contains_point _) (contains_mul (hx i) (hy i)))

inductive Metric
  | dQ2 | paretoEnergy | repairEnergy | finiteTailEnergy | product2 | signedHead
  | exactHeadLower | completionSurplus | projectionError2 | interpolationCost
  | minimumError | minimumNormError
  deriving DecidableEq

instance : Fintype Metric where
  elems := {.dQ2, .paretoEnergy, .repairEnergy, .finiteTailEnergy, .product2,
    .signedHead, .exactHeadLower, .completionSurplus, .projectionError2,
    .interpolationCost, .minimumError, .minimumNormError}
  complete := by intro m; cases m <;> simp

/-- The scalar table is evaluated only after all complete Gram entries,
normal-equation solutions, repair coefficients and physical head values have
already been enclosed. This evaluator never discards a signed cross term. -/
def metrics (G P J : ι → ι → RatInterval) (q : ι → RatInterval) (Z : RatInterval)
    (d cq projection repair interpolationCorrection : ι → RatInterval)
    (rhead bhead : κ → RatInterval) (w : κ → ℚ) : Metric → RatInterval :=
  let cross := crossVector G P d
  let dQ := div (quadratic G d) Z
  let pEnergy := quadratic P d
  let repairEnergy := div (quadratic G repair) Z
  let tail := div (sub (sub Z (linearForm q cq)) (headPair w rhead rhead)) Z
  let signed := div (headPair w rhead bhead) Z
  let lower := add (div (headPair w bhead bhead) Z) (div (mul signed signed) tail)
  let projError := div (sub (quadratic J d) (linearForm cross projection)) Z
  let interpolation := div (quadratic G interpolationCorrection) Z
  let minNormError := div (squaredError (quadratic J d) cross G repair) Z
  fun m => match m with
    | .dQ2 => dQ
    | .paretoEnergy => pEnergy
    | .repairEnergy => repairEnergy
    | .finiteTailEnergy => tail
    | .product2 => mul repairEnergy tail
    | .signedHead => signed
    | .exactHeadLower => lower
    | .completionSurplus => sub repairEnergy lower
    | .projectionError2 => projError
    | .interpolationCost => interpolation
    | .minimumError => add projError interpolation
    | .minimumNormError => minNormError

def realMetrics (G P J : ι → ι → ℝ) (q : ι → ℝ) (Z : ℝ)
    (d cq projection repair interpolationCorrection : ι → ℝ)
    (rhead bhead : κ → ℝ) (w : κ → ℚ) : Metric → ℝ :=
  let quad := fun (A : ι → ι → ℝ) (x : ι → ℝ) => ∑ i, ∑ j, x i*A i j*x j
  let lin := fun (b x : ι → ℝ) => ∑ i, b i*x i
  let cross := realCrossVector G P d
  let dQ := quad G d/Z
  let pEnergy := quad P d
  let repairEnergy := quad G repair/Z
  let tail := (Z-lin q cq-realHeadPair w rhead rhead)/Z
  let signed := realHeadPair w rhead bhead/Z
  let lower := realHeadPair w bhead bhead/Z+signed*signed/tail
  let projError := (quad J d-lin cross projection)/Z
  let interpolation := quad G interpolationCorrection/Z
  let minNormError := (quad J d-2*lin cross repair+quad G repair)/Z
  fun m => match m with
    | .dQ2 => dQ
    | .paretoEnergy => pEnergy
    | .repairEnergy => repairEnergy
    | .finiteTailEnergy => tail
    | .product2 => repairEnergy*tail
    | .signedHead => signed
    | .exactHeadLower => lower
    | .completionSurplus => repairEnergy-lower
    | .projectionError2 => projError
    | .interpolationCost => interpolation
    | .minimumError => projError+interpolation
    | .minimumNormError => minNormError

theorem metrics_contains
    (GI PI JI : ι → ι → RatInterval) (qI : ι → RatInterval) (ZI : RatInterval)
    (dI cqI projectionI repairI correctionI : ι → RatInterval) (rhI bhI : κ → RatInterval)
    (w : κ → ℚ) (G P J : ι → ι → ℝ) (q : ι → ℝ) (Z : ℝ)
    (d cq projection repair correction : ι → ℝ) (rh bh : κ → ℝ)
    (hG : ∀ i j, (GI i j).Contains (G i j)) (hP : ∀ i j, (PI i j).Contains (P i j))
    (hJ : ∀ i j, (JI i j).Contains (J i j)) (hq : ∀ i, (qI i).Contains (q i))
    (hZ : ZI.Contains Z) (hZpos : 0 < ZI.lo)
    (hd : ∀ i, (dI i).Contains (d i)) (hcq : ∀ i, (cqI i).Contains (cq i))
    (hproj : ∀ i, (projectionI i).Contains (projection i))
    (hrepair : ∀ i, (repairI i).Contains (repair i))
    (hcorrection : ∀ i, (correctionI i).Contains (correction i))
    (hrh : ∀ i, (rhI i).Contains (rh i)) (hbh : ∀ i, (bhI i).Contains (bh i))
    (htail : 0 < (div (sub (sub ZI (linearForm qI cqI))
      (headPair w rhI rhI)) ZI).lo) (m : Metric) :
    (metrics GI PI JI qI ZI dI cqI projectionI repairI correctionI rhI bhI w m).Contains
      (realMetrics G P J q Z d cq projection repair correction rh bh w m) := by
  have hc := crossVector_contains GI PI dI G P d hG hP hd
  have hqd := quadratic_contains GI dI G d hG hd
  have hpd := quadratic_contains PI dI P d hP hd
  have hjd := quadratic_contains JI dI J d hJ hd
  have hqr := quadratic_contains GI repairI G repair hG hrepair
  have hfit := linearForm_contains qI cqI q cq hq hcq
  have htailI := contains_div_pos
    (contains_sub (contains_sub hZ hfit) (headPair_contains w rhI rhI rh rh hrh hrh)) hZ hZpos
  have hsign := contains_div_pos (headPair_contains w rhI bhI rh bh hrh hbh) hZ hZpos
  have hlower := contains_add
    (contains_div_pos (headPair_contains w bhI bhI bh bh hbh hbh) hZ hZpos)
    (contains_div_pos (contains_mul hsign hsign) htailI htail)
  have hrepairEnergy := contains_div_pos hqr hZ hZpos
  have hprojError := contains_div_pos
    (contains_sub hjd (linearForm_contains _ _ _ _ hc hproj)) hZ hZpos
  have hinterp := contains_div_pos
    (quadratic_contains _ _ _ _ hG hcorrection)
    hZ hZpos
  have hnormError := contains_div_pos
    (squaredError_contains _ _ _ _ _ _ _ _ hjd hc hG hrepair) hZ hZpos
  cases m
  · exact contains_div_pos hqd hZ hZpos
  · exact hpd
  · exact hrepairEnergy
  · exact htailI
  · exact contains_mul hrepairEnergy htailI
  · exact hsign
  · exact hlower
  · exact contains_sub hrepairEnergy hlower
  · exact hprojError
  · exact hinterp
  · exact contains_add hprojError hinterp
  · exact hnormError

end RiemannResearch.RH.MatchedReciprocalIntervals
