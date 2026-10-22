import RiemannResearch.RH.ArithmeticFiniteFourthLevelCertificate

/-!
# Exact fifth-level five-mode primitive enclosures

Rigorous outward rational bounds on the 1/256 grid at C*=5373/2000.
Only the sixteen odd grid points require new exponential estimates; the
sixteen even points reuse the published fourth-level certificate.
Source: user-provided FifthLevel_Paper_Recon_v47.md supplies the rational
candidate endpoints. Every inequality in this module is proved, not assumed.
No arithmetic positivity or RH conclusion is asserted.
-/
open scoped BigOperators
namespace RiemannResearch.RH
noncomputable section

theorem fifthLevelPrimitive_sixteenth_1_bounds :
    (-2029566407/1000000000000000000 : ℝ) ≤ fourthLevelPrimitive (5373/2000) (1/256) ∧
    fourthLevelPrimitive (5373/2000) (1/256) ≤ (-2029566406/1000000000000000000 : ℝ) := by
  have h0 := Real.exp_bound (x := (1/512 : ℝ)) (by norm_num) (n := 18) (by norm_num)
  have h1 := Real.exp_bound (x := (-5/1024 : ℝ)) (by norm_num) (n := 18) (by norm_num)
  have h2 := Real.exp_bound (x := (-9/1024 : ℝ)) (by norm_num) (n := 18) (by norm_num)
  have h3 := Real.exp_bound (x := (-13/1024 : ℝ)) (by norm_num) (n := 18) (by norm_num)
  have h4 := Real.exp_bound (x := (-17/1024 : ℝ)) (by norm_num) (n := 18) (by norm_num)
  norm_num [Finset.sum_range_succ] at h0 h1 h2 h3 h4
  have s1 := exp_double_bounds_of_abs h1 (by norm_num)
  norm_num at s1
  have s2 := exp_double_bounds_of_abs h2 (by norm_num)
  norm_num at s2
  have s3 := exp_double_bounds_of_abs h3 (by norm_num)
  norm_num at s3
  have s4 := exp_double_bounds_of_abs h4 (by norm_num)
  norm_num at s4
  norm_num [fourthLevelPrimitive]
  constructor <;> linarith [(abs_le.mp h0).1, (abs_le.mp h0).2,
    s1.1, s1.2, s2.1, s2.2, s3.1, s3.2, s4.1, s4.2]

theorem fifthLevelPrimitive_sixteenth_3_bounds :
    (-53263038971/1000000000000000000 : ℝ) ≤ fourthLevelPrimitive (5373/2000) (3/256) ∧
    fourthLevelPrimitive (5373/2000) (3/256) ≤ (-53263038970/1000000000000000000 : ℝ) := by
  have h0 := Real.exp_bound (x := (3/512 : ℝ)) (by norm_num) (n := 18) (by norm_num)
  have h1 := Real.exp_bound (x := (-15/1024 : ℝ)) (by norm_num) (n := 18) (by norm_num)
  have h2 := Real.exp_bound (x := (-27/1024 : ℝ)) (by norm_num) (n := 18) (by norm_num)
  have h3 := Real.exp_bound (x := (-39/1024 : ℝ)) (by norm_num) (n := 18) (by norm_num)
  have h4 := Real.exp_bound (x := (-51/1024 : ℝ)) (by norm_num) (n := 18) (by norm_num)
  norm_num [Finset.sum_range_succ] at h0 h1 h2 h3 h4
  have s1 := exp_double_bounds_of_abs h1 (by norm_num)
  norm_num at s1
  have s2 := exp_double_bounds_of_abs h2 (by norm_num)
  norm_num at s2
  have s3 := exp_double_bounds_of_abs h3 (by norm_num)
  norm_num at s3
  have s4 := exp_double_bounds_of_abs h4 (by norm_num)
  norm_num at s4
  norm_num [fourthLevelPrimitive]
  constructor <;> linarith [(abs_le.mp h0).1, (abs_le.mp h0).2,
    s1.1, s1.2, s2.1, s2.2, s3.1, s3.2, s4.1, s4.2]

theorem fifthLevelPrimitive_sixteenth_5_bounds :
    (-239644921451/1000000000000000000 : ℝ) ≤ fourthLevelPrimitive (5373/2000) (5/256) ∧
    fourthLevelPrimitive (5373/2000) (5/256) ≤ (-239644921450/1000000000000000000 : ℝ) := by
  have h0 := Real.exp_bound (x := (5/512 : ℝ)) (by norm_num) (n := 18) (by norm_num)
  have h1 := Real.exp_bound (x := (-25/1024 : ℝ)) (by norm_num) (n := 18) (by norm_num)
  have h2 := Real.exp_bound (x := (-45/1024 : ℝ)) (by norm_num) (n := 18) (by norm_num)
  have h3 := Real.exp_bound (x := (-65/1024 : ℝ)) (by norm_num) (n := 18) (by norm_num)
  have h4 := Real.exp_bound (x := (-85/1024 : ℝ)) (by norm_num) (n := 18) (by norm_num)
  norm_num [Finset.sum_range_succ] at h0 h1 h2 h3 h4
  have s1 := exp_double_bounds_of_abs h1 (by norm_num)
  norm_num at s1
  have s2 := exp_double_bounds_of_abs h2 (by norm_num)
  norm_num at s2
  have s3 := exp_double_bounds_of_abs h3 (by norm_num)
  norm_num at s3
  have s4 := exp_double_bounds_of_abs h4 (by norm_num)
  norm_num at s4
  norm_num [fourthLevelPrimitive]
  constructor <;> linarith [(abs_le.mp h0).1, (abs_le.mp h0).2,
    s1.1, s1.2, s2.1, s2.2, s3.1, s3.2, s4.1, s4.2]

theorem fifthLevelPrimitive_sixteenth_7_bounds :
    (-638973934981/1000000000000000000 : ℝ) ≤ fourthLevelPrimitive (5373/2000) (7/256) ∧
    fourthLevelPrimitive (5373/2000) (7/256) ≤ (-638973934980/1000000000000000000 : ℝ) := by
  have h0 := Real.exp_bound (x := (7/512 : ℝ)) (by norm_num) (n := 18) (by norm_num)
  have h1 := Real.exp_bound (x := (-35/1024 : ℝ)) (by norm_num) (n := 18) (by norm_num)
  have h2 := Real.exp_bound (x := (-63/1024 : ℝ)) (by norm_num) (n := 18) (by norm_num)
  have h3 := Real.exp_bound (x := (-91/1024 : ℝ)) (by norm_num) (n := 18) (by norm_num)
  have h4 := Real.exp_bound (x := (-119/1024 : ℝ)) (by norm_num) (n := 18) (by norm_num)
  norm_num [Finset.sum_range_succ] at h0 h1 h2 h3 h4
  have s1 := exp_double_bounds_of_abs h1 (by norm_num)
  norm_num at s1
  have s2 := exp_double_bounds_of_abs h2 (by norm_num)
  norm_num at s2
  have s3 := exp_double_bounds_of_abs h3 (by norm_num)
  norm_num at s3
  have s4 := exp_double_bounds_of_abs h4 (by norm_num)
  norm_num at s4
  norm_num [fourthLevelPrimitive]
  constructor <;> linarith [(abs_le.mp h0).1, (abs_le.mp h0).2,
    s1.1, s1.2, s2.1, s2.2, s3.1, s3.2, s4.1, s4.2]

theorem fifthLevelPrimitive_sixteenth_9_bounds :
    (-1319409804407/1000000000000000000 : ℝ) ≤ fourthLevelPrimitive (5373/2000) (9/256) ∧
    fourthLevelPrimitive (5373/2000) (9/256) ≤ (-1319409804406/1000000000000000000 : ℝ) := by
  have h0 := Real.exp_bound (x := (9/512 : ℝ)) (by norm_num) (n := 18) (by norm_num)
  have h1 := Real.exp_bound (x := (-45/1024 : ℝ)) (by norm_num) (n := 18) (by norm_num)
  have h2 := Real.exp_bound (x := (-81/1024 : ℝ)) (by norm_num) (n := 18) (by norm_num)
  have h3 := Real.exp_bound (x := (-117/1024 : ℝ)) (by norm_num) (n := 18) (by norm_num)
  have h4 := Real.exp_bound (x := (-153/1024 : ℝ)) (by norm_num) (n := 18) (by norm_num)
  norm_num [Finset.sum_range_succ] at h0 h1 h2 h3 h4
  have s1 := exp_double_bounds_of_abs h1 (by norm_num)
  norm_num at s1
  have s2 := exp_double_bounds_of_abs h2 (by norm_num)
  norm_num at s2
  have s3 := exp_double_bounds_of_abs h3 (by norm_num)
  norm_num at s3
  have s4 := exp_double_bounds_of_abs h4 (by norm_num)
  norm_num at s4
  norm_num [fourthLevelPrimitive]
  constructor <;> linarith [(abs_le.mp h0).1, (abs_le.mp h0).2,
    s1.1, s1.2, s2.1, s2.2, s3.1, s3.2, s4.1, s4.2]

theorem fifthLevelPrimitive_sixteenth_11_bounds :
    (-2340039908925/1000000000000000000 : ℝ) ≤ fourthLevelPrimitive (5373/2000) (11/256) ∧
    fourthLevelPrimitive (5373/2000) (11/256) ≤ (-2340039908924/1000000000000000000 : ℝ) := by
  have h0 := Real.exp_bound (x := (11/512 : ℝ)) (by norm_num) (n := 18) (by norm_num)
  have h1 := Real.exp_bound (x := (-55/1024 : ℝ)) (by norm_num) (n := 18) (by norm_num)
  have h2 := Real.exp_bound (x := (-99/1024 : ℝ)) (by norm_num) (n := 18) (by norm_num)
  have h3 := Real.exp_bound (x := (-143/1024 : ℝ)) (by norm_num) (n := 18) (by norm_num)
  have h4 := Real.exp_bound (x := (-187/1024 : ℝ)) (by norm_num) (n := 18) (by norm_num)
  norm_num [Finset.sum_range_succ] at h0 h1 h2 h3 h4
  have s1 := exp_double_bounds_of_abs h1 (by norm_num)
  norm_num at s1
  have s2 := exp_double_bounds_of_abs h2 (by norm_num)
  norm_num at s2
  have s3 := exp_double_bounds_of_abs h3 (by norm_num)
  norm_num at s3
  have s4 := exp_double_bounds_of_abs h4 (by norm_num)
  norm_num at s4
  norm_num [fourthLevelPrimitive]
  constructor <;> linarith [(abs_le.mp h0).1, (abs_le.mp h0).2,
    s1.1, s1.2, s2.1, s2.2, s3.1, s3.2, s4.1, s4.2]

theorem fifthLevelPrimitive_sixteenth_13_bounds :
    (-3751419507908/1000000000000000000 : ℝ) ≤ fourthLevelPrimitive (5373/2000) (13/256) ∧
    fourthLevelPrimitive (5373/2000) (13/256) ≤ (-3751419507907/1000000000000000000 : ℝ) := by
  have h0 := Real.exp_bound (x := (13/512 : ℝ)) (by norm_num) (n := 18) (by norm_num)
  have h1 := Real.exp_bound (x := (-65/1024 : ℝ)) (by norm_num) (n := 18) (by norm_num)
  have h2 := Real.exp_bound (x := (-117/1024 : ℝ)) (by norm_num) (n := 18) (by norm_num)
  have h3 := Real.exp_bound (x := (-169/1024 : ℝ)) (by norm_num) (n := 18) (by norm_num)
  have h4 := Real.exp_bound (x := (-221/1024 : ℝ)) (by norm_num) (n := 18) (by norm_num)
  norm_num [Finset.sum_range_succ] at h0 h1 h2 h3 h4
  have s1 := exp_double_bounds_of_abs h1 (by norm_num)
  norm_num at s1
  have s2 := exp_double_bounds_of_abs h2 (by norm_num)
  norm_num at s2
  have s3 := exp_double_bounds_of_abs h3 (by norm_num)
  norm_num at s3
  have s4 := exp_double_bounds_of_abs h4 (by norm_num)
  norm_num at s4
  norm_num [fourthLevelPrimitive]
  constructor <;> linarith [(abs_le.mp h0).1, (abs_le.mp h0).2,
    s1.1, s1.2, s2.1, s2.2, s3.1, s3.2, s4.1, s4.2]

theorem fifthLevelPrimitive_sixteenth_15_bounds :
    (-5596086944461/1000000000000000000 : ℝ) ≤ fourthLevelPrimitive (5373/2000) (15/256) ∧
    fourthLevelPrimitive (5373/2000) (15/256) ≤ (-5596086944460/1000000000000000000 : ℝ) := by
  have h0 := Real.exp_bound (x := (15/512 : ℝ)) (by norm_num) (n := 18) (by norm_num)
  have h1 := Real.exp_bound (x := (-75/1024 : ℝ)) (by norm_num) (n := 18) (by norm_num)
  have h2 := Real.exp_bound (x := (-135/1024 : ℝ)) (by norm_num) (n := 18) (by norm_num)
  have h3 := Real.exp_bound (x := (-195/1024 : ℝ)) (by norm_num) (n := 18) (by norm_num)
  have h4 := Real.exp_bound (x := (-255/1024 : ℝ)) (by norm_num) (n := 18) (by norm_num)
  norm_num [Finset.sum_range_succ] at h0 h1 h2 h3 h4
  have s1 := exp_double_bounds_of_abs h1 (by norm_num)
  norm_num at s1
  have s2 := exp_double_bounds_of_abs h2 (by norm_num)
  norm_num at s2
  have s3 := exp_double_bounds_of_abs h3 (by norm_num)
  norm_num at s3
  have s4 := exp_double_bounds_of_abs h4 (by norm_num)
  norm_num at s4
  norm_num [fourthLevelPrimitive]
  constructor <;> linarith [(abs_le.mp h0).1, (abs_le.mp h0).2,
    s1.1, s1.2, s2.1, s2.2, s3.1, s3.2, s4.1, s4.2]

theorem fifthLevelPrimitive_sixteenth_17_bounds :
    (-7909055150355/1000000000000000000 : ℝ) ≤ fourthLevelPrimitive (5373/2000) (17/256) ∧
    fourthLevelPrimitive (5373/2000) (17/256) ≤ (-7909055150354/1000000000000000000 : ℝ) := by
  have h0 := Real.exp_bound (x := (17/512 : ℝ)) (by norm_num) (n := 18) (by norm_num)
  have h1 := Real.exp_bound (x := (-85/1024 : ℝ)) (by norm_num) (n := 18) (by norm_num)
  have h2 := Real.exp_bound (x := (-153/1024 : ℝ)) (by norm_num) (n := 18) (by norm_num)
  have h3 := Real.exp_bound (x := (-221/1024 : ℝ)) (by norm_num) (n := 18) (by norm_num)
  have h4 := Real.exp_bound (x := (-289/1024 : ℝ)) (by norm_num) (n := 18) (by norm_num)
  norm_num [Finset.sum_range_succ] at h0 h1 h2 h3 h4
  have s1 := exp_double_bounds_of_abs h1 (by norm_num)
  norm_num at s1
  have s2 := exp_double_bounds_of_abs h2 (by norm_num)
  norm_num at s2
  have s3 := exp_double_bounds_of_abs h3 (by norm_num)
  norm_num at s3
  have s4 := exp_double_bounds_of_abs h4 (by norm_num)
  norm_num at s4
  norm_num [fourthLevelPrimitive]
  constructor <;> linarith [(abs_le.mp h0).1, (abs_le.mp h0).2,
    s1.1, s1.2, s2.1, s2.2, s3.1, s3.2, s4.1, s4.2]

theorem fifthLevelPrimitive_sixteenth_19_bounds :
    (-10718280701712/1000000000000000000 : ℝ) ≤ fourthLevelPrimitive (5373/2000) (19/256) ∧
    fourthLevelPrimitive (5373/2000) (19/256) ≤ (-10718280701711/1000000000000000000 : ℝ) := by
  have h0 := Real.exp_bound (x := (19/512 : ℝ)) (by norm_num) (n := 18) (by norm_num)
  have h1 := Real.exp_bound (x := (-95/1024 : ℝ)) (by norm_num) (n := 18) (by norm_num)
  have h2 := Real.exp_bound (x := (-171/1024 : ℝ)) (by norm_num) (n := 18) (by norm_num)
  have h3 := Real.exp_bound (x := (-247/1024 : ℝ)) (by norm_num) (n := 18) (by norm_num)
  have h4 := Real.exp_bound (x := (-323/1024 : ℝ)) (by norm_num) (n := 18) (by norm_num)
  norm_num [Finset.sum_range_succ] at h0 h1 h2 h3 h4
  have s1 := exp_double_bounds_of_abs h1 (by norm_num)
  norm_num at s1
  have s2 := exp_double_bounds_of_abs h2 (by norm_num)
  norm_num at s2
  have s3 := exp_double_bounds_of_abs h3 (by norm_num)
  norm_num at s3
  have s4 := exp_double_bounds_of_abs h4 (by norm_num)
  norm_num at s4
  norm_num [fourthLevelPrimitive]
  constructor <;> linarith [(abs_le.mp h0).1, (abs_le.mp h0).2,
    s1.1, s1.2, s2.1, s2.2, s3.1, s3.2, s4.1, s4.2]

theorem fifthLevelPrimitive_sixteenth_21_bounds :
    (-14045111604850/1000000000000000000 : ℝ) ≤ fourthLevelPrimitive (5373/2000) (21/256) ∧
    fourthLevelPrimitive (5373/2000) (21/256) ≤ (-14045111604849/1000000000000000000 : ℝ) := by
  have h0 := Real.exp_bound (x := (21/512 : ℝ)) (by norm_num) (n := 18) (by norm_num)
  have h1 := Real.exp_bound (x := (-105/1024 : ℝ)) (by norm_num) (n := 18) (by norm_num)
  have h2 := Real.exp_bound (x := (-189/1024 : ℝ)) (by norm_num) (n := 18) (by norm_num)
  have h3 := Real.exp_bound (x := (-273/1024 : ℝ)) (by norm_num) (n := 18) (by norm_num)
  have h4 := Real.exp_bound (x := (-357/1024 : ℝ)) (by norm_num) (n := 18) (by norm_num)
  norm_num [Finset.sum_range_succ] at h0 h1 h2 h3 h4
  have s1 := exp_double_bounds_of_abs h1 (by norm_num)
  norm_num at s1
  have s2 := exp_double_bounds_of_abs h2 (by norm_num)
  norm_num at s2
  have s3 := exp_double_bounds_of_abs h3 (by norm_num)
  norm_num at s3
  have s4 := exp_double_bounds_of_abs h4 (by norm_num)
  norm_num at s4
  norm_num [fourthLevelPrimitive]
  constructor <;> linarith [(abs_le.mp h0).1, (abs_le.mp h0).2,
    s1.1, s1.2, s2.1, s2.2, s3.1, s3.2, s4.1, s4.2]

theorem fifthLevelPrimitive_sixteenth_23_bounds :
    (-17904714925855/1000000000000000000 : ℝ) ≤ fourthLevelPrimitive (5373/2000) (23/256) ∧
    fourthLevelPrimitive (5373/2000) (23/256) ≤ (-17904714925854/1000000000000000000 : ℝ) := by
  have h0 := Real.exp_bound (x := (23/512 : ℝ)) (by norm_num) (n := 18) (by norm_num)
  have h1 := Real.exp_bound (x := (-115/1024 : ℝ)) (by norm_num) (n := 18) (by norm_num)
  have h2 := Real.exp_bound (x := (-207/1024 : ℝ)) (by norm_num) (n := 18) (by norm_num)
  have h3 := Real.exp_bound (x := (-299/1024 : ℝ)) (by norm_num) (n := 18) (by norm_num)
  have h4 := Real.exp_bound (x := (-391/1024 : ℝ)) (by norm_num) (n := 18) (by norm_num)
  norm_num [Finset.sum_range_succ] at h0 h1 h2 h3 h4
  have s1 := exp_double_bounds_of_abs h1 (by norm_num)
  norm_num at s1
  have s2 := exp_double_bounds_of_abs h2 (by norm_num)
  norm_num at s2
  have s3 := exp_double_bounds_of_abs h3 (by norm_num)
  norm_num at s3
  have s4 := exp_double_bounds_of_abs h4 (by norm_num)
  norm_num at s4
  norm_num [fourthLevelPrimitive]
  constructor <;> linarith [(abs_le.mp h0).1, (abs_le.mp h0).2,
    s1.1, s1.2, s2.1, s2.2, s3.1, s3.2, s4.1, s4.2]

theorem fifthLevelPrimitive_sixteenth_25_bounds :
    (-22306485315369/1000000000000000000 : ℝ) ≤ fourthLevelPrimitive (5373/2000) (25/256) ∧
    fourthLevelPrimitive (5373/2000) (25/256) ≤ (-22306485315368/1000000000000000000 : ℝ) := by
  have h0 := Real.exp_bound (x := (25/512 : ℝ)) (by norm_num) (n := 18) (by norm_num)
  have h1 := Real.exp_bound (x := (-125/1024 : ℝ)) (by norm_num) (n := 18) (by norm_num)
  have h2 := Real.exp_bound (x := (-225/1024 : ℝ)) (by norm_num) (n := 18) (by norm_num)
  have h3 := Real.exp_bound (x := (-325/1024 : ℝ)) (by norm_num) (n := 18) (by norm_num)
  have h4 := Real.exp_bound (x := (-425/1024 : ℝ)) (by norm_num) (n := 18) (by norm_num)
  norm_num [Finset.sum_range_succ] at h0 h1 h2 h3 h4
  have s1 := exp_double_bounds_of_abs h1 (by norm_num)
  norm_num at s1
  have s2 := exp_double_bounds_of_abs h2 (by norm_num)
  norm_num at s2
  have s3 := exp_double_bounds_of_abs h3 (by norm_num)
  norm_num at s3
  have s4 := exp_double_bounds_of_abs h4 (by norm_num)
  norm_num at s4
  norm_num [fourthLevelPrimitive]
  constructor <;> linarith [(abs_le.mp h0).1, (abs_le.mp h0).2,
    s1.1, s1.2, s2.1, s2.2, s3.1, s3.2, s4.1, s4.2]

theorem fifthLevelPrimitive_sixteenth_27_bounds :
    (-27254435421677/1000000000000000000 : ℝ) ≤ fourthLevelPrimitive (5373/2000) (27/256) ∧
    fourthLevelPrimitive (5373/2000) (27/256) ≤ (-27254435421676/1000000000000000000 : ℝ) := by
  have h0 := Real.exp_bound (x := (27/512 : ℝ)) (by norm_num) (n := 18) (by norm_num)
  have h1 := Real.exp_bound (x := (-135/1024 : ℝ)) (by norm_num) (n := 18) (by norm_num)
  have h2 := Real.exp_bound (x := (-243/1024 : ℝ)) (by norm_num) (n := 18) (by norm_num)
  have h3 := Real.exp_bound (x := (-351/1024 : ℝ)) (by norm_num) (n := 18) (by norm_num)
  have h4 := Real.exp_bound (x := (-459/1024 : ℝ)) (by norm_num) (n := 18) (by norm_num)
  norm_num [Finset.sum_range_succ] at h0 h1 h2 h3 h4
  have s1 := exp_double_bounds_of_abs h1 (by norm_num)
  norm_num at s1
  have s2 := exp_double_bounds_of_abs h2 (by norm_num)
  norm_num at s2
  have s3 := exp_double_bounds_of_abs h3 (by norm_num)
  norm_num at s3
  have s4 := exp_double_bounds_of_abs h4 (by norm_num)
  norm_num at s4
  norm_num [fourthLevelPrimitive]
  constructor <;> linarith [(abs_le.mp h0).1, (abs_le.mp h0).2,
    s1.1, s1.2, s2.1, s2.2, s3.1, s3.2, s4.1, s4.2]

theorem fifthLevelPrimitive_sixteenth_29_bounds :
    (-32747569130116/1000000000000000000 : ℝ) ≤ fourthLevelPrimitive (5373/2000) (29/256) ∧
    fourthLevelPrimitive (5373/2000) (29/256) ≤ (-32747569130115/1000000000000000000 : ℝ) := by
  have h0 := Real.exp_bound (x := (29/512 : ℝ)) (by norm_num) (n := 18) (by norm_num)
  have h1 := Real.exp_bound (x := (-145/1024 : ℝ)) (by norm_num) (n := 18) (by norm_num)
  have h2 := Real.exp_bound (x := (-261/1024 : ℝ)) (by norm_num) (n := 18) (by norm_num)
  have h3 := Real.exp_bound (x := (-377/1024 : ℝ)) (by norm_num) (n := 18) (by norm_num)
  have h4 := Real.exp_bound (x := (-493/1024 : ℝ)) (by norm_num) (n := 18) (by norm_num)
  norm_num [Finset.sum_range_succ] at h0 h1 h2 h3 h4
  have s1 := exp_double_bounds_of_abs h1 (by norm_num)
  norm_num at s1
  have s2 := exp_double_bounds_of_abs h2 (by norm_num)
  norm_num at s2
  have s3 := exp_double_bounds_of_abs h3 (by norm_num)
  norm_num at s3
  have s4 := exp_double_bounds_of_abs h4 (by norm_num)
  norm_num at s4
  norm_num [fourthLevelPrimitive]
  constructor <;> linarith [(abs_le.mp h0).1, (abs_le.mp h0).2,
    s1.1, s1.2, s2.1, s2.2, s3.1, s3.2, s4.1, s4.2]

theorem fifthLevelPrimitive_sixteenth_31_bounds :
    (-38780238514960/1000000000000000000 : ℝ) ≤ fourthLevelPrimitive (5373/2000) (31/256) ∧
    fourthLevelPrimitive (5373/2000) (31/256) ≤ (-38780238514959/1000000000000000000 : ℝ) := by
  have h0 := Real.exp_bound (x := (31/512 : ℝ)) (by norm_num) (n := 18) (by norm_num)
  have h1 := Real.exp_bound (x := (-155/1024 : ℝ)) (by norm_num) (n := 18) (by norm_num)
  have h2 := Real.exp_bound (x := (-279/1024 : ℝ)) (by norm_num) (n := 18) (by norm_num)
  have h3 := Real.exp_bound (x := (-403/1024 : ℝ)) (by norm_num) (n := 18) (by norm_num)
  have h4 := Real.exp_bound (x := (-527/1024 : ℝ)) (by norm_num) (n := 18) (by norm_num)
  norm_num [Finset.sum_range_succ] at h0 h1 h2 h3 h4
  have s1 := exp_double_bounds_of_abs h1 (by norm_num)
  norm_num at s1
  have s2 := exp_double_bounds_of_abs h2 (by norm_num)
  norm_num at s2
  have s3 := exp_double_bounds_of_abs h3 (by norm_num)
  norm_num at s3
  have s4 := exp_double_bounds_of_abs h4 (by norm_num)
  norm_num at s4
  norm_num [fourthLevelPrimitive]
  constructor <;> linarith [(abs_le.mp h0).1, (abs_le.mp h0).2,
    s1.1, s1.2, s2.1, s2.2, s3.1, s3.2, s4.1, s4.2]

def fifthLevelSamples : Fin 33 → ℝ :=
  fun i => fourthLevelPrimitive (5373/2000) (i.val/256)

def fifthLevelSamplesLower : Fin 33 → ℚ :=
  fun i => ![0,-2029566407,-16007754766,-53263038971,-124465267437,-239644921451,-408211913058,-638973934981,-940154374694,-1319409804407,-1783847058417,-2340039908925,-2994045351101,-3751419507908,-4617233164834,-5596086944461,-6692126130458,-7909055150355,-9250151726173,-10718280701712,-12315907555091,-14045111604850,-15907598917710,-17904714925855,-20037456761388,-22306485315369,-24712137028672,-27254435421677,-29933102369600,-32747569130116,-35696987129701,-38780238514960,-41995946475046] i / 1000000000000000000

def fifthLevelSamplesUpper : Fin 33 → ℚ :=
  fun i => if i = 0 then 0 else fifthLevelSamplesLower i + 1/1000000000000000000

theorem fifthLevelSamples_bounds (i : Fin 33) :
    (fifthLevelSamplesLower i : ℝ) ≤ fifthLevelSamples i ∧
      fifthLevelSamples i ≤ (fifthLevelSamplesUpper i : ℝ) := by
  fin_cases i
  · norm_num [fifthLevelSamples, fifthLevelSamplesLower, fifthLevelSamplesUpper,
      fourthLevelPrimitive_zero]
  · convert fifthLevelPrimitive_sixteenth_1_bounds using 1 <;>
      norm_num [fifthLevelSamples, fifthLevelSamplesLower, fifthLevelSamplesUpper]
  · convert fourthLevelPrimitive_sixteenth_1_bounds using 1 <;>
      norm_num [fifthLevelSamples, fifthLevelSamplesLower, fifthLevelSamplesUpper]
  · convert fifthLevelPrimitive_sixteenth_3_bounds using 1 <;>
      norm_num [fifthLevelSamples, fifthLevelSamplesLower, fifthLevelSamplesUpper]
  · convert fourthLevelPrimitive_sixteenth_2_bounds using 1 <;>
      norm_num [fifthLevelSamples, fifthLevelSamplesLower, fifthLevelSamplesUpper]
  · convert fifthLevelPrimitive_sixteenth_5_bounds using 1 <;>
      norm_num [fifthLevelSamples, fifthLevelSamplesLower, fifthLevelSamplesUpper]
  · convert fourthLevelPrimitive_sixteenth_3_bounds using 1 <;>
      norm_num [fifthLevelSamples, fifthLevelSamplesLower, fifthLevelSamplesUpper]
  · convert fifthLevelPrimitive_sixteenth_7_bounds using 1 <;>
      norm_num [fifthLevelSamples, fifthLevelSamplesLower, fifthLevelSamplesUpper]
  · convert fourthLevelPrimitive_sixteenth_4_bounds using 1 <;>
      norm_num [fifthLevelSamples, fifthLevelSamplesLower, fifthLevelSamplesUpper]
  · convert fifthLevelPrimitive_sixteenth_9_bounds using 1 <;>
      norm_num [fifthLevelSamples, fifthLevelSamplesLower, fifthLevelSamplesUpper]
  · convert fourthLevelPrimitive_sixteenth_5_bounds using 1 <;>
      norm_num [fifthLevelSamples, fifthLevelSamplesLower, fifthLevelSamplesUpper]
  · convert fifthLevelPrimitive_sixteenth_11_bounds using 1 <;>
      norm_num [fifthLevelSamples, fifthLevelSamplesLower, fifthLevelSamplesUpper]
  · convert fourthLevelPrimitive_sixteenth_6_bounds using 1 <;>
      norm_num [fifthLevelSamples, fifthLevelSamplesLower, fifthLevelSamplesUpper]
  · convert fifthLevelPrimitive_sixteenth_13_bounds using 1 <;>
      norm_num [fifthLevelSamples, fifthLevelSamplesLower, fifthLevelSamplesUpper]
  · convert fourthLevelPrimitive_sixteenth_7_bounds using 1 <;>
      norm_num [fifthLevelSamples, fifthLevelSamplesLower, fifthLevelSamplesUpper]
  · convert fifthLevelPrimitive_sixteenth_15_bounds using 1 <;>
      norm_num [fifthLevelSamples, fifthLevelSamplesLower, fifthLevelSamplesUpper]
  · convert fourthLevelPrimitive_sixteenth_8_bounds using 1 <;>
      norm_num [fifthLevelSamples, fifthLevelSamplesLower, fifthLevelSamplesUpper]
  · convert fifthLevelPrimitive_sixteenth_17_bounds using 1 <;>
      norm_num [fifthLevelSamples, fifthLevelSamplesLower, fifthLevelSamplesUpper]
  · convert fourthLevelPrimitive_sixteenth_9_bounds using 1 <;>
      norm_num [fifthLevelSamples, fifthLevelSamplesLower, fifthLevelSamplesUpper]
  · convert fifthLevelPrimitive_sixteenth_19_bounds using 1 <;>
      norm_num [fifthLevelSamples, fifthLevelSamplesLower, fifthLevelSamplesUpper]
  · convert fourthLevelPrimitive_sixteenth_10_bounds using 1 <;>
      norm_num [fifthLevelSamples, fifthLevelSamplesLower, fifthLevelSamplesUpper]
  · convert fifthLevelPrimitive_sixteenth_21_bounds using 1 <;>
      norm_num [fifthLevelSamples, fifthLevelSamplesLower, fifthLevelSamplesUpper]
  · convert fourthLevelPrimitive_sixteenth_11_bounds using 1 <;>
      norm_num [fifthLevelSamples, fifthLevelSamplesLower, fifthLevelSamplesUpper]
  · convert fifthLevelPrimitive_sixteenth_23_bounds using 1 <;>
      norm_num [fifthLevelSamples, fifthLevelSamplesLower, fifthLevelSamplesUpper]
  · convert fourthLevelPrimitive_sixteenth_12_bounds using 1 <;>
      norm_num [fifthLevelSamples, fifthLevelSamplesLower, fifthLevelSamplesUpper]
  · convert fifthLevelPrimitive_sixteenth_25_bounds using 1 <;>
      norm_num [fifthLevelSamples, fifthLevelSamplesLower, fifthLevelSamplesUpper]
  · convert fourthLevelPrimitive_sixteenth_13_bounds using 1 <;>
      norm_num [fifthLevelSamples, fifthLevelSamplesLower, fifthLevelSamplesUpper]
  · convert fifthLevelPrimitive_sixteenth_27_bounds using 1 <;>
      norm_num [fifthLevelSamples, fifthLevelSamplesLower, fifthLevelSamplesUpper]
  · convert fourthLevelPrimitive_sixteenth_14_bounds using 1 <;>
      norm_num [fifthLevelSamples, fifthLevelSamplesLower, fifthLevelSamplesUpper]
  · convert fifthLevelPrimitive_sixteenth_29_bounds using 1 <;>
      norm_num [fifthLevelSamples, fifthLevelSamplesLower, fifthLevelSamplesUpper]
  · convert fourthLevelPrimitive_sixteenth_15_bounds using 1 <;>
      norm_num [fifthLevelSamples, fifthLevelSamplesLower, fifthLevelSamplesUpper]
  · convert fifthLevelPrimitive_sixteenth_31_bounds using 1 <;>
      norm_num [fifthLevelSamples, fifthLevelSamplesLower, fifthLevelSamplesUpper]
  · convert fourthLevelPrimitive_sixteenth_16_bounds using 1 <;>
      norm_num [fifthLevelSamples, fifthLevelSamplesLower, fifthLevelSamplesUpper]

end
end RiemannResearch.RH
