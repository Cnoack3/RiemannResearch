/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! # Rational polynomial enclosure of Conrey's optimized stop-loss profile

Set t = exp(-2u/7). The logarithm is log((1-t^11)/(1-t^4)).
A lower Taylor polynomial for exp((267/250)t^4) reduces the comparison
to a degree-fifteen polynomial. Its Bernstein coefficients on four dyadic
intervals are nonnegative. The identities are verified by the ring tactic. -/

noncomputable section
namespace RiemannResearch.Analysis.ConreyStopLossEnvelope

private def blend (x y : ℝ) : List ℕ → ℝ
  | [] => 0
  | c :: cs => c * y ^ cs.length + x * blend x y cs

private theorem blend_nonneg {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (cs : List ℕ) :
    0 ≤ blend x y cs := by
  induction cs with
  | nil => simp [blend]
  | cons c cs ih => dsimp [blend]; positivity

private def taylorFourth (z : ℝ) := 1 + z + z^2/2 + z^3/6 + z^4/24

private theorem taylorFourth_le_exp {z : ℝ} (hz : 0 ≤ z) : taylorFourth z ≤ Real.exp z := by
  have h := Real.sum_le_exp_of_nonneg hz 5
  norm_num [Finset.sum_range_succ, Nat.factorial] at h
  unfold taylorFourth
  linarith only [h]

private def residual (t : ℝ) :=
  (1-t^4)*taylorFourth ((267/250)*t^4) - (1-t^11)

-- The integer coefficients are the rational Bernstein coefficients after
-- multiplication by their common positive denominator on each interval.
private def cell0 : List ℕ := [69632000000000, 1079296000000000, 7816192000000000, 35085824000000000, 109155475968000000, 249192613632000000, 430914515072000000, 574133375424000000, 593400927324288000, 474939054004160000, 291343115965984000, 134179937745136000, 44778639422148056, 10186733499278196, 1406880441761238, 88545583647605]

set_option maxHeartbeats 1000000 in
private theorem cell0_identity (t : ℝ) :
    (31250000000 : ℝ) * residual t =
      t^4 * (1-t) * blend (t-(0 : ℝ)) ((1/2 : ℝ)-t) cell0 := by
  norm_num [residual, taylorFourth, blend, cell0]
  <;> ring

private def cell1 : List ℕ := [2901461684964720640, 42232558753890091008, 284863131584863641600, 1179858453946675572736, 3351464569669835442176, 6904879314364414991360, 10637839185542320259584, 12448118048518563106560, 11118949425880029310848, 7549173518245975870528, 3842471302643411340000, 1429017938198858821008, 372072609372036188440, 63202835978491406516, 6187441372952818646, 266459745237902725]

set_option maxHeartbeats 1000000 in
private theorem cell1_identity (t : ℝ) :
    (31250000000 : ℝ) * residual t =
      t^4 * (1-t) * blend (t-(1/2 : ℝ)) ((3/4 : ℝ)-t) cell1 := by
  norm_num [residual, taylorFourth, blend, cell1]
  <;> ring

private def cell2 : List ℕ := [8731352931955596492800, 95080401514541940391936, 451663933966672678985728, 1223808940394107581378560, 2158065206384510050584576, 3190537819301994405534720, 6161035915794563763044864, 14121813264469938172653312, 26211293300595480596584320, 35038308174734030849843264, 33409021092856387113460960, 22675023426408006700541584, 10757668236984266999890712, 3404390121996632812974900, 647634985412107180641174, 56151876106693210407365]

set_option maxHeartbeats 1000000 in
private theorem cell2_identity (t : ℝ) :
    (31250000000 : ℝ) * residual t =
      t^4 * (1-t) * blend (t-(3/4 : ℝ)) ((7/8 : ℝ)-t) cell2 := by
  norm_num [residual, taylorFourth, blend, cell2]
  <;> ring

private def cell3 : List ℕ := [56151876106693210407365, 1036921297788689131579776, 8854398495268780126115328, 46410169273284458266877952, 167104600451858641621086208, 438110438841051290570981376, 864571187731271960415961088, 1308469922620327655966244864, 1532013971462816717598621696, 1388369882247600847626174464, 966312639939417320233893888, 507455256039857417078439936, 194702271442254042243268608, 51543065935095435888689152, 8420580941262125298352128, 640146085250487912759296]

set_option maxHeartbeats 1000000 in
private theorem cell3_identity (t : ℝ) :
    (31250000000 : ℝ) * residual t =
      t^4 * (1-t) * blend (t-(7/8 : ℝ)) ((1 : ℝ)-t) cell3 := by
  norm_num [residual, taylorFourth, blend, cell3]
  <;> ring

private theorem residual_nonneg {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) : 0 ≤ residual t := by
  have hmul : 0 ≤ t^4*(1-t) := mul_nonneg (pow_nonneg ht _) (sub_nonneg.mpr ht1)
  by_cases hr0 : t ≤ 1/2
  · have h := mul_nonneg hmul (blend_nonneg (x:=t-(0:ℝ)) (y:=(1/2:ℝ)-t) (by linarith) (by linarith) cell0)
    rw [← cell0_identity] at h
    linarith only [h]
  by_cases hr1 : t ≤ 3/4
  · have h := mul_nonneg hmul (blend_nonneg (x:=t-(1/2:ℝ)) (y:=(3/4:ℝ)-t) (by linarith) (by linarith) cell1)
    rw [← cell1_identity] at h
    linarith only [h]
  by_cases hr2 : t ≤ 7/8
  · have h := mul_nonneg hmul (blend_nonneg (x:=t-(3/4:ℝ)) (y:=(7/8:ℝ)-t) (by linarith) (by linarith) cell2)
    rw [← cell2_identity] at h
    linarith only [h]
  have h := mul_nonneg hmul (blend_nonneg (x:=t-(7/8:ℝ)) (y:=(1:ℝ)-t) (by linarith) (by linarith) cell3)
  rw [← cell3_identity] at h
  linarith only [h]

/-- Rational envelope of the degree-eleven/four quotient on the open unit interval. -/
theorem quotient_le_exp {t : ℝ} (ht : 0 ≤ t) (ht1 : t < 1) :
    (1-t^11)/(1-t^4) ≤ Real.exp ((267/250)*t^4) := by
  have h := residual_nonneg ht ht1.le
  apply le_trans _ (taylorFourth_le_exp (by positivity))
  apply (div_le_iff₀ (sub_pos.mpr (pow_lt_one₀ ht ht1 (by norm_num)))).mpr
  unfold residual at h
  linarith only [h]

/-- Continuous value of the log quotient at t = 1. -/
theorem boundary_le_exp : (11/4 : ℝ) ≤ Real.exp (267/250) := by
  apply le_trans _ (taylorFourth_le_exp (by norm_num))
  norm_num [taylorFourth]

end RiemannResearch.Analysis.ConreyStopLossEnvelope
