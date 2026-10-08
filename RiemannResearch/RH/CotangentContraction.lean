/-
Copyright (c) 2026 Christian Noack. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Noack
-/
import RiemannResearch.RH.CotangentMultiplication
import RiemannResearch.RH.ArithmeticPacketCore
import RiemannResearch.RH.IntegerDPPPacketRankTwo

/-!
# Finite arithmetic contraction to the specified double-V core

Common periods may be chosen as `a*b`, which avoids any gcd/lcm reindexing.
All sums are finite. This module retains endpoint values and signed divisor
terms before applying cotangent reflection or multiplication.
-/

noncomputable section
open Matrix
open scoped BigOperators
namespace RiemannResearch.RH.Pareto

private theorem sum_range_mul_blocks (f : ℕ → ℝ) (a q : ℕ) :
    (∑ r ∈ Finset.range (a*q), f r) =
      ∑ t ∈ Finset.range q, ∑ s ∈ Finset.range a, f (a*t+s) := by
  induction q with
  | zero => simp
  | succ q ih => rw [Nat.mul_succ, Finset.sum_range_add, ih, Finset.sum_range_succ]

private theorem finite_difference_parts (h k : ℕ → ℝ) (n : ℕ) :
    (∑ r ∈ Finset.range n, h r * (k r-k (r+1))) =
      h 0*k 0-h n*k n +
        ∑ r ∈ Finset.range n, (h (r+1)-h r)*k (r+1) := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ, ih, Finset.sum_range_succ]; ring

theorem periodCotangent_zero (Q : ℕ) : periodCotangent Q 0 = 0 := by
  simp [periodCotangent]

theorem periodCotangent_terminal (Q : ℕ) (hQ : 0 < Q) : periodCotangent Q Q = 0 := by
  unfold periodCotangent
  have he : Real.pi*(Q : ℝ)/(Q : ℝ) = Real.pi := by
    exact mul_div_cancel_right₀ Real.pi (by positivity)
  rw [he, Real.sin_pi]
  simp

theorem periodCotangent_negative_reflection (Q r : ℕ) (hQ : 0 < Q)
    (hrQ : r ≤ Q) : periodCotangent Q (Q-r) = -periodCotangent Q r := by
  have he : Real.pi*((Q-r : ℕ) : ℝ)/(Q : ℝ) =
      Real.pi-Real.pi*(r : ℝ)/(Q : ℝ) := by
    rw [Nat.cast_sub hrQ]
    field_simp
  unfold periodCotangent
  rw [he, Real.cos_pi_sub, Real.sin_pi_sub]
  ring

/-- A symmetric finite multiplier contributes zero to the odd cotangent sum. -/
theorem symmetric_cotangent_sum_zero (Q : ℕ) (hQ : 0 < Q) (f : ℕ → ℝ)
    (hf : ∀ r, 0 < r → r < Q → f (Q-r) = f r) :
    (∑ r ∈ Finset.range Q, f r * periodCotangent Q r) = 0 := by
  have he : (∑ r ∈ Finset.Ico 1 Q, f (Q-r)*periodCotangent Q (Q-r)) =
      ∑ r ∈ Finset.Ico 1 Q, f r*periodCotangent Q r := by
    apply Finset.sum_bij (fun r _ => Q-r)
    · intro r hr
      have h := Finset.mem_Ico.mp hr
      exact Finset.mem_Ico.mpr ⟨by omega, by omega⟩
    · intro r hr s hs hrs
      have h1 := Finset.mem_Ico.mp hr
      have h2 := Finset.mem_Ico.mp hs
      omega
    · intro s hs
      have h := Finset.mem_Ico.mp hs
      refine ⟨Q-s, Finset.mem_Ico.mpr ⟨by omega, by omega⟩, ?_⟩
      omega
    · intro r hr
      rfl
  have hn : (∑ r ∈ Finset.Ico 1 Q, f (Q-r)*periodCotangent Q (Q-r)) =
      -(∑ r ∈ Finset.Ico 1 Q, f r*periodCotangent Q r) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro r hr
    have h := Finset.mem_Ico.mp hr
    rw [hf r (by omega) h.2, periodCotangent_negative_reflection Q r hQ (by omega)]
    ring
  rw [hn] at he
  have hz : (∑ r ∈ Finset.Ico 1 Q, f r*periodCotangent Q r) = 0 := by linarith
  rw [Finset.sum_Ico_eq_sub _ (by omega)] at hz
  simpa only [Finset.sum_range_one, periodCotangent_zero, mul_zero, sub_zero] using hz

/-- A single nonzero block residue has exactly its full multiplication sum. -/
theorem periodCotangent_block_sum (a q r : ℕ) (ha : 0 < a) (hq : 0 < q)
    (hr : 0 < r) (hra : r < a) :
    (∑ t ∈ Finset.range q, periodCotangent (a*q) (a*t+r)) =
      (q : ℝ)*periodCotangent a r := by
  let x : ℝ := (r : ℝ)/((a : ℝ)*(q : ℝ))
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have hx : 0 < x := by dsimp [x]; positivity
  have hqx : (q : ℝ)*x < 1 := by
    have he : (q : ℝ)*x = (r : ℝ)/(a : ℝ) := by dsimp [x]; field_simp
    rw [he]
    exact (div_lt_one haR).mpr (by exact_mod_cast hra)
  have hm := cotangent_finite_multiplication q hq x hx hqx
  rw [Fin.sum_univ_eq_sum_range (fun t => cotangentAt (x+(t : ℝ)/q))] at hm
  convert hm using 1
  · apply Finset.sum_congr rfl
    intro t _
    unfold periodCotangent cotangentAt
    have he : Real.pi*((a*t+r : ℕ) : ℝ)/((a*q : ℕ) : ℝ) =
        Real.pi*(x+(t : ℝ)/q) := by
      dsimp [x]
      push_cast
      field_simp
      ring
    rw [he]
  · unfold periodCotangent cotangentAt
    have he : Real.pi*((q : ℝ)*x) = Real.pi*(r : ℝ)/(a : ℝ) := by
      dsimp [x]
      field_simp
    rw [he]

theorem cotangentV_eq_range (c b : ℕ) (hb : 0 < b) :
    cotangentV c b = 1/(b : ℝ) *
      ∑ r ∈ Finset.range b, residue b (c*r)*periodCotangent b r := by
  unfold cotangentV periodCotangent residue
  have he (r : ℕ) : (((c*r % b : ℕ) : ℝ)/(b : ℝ)) *
      (Real.cos (Real.pi*(r : ℝ)/(b : ℝ))/Real.sin (Real.pi*(r : ℝ)/(b : ℝ))) =
      (1/(b : ℝ)) * (((c*r % b : ℕ) : ℝ) *
        (Real.cos (Real.pi*(r : ℝ)/(b : ℝ))/Real.sin (Real.pi*(r : ℝ)/(b : ℝ)))) := by ring
  simp_rw [he]
  rw [← Finset.mul_sum, Finset.sum_Ico_eq_sub _ (by omega)]
  simp

/-- The whole residue cotangent sum contracts to its own conductor. -/
theorem residue_periodCotangent_sum (a q : ℕ) (ha : 0 < a) (hq : 0 < q) :
    (∑ r ∈ Finset.range (a*q), residue a r * periodCotangent (a*q) r) =
      ((a*q : ℕ) : ℝ)*cotangentV 1 a := by
  rw [sum_range_mul_blocks, Finset.sum_comm]
  have hp (s t : ℕ) : residue a (a*t+s) = residue a s := by
    simp [residue, Nat.add_mod, Nat.mul_mod_right]
  simp_rw [hp, ← Finset.mul_sum]
  have hpoint (s : ℕ) (hs : s ∈ Finset.range a) :
      residue a s * (∑ t ∈ Finset.range q, periodCotangent (a*q) (a*t+s)) =
        (q : ℝ)*(residue a s * periodCotangent a s) := by
    by_cases hs0 : s = 0
    · simp [hs0, residue]
    have hslt := Finset.mem_range.mp hs
    rw [periodCotangent_block_sum a q s ha hq (by omega) hslt]
    ring
  rw [Finset.sum_congr rfl hpoint, ← Finset.mul_sum, cotangentV_eq_range 1 a ha]
  have hs : (∑ s ∈ Finset.range a, residue a s*periodCotangent a s) =
      ∑ s ∈ Finset.range a, residue a (1*s)*periodCotangent a s := by simp
  rw [hs]
  push_cast
  field_simp [ne_of_gt (show (0 : ℝ) < a by exact_mod_cast ha)]

/-- Retains the entire arithmetic mixed divisibility term. Choosing the
common period `a*b` avoids gcd special cases. -/
theorem divisible_residue_periodCotangent_sum (a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    (∑ r ∈ Finset.range (a*b),
      (if a ∣ r then (a : ℝ) else 0) * residue b r * periodCotangent (a*b) r) =
      ((a*b : ℕ) : ℝ)*cotangentV a b := by
  rw [sum_range_mul_blocks]
  have hinner (t : ℕ) (ht : t ∈ Finset.range b) :
      (∑ s ∈ Finset.range a,
        (if a ∣ a*t+s then (a : ℝ) else 0) * residue b (a*t+s) *
          periodCotangent (a*b) (a*t+s)) =
      (a : ℝ)*residue b (a*t)*periodCotangent b t := by
    rw [Finset.sum_eq_single 0]
    · have he : Real.pi*((a*t : ℕ) : ℝ)/((a*b : ℕ) : ℝ) =
          Real.pi*(t : ℝ)/(b : ℝ) := by
        push_cast
        field_simp
      simp only [add_zero, dvd_mul_right, if_true, periodCotangent]
      rw [he]
    · intro s hs hs0
      have hslt := Finset.mem_range.mp hs
      have hn : ¬ a ∣ a*t+s := by
        rw [Nat.dvd_iff_mod_eq_zero]
        simpa [Nat.add_mod, Nat.mul_mod_right, Nat.mod_eq_of_lt hslt] using hs0
      simp [hn]
    · intro hn
      exact (hn (Finset.mem_range.mpr ha)).elim
  rw [Finset.sum_congr rfl hinner, cotangentV_eq_range a b hb]
  simp_rw [mul_assoc, ← Finset.mul_sum]
  push_cast
  field_simp [ne_of_gt (show (0 : ℝ) < b by exact_mod_cast hb)]

def divisibleAmplitude (a r : ℕ) : ℝ := if a ∣ r then (a : ℝ) else 0

/-- The centered product's exact arithmetic first difference. -/
theorem centeredResidueProduct_difference (a b r : ℕ) (hr : 0 < r) :
    centeredResidueProduct a b r-centeredResidueProduct a b (r-1) =
      residue a r+residue b r-((a : ℝ)+(b : ℝ))/2 -
        divisibleAmplitude a r*residue b r-divisibleAmplitude b r*residue a r +
        divisibleAmplitude a r*((b : ℝ)+1)/2 +
        divisibleAmplitude b r*((a : ℝ)+1)/2-
        divisibleAmplitude a r*divisibleAmplitude b r := by
  have h1 := residue_difference a r hr
  have h2 := residue_difference b r hr
  have he1 : residue a (r-1) = residue a r-1+divisibleAmplitude a r := by
    simpa [divisibleAmplitude] using (show residue a (r-1) =
      residue a r-1+(if a ∣ r then (a : ℝ) else 0) by linarith)
  have he2 : residue b (r-1) = residue b r-1+divisibleAmplitude b r := by
    simpa [divisibleAmplitude] using (show residue b (r-1) =
      residue b r-1+(if b ∣ r then (b : ℝ) else 0) by linarith)
  unfold centeredResidueProduct
  rw [he1, he2]
  ring

private def symmetricDifferenceCorrection (a b r : ℕ) : ℝ :=
  -((a : ℝ)+(b : ℝ))/2 + divisibleAmplitude a r*((b : ℝ)+1)/2 +
    divisibleAmplitude b r*((a : ℝ)+1)/2-divisibleAmplitude a r*divisibleAmplitude b r

private theorem divisibleAmplitude_reflection (a Q r : ℕ) (haQ : a ∣ Q) (hrQ : r ≤ Q) :
    divisibleAmplitude a (Q-r) = divisibleAmplitude a r := by
  have he : a ∣ Q-r ↔ a ∣ r := by
    constructor
    · intro h
      have hh := Nat.dvd_sub haQ h
      rw [show Q-(Q-r) = r by omega] at hh
      exact hh
    · intro h
      exact Nat.dvd_sub haQ h
  simp [divisibleAmplitude, he]

/-- The arithmetic centered product has exactly the proposed cotangent sum,
including the two single-conductor corrections before Möbius cancellation. -/
theorem residueDifferenceCotangentCore_contract (a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    residueDifferenceCotangentCore (a*b) a b = -(1/2 : ℝ) *
      (cotangentV a b+cotangentV b a-cotangentV 1 a-cotangentV 1 b) := by
  have hQ : 0 < a*b := Nat.mul_pos ha hb
  let h := centeredResidueProduct a b
  let k := periodCotangent (a*b)
  let F : ℕ → ℝ := fun r => (h r-h (r-1))*k r
  have hparts := finite_difference_parts h k (a*b)
  have hz : h 0 = 0 := centeredResidueProduct_zero a b
  have hkQ : k (a*b) = 0 := periodCotangent_terminal (a*b) hQ
  have hF0 : F 0 = 0 := by simp [F]
  have hFQ : F (a*b) = 0 := by simp [F, hkQ]
  have hshift : (∑ r ∈ Finset.range (a*b), F (r+1)) =
      ∑ r ∈ Finset.range (a*b), F r := by
    have he := Finset.sum_range_sub' F (a*b)
    rw [Finset.sum_sub_distrib, hF0, hFQ] at he
    linarith
  simp only [hz, hkQ, zero_mul, mul_zero, sub_zero, zero_add] at hparts
  have hepart : (∑ r ∈ Finset.range (a*b), h r*(k r-k (r+1))) =
      ∑ r ∈ Finset.range (a*b), F r := by
    rw [hparts]
    have hepoint (r : ℕ) : (h (r+1)-h r)*k (r+1) = F (r+1) := by
      simp [F]
    simp_rw [hepoint]
    exact hshift
  have hsymmetric : (∑ r ∈ Finset.range (a*b),
      symmetricDifferenceCorrection a b r*k r) = 0 := by
    apply symmetric_cotangent_sum_zero (a*b) hQ (symmetricDifferenceCorrection a b)
    intro r hr hrQ
    unfold symmetricDifferenceCorrection
    rw [divisibleAmplitude_reflection a (a*b) r (dvd_mul_right a b) (by omega),
      divisibleAmplitude_reflection b (a*b) r (dvd_mul_left b a) (by omega)]
  have hdelta (r : ℕ) : F r =
      (residue a r+residue b r-divisibleAmplitude a r*residue b r-
        divisibleAmplitude b r*residue a r)*k r +
        symmetricDifferenceCorrection a b r*k r := by
    by_cases hr0 : r = 0
    · subst r
      simp [F, k, periodCotangent_zero]
    · dsimp only [F, h]
      rw [centeredResidueProduct_difference a b r (by omega)]
      unfold symmetricDifferenceCorrection
      ring
  have hsum : (∑ r ∈ Finset.range (a*b), F r) =
      ((a*b : ℕ) : ℝ) *
        (cotangentV 1 a+cotangentV 1 b-cotangentV a b-cotangentV b a) := by
    simp_rw [hdelta, Finset.sum_add_distrib]
    rw [hsymmetric, add_zero]
    simp only [sub_mul, add_mul, Finset.sum_sub_distrib, Finset.sum_add_distrib]
    have hbsource : (∑ r ∈ Finset.range (a*b), residue b r*k r) =
        ((a*b : ℕ) : ℝ)*cotangentV 1 b := by
      simpa [k, Nat.mul_comm] using residue_periodCotangent_sum b a hb ha
    have hamixed : (∑ r ∈ Finset.range (a*b), divisibleAmplitude a r*residue b r*k r) =
        ((a*b : ℕ) : ℝ)*cotangentV a b := by
      exact divisible_residue_periodCotangent_sum a b ha hb
    have hbmixed : (∑ r ∈ Finset.range (a*b), divisibleAmplitude b r*residue a r*k r) =
        ((a*b : ℕ) : ℝ)*cotangentV b a := by
      simpa [divisibleAmplitude, k, Nat.mul_comm] using divisible_residue_periodCotangent_sum b a hb ha
    rw [show (∑ r ∈ Finset.range (a*b), residue a r*k r) =
        ((a*b : ℕ) : ℝ)*cotangentV 1 a from residue_periodCotangent_sum a b ha hb,
      hbsource, hamixed, hbmixed]
    ring
  unfold residueDifferenceCotangentCore
  rw [Fin.sum_univ_eq_sum_range (fun r => centeredResidueProduct a b r *
    (periodCotangent (a*b) r-periodCotangent (a*b) (r+1)))]
  change 1/(2*((a*b : ℕ) : ℝ)) * (∑ r ∈ Finset.range (a*b), h r*(k r-k (r+1))) = _
  rw [hepart, hsum]
  field_simp [ne_of_gt (show (0 : ℝ) < ((a*b : ℕ) : ℝ) by exact_mod_cast hQ)]
  ring

/-- The cotangent-difference core is independent of its chosen common period. -/
theorem residueDifferenceCotangentCore_period_independent (Q P a b : ℕ)
    (hQ : 0 < Q) (hP : 0 < P) (ha : 0 < a) (hb : 0 < b)
    (haQ : a ∣ Q) (hbQ : b ∣ Q) (haP : a ∣ P) (hbP : b ∣ P) :
    residueDifferenceCotangentCore Q a b = residueDifferenceCotangentCore P a b := by
  have h1 := paretoInner_residue_eq_differenceCotangentCore Q a b hQ ha hb haQ hbQ
  have h2 := paretoInner_residue_eq_differenceCotangentCore P a b hP ha hb haP hbP
  nlinarith [Real.pi_pos]

theorem residueDifferenceCotangentCore_eq_V (Q a b : ℕ) (hQ : 0 < Q)
    (ha : 0 < a) (hb : 0 < b) (haQ : a ∣ Q) (hbQ : b ∣ Q) :
    residueDifferenceCotangentCore Q a b = -(1/2 : ℝ) *
      (cotangentV a b+cotangentV b a-cotangentV 1 a-cotangentV 1 b) := by
  rw [residueDifferenceCotangentCore_period_independent Q (a*b) a b hQ
    (Nat.mul_pos ha hb) ha hb haQ hbQ (dvd_mul_right a b) (dvd_mul_left b a)]
  exact residueDifferenceCotangentCore_contract a b ha hb

private theorem zero_sum_single_coordinate_correction {ι κ : Type*} [Fintype ι] [Fintype κ]
    (u x : ι → ℝ) (v y : κ → ℝ) (hu : ∑ i, u i = 0) (hv : ∑ j, v j = 0) :
    (∑ i, ∑ j, u i*v j*(x i+y j)) = 0 := by
  have hp (i : ι) (j : κ) : u i*v j*(x i+y j) =
      (u i*x i)*v j+u i*(v j*y j) := by ring
  simp_rw [hp, Finset.sum_add_distrib]
  have hleft : (∑ i, ∑ j, (u i*x i)*v j) = 0 := by
    simp_rw [← Finset.mul_sum, hv, mul_zero]
    simp
  have hright : (∑ i, ∑ j, u i*(v j*y j)) = 0 := by
    simp_rw [← Finset.mul_sum]
    rw [← Finset.sum_mul, hu, zero_mul]
  rw [hleft, hright]
  ring

private theorem divisor_double_sum (d e : ℕ) (f : ℕ → ℕ → ℝ) :
    (∑ a : d.divisors, ∑ b : e.divisors, f a.val b.val) =
      ∑ a ∈ d.divisors, ∑ b ∈ e.divisors, f a b := by
  calc
    _ = ∑ a : d.divisors, ∑ b ∈ e.divisors, f a.val b := by
      apply Finset.sum_congr rfl
      intro a _
      exact Finset.sum_coe_sort e.divisors (fun b : ℕ => f a.val b)
    _ = _ := Finset.sum_coe_sort d.divisors (fun a : ℕ =>
      ∑ b ∈ e.divisors, f a b)

/-- The complete signed divisor contraction is the already specified core. -/
theorem packetDifferenceCotangentCoreEntry_eq_ramanujanCotangentCoreEntry
    (Q d e : ℕ) (hQ : 0 < Q) (hd : 1 < d) (he : 1 < e)
    (hdQ : d ∣ Q) (heQ : e ∣ Q) :
    packetDifferenceCotangentCoreEntry Q d e = ramanujanCotangentCoreEntry d e := by
  have hpoint (a : d.divisors) (b : e.divisors) := residueDifferenceCotangentCore_eq_V Q
    a.val b.val hQ (Nat.pos_of_mem_divisors a.property) (Nat.pos_of_mem_divisors b.property)
    (dvd_trans (Nat.dvd_of_mem_divisors a.property) hdQ)
    (dvd_trans (Nat.dvd_of_mem_divisors b.property) heQ)
  have hud : (∑ a : d.divisors, (ArithmeticFunction.moebius (d/a.val) : ℝ)) = 0 := by
    rw [Finset.sum_coe_sort d.divisors (fun a : ℕ =>
      (ArithmeticFunction.moebius (d/a) : ℝ))]
    exact sum_moebius_div d hd
  have hue : (∑ b : e.divisors, (ArithmeticFunction.moebius (e/b.val) : ℝ)) = 0 := by
    rw [Finset.sum_coe_sort e.divisors (fun b : ℕ =>
      (ArithmeticFunction.moebius (e/b) : ℝ))]
    exact sum_moebius_div e he
  have hz := zero_sum_single_coordinate_correction
    (fun a : d.divisors => (ArithmeticFunction.moebius (d/a.val) : ℝ))
    (fun a => cotangentV 1 a.val)
    (fun b : e.divisors => (ArithmeticFunction.moebius (e/b.val) : ℝ))
    (fun b => cotangentV 1 b.val) hud hue
  unfold packetDifferenceCotangentCoreEntry
  simp_rw [hpoint]
  unfold ramanujanCotangentCoreEntry
  rw [← divisor_double_sum d e (fun a b =>
    (ArithmeticFunction.moebius (d/a) : ℝ) *
      (ArithmeticFunction.moebius (e/b) : ℝ) * (cotangentV a b + cotangentV b a))]
  have hp (a : d.divisors) (b : e.divisors) :
      (ArithmeticFunction.moebius (d/a.val) : ℝ)*(ArithmeticFunction.moebius (e/b.val) : ℝ)*
        (-(1/2 : ℝ)*(cotangentV a.val b.val+cotangentV b.val a.val-
          cotangentV 1 a.val-cotangentV 1 b.val)) =
      -(1/2 : ℝ)*((ArithmeticFunction.moebius (d/a.val) : ℝ)*
        (ArithmeticFunction.moebius (e/b.val) : ℝ)*(cotangentV a.val b.val+cotangentV b.val a.val)) +
      (1/2 : ℝ)*((ArithmeticFunction.moebius (d/a.val) : ℝ)*
        (ArithmeticFunction.moebius (e/b.val) : ℝ)*(cotangentV 1 a.val+cotangentV 1 b.val)) := by ring
  simp_rw [hp, Finset.sum_add_distrib, ← Finset.mul_sum]
  rw [hz]
  ring

/-- The specified double-cotangent core realizes the actual packet Gram.
Each pair uses its product period; no common-period premise is supplied. -/
theorem packet_inner_eq_specifiedCotangentCore (d e : ℕ) (hd : 1 < d) (he : 1 < e) :
    paretoInner (ramanujanPacket d) (ramanujanPacket e) =
      Real.pi * ramanujanCotangentCoreEntry d e +
        (ArithmeticFunction.vonMangoldt d * (Nat.totient e : ℝ) +
          (Nat.totient d : ℝ) * ArithmeticFunction.vonMangoldt e) / 2 := by
  have hQ : 0 < d*e := Nat.mul_pos (by omega) (by omega)
  have h := packet_inner_eq_differenceCotangentCore (d*e) d e hQ hd he
    (dvd_mul_right d e) (dvd_mul_left e d)
  rw [packetDifferenceCotangentCoreEntry_eq_ramanujanCotangentCoreEntry
    (d*e) d e hQ hd he (dvd_mul_right d e) (dvd_mul_left e d)] at h
  exact h

/-- Legal conductors suffice to identify the originally specified arithmetic
matrix with the actual physical core. All physical providers transfer by this equality. -/
theorem specified_core_eq_derivedCore_of_legal (s : Finset ℕ)
    (hs : ∀ q ∈ s, 1 < q) :
    (fun i j : s => ramanujanCotangentCoreEntry i.val j.val) =
      PhysicalPacketCore.derivedCore s := by
  ext i j
  have h := packet_inner_eq_specifiedCotangentCore i.val j.val
    (hs i.val i.property) (hs j.val j.property)
  simp only [PhysicalPacketCore.derivedCore, ramanujanGramMatrix,
    ramanujanVonMangoldtVector, ramanujanTotientVector]
  apply (eq_div_iff Real.pi_ne_zero).mpr
  linarith

/-- Strict mean-kernel positivity of the originally specified arithmetic core. -/
theorem specified_core_positiveOnMeanKernel_of_legal (s : Finset ℕ)
    (hs : ∀ q ∈ s, 1 < q) :
    RiemannResearch.LinearAlgebra.MeanOneCoreInertia.PositiveOnMeanKernel
      (fun i j : s => ramanujanCotangentCoreEntry i.val j.val)
      (ramanujanTotientVector s) := by
  rw [specified_core_eq_derivedCore_of_legal s hs]
  exact PhysicalPacketCore.derivedCore_positiveOnMeanKernel s hs

/-- A legal family containing an odd prime has a nonsingular specified core. -/
theorem specified_core_det_ne_zero_of_legal (s : Finset ℕ)
    (hs : ∀ q ∈ s, 1 < q) (hodd : ∃ p ∈ s, p.Prime ∧ 2 < p) :
    Matrix.det (fun i j : s => ramanujanCotangentCoreEntry i.val j.val) ≠ 0 := by
  rw [specified_core_eq_derivedCore_of_legal s hs]
  exact PhysicalPacketCore.derivedCore_det_ne_zero s hs hodd

/-- Exact inertia: one negative scalar square and a strictly positive mean kernel. -/
theorem specified_core_lorentz_completion (s : Finset ℕ)
    (hs : ∀ q ∈ s, 1 < q) (hodd : ∃ p ∈ s, p.Prime ∧ 2 < p) (x : s → ℝ) :
    let F : Matrix s s ℝ := fun i j => ramanujanCotangentCoreEntry i.val j.val
    let C := ramanujanTotientVector s ⬝ᵥ (F⁻¹ *ᵥ ramanujanTotientVector s)
    let z := x - ((ramanujanTotientVector s ⬝ᵥ x)/C) •
      (F⁻¹ *ᵥ ramanujanTotientVector s)
    C < 0 ∧ ramanujanTotientVector s ⬝ᵥ z = 0 ∧
      x ⬝ᵥ (F *ᵥ x) = (ramanujanTotientVector s ⬝ᵥ x)^2/C + z ⬝ᵥ (F *ᵥ z) ∧
      (z ≠ 0 → 0 < z ⬝ᵥ (F *ᵥ z)) := by
  dsimp only
  rw [specified_core_eq_derivedCore_of_legal s hs]
  have hC := PhysicalPacketCore.inverseCharge_neg s hs hodd
  have hpos := PhysicalPacketCore.derivedCore_positiveOnMeanKernel s hs
  obtain ⟨hm, he⟩ := RiemannResearch.LinearAlgebra.MeanOneCoreInertia.lorentz_completion
    (PhysicalPacketCore.derivedCore s) (PhysicalPacketCore.derivedCore s)⁻¹
    (ramanujanTotientVector s) x
    (PhysicalPacketCore.derivedCore_mul_inverse s hs hodd)
    (PhysicalPacketCore.derivedCore_transpose s) (ne_of_lt hC)
  exact ⟨hC, hm, he, fun hz => hpos _ hm hz⟩

/-- The explicit constrained optimizer, its mean and exact complete minimum. -/
theorem specified_core_constrainedOptimizer (s : Finset ℕ)
    (hs : ∀ q ∈ s, 1 < q) (hodd : ∃ p ∈ s, p.Prime ∧ 2 < p) :
    let F : Matrix s s ℝ := fun i j => ramanujanCotangentCoreEntry i.val j.val
    let C := ramanujanTotientVector s ⬝ᵥ (F⁻¹ *ᵥ ramanujanTotientVector s)
    let c₀ := (2/C) • (F⁻¹ *ᵥ ramanujanTotientVector s)
    C < 0 ∧ ramanujanTotientVector s ⬝ᵥ c₀ = 2 ∧
      paretoError (PhysicalPacketCore.synthesis s c₀) = 1 + 4*Real.pi/C := by
  dsimp only
  rw [specified_core_eq_derivedCore_of_legal s hs]
  exact ⟨PhysicalPacketCore.inverseCharge_neg s hs hodd,
    PhysicalPacketCore.constrainedOptimizer_totient s hs hodd,
    PhysicalPacketCore.constrainedOptimizer_error s hs hodd⟩

/-- The actual unique constrained minimum, expressed using the specified core. -/
theorem specified_core_constrainedOptimizer_unique_minimum (s : Finset ℕ)
    (hs : ∀ q ∈ s, 1 < q) (hodd : ∃ p ∈ s, p.Prime ∧ 2 < p)
    (c : s → ℝ) (hc : ramanujanTotientVector s ⬝ᵥ c = 2) :
    let F : Matrix s s ℝ := fun i j => ramanujanCotangentCoreEntry i.val j.val
    let C := ramanujanTotientVector s ⬝ᵥ (F⁻¹ *ᵥ ramanujanTotientVector s)
    let c₀ := (2/C) • (F⁻¹ *ᵥ ramanujanTotientVector s)
    1 + 4*Real.pi/C ≤ paretoError (PhysicalPacketCore.synthesis s c) ∧
      (paretoError (PhysicalPacketCore.synthesis s c) = 1 + 4*Real.pi/C ↔ c = c₀) := by
  dsimp only
  rw [specified_core_eq_derivedCore_of_legal s hs]
  exact PhysicalPacketCore.constrainedOptimizer_unique_minimum s hs hodd c hc

/-- The original full Pareto Gram is the proposed rank-two perturbation of
the already specified double-cotangent arithmetic core. -/
theorem ramanujanGramMatrix_eq_rankTwo_specified_core (Q : ℕ) (s : Finset ℕ)
    (hQ : 0 < Q) (hs : ∀ q ∈ s, 1 < q) (hsQ : ∀ q ∈ s, q ∣ Q) :
    ramanujanGramMatrix s = RiemannResearch.LinearAlgebra.RankTwoWoodbury.rankTwoMatrix Real.pi
      (fun i j : s => ramanujanCotangentCoreEntry i.val j.val)
      (ramanujanVonMangoldtVector s) (ramanujanTotientVector s) := by
  rw [specified_core_eq_derivedCore_of_legal s hs]
  exact PhysicalPacketCore.gram_eq_rankTwo_derivedCore s

/-- Exact equality transfers the physical inertia and optimizer declarations
to the initially specified cotangent core, with no analytic core premise. -/
theorem specified_core_eq_derivedCore (Q : ℕ) (s : Finset ℕ)
    (hQ : 0 < Q) (hs : ∀ q ∈ s, 1 < q) (hsQ : ∀ q ∈ s, q ∣ Q) :
    (fun i j : s => ramanujanCotangentCoreEntry i.val j.val) = PhysicalPacketCore.derivedCore s := by
  rw [← arithmeticPacketCore_eq_derivedCore Q s hQ hs hsQ]
  ext i j
  exact (packetDifferenceCotangentCoreEntry_eq_ramanujanCotangentCoreEntry Q i.val j.val hQ
    (hs i.val i.property) (hs j.val j.property)
    (hsQ i.val i.property) (hsQ j.val j.property)).symm

end RiemannResearch.RH.Pareto
