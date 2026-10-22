import Mathlib.Data.Real.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Finite triangular energies, threshold counts, and collision atoms

These are deterministic finite identities and inequalities. A label may be an ordered
pair of zero occurrences, and its distance may be a scaled ordinate difference. The
normalizing real count `N` is separate from the cardinality of the label set; in a pair
application one normally uses the number of ordinates, not the number of pairs.

All normalization inequalities assume `0 ≤ N`, so they also hold algebraically for
`N = 0` under totalized division. A probability or empirical-count interpretation
requires the corresponding positive count. No zero-distribution input or RH premise
is used.
Source: elementary hinge and secant argument in the user's
ordinate-pair-correlation program, 2026-10-11.
-/

open scoped BigOperators

namespace RiemannResearch.Analysis.OrdinateTriangleSecants

def hinge (lam d : ℝ) : ℝ := max (lam - |d|) 0

lemma hinge_nonneg (lam d : ℝ) : 0 ≤ hinge lam d :=
  le_max_right _ _

lemma hinge_of_abs_le {lam d : ℝ} (h : |d| ≤ lam) :
    hinge lam d = lam - |d| := by
  exact max_eq_left (sub_nonneg.mpr h)

lemma hinge_of_le_abs {lam d : ℝ} (h : lam ≤ |d|) :
    hinge lam d = 0 := by
  exact max_eq_right (sub_nonpos.mpr h)

@[simp] lemma hinge_zero (d : ℝ) : hinge 0 d = 0 :=
  hinge_of_le_abs (abs_nonneg d)

lemma hinge_mono {a b : ℝ} (hab : a ≤ b) (d : ℝ) :
    hinge a d ≤ hinge b d := by
  exact max_le_max (sub_le_sub_right hab _) le_rfl

/-- Convexity of one triangular summand as a function of its window width. -/
lemma hinge_convex (a b d t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    hinge ((1 - t) * a + t * b) d ≤
      (1 - t) * hinge a d + t * hinge b d := by
  have ha : a - |d| ≤ hinge a d := le_max_left _ _
  have hb : b - |d| ≤ hinge b d := le_max_left _ _
  have ha' := mul_le_mul_of_nonneg_left ha (sub_nonneg.mpr ht1)
  have hb' := mul_le_mul_of_nonneg_left hb ht0
  have hna := mul_nonneg (sub_nonneg.mpr ht1) (hinge_nonneg a d)
  have hnb := mul_nonneg ht0 (hinge_nonneg b d)
  change max _ 0 ≤ _
  apply max_le
  · nlinarith
  · exact add_nonneg hna hnb

/-- The lower secant uses the inclusive count at the left endpoint. -/
lemma hinge_sub_lower (a b d : ℝ) (hab : a < b) :
    (b - a) * (if |d| ≤ a then (1 : ℝ) else 0) ≤ hinge b d - hinge a d := by
  split_ifs with h
  · rw [hinge_of_abs_le h, hinge_of_abs_le (le_trans h hab.le)]
    simp only [mul_one]
    linarith
  · simpa only [mul_zero] using sub_nonneg.mpr (hinge_mono hab.le d)

/-- The upper secant uses the strict count at the right endpoint. -/
lemma hinge_sub_upper (a b d : ℝ) (hab : a < b) :
    hinge b d - hinge a d ≤ (b - a) * (if |d| < b then (1 : ℝ) else 0) := by
  split_ifs with h
  · rw [hinge_of_abs_le h.le]
    have ha : a - |d| ≤ hinge a d := le_max_left _ _
    simp only [mul_one]
    linarith
  · have hb : b ≤ |d| := le_of_not_gt h
    rw [hinge_of_le_abs hb, hinge_of_le_abs (le_trans hab.le hb)]
    simp

variable {ι : Type*}

noncomputable def triangleSum (s : Finset ι) (d : ι → ℝ) (lam : ℝ) : ℝ :=
  ∑ i ∈ s, hinge lam (d i)

noncomputable def strictSum (s : Finset ι) (d : ι → ℝ) (lam : ℝ) : ℝ :=
  ∑ i ∈ s, if |d i| < lam then (1 : ℝ) else 0

noncomputable def inclusiveSum (s : Finset ι) (d : ι → ℝ) (lam : ℝ) : ℝ :=
  ∑ i ∈ s, if |d i| ≤ lam then (1 : ℝ) else 0

noncomputable def triangleEnergy (s : Finset ι) (d : ι → ℝ) (N lam : ℝ) : ℝ :=
  triangleSum s d lam / N

noncomputable def strictMass (s : Finset ι) (d : ι → ℝ) (N lam : ℝ) : ℝ :=
  strictSum s d lam / N

noncomputable def inclusiveMass (s : Finset ι) (d : ι → ℝ) (N lam : ℝ) : ℝ :=
  inclusiveSum s d lam / N

noncomputable def collisionMass (s : Finset ι) (d : ι → ℝ) (N : ℝ) : ℝ :=
  inclusiveMass s d N 0

@[simp] lemma triangleSum_zero (s : Finset ι) (d : ι → ℝ) :
    triangleSum s d 0 = 0 := by
  simp [triangleSum]

@[simp] lemma triangleEnergy_zero (s : Finset ι) (d : ι → ℝ) (N : ℝ) :
    triangleEnergy s d N 0 = 0 := by
  simp [triangleEnergy]

lemma collisionMass_eq_zero_distance_sum (s : Finset ι) (d : ι → ℝ) (N : ℝ) :
    collisionMass s d N = (∑ i ∈ s, if d i = 0 then (1 : ℝ) else 0) / N := by
  simp [collisionMass, inclusiveMass, inclusiveSum]

lemma triangleSum_convex (s : Finset ι) (d : ι → ℝ)
    (a b t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    triangleSum s d ((1 - t) * a + t * b) ≤
      (1 - t) * triangleSum s d a + t * triangleSum s d b := by
  unfold triangleSum
  calc
    (∑ i ∈ s, hinge ((1 - t) * a + t * b) (d i)) ≤
        ∑ i ∈ s, ((1 - t) * hinge a (d i) + t * hinge b (d i)) := by
      exact Finset.sum_le_sum fun i _ => hinge_convex a b (d i) t ht0 ht1
    _ = _ := by rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]

lemma triangleEnergy_convex (s : Finset ι) (d : ι → ℝ)
    (N a b t : ℝ) (hN : 0 ≤ N) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    triangleEnergy s d N ((1 - t) * a + t * b) ≤
      (1 - t) * triangleEnergy s d N a + t * triangleEnergy s d N b := by
  unfold triangleEnergy
  calc
    _ ≤ ((1 - t) * triangleSum s d a + t * triangleSum s d b) / N :=
      div_le_div_of_nonneg_right (triangleSum_convex s d a b t ht0 ht1) hN
    _ = _ := by ring

lemma strictSum_le_inclusiveSum (s : Finset ι) (d : ι → ℝ) (lam : ℝ) :
    strictSum s d lam ≤ inclusiveSum s d lam := by
  unfold strictSum inclusiveSum
  apply Finset.sum_le_sum
  intro i _
  by_cases h : |d i| < lam
  · simp [h, h.le]
  · simp only [h, if_false]
    split_ifs <;> norm_num

lemma strictMass_le_inclusiveMass (s : Finset ι) (d : ι → ℝ)
    (N lam : ℝ) (hN : 0 ≤ N) :
    strictMass s d N lam ≤ inclusiveMass s d N lam :=
  div_le_div_of_nonneg_right (strictSum_le_inclusiveSum s d lam) hN

lemma triangleSum_sub_lower (s : Finset ι) (d : ι → ℝ)
    (a b : ℝ) (hab : a < b) :
    (b - a) * inclusiveSum s d a ≤ triangleSum s d b - triangleSum s d a := by
  unfold inclusiveSum triangleSum
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  exact Finset.sum_le_sum fun i _ => hinge_sub_lower a b (d i) hab

lemma triangleSum_sub_upper (s : Finset ι) (d : ι → ℝ)
    (a b : ℝ) (hab : a < b) :
    triangleSum s d b - triangleSum s d a ≤ (b - a) * strictSum s d b := by
  unfold strictSum triangleSum
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  exact Finset.sum_le_sum fun i _ => hinge_sub_upper a b (d i) hab

lemma triangleEnergy_sub_lower (s : Finset ι) (d : ι → ℝ)
    (N a b : ℝ) (hN : 0 ≤ N) (hab : a < b) :
    (b - a) * inclusiveMass s d N a ≤
      triangleEnergy s d N b - triangleEnergy s d N a := by
  have h := div_le_div_of_nonneg_right (triangleSum_sub_lower s d a b hab) hN
  simpa only [inclusiveMass, triangleEnergy, mul_div_assoc, sub_div] using h

lemma triangleEnergy_sub_upper (s : Finset ι) (d : ι → ℝ)
    (N a b : ℝ) (hN : 0 ≤ N) (hab : a < b) :
    triangleEnergy s d N b - triangleEnergy s d N a ≤
      (b - a) * strictMass s d N b := by
  have h := div_le_div_of_nonneg_right (triangleSum_sub_upper s d a b hab) hN
  simpa only [strictMass, triangleEnergy, mul_div_assoc, sub_div] using h

/-- Exact strict/inclusive endpoint convention for every finite secant. -/
theorem triangleEnergy_secant_bounds (s : Finset ι) (d : ι → ℝ)
    (N a b : ℝ) (hN : 0 ≤ N) (hab : a < b) :
    inclusiveMass s d N a ≤
        (triangleEnergy s d N b - triangleEnergy s d N a) / (b - a) ∧
      (triangleEnergy s d N b - triangleEnergy s d N a) / (b - a) ≤
        strictMass s d N b := by
  have hpos : 0 < b - a := sub_pos.mpr hab
  constructor
  · apply (le_div_iff₀ hpos).2
    simpa only [mul_comm] using triangleEnergy_sub_lower s d N a b hN hab
  · apply (div_le_iff₀ hpos).2
    simpa only [mul_comm] using triangleEnergy_sub_upper s d N a b hN hab

theorem triangleEnergy_centered_secants (s : Finset ι) (d : ι → ℝ)
    (N lam eps : ℝ) (hN : 0 ≤ N) (heps : 0 < eps) :
    (triangleEnergy s d N lam - triangleEnergy s d N (lam - eps)) / eps ≤
        strictMass s d N lam ∧
      strictMass s d N lam ≤ inclusiveMass s d N lam ∧
      inclusiveMass s d N lam ≤
        (triangleEnergy s d N (lam + eps) - triangleEnergy s d N lam) / eps := by
  have hl := triangleEnergy_secant_bounds s d N (lam - eps) lam hN (by linarith)
  have hr := triangleEnergy_secant_bounds s d N lam (lam + eps) hN (by linarith)
  have hleft : lam - (lam - eps) = eps := by ring
  have hright : (lam + eps) - lam = eps := by ring
  exact ⟨by simpa only [hleft] using hl.2,
    strictMass_le_inclusiveMass s d N lam hN,
    by simpa only [hright] using hr.1⟩

/-- Zero-distance labels contribute exactly a linear collision atom to every window. -/
theorem collisionMass_mul_le_triangleEnergy (s : Finset ι) (d : ι → ℝ)
    (N eps : ℝ) (hN : 0 ≤ N) (heps : 0 ≤ eps) :
    collisionMass s d N * eps ≤ triangleEnergy s d N eps := by
  by_cases hzero : eps = 0
  · simp [hzero]
  · have hpos : 0 < eps := lt_of_le_of_ne heps (Ne.symm hzero)
    have h := triangleEnergy_sub_lower s d N 0 eps hN hpos
    simpa only [sub_zero, triangleEnergy_zero, collisionMass, mul_comm] using h

/-- The whole window energy is bounded by its width times the strict threshold mass. -/
theorem triangleEnergy_le_width_mul_strictMass (s : Finset ι) (d : ι → ℝ)
    (N eps : ℝ) (hN : 0 ≤ N) (heps : 0 < eps) :
    triangleEnergy s d N eps ≤ eps * strictMass s d N eps := by
  have h := triangleEnergy_sub_upper s d N 0 eps hN heps
  simpa only [sub_zero, triangleEnergy_zero] using h

end RiemannResearch.Analysis.OrdinateTriangleSecants

namespace RiemannResearch.Analysis.OrdinateTriangleSecants

variable {ι : Type*}

/-- Three finite energy-error bounds transfer target secants to the inclusive count.
The target function need not be differentiable or convex. -/
theorem inclusiveMass_of_three_energy_errors (s : Finset ι) (d : ι → ℝ)
    (G : ℝ → ℝ) (N lam eps eta B : ℝ)
    (hN : 0 ≤ N) (heps : 0 < eps) (_heta : 0 ≤ eta)
    (hminus : |triangleEnergy s d N (lam - eps) - G (lam - eps)| ≤ eta)
    (hcenter : |triangleEnergy s d N lam - G lam| ≤ eta)
    (hplus : |triangleEnergy s d N (lam + eps) - G (lam + eps)| ≤ eta)
    (hGleft : B - eps ≤ (G lam - G (lam - eps)) / eps)
    (hGright : (G (lam + eps) - G lam) / eps ≤ B + eps) :
    B - eps - 2 * eta / eps ≤ inclusiveMass s d N lam ∧
      inclusiveMass s d N lam ≤ B + eps + 2 * eta / eps := by
  have hm := abs_le.mp hminus
  have hc := abs_le.mp hcenter
  have hp := abs_le.mp hplus
  have hleftError :
      (G lam - G (lam - eps)) - 2 * eta ≤
        triangleEnergy s d N lam - triangleEnergy s d N (lam - eps) := by
    linarith [hm.2, hc.1]
  have hrightError :
      triangleEnergy s d N (lam + eps) - triangleEnergy s d N lam ≤
        (G (lam + eps) - G lam) + 2 * eta := by
    linarith [hp.2, hc.1]
  have hl := div_le_div_of_nonneg_right hleftError heps.le
  have hr := div_le_div_of_nonneg_right hrightError heps.le
  rw [sub_div] at hl
  rw [add_div] at hr
  obtain ⟨hsecLeft, hcounts, hsecRight⟩ :=
    triangleEnergy_centered_secants s d N lam eps hN heps
  constructor
  · linarith
  · linarith

/-- Equivalent target hypotheses before division by the window width. -/
theorem inclusiveMass_of_three_energy_errors_mul (s : Finset ι) (d : ι → ℝ)
    (G : ℝ → ℝ) (N lam eps eta B : ℝ)
    (hN : 0 ≤ N) (heps : 0 < eps) (heta : 0 ≤ eta)
    (hminus : |triangleEnergy s d N (lam - eps) - G (lam - eps)| ≤ eta)
    (hcenter : |triangleEnergy s d N lam - G lam| ≤ eta)
    (hplus : |triangleEnergy s d N (lam + eps) - G (lam + eps)| ≤ eta)
    (hGleft : eps * (B - eps) ≤ G lam - G (lam - eps))
    (hGright : G (lam + eps) - G lam ≤ eps * (B + eps)) :
    B - eps - 2 * eta / eps ≤ inclusiveMass s d N lam ∧
      inclusiveMass s d N lam ≤ B + eps + 2 * eta / eps := by
  apply inclusiveMass_of_three_energy_errors s d G N lam eps eta B hN heps heta
    hminus hcenter hplus
  · apply (le_div_iff₀ heps).2
    simpa only [mul_comm] using hGleft
  · apply (div_le_iff₀ heps).2
    simpa only [mul_comm] using hGright

end RiemannResearch.Analysis.OrdinateTriangleSecants
