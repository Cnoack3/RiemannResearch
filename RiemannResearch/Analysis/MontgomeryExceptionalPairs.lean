/-
Copyright (c) 2026 RiemannResearch contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: RiemannResearch contributors
-/
import Mathlib.Analysis.MeanInequalities
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Removing exceptional zero copies from a pair sum

For Lamzouri's test functions the absolute summand is bounded by a constant
times a symmetric nonnegative ordinate kernel times an exponential of the
sum of the two absolute scaled horizontal displacements. See (3.4), (3.8)
and Lemmas 2.1 and 2.3 of https://arxiv.org/html/2611.14486v1 .
Here the exponential moment and the crowding moments are explicit inputs.
Direct weighted Hölder on the pairs incident to an exceptional copy retains
the two independent exponents. Occurrence labels may have equal ordinates.
-/

noncomputable section
open scoped BigOperators
namespace RiemannResearch.Analysis.MontgomeryExceptionalPairs

variable {ι : Type*} [DecidableEq ι]

/-- Raw ordinate-kernel row mass, including the diagonal. -/
def rowMass (s : Finset ι) (K : ι → ι → ℝ) (i : ι) : ℝ :=
  ∑ j ∈ s, K i j

/-- All ordered pairs with at least one exceptional occurrence. -/
def incident (s E : Finset ι) : Finset (ι × ι) :=
  (E ×ˢ s) ∪ (s ×ˢ E)

theorem signed_deletion_identity {V : Type*} [AddCommGroup V]
    (s E : Finset ι) (hE : E ⊆ s) (F : ι × ι → V) :
    (∑ e ∈ s ×ˢ s, F e) - (∑ e ∈ (s \ E) ×ˢ (s \ E), F e) =
      ∑ e ∈ incident s E, F e := by
  have hs : incident s E ⊆ s ×ˢ s := by
    intro e he
    rcases Finset.mem_union.mp he with h | h <;>
      obtain ⟨h₁, h₂⟩ := Finset.mem_product.mp h
    · exact Finset.mem_product.mpr ⟨hE h₁, h₂⟩
    · exact Finset.mem_product.mpr ⟨h₁, hE h₂⟩
  have heq : (s ×ˢ s) \ incident s E = (s \ E) ×ˢ (s \ E) := by
    ext e
    simp only [incident, Finset.mem_sdiff, Finset.mem_union, Finset.mem_product]
    tauto
  have h := Finset.sum_sdiff hs (f := F)
  rw [heq] at h
  exact sub_eq_iff_eq_add.mpr (by rw [← h, add_comm])

/-- Pair mass incident to a set with small one-point mass. -/
theorem incident_mass_le (s E : Finset ι) (hE : E ⊆ s) (K : ι → ι → ℝ)
    (hK : ∀ i j, 0 ≤ K i j) (hsym : ∀ i j, K i j = K j i)
    {m δ q R : ℝ} (hm : 0 ≤ m) (hq : 1 ≤ q)
    (hδ : (∑ _i ∈ E, m) ≤ δ)
    (hR : (∑ i ∈ s, m * rowMass s K i ^ q) ≤ R) :
    (∑ e ∈ incident s E, m * K e.1 e.2) ≤ 2 * δ ^ (1 - q⁻¹) * R ^ q⁻¹ := by
  have hr i : 0 ≤ rowMass s K i := Finset.sum_nonneg fun j _ => hK i j
  have hq0 : 0 < q := by linarith
  have hq1 : 0 ≤ 1 - q⁻¹ := sub_nonneg.mpr (inv_le_one_of_one_le₀ hq)
  have hsmall := Real.inner_le_weight_mul_Lp_of_nonneg E hq (fun _ => m)
    (rowMass s K) (fun _ => hm) hr
  have hR' : (∑ i ∈ E, m * rowMass s K i ^ q) ≤ R :=
    (Finset.sum_le_sum_of_subset_of_nonneg hE
      (fun i _ _ => mul_nonneg hm (Real.rpow_nonneg (hr i) _))).trans hR
  have hone : (∑ i ∈ E, m * rowMass s K i) ≤ δ ^ (1 - q⁻¹) * R ^ q⁻¹ :=
    hsmall.trans (mul_le_mul
      (Real.rpow_le_rpow (Finset.sum_nonneg (fun _ _ => hm)) hδ hq1)
      (Real.rpow_le_rpow (Finset.sum_nonneg (fun i _ =>
        mul_nonneg hm (Real.rpow_nonneg (hr i) _))) hR' (inv_nonneg.mpr hq0.le))
      (Real.rpow_nonneg (Finset.sum_nonneg (fun i _ =>
        mul_nonneg hm (Real.rpow_nonneg (hr i) _))) _)
      (Real.rpow_nonneg ((Finset.sum_nonneg fun _ _ => hm).trans hδ) _))
  have hleft : (∑ e ∈ E ×ˢ s, m * K e.1 e.2) = ∑ i ∈ E, m * rowMass s K i := by
    rw [Finset.sum_product]
    simp only [rowMass, Finset.mul_sum]
  have hright : (∑ e ∈ s ×ˢ E, m * K e.1 e.2) = ∑ i ∈ E, m * rowMass s K i := by
    rw [Finset.sum_product, Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    simp only [rowMass, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by rw [hsym j i]
  have hboth := Finset.sum_union_inter (s₁ := E ×ˢ s) (s₂ := s ×ˢ E)
    (f := fun e : ι × ι => m * K e.1 e.2)
  have hpos : 0 ≤ ∑ e ∈ (E ×ˢ s) ∩ (s ×ˢ E), m * K e.1 e.2 :=
    Finset.sum_nonneg fun e _ => mul_nonneg hm (hK _ _)
  rw [hleft, hright] at hboth
  unfold incident
  linarith

omit [DecidableEq ι] in
/-- The pair exponential moment costs one horizontal moment at twice the
frequency, with an independently adjustable Hölder margin for the row mass. -/
theorem pair_exp_moment_le (s : Finset ι) (K : ι → ι → ℝ)
    (hK : ∀ i j, 0 ≤ K i j) (hsym : ∀ i j, K i j = K j i)
    (X : ι → ℝ) {m p θ r t D R : ℝ} (hm : 0 ≤ m)
    (hrt : Real.HolderConjugate r t)
    (hD : (∑ i ∈ s, m * Real.exp ((2 * p * θ * r) * X i)) ≤ D)
    (hR : (∑ i ∈ s, m * rowMass s K i ^ t) ≤ R) :
    (∑ e ∈ s ×ˢ s, (m * K e.1 e.2) * Real.exp (θ * (X e.1 + X e.2)) ^ p)
      ≤ (D / r + R / t) := by
  let A (i : ι) := Real.exp (2 * p * θ * X i)
  have hmajor (i j : ι) : Real.exp (θ * (X i + X j)) ^ p ≤ (A i + A j) / 2 := by
    let u := Real.exp (p * θ * X i)
    let v := Real.exp (p * θ * X j)
    have hu : A i = u ^ 2 := by
      dsimp [A, u]
      rw [pow_two, ← Real.exp_add]
      congr 1
      ring
    have hv : A j = v ^ 2 := by
      dsimp [A, v]
      rw [pow_two, ← Real.exp_add]
      congr 1
      ring
    have huv : Real.exp (θ * (X i + X j)) ^ p = u*v := by
      dsimp [u, v]
      rw [← Real.exp_mul, ← Real.exp_add]
      congr 1
      ring
    rw [hu, hv, huv]
    nlinarith [sq_nonneg (u-v)]
  have hrow (i : ι) : 0 ≤ rowMass s K i := Finset.sum_nonneg fun j _ => hK i j
  have hrows : (∑ i ∈ s, m * (A i * rowMass s K i)) ≤ D / r + R / t := by
    calc
      _ ≤ ∑ i ∈ s, m * ((A i) ^ r / r + rowMass s K i ^ t / t) :=
        Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left
          (Real.young_inequality_of_nonneg (Real.exp_nonneg _) (hrow i) hrt) hm
      _ = (∑ i ∈ s, m * Real.exp ((2 * p * θ * r) * X i)) / r +
        (∑ i ∈ s, m * rowMass s K i ^ t) / t := by
          simp only [A, ← Real.exp_mul, Finset.sum_div, ← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro i _
          rw [show 2 * p * θ * X i * r = 2 * p * θ * r * X i by ring]
          ring
      _ ≤ _ := add_le_add (div_le_div_of_nonneg_right hD hrt.pos.le)
        (div_le_div_of_nonneg_right hR hrt.symm.pos.le)
  have hcol : (∑ i ∈ s, ∑ j ∈ s, (m * K i j) * A j) =
      ∑ i ∈ s, ∑ j ∈ s, (m * K i j) * A i := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by rw [hsym j i]
  have hleft : (∑ i ∈ s, ∑ j ∈ s, (m * K i j) * A i) =
      ∑ i ∈ s, m * (A i * rowMass s K i) := by
    apply Finset.sum_congr rfl
    intro i _
    simp only [rowMass, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  calc
    _ ≤ ∑ e ∈ s ×ˢ s, (m * K e.1 e.2) * ((A e.1 + A e.2) / 2) :=
      Finset.sum_le_sum fun e _ => mul_le_mul_of_nonneg_left (hmajor _ _) (mul_nonneg hm (hK _ _))
    _ = ∑ i ∈ s, m * (A i * rowMass s K i) := by
      simp only [← mul_div_assoc, ← Finset.sum_div]
      rw [Finset.sum_product]
      simp only [mul_add, Finset.sum_add_distrib]
      rw [hcol, hleft]
      ring
    _ ≤ _ := hrows

/-- Direct deletion bound. The mass exponent is
`(1 - q⁻¹) * (1 - p⁻¹)`; the other factors involve only the supplied moments. -/
theorem incident_exp_le (s E : Finset ι) (hE : E ⊆ s) (K : ι → ι → ℝ)
    (hK : ∀ i j, 0 ≤ K i j) (hsym : ∀ i j, K i j = K j i)
    (X : ι → ℝ) {m δ θ p q r t D Q R : ℝ} (hm : 0 ≤ m)
    (hp : 1 ≤ p) (hq : 1 ≤ q) (hrt : Real.HolderConjugate r t)
    (hδ : (∑ _i ∈ E, m) ≤ δ)
    (hQ : (∑ i ∈ s, m * rowMass s K i ^ q) ≤ Q)
    (hD : (∑ i ∈ s, m * Real.exp ((2 * p * θ * r) * X i)) ≤ D)
    (hR : (∑ i ∈ s, m * rowMass s K i ^ t) ≤ R) :
    (∑ e ∈ incident s E, (m * K e.1 e.2) * Real.exp (θ * (X e.1 + X e.2))) ≤
      (2 * δ ^ (1 - q⁻¹) * Q ^ q⁻¹) ^ (1 - p⁻¹) *
        (D / r + R / t) ^ p⁻¹ := by
  have hs : incident s E ⊆ s ×ˢ s := by
    intro e he
    rcases Finset.mem_union.mp he with h | h <;>
      obtain ⟨h₁, h₂⟩ := Finset.mem_product.mp h
    · exact Finset.mem_product.mpr ⟨hE h₁, h₂⟩
    · exact Finset.mem_product.mpr ⟨h₁, hE h₂⟩
  have hw (e : ι × ι) : 0 ≤ m * K e.1 e.2 := mul_nonneg hm (hK _ _)
  have h := Real.inner_le_weight_mul_Lp_of_nonneg (incident s E) hp
    (fun e => m * K e.1 e.2) (fun e => Real.exp (θ * (X e.1 + X e.2))) hw
    (fun _ => Real.exp_nonneg _)
  have hm' := incident_mass_le s E hE K hK hsym hm hq hδ hQ
  have hsub : (∑ e ∈ incident s E,
      (m * K e.1 e.2) * Real.exp (θ * (X e.1 + X e.2)) ^ p) ≤
      (D / r + R / t) :=
    (Finset.sum_le_sum_of_subset_of_nonneg hs (fun e _ _ => mul_nonneg
      (hw e) (Real.rpow_nonneg (Real.exp_nonneg _) _))).trans
      (pair_exp_moment_le s K hK hsym X hm hrt hD hR)
  have hm0 := Finset.sum_nonneg (s := incident s E) (fun e _ => hw e)
  have he0 : 0 ≤ ∑ e ∈ incident s E,
      (m * K e.1 e.2) * Real.exp (θ * (X e.1 + X e.2)) ^ p :=
    Finset.sum_nonneg (fun e _ => mul_nonneg (hw e) (Real.rpow_nonneg (Real.exp_nonneg _) _))
  exact h.trans (mul_le_mul
    (Real.rpow_le_rpow hm0 hm' (sub_nonneg.mpr (inv_le_one_of_one_le₀ hp)))
    (Real.rpow_le_rpow he0 hsub (inv_nonneg.mpr (by linarith)))
    (Real.rpow_nonneg he0 _) (Real.rpow_nonneg (hm0.trans hm') _))


/-- Optimize two independent Hölder exponents. Every strict exponent below
`1 - 7*θ/4` is obtained at a horizontal moment order strictly below `8/7`. -/
theorem exists_removal_exponents {θ κ : ℝ}
    (hθ : 0 < θ) (hκ : 0 ≤ κ) (hgap : κ < 1 - 7 * θ / 4) :
    ∃ p q r t : ℝ, 1 < p ∧ 1 < q ∧ Real.HolderConjugate r t ∧
      2 * p * θ * r < 8 / 7 ∧ κ < (1 - q⁻¹) * (1 - p⁻¹) := by
  obtain ⟨v, hv₁, hv₂⟩ := exists_between (show 7 * θ / 4 < 1 - κ by linarith)
  have hv : 0 < v := by linarith
  have hv' : v < 1 := by linarith
  obtain ⟨w, hw₁, hw₂⟩ := exists_between (show (7 * θ / 4) / v < 1 by
    apply (div_lt_iff₀ hv).mpr
    linarith)
  have hw : 0 < w := lt_trans (by positivity) hw₁
  have hzw : 0 < 1 - κ / (1 - v) := by
    apply sub_pos.mpr
    apply (div_lt_iff₀ (sub_pos.mpr hv')).mpr
    linarith
  obtain ⟨z, hz₁, hz₂⟩ := exists_between hzw
  have hz' : z < 1 := hz₂.trans_le (sub_le_self _ (div_nonneg hκ (sub_pos.mpr hv').le))
  refine ⟨v⁻¹, z⁻¹, w⁻¹, (1 - w)⁻¹, ?_, ?_,
    Real.HolderConjugate.inv_one_sub_inv hw hw₂, ?_, ?_⟩
  · rw [← one_div, lt_div_iff₀ hv]
    linarith
  · rw [← one_div, lt_div_iff₀ hz₁]
    linarith
  · have ha := (div_lt_iff₀ hv).mp hw₁
    rw [show 2 * v⁻¹ * θ * w⁻¹ = (2 * θ) / (v * w) by ring, div_lt_iff₀ (mul_pos hv hw)]
    linarith only [ha]
  · simp only [inv_inv]
    have hz : κ / (1 - v) < 1 - z := by linarith
    exact (div_lt_iff₀ (sub_pos.mpr hv')).mp hz


/-- Absolute control of the signed difference of the complete and retained
pair sums. The test can have complex values and the exceptional set is arbitrary. -/
theorem norm_signed_deletion_le {V : Type*} [SeminormedAddCommGroup V]
    (s E : Finset ι) (hE : E ⊆ s) (K : ι → ι → ℝ)
    (hK : ∀ i j, 0 ≤ K i j) (hsym : ∀ i j, K i j = K j i)
    (X : ι → ℝ) (F : ι × ι → V) {m δ θ p q r t D Q R A : ℝ}
    (hm : 0 ≤ m) (hA : 0 ≤ A) (hp : 1 ≤ p) (hq : 1 ≤ q)
    (hrt : Real.HolderConjugate r t) (hδ : (∑ _i ∈ E, m) ≤ δ)
    (hQ : (∑ i ∈ s, m * rowMass s K i ^ q) ≤ Q)
    (hD : (∑ i ∈ s, m * Real.exp ((2 * p * θ * r) * X i)) ≤ D)
    (hR : (∑ i ∈ s, m * rowMass s K i ^ t) ≤ R)
    (hF : ∀ e ∈ incident s E, ‖F e‖ ≤
      A * ((m * K e.1 e.2) * Real.exp (θ * (X e.1 + X e.2)))) :
    ‖(∑ e ∈ s ×ˢ s, F e) - (∑ e ∈ (s \ E) ×ˢ (s \ E), F e)‖ ≤
      A * ((2 * δ ^ (1 - q⁻¹) * Q ^ q⁻¹) ^ (1 - p⁻¹) *
        (D / r + R / t) ^ p⁻¹) := by
  rw [signed_deletion_identity s E hE F]
  refine (norm_sum_le _ _).trans ((Finset.sum_le_sum hF).trans ?_)
  rw [← Finset.mul_sum]
  exact mul_le_mul_of_nonneg_left (incident_exp_le s E hE K hK hsym X hm hp hq
    hrt hδ hQ hD hR) hA


omit [DecidableEq ι] in
/-- The bounded-strip Taylor factor can be summed against actual crowding
rows at the cost of any fixed row moment. This keeps the quadratic
displacements inside the mean when a scaled strip of width one is retained. -/
theorem retained_quadratic_row_le (s G : Finset ι) (hG : G ⊆ s)
    (X Y : ι → ℝ) (hGbox : ∀ i ∈ G, X i ^ 2 ≤ 1) (hY : ∀ i, 0 ≤ Y i)
    {m ε q R : ℝ} (hm : 0 ≤ m) (hq : 1 ≤ q)
    (hε : (∑ i ∈ s, m * X i ^ 2) ≤ ε)
    (hR : (∑ i ∈ s, m * Y i ^ q) ≤ R) :
    (∑ i ∈ G, (m * X i ^ 2) * Y i) ≤ ε ^ (1-q⁻¹) * R ^ q⁻¹ := by
  have hweight i : 0 ≤ m * X i ^ 2 := mul_nonneg hm (sq_nonneg _)
  have hε' : (∑ i ∈ G, m * X i ^ 2) ≤ ε :=
    (Finset.sum_le_sum_of_subset_of_nonneg hG fun i _ _ => hweight i).trans hε
  have hyq i : 0 ≤ Y i ^ q := Real.rpow_nonneg (hY i) _
  have hR' : (∑ i ∈ G, (m * X i ^ 2) * Y i ^ q) ≤ R := by
    calc
      _ ≤ ∑ i ∈ G, m * Y i ^ q := by
        apply Finset.sum_le_sum
        intro i hi
        exact mul_le_mul_of_nonneg_right ((mul_le_mul_of_nonneg_left
          (hGbox i hi) hm).trans_eq (mul_one _)) (hyq i)
      _ ≤ _ := (Finset.sum_le_sum_of_subset_of_nonneg hG
        (fun i _ _ => mul_nonneg hm (hyq i))).trans hR
  have hw0 := Finset.sum_nonneg (s := G) (fun i _ => hweight i)
  have hR0 : 0 ≤ ∑ i ∈ G, (m * X i ^ 2) * Y i ^ q :=
    Finset.sum_nonneg fun i _ => mul_nonneg (hweight i) (hyq i)
  apply (Real.inner_le_weight_mul_Lp_of_nonneg G hq _ _ hweight hY).trans
  exact mul_le_mul
    (Real.rpow_le_rpow hw0 hε' (sub_nonneg.mpr (inv_le_one_of_one_le₀ hq)))
    (Real.rpow_le_rpow hR0 hR' (inv_nonneg.mpr (by linarith)))
    (Real.rpow_nonneg hR0 _) (Real.rpow_nonneg (hw0.trans hε') _)

end RiemannResearch.Analysis.MontgomeryExceptionalPairs
