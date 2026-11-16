import RiemannResearch.RH.ExactHeadFloorExtension
import RiemannResearch.RH.ExactHeadGreenPareto
import RiemannResearch.RH.ExactHeadGreenClosure

/-!
# Concrete Mobius-head floor profiles
A finite divisor-supported floor polynomial with Mobius coefficients below x
has an actual legal residue extension, an exact head, and the exact terminal
energy split. Its upper normal equations give the signed root identity.
Only the uniform relative profile energy and one-sided signed moment estimates
remain hypotheses in the final conditional criterion.
-/
noncomputable section
open scoped BigOperators
namespace RiemannResearch.RH.Pareto.MobiusHeadGreen
open RiemannResearch.Analysis.FiniteProfileEnergy
open RiemannResearch.Analysis.GreenProfileBounds
open RiemannResearch.RH.ExactHeadGreenProfile
open RiemannResearch.RH.ArithmeticCumulative
open FloorProfileExtension

def residual (P : ℕ) (c : ℕ → ℝ) (r : ℕ) : ℝ :=
  (∑ d ∈ Finset.Icc 1 P, c d * grid d r) - 1

def q (P : ℕ) (c : ℕ → ℝ) : ℝ :=
  energy (Finset.Icc 1 (P - 1)) (progressionWeight P) (residual P c)

def tau (P : ℕ) (c : ℕ → ℝ) : ℝ :=
  pairing (Finset.Icc 1 (P - 1)) (progressionWeight P) (residual P c) (fun _ => 1)

def profile (P : ℕ) (c : ℕ → ℝ) (d : ℕ) : ℝ :=
  (d : ℝ) * score (Finset.Icc 1 (P - 1)) (progressionWeight P) (residual P c) d

theorem mobius_floor_head (P x : ℕ) (hx : x ≤ P) (c : ℕ → ℝ)
    (hlow : ∀ d, 1 ≤ d → d ≤ x → c d = (ArithmeticFunction.moebius d : ℝ))
    (n : ℕ) (hn : 0 < n) (hnx : n ≤ x) :
    (∑ d ∈ Finset.Icc 1 P, c d * grid d n) = 1 := by
  have hsub : Finset.Icc 1 x ⊆ Finset.Icc 1 P := Finset.Icc_subset_Icc_right hx
  calc
    _ = ∑ d ∈ Finset.Icc 1 x, c d * grid d n := by
      symm
      apply Finset.sum_subset hsub
      intro d hd hdx
      have hxd : x < d := by
        have hd1 := (Finset.mem_Icc.mp hd).1
        by_contra! h
        exact hdx (Finset.mem_Icc.mpr ⟨hd1,h⟩)
      simp [grid,Nat.div_eq_of_lt (hnx.trans_lt hxd)]
    _ = ∑ d ∈ Finset.Icc 1 x, (ArithmeticFunction.moebius d : ℝ) * (n / d : ℕ) := by
      apply Finset.sum_congr rfl
      intro d hd
      rw [hlow d (Finset.mem_Icc.mp hd).1 (Finset.mem_Icc.mp hd).2]
      rfl
    _ = 1 := finite_mobius_floor_sum x n hn hnx

theorem residual_head (P x : ℕ) (hx : x ≤ P) (c : ℕ → ℝ)
    (hlow : ∀ d, 1 ≤ d → d ≤ x → c d = (ArithmeticFunction.moebius d : ℝ))
    (n : ℕ) (hn : 0 < n) (hnx : n ≤ x) : residual P c n = 0 := by
  unfold residual
  rw [mobius_floor_head P x hx c hlow n hn hnx, sub_self]

theorem q_nonneg (P : ℕ) (c : ℕ → ℝ) : 0 ≤ q P c :=
  energy_nonneg _ _ _ (fun r _ => progressionWeight_nonneg P r)

theorem signed_root_identity (P x : ℕ) (hx : x ≤ P) (c : ℕ → ℝ)
    (hlow : ∀ d, 1 ≤ d → d ≤ x → c d = (ArithmeticFunction.moebius d : ℝ))
    (hupper : ∀ d ∈ Finset.Icc 1 P, x < d → c d ≠ 0 →
      score (Finset.Icc 1 (P - 1)) (progressionWeight P) (residual P c) d = 0) :
    MobiusAffineProfile.signedSum x (profile P c) = q P c + tau P c := by
  have hfilter : (Finset.Icc 1 P).filter (fun d => d ≤ x) = Finset.Icc 1 x := by
    ext d
    simp only [Finset.mem_filter, Finset.mem_Icc]
    omega
  have hroot := root_identity_of_weighted_upper (Finset.Icc 1 (P - 1)) (Finset.Icc 1 P)
    (progressionWeight P) (residual P c) (residual P c) c x
    (fun _ => rfl) (by simp [pairing,energy,pow_two,mul_assoc]) (by
      intro d hd hxd
      by_cases hc : c d = 0
      · simp [hc]
      · rw [hupper d hd hxd hc, mul_zero])
  rw [hfilter] at hroot
  change _ = energy _ _ _ + pairing _ _ _ _
  rw [← hroot]
  unfold MobiusAffineProfile.signedSum profile
  apply Finset.sum_congr rfl
  intro d hd
  rw [hlow d (Finset.mem_Icc.mp hd).1 (Finset.mem_Icc.mp hd).2]
  have hd0 : (d : ℝ) ≠ 0 := by
    have := (Finset.mem_Icc.mp hd).1
    exact_mod_cast (show d ≠ 0 by omega)
  field_simp [hd0]

theorem actual_tail_charge (P x : ℕ) (hP : 0 < P) (hx : x ≤ P) (c : ℕ → ℝ)
    (hlow : ∀ d, 1 ≤ d → d ≤ x → c d = (ArithmeticFunction.moebius d : ℝ)) :
    tau P c ^ 2 ≤ q P c / ((x : ℝ) + 1) := by
  apply ExactHeadGreen.tail_charge_sq_le P x hP hx (Finset.Icc 1 (P - 1))
    (Finset.Icc_subset_Icc_right (Nat.sub_le _ _)) (residual P c)
  intro r hr hrx
  exact residual_head P x hx c hlow r (Finset.mem_Icc.mp hr).1 hrx

private theorem sum_Icc_eq_range (P : ℕ) (f : ℕ → ℝ) :
    (∑ r ∈ Finset.Icc 1 P, f r) = ∑ j ∈ Finset.range P, f (j + 1) := by
  induction P with
  | zero => simp
  | succ P ih => rw [Finset.sum_Icc_succ_top (by omega), Finset.sum_range_succ, ih]

theorem actual_energy_split (P : ℕ) (hP : 0 < P) (c : ℕ → ℝ)
    (hdiv : ∀ d ∈ Finset.Icc 1 P, c d ≠ 0 → d ∣ P) :
    ‖hilbertOne - hilbertExtension P hP (Finset.Icc 1 P) c
      (fun d hd => (Finset.mem_Icc.mp hd).1)‖ ^ 2 =
      progressionWeight P P + q P c := by
  rw [hilbertExtension_error_split P hP (Finset.Icc 1 P) c _ hdiv]
  congr 1
  let F : ℕ → ℝ := fun r => if r < P then progressionWeight P r *
    (1 - ∑ d ∈ Finset.Icc 1 P, c d * grid d r) ^ 2 else 0
  have hh := sum_Icc_eq_range P F
  rw [← Fin.sum_univ_eq_sum_range] at hh
  change (∑ r : Fin P, F (r.val + 1)) = q P c
  rw [← hh]
  dsimp only [F]
  have hfilter : (Finset.Icc 1 P).filter (fun r => r < P) = Finset.Icc 1 (P - 1) := by
    ext r
    simp only [Finset.mem_filter, Finset.mem_Icc]
    omega
  change (∑ r ∈ Finset.Icc 1 P, if r < P then _ else 0) = _
  rw [← Finset.sum_filter, hfilter]
  unfold q energy residual
  apply Finset.sum_congr rfl
  intro r hr
  ring


/-- A concrete sufficient RH criterion using actual legal floor profiles.
The two cofinal analytic bounds replace vanishing energy and coefficient
compactness. Finite normal equations are required only at active coefficients. -/
theorem riemannHypothesis_of_cofinal_mobius_profiles
    (P : ℕ → ℕ) (hP : ∀ x, x < P x) (c h : ℕ → ℕ → ℝ)
    (hlow : ∀ x d, 1 ≤ d → d ≤ x → c x d = (ArithmeticFunction.moebius d : ℝ))
    (hdiv : ∀ x, ∀ d ∈ Finset.Icc 1 (P x), c x d ≠ 0 → d ∣ P x)
    (hupper : ∀ x, ∀ d ∈ Finset.Icc 1 (P x), x < d → c x d ≠ 0 →
      score (Finset.Icc 1 (P x - 1)) (progressionWeight (P x)) (residual (P x) (c x)) d = 0)
    (C B : ℝ) (hC : 0 ≤ C)
    (hdata : ∀ J, ∃ x, J ≤ x ∧
      mass (Finset.Icc 1 x) MobiusAffineProfile.weight *
        energy (Finset.Icc 1 x) MobiusAffineProfile.weight
          (fun d => profile (P x) (c x) d - h x d) ≤ C * q (P x) (c x) ∧
      MobiusAffineProfile.signedSum x (h x) ≤ B) :
    RiemannHypothesis := by
  have hPpos (x : ℕ) : 0 < P x := lt_of_le_of_lt (Nat.zero_le x) (hP x)
  let hd := fun x d (hd : d ∈ Finset.Icc 1 (P x)) => (Finset.mem_Icc.mp hd).1
  let f (x : ℕ) := hilbertExtension (P x) (hPpos x) (Finset.Icc 1 (P x)) (c x) (hd x)
  choose n hn he hm using hdata
  refine riemannHypothesis_of_bounded_exact_head_residuals (Set.Ici 1)
    (by intro a ha; exact ha) (fun J => f (n J))
    (fun J => hilbertExtension_legal _ _ _ _ _) ?_ (1 + 2 * B + 2 * C + 2) ?_
  · intro J k hk hkJ
    apply hilbertExtension_head (P (n J)) (hPpos (n J)) _ (c (n J)) _ (n J) (hP (n J))
      (mobius_floor_head (P (n J)) (n J) (hP (n J)).le (c (n J)) (hlow (n J)))
    · exact hk
    · exact hkJ.trans (hn J)
  · intro J
    let x := n J
    have hq := q_nonneg (P x) (c x)
    have ht : tau (P x) (c x) ^ 2 ≤ 1 * q (P x) (c x) := by
      have hh := actual_tail_charge (P x) x (hPpos x) (hP x).le (c x) (hlow x)
      have hh' : q (P x) (c x) / ((x : ℝ) + 1) ≤ q (P x) (c x) :=
        div_le_self hq (by have hx0 : (0 : ℝ) ≤ x := Nat.cast_nonneg x; linarith)
      simpa using hh.trans hh'
    have herr := (MobiusAffineProfile.profile_error_sq_le x (profile (P x) (c x)) (h x)).trans (he J)
    have hqb := energy_le_of_relative_profile hq hC (show (0 : ℝ) ≤ 1 by norm_num)
      (signed_root_identity (P x) x (hP x).le (c x) (hlow x) (hupper x))
      ht herr (hm J)
    have hterm : progressionWeight (P x) (P x) ≤ 1 := by
      have hh := Finset.single_le_sum (s := Finset.Icc 1 (P x))
        (f := progressionWeight (P x)) (fun r _ => progressionWeight_nonneg _ r)
        (Finset.mem_Icc.mpr ⟨hPpos x, le_rfl⟩)
      simpa [ExactHeadGreen.period_mass (P x) (hPpos x)] using hh
    change ‖hilbertOne - hilbertExtension (P x) (hPpos x) _ (c x) _‖ ^ 2 ≤ _
    rw [actual_energy_split (P x) (hPpos x) (c x) (hdiv x)]
    linarith

/-- Stronger cofinal criterion: the signed moment need only stay below q by a
fixed proportional margin, up to an additive constant. -/
theorem riemannHypothesis_of_cofinal_mobius_profile_deficit
    (P : ℕ → ℕ) (hP : ∀ x, x < P x) (c h : ℕ → ℕ → ℝ)
    (hlow : ∀ x d, 1 ≤ d → d ≤ x → c x d = (ArithmeticFunction.moebius d : ℝ))
    (hdiv : ∀ x, ∀ d ∈ Finset.Icc 1 (P x), c x d ≠ 0 → d ∣ P x)
    (hupper : ∀ x, ∀ d ∈ Finset.Icc 1 (P x), x < d → c x d ≠ 0 →
      score (Finset.Icc 1 (P x - 1)) (progressionWeight (P x)) (residual (P x) (c x)) d = 0)
    (δ C B : ℝ) (hδ : 0 < δ) (hC : 0 ≤ C)
    (hdata : ∀ J, ∃ x, J ≤ x ∧
      mass (Finset.Icc 1 x) MobiusAffineProfile.weight *
        energy (Finset.Icc 1 x) MobiusAffineProfile.weight
          (fun d => profile (P x) (c x) d - h x d) ≤ C * q (P x) (c x) ∧
      MobiusAffineProfile.signedSum x (h x) ≤ (1 - δ) * q (P x) (c x) + B) :
    RiemannHypothesis := by
  have hPpos (x : ℕ) : 0 < P x := lt_of_le_of_lt (Nat.zero_le x) (hP x)
  let hd := fun x d (hd : d ∈ Finset.Icc 1 (P x)) => (Finset.mem_Icc.mp hd).1
  let f (x : ℕ) := hilbertExtension (P x) (hPpos x) (Finset.Icc 1 (P x)) (c x) (hd x)
  choose n hn he hm using hdata
  refine riemannHypothesis_of_bounded_exact_head_residuals (Set.Ici 1)
    (by intro a ha; exact ha) (fun J => f (n J))
    (fun J => hilbertExtension_legal _ _ _ _ _) ?_ (1 + (2 * δ * B + 2 * C + 2) / δ ^ 2) ?_
  · intro J k hk hkJ
    apply hilbertExtension_head (P (n J)) (hPpos (n J)) _ (c (n J)) _ (n J) (hP (n J))
      (mobius_floor_head (P (n J)) (n J) (hP (n J)).le (c (n J)) (hlow (n J)))
    · exact hk
    · exact hkJ.trans (hn J)
  · intro J
    let x := n J
    have hq := q_nonneg (P x) (c x)
    have ht : tau (P x) (c x) ^ 2 ≤ 1 * q (P x) (c x) := by
      have hh := actual_tail_charge (P x) x (hPpos x) (hP x).le (c x) (hlow x)
      have hh' : q (P x) (c x) / ((x : ℝ) + 1) ≤ q (P x) (c x) :=
        div_le_self hq (by have hx0 : (0 : ℝ) ≤ x := Nat.cast_nonneg x; linarith)
      simpa using hh.trans hh'
    have herr := (MobiusAffineProfile.profile_error_sq_le x (profile (P x) (c x)) (h x)).trans (he J)
    have hqb := energy_scaled_le_of_profile_deficit hq hδ hC (show (0 : ℝ) ≤ 1 by norm_num)
      (signed_root_identity (P x) x (hP x).le (c x) (hlow x) (hupper x))
      ht herr (hm J)
    have hterm : progressionWeight (P x) (P x) ≤ 1 := by
      have hh := Finset.single_le_sum (s := Finset.Icc 1 (P x))
        (f := progressionWeight (P x)) (fun r _ => progressionWeight_nonneg _ r)
        (Finset.mem_Icc.mpr ⟨hPpos x, le_rfl⟩)
      simpa [ExactHeadGreen.period_mass (P x) (hPpos x)] using hh
    change ‖hilbertOne - hilbertExtension (P x) (hPpos x) _ (c x) _‖ ^ 2 ≤ _
    rw [actual_energy_split (P x) (hPpos x) (c x) (hdiv x)]
    have hd2 : 0 < δ ^ 2 := sq_pos_of_pos hδ
    have heq : q (P x) (c x) ≤ (2 * δ * B + 2 * C + 2) / δ ^ 2 := by
      apply (le_div_iff₀ hd2).mpr
      nlinarith only [hqb]
    linarith only [hterm, heq]

end RiemannResearch.RH.Pareto.MobiusHeadGreen
