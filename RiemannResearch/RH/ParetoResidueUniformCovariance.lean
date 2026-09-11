import RiemannResearch.RH.ParetoResidueDuality
import Mathlib.Data.Nat.ModEq
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Uniform residue covariance by conditioning on the gcd residue

The equivalence below identifies an actual residue modulo `lcm L K` with
its common residue modulo `gcd L K` and its two remaining CRT coordinates.
The uniform product measure then gives conditional independence. This file
never substitutes uniform residue weights for the Pareto distribution.
-/

open scoped BigOperators
namespace RiemannResearch.RH.Pareto
noncomputable section

private theorem range_real_sum (n : ℕ) :
    (∑ i ∈ Finset.range n, (i : ℝ)) = (n : ℝ) * ((n : ℝ) - 1) / 2 := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ, ih]; push_cast; ring

private theorem range_real_square_sum (n : ℕ) :
    (∑ i ∈ Finset.range n, (i : ℝ)^2) =
      (n : ℝ) * ((n : ℝ) - 1) * (2 * (n : ℝ) - 1) / 6 := by
  induction n with
  | zero => simp
  | succ n ih => rw [Finset.sum_range_succ, ih]; push_cast; ring

theorem fin_real_sum (n : ℕ) :
    (∑ i : Fin n, (i.val : ℝ)) = (n : ℝ) * ((n : ℝ) - 1) / 2 := by
  rw [Fin.sum_univ_eq_sum_range, range_real_sum]

theorem fin_real_centered_sum (n : ℕ) :
    (∑ i : Fin n, ((i.val : ℝ) - ((n : ℝ) - 1) / 2)) = 0 := by
  rw [Finset.sum_sub_distrib, fin_real_sum]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

theorem fin_real_centered_square_sum (n : ℕ) :
    (∑ i : Fin n, ((i.val : ℝ) - ((n : ℝ) - 1) / 2)^2) =
      (n : ℝ) * ((n : ℝ)^2 - 1) / 12 := by
  have hs := fin_real_sum n
  have hss : (∑ i : Fin n, (i.val : ℝ)^2) =
      (n : ℝ) * ((n : ℝ) - 1) * (2 * (n : ℝ) - 1) / 6 := by
    rw [Fin.sum_univ_eq_sum_range (fun i : ℕ => (i : ℝ)^2) n,
      range_real_square_sum]
  simp_rw [sub_sq]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, hss]
  simp only [← Finset.mul_sum, ← Finset.sum_mul, hs, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

/-- Actual CRT coordinates, with the common gcd residue recorded only once. -/
def residueCRTCoordinates (L K : ℕ) (hL : 0 < L) (hK : 0 < K)
    (n : Fin (Nat.lcm L K)) :
    Fin (Nat.gcd L K) × (Fin (L / Nat.gcd L K) × Fin (K / Nat.gcd L K)) :=
  (⟨n.val % Nat.gcd L K, Nat.mod_lt _ (Nat.gcd_pos_of_pos_left K hL)⟩,
    ⟨(n.val % L) / Nat.gcd L K, Nat.div_lt_of_lt_mul (by
      rw [Nat.mul_div_cancel' (Nat.gcd_dvd_left L K)]
      exact Nat.mod_lt _ hL)⟩,
    ⟨(n.val % K) / Nat.gcd L K, Nat.div_lt_of_lt_mul (by
      rw [Nat.mul_div_cancel' (Nat.gcd_dvd_right L K)]
      exact Nat.mod_lt _ hK)⟩)

theorem residueCRTCoordinates_injective (L K : ℕ) (hL : 0 < L) (hK : 0 < K) :
    Function.Injective (residueCRTCoordinates L K hL hK) := by
  intro x y h
  have h0 := congrArg (fun z => z.1.val) h
  have h1 := congrArg (fun z => z.2.1.val) h
  have h2 := congrArg (fun z => z.2.2.val) h
  change x.val % Nat.gcd L K = y.val % Nat.gcd L K at h0
  change (x.val % L) / Nat.gcd L K = (y.val % L) / Nat.gcd L K at h1
  change (x.val % K) / Nat.gcd L K = (y.val % K) / Nat.gcd L K at h2
  have hLxy : x.val ≡ y.val [MOD L] := by
    have hx := Nat.mod_add_div (x.val % L) (Nat.gcd L K)
    have hy := Nat.mod_add_div (y.val % L) (Nat.gcd L K)
    rw [Nat.mod_mod_of_dvd _ (Nat.gcd_dvd_left L K), h0, h1] at hx
    rw [Nat.mod_mod_of_dvd _ (Nat.gcd_dvd_left L K)] at hy
    exact hx.symm.trans hy
  have hKxy : x.val ≡ y.val [MOD K] := by
    have hx := Nat.mod_add_div (x.val % K) (Nat.gcd L K)
    have hy := Nat.mod_add_div (y.val % K) (Nat.gcd L K)
    rw [Nat.mod_mod_of_dvd _ (Nat.gcd_dvd_right L K), h0, h2] at hx
    rw [Nat.mod_mod_of_dvd _ (Nat.gcd_dvd_right L K)] at hy
    exact hx.symm.trans hy
  apply Fin.ext
  have hc := Nat.mod_lcm hLxy hKxy
  change x.val % Nat.lcm L K = y.val % Nat.lcm L K at hc
  simpa only [Nat.mod_eq_of_lt x.isLt, Nat.mod_eq_of_lt y.isLt] using hc

theorem residueCRTCoordinates_surjective (L K : ℕ) (hL : 0 < L) (hK : 0 < K) :
    Function.Surjective (residueCRTCoordinates L K hL hK) := by
  rintro ⟨c, i, j⟩
  let d := Nat.gcd L K
  have hd : 0 < d := Nat.gcd_pos_of_pos_left K hL
  have hc : c.val < d := c.isLt
  have hi : c.val + d * i.val < L := by
    have hh := Nat.mul_le_mul_left d (Nat.succ_le_of_lt i.isLt)
    have he : d * (L / d) = L := Nat.mul_div_cancel' (Nat.gcd_dvd_left L K)
    rw [he] at hh
    nlinarith
  have hj : c.val + d * j.val < K := by
    have hh := Nat.mul_le_mul_left d (Nat.succ_le_of_lt j.isLt)
    have he : d * (K / d) = K := Nat.mul_div_cancel' (Nat.gcd_dvd_right L K)
    rw [he] at hh
    nlinarith
  have hcompat : c.val + d * i.val ≡ c.val + d * j.val [MOD Nat.gcd L K] := by
    change (c.val + d * i.val) % d = (c.val + d * j.val) % d
    simp [Nat.add_mod]
  let n := Nat.chineseRemainder' hcompat
  let x : Fin (Nat.lcm L K) :=
    ⟨n.val, Nat.chineseRemainder'_lt_lcm hcompat (by omega) (by omega)⟩
  have hxL : x.val % L = c.val + d * i.val := by
    have hn := n.property.1
    change x.val % L = (c.val + d * i.val) % L at hn
    simpa only [Nat.mod_eq_of_lt hi] using hn
  have hxK : x.val % K = c.val + d * j.val := by
    have hn := n.property.2
    change x.val % K = (c.val + d * j.val) % K at hn
    simpa only [Nat.mod_eq_of_lt hj] using hn
  have hxd : x.val % d = c.val := by
    rw [← Nat.mod_mod_of_dvd _ (Nat.gcd_dvd_left L K), hxL]
    change (c.val + d * i.val) % d = c.val
    simp [Nat.add_mod, Nat.mod_eq_of_lt hc]
  refine ⟨x, ?_⟩
  apply Prod.ext
  · apply Fin.ext
    exact hxd
  · apply Prod.ext
    · apply Fin.ext
      change (x.val % L) / d = i.val
      simp [hxL, Nat.add_mul_div_left, Nat.div_eq_of_lt hc, hd]
    · apply Fin.ext
      change (x.val % K) / d = j.val
      simp [hxK, Nat.add_mul_div_left, Nat.div_eq_of_lt hc, hd]

def residueCRTEquiv (L K : ℕ) (hL : 0 < L) (hK : 0 < K) :
    Fin (Nat.lcm L K) ≃
      Fin (Nat.gcd L K) × (Fin (L / Nat.gcd L K) × Fin (K / Nat.gcd L K)) :=
  Equiv.ofBijective (residueCRTCoordinates L K hL hK)
    ⟨residueCRTCoordinates_injective L K hL hK,
      residueCRTCoordinates_surjective L K hL hK⟩

/-- The exact common-period CRT identity for every function of the two residues. -/
theorem sum_residuePair_eq_crt (L K : ℕ) (hL : 0 < L) (hK : 0 < K)
    (f : ℕ → ℕ → ℝ) :
    (∑ n : Fin (Nat.lcm L K), f (n.val % L) (n.val % K)) =
      ∑ c : Fin (Nat.gcd L K), ∑ i : Fin (L / Nat.gcd L K),
        ∑ j : Fin (K / Nat.gcd L K),
          f (c.val + Nat.gcd L K * i.val) (c.val + Nat.gcd L K * j.val) := by
  let e := residueCRTEquiv L K hL hK
  have h := e.sum_comp (fun z =>
    f (z.1.val + Nat.gcd L K * z.2.1.val)
      (z.1.val + Nat.gcd L K * z.2.2.val))
  simp only [Fintype.sum_prod_type] at h
  convert h using 1
  apply Finset.sum_congr rfl
  intro n hn
  dsimp [e, residueCRTEquiv, residueCRTCoordinates]
  congr 1
  · change n.val % L = n.val % Nat.gcd L K +
      Nat.gcd L K * ((n.val % L) / Nat.gcd L K)
    simpa only [Nat.mod_mod_of_dvd _ (Nat.gcd_dvd_left L K)] using
      (Nat.mod_add_div (n.val % L) (Nat.gcd L K)).symm
  · change n.val % K = n.val % Nat.gcd L K +
      Nat.gcd L K * ((n.val % K) / Nat.gcd L K)
    simpa only [Nat.mod_mod_of_dvd _ (Nat.gcd_dvd_right L K)] using
      (Nat.mod_add_div (n.val % K) (Nat.gcd L K)).symm

private theorem sum_centered_affine_product (a b : ℕ) (x d : ℝ) :
    (∑ i : Fin a, ∑ j : Fin b,
      (x + d * ((i.val : ℝ) - ((a : ℝ)-1)/2)) *
      (x + d * ((j.val : ℝ) - ((b : ℝ)-1)/2))) =
      (a : ℝ) * (b : ℝ) * x^2 := by
  have hs (n : ℕ) :
      (∑ i : Fin n, (x + d * ((i.val : ℝ) - ((n : ℝ)-1)/2))) =
        (n : ℝ) * x := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, fin_real_centered_sum]
    simp
  calc
    _ = (∑ i : Fin a, (x + d * ((i.val : ℝ) - ((a : ℝ)-1)/2))) *
        (∑ j : Fin b, (x + d * ((j.val : ℝ) - ((b : ℝ)-1)/2))) := by
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro i hi
          rw [Finset.mul_sum]
    _ = _ := by rw [hs a, hs b]; ring

/-- Exact centered mixed sum for the actual residue functions on their lcm. -/
theorem residue_uniform_covariance_sum_lcm (L K : ℕ) (hL : 0 < L) (hK : 0 < K) :
    (∑ n : Fin (Nat.lcm L K),
      (((n.val % L : ℕ) : ℝ) - ((L : ℝ)-1)/2) *
      (((n.val % K : ℕ) : ℝ) - ((K : ℝ)-1)/2)) =
      (Nat.lcm L K : ℝ) * ((Nat.gcd L K : ℝ)^2-1)/12 := by
  let d := Nat.gcd L K
  let a := L / d
  let b := K / d
  have hLa : (L : ℝ) = (d : ℝ) * (a : ℝ) := by
    exact_mod_cast (Nat.mul_div_cancel' (Nat.gcd_dvd_left L K)).symm
  have hKb : (K : ℝ) = (d : ℝ) * (b : ℝ) := by
    exact_mod_cast (Nat.mul_div_cancel' (Nat.gcd_dvd_right L K)).symm
  have hQ : (Nat.lcm L K : ℝ) = (d : ℝ) * ((a : ℝ) * (b : ℝ)) := by
    have hc := Fintype.card_congr (residueCRTEquiv L K hL hK)
    simp only [Fintype.card_fin, Fintype.card_prod] at hc
    exact_mod_cast hc
  rw [sum_residuePair_eq_crt L K hL hK
    (fun l k : ℕ => ((l : ℝ)-((L : ℝ)-1)/2) * ((k : ℝ)-((K : ℝ)-1)/2))]
  change (∑ c : Fin d, ∑ i : Fin a, ∑ j : Fin b,
    (((c.val + d*i.val : ℕ) : ℝ)-((L : ℝ)-1)/2) *
    (((c.val + d*j.val : ℕ) : ℝ)-((K : ℝ)-1)/2)) = _
  have hpoint (c : Fin d) (i : Fin a) (j : Fin b) :
      (((c.val + d*i.val : ℕ) : ℝ)-((L : ℝ)-1)/2) *
      (((c.val + d*j.val : ℕ) : ℝ)-((K : ℝ)-1)/2) =
      (((c.val : ℝ)-((d : ℝ)-1)/2) +
        (d : ℝ)*((i.val : ℝ)-((a : ℝ)-1)/2)) *
      (((c.val : ℝ)-((d : ℝ)-1)/2) +
        (d : ℝ)*((j.val : ℝ)-((b : ℝ)-1)/2)) := by
    push_cast
    rw [hLa, hKb]
    ring
  simp_rw [hpoint, sum_centered_affine_product]
  rw [← Finset.mul_sum, fin_real_centered_square_sum]
  rw [hQ]
  ring

/-- Under uniform residues, conditioning on the gcd leaves covariance
exactly equal to the variance of the shared gcd coordinate. -/
theorem residue_uniform_covariance_lcm (L K : ℕ) (hL : 0 < L) (hK : 0 < K) :
    (∑ n : Fin (Nat.lcm L K),
      (((n.val % L : ℕ) : ℝ) - ((L : ℝ)-1)/2) *
      (((n.val % K : ℕ) : ℝ) - ((K : ℝ)-1)/2)) /
        (Nat.lcm L K : ℝ) = ((Nat.gcd L K : ℝ)^2-1)/12 := by
  rw [residue_uniform_covariance_sum_lcm L K hL hK]
  have hQ : (Nat.lcm L K : ℝ) ≠ 0 := by
    exact_mod_cast Nat.lcm_ne_zero (Nat.ne_of_gt hL) (Nat.ne_of_gt hK)
  field_simp

/-- Replication of an exact residue-pair sum over a larger common period. -/
theorem residuePair_sum_period_mul (L K P t : ℕ) (hLP : L ∣ P) (hKP : K ∣ P)
    (f : ℕ → ℕ → ℝ) :
    (∑ n : Fin (P*t), f (n.val % L) (n.val % K)) =
      (t : ℝ) * ∑ n : Fin P, f (n.val % L) (n.val % K) := by
  rw [Nat.mul_comm P t]
  have h := (finProdFinEquiv (m := t) (n := P)).sum_comp
    (fun n => f (n.val % L) (n.val % K))
  rw [← h]
  simp only [Fintype.sum_prod_type, finProdFinEquiv_apply_val,
    Nat.add_mod, Nat.mul_mod, Nat.mod_eq_zero_of_dvd hLP,
    Nat.mod_eq_zero_of_dvd hKP, zero_mul, Nat.zero_mod, add_zero, Nat.mod_mod,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- Exact gcd covariance sum on every common period. -/
theorem residue_uniform_covariance_sum (L K Q : ℕ) (hL : 0 < L) (hK : 0 < K)
    (hLQ : L ∣ Q) (hKQ : K ∣ Q) :
    (∑ n ∈ Finset.range Q,
      (residue L n - ((L : ℝ)-1)/2) *
      (residue K n - ((K : ℝ)-1)/2)) =
      (Q : ℝ) * ((Nat.gcd L K : ℝ)^2-1)/12 := by
  obtain ⟨t, rfl⟩ := Nat.lcm_dvd hLQ hKQ
  rw [Finset.sum_range]
  simp only [residue]
  rw [residuePair_sum_period_mul L K (Nat.lcm L K) t
      (Nat.dvd_lcm_left L K) (Nat.dvd_lcm_right L K)
      (fun l k : ℕ => ((l : ℝ)-((L : ℝ)-1)/2) * ((k : ℝ)-((K : ℝ)-1)/2)),
    residue_uniform_covariance_sum_lcm L K hL hK]
  push_cast
  ring

theorem residue_uniform_covariance (L K Q : ℕ) (hL : 0 < L) (hK : 0 < K)
    (hQ : 0 < Q) (hLQ : L ∣ Q) (hKQ : K ∣ Q) :
    (∑ n ∈ Finset.range Q,
      (residue L n - ((L : ℝ)-1)/2) *
      (residue K n - ((K : ℝ)-1)/2)) / (Q : ℝ) =
      ((Nat.gcd L K : ℝ)^2-1)/12 := by
  rw [residue_uniform_covariance_sum L K Q hL hK hLQ hKQ]
  have hQ0 : (Q : ℝ) ≠ 0 := by positivity
  field_simp

/-- The centers used in the covariance theorem are the actual uniform means. -/
theorem residue_uniform_mean_sum (L Q : ℕ) (hL : 0 < L) (hLQ : L ∣ Q) :
    (∑ n ∈ Finset.range Q, residue L n) = (Q : ℝ) * ((L : ℝ)-1)/2 := by
  obtain ⟨t, rfl⟩ := hLQ
  rw [Finset.sum_range]
  simp only [residue]
  have hs := residuePair_sum_period_mul L L L t (dvd_refl L) (dvd_refl L)
    (fun i _ => (i : ℝ))
  simp only [Nat.mod_eq_of_lt (Fin.isLt _)] at hs
  rw [hs, fin_real_sum]
  push_cast
  ring

end
end RiemannResearch.RH.Pareto
