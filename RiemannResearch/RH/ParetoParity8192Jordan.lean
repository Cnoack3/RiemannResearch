import RiemannResearch.RH.ParetoParity8192Data
import RiemannResearch.RH.ParetoUniformJordanVariance
import Mathlib.Tactic.NormNum

/-! # Arithmetic of the conductor-8192 residue trial

The CRT quadratic form is evaluated through sums over multiples and the
Jordan totient. This reduces the number of coefficient lookups from a
quadratic double sum to a harmonic sum over the conductor dictionary.
-/

open scoped BigOperators
namespace RiemannResearch.RH.Pareto.PrimePowerSchur.Conductor8192

private def jordanFuel : ℕ → ℕ → ℕ
  | 0, _ => 1
  | fuel+1, n =>
    if n ≤ 1 then 1 else
      let p := n.minFac
      let q := n/p
      (if p ∣ q then p^2 else p^2-1) * jordanFuel fuel q

private theorem jordanFuel_spec {fuel n : ℕ} (hn : 0 < n) (hf : n ≤ 2^fuel) :
    (jordanFuel fuel n : ℝ) = jordanTwo n := by
  induction fuel generalizing n with
  | zero =>
    have : n = 1 := by simpa using (le_antisymm (by simpa using hf) hn)
    subst n
    simp [jordanFuel]
  | succ fuel ih =>
    by_cases h : n ≤ 1
    · have : n = 1 := by omega
      subst n
      simp [jordanFuel]
    · let p := n.minFac
      let q := n/p
      have hp : p.Prime := Nat.minFac_prime (by omega)
      have hd : p ∣ n := Nat.minFac_dvd n
      have hq : 0 < q := Nat.div_pos (Nat.le_of_dvd hn hd) hp.pos
      have he : p*q = n := Nat.mul_div_cancel' hd
      have hrec := jordanTwo_prime_mul p q hp hq
      rw [he] at hrec
      rw [jordanFuel,if_neg h]
      change (((if p ∣ q then p^2 else p^2-1) * jordanFuel fuel q : ℕ) : ℝ) = _
      have h2q : 2*q ≤ n := by
        rw [← he]
        exact Nat.mul_le_mul_right q hp.two_le
      rw [pow_succ] at hf
      rw [Nat.cast_mul, ih hq (by omega),hrec]
      have hp1 : 1 ≤ p^2 := pow_pos hp.pos 2
      split_ifs <;> simp [Nat.cast_sub hp1]

private def multipleSum (k : ℕ) : ℤ :=
  ∑ j ∈ Finset.range (8192/k), coeff (k*(j+1))

private theorem multipleSum_spec {k : ℕ} (hk : k ∈ support) :
    (multipleSum k : ℝ) =
      ∑ d ∈ support, (coeff d : ℝ)*divisorIncidence d k := by
  have h2 := (Finset.mem_Icc.mp hk).1
  have hk0 : 0 < k := by omega
  have hinj : Function.Injective (fun j : ℕ => k*(j+1)) := by
    intro i j hij
    exact Nat.add_right_cancel (Nat.eq_of_mul_eq_mul_left hk0 hij)
  have himg : (Finset.range (8192/k)).image (fun j => k*(j+1)) =
      support.filter (fun d => k ∣ d) := by
    ext d
    simp only [Finset.mem_image,Finset.mem_range,Finset.mem_filter,support,Finset.mem_Icc]
    constructor
    · rintro ⟨j,hj,rfl⟩
      refine ⟨⟨by nlinarith,?_⟩,dvd_mul_right _ _⟩
      have hq := (Nat.le_div_iff_mul_le hk0).mp (show j+1≤8192/k by omega)
      simpa only [Nat.mul_comm] using hq
    · rintro ⟨⟨hd,hle⟩,m, rfl⟩
      have hm : 0 < m := by cases m with
        | zero => simp at hd
        | succ m => omega
      refine ⟨m-1, ?_,by rw [Nat.sub_add_cancel hm]⟩
      have hq := (Nat.le_div_iff_mul_le hk0).mpr (by simpa [Nat.mul_comm] using hle)
      omega
  rw [multipleSum,Int.cast_sum]
  change (∑ j ∈ Finset.range (8192/k), (coeff (k*(j+1)) : ℝ)) = _
  rw [← Finset.sum_image (f:=fun d => (coeff d : ℝ)) (fun _ _ _ _ h => hinj h),
      himg,Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro d hd
  by_cases h : k ∣ d <;> simp [divisorIncidence,h]

private theorem gcdKernel (d e : ℕ) (hd : d ∈ support) (_he : e ∈ support) :
    ((d.gcd e : ℕ):ℝ)^2 - 1 =
      ∑ k ∈ support, jordanTwo k * divisorIncidence d k * divisorIncidence e k := by
  let g := d.gcd e
  have hd0 : 0 < d := by have := (Finset.mem_Icc.mp hd).1; omega
  have hg0 : 0 < g := Nat.gcd_pos_of_pos_left _ hd0
  have hgB : g ≤ 8192 := (Nat.le_of_dvd hd0 (Nat.gcd_dvd_left d e)).trans (Finset.mem_Icc.mp hd).2
  have h1 : 1 ∈ g.divisors := Nat.mem_divisors.mpr ⟨one_dvd _,hg0.ne'⟩
  have ht := Finset.sum_erase_add g.divisors jordanTwo h1
  rw [sum_divisors_jordanTwo g hg0, jordanTwo_one] at ht
  have hset : support.filter (fun k => k∣d ∧ k∣e) = g.divisors.erase 1 := by
    ext k
    simp only [support,Finset.mem_filter,Finset.mem_Icc,Finset.mem_erase,Nat.mem_divisors,
      g,Nat.dvd_gcd_iff]
    constructor
    · rintro ⟨⟨hk,_⟩,hkd,hke⟩
      exact ⟨by omega,⟨hkd,hke⟩,hg0.ne'⟩
    · rintro ⟨hne,⟨hkd,hke⟩,_⟩
      have hdiv : k ∣ g := Nat.dvd_gcd hkd hke
      have hk0 : 0 < k := Nat.pos_of_dvd_of_pos hdiv hg0
      exact ⟨⟨by omega,(Nat.le_of_dvd hg0 hdiv).trans hgB⟩,hkd,hke⟩
  calc
    _ = ∑ k ∈ g.divisors.erase 1, jordanTwo k := by dsimp [g] at ht ⊢; linarith only [ht]
    _ = _ := by
      rw [← hset,Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro k hk
      by_cases hkd : k∣d <;> by_cases hke : k∣e <;> simp [divisorIncidence,hkd,hke]

def jordanEnergy : ℤ := ∑ k ∈ support, (jordanFuel 13 k : ℤ)*(multipleSum k)^2

theorem covariance_eq_jordanEnergy : covariance = jordanEnergy := by
  apply Int.cast_injective (α:=ℝ)
  simp only [covariance,jordanEnergy,Int.cast_sum,Int.cast_mul,Int.cast_pow,Int.cast_sub,
    Int.cast_natCast,Int.cast_one]
  calc
    _ = ∑ d ∈ support, ∑ e ∈ support, (coeff d : ℝ)*(coeff e : ℝ)*
        (∑ k ∈ support, jordanTwo k * divisorIncidence d k * divisorIncidence e k) := by
      apply Finset.sum_congr rfl
      intro d hd
      apply Finset.sum_congr rfl
      intro e he
      rw [gcdKernel d e hd he]
    _ = _ := by
      rw [finite_gram_diagonal]
      apply Finset.sum_congr rfl
      intro k hk
      rw [multipleSum_spec hk,jordanFuel_spec (by have := (Finset.mem_Icc.mp hk).1; omega)
        (show k ≤ 2^13 by exact (Finset.mem_Icc.mp hk).2)]

private def fastMultiple (k : ℕ) : ℤ :=
  intFold (fun j => coeff (k*(j+1))) (8192/k) 0

private theorem fastMultiple_spec (k : ℕ) : fastMultiple k = multipleSum k := by
  simp [fastMultiple,multipleSum,intFold_eq]

def fastJordan : ℤ :=
  fastSum (fun k => (jordanFuel 13 k : ℤ) * (fastMultiple k)^2)

theorem fastJordan_spec : fastJordan = jordanEnergy := by
  unfold fastJordan jordanEnergy
  rw [fastSum_spec]
  simp only [fastMultiple_spec]

end RiemannResearch.RH.Pareto.PrimePowerSchur.Conductor8192
