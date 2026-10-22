import RiemannResearch.RH.CanonicalMobiusSublinearEnergy
import RiemannResearch.RH.MobiusQuantitativeRate

/-!
# Quantitative complete energy of canonical Mobius approximants

Source: the user's September 24, 2026 request to strengthen the unconditional
estimate behind the moving Hardy bound. The arithmetic inputs are the existing
formal quantitative PNT provider and exact Mobius floor-tail identities.
A harmonic quotient sum controls the middle window; the entire far tail is
bounded and retained. Optimizing two finite cutoffs gives the explicit
logarithmic ceiling and a vanishing normalized residual-energy budget.
No cancellation or RH-strength premise remains in the assembled providers.
-/

noncomputable section
open Filter
open scoped BigOperators Topology
namespace RiemannResearch.RH.Pareto

theorem canonicalMobiusHead_harmonic_window_bound (N n K : ℕ)
    (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hNn : N < n) (hnK : n ≤ K*N)
    (hM : ∀ t : ℕ, N ≤ t → |∑ d ∈ Finset.Icc 1 t,
      (ArithmeticFunction.moebius d : ℝ)| ≤ A*(t : ℝ))
    (hm : |mobiusReciprocalSum N| ≤ B) :
    |canonicalMobiusHead N n| ≤ 1 + (n : ℝ)*(A*((harmonic K : ℝ)+1)+B) := by
  classical
  let M : ℕ → ℝ := fun t => ∑ d ∈ Finset.Icc 1 t, (ArithmeticFunction.moebius d : ℝ)
  let q := n/(N+1)
  let T : ℝ := ∑ k ∈ Finset.Icc 1 q, (M (n/k)-M N)
  have hqN : q*(N+1) ≤ n := Nat.div_mul_le_self n (N+1)
  have hqK : q ≤ K := by
    by_contra h
    have : K < q := Nat.lt_of_not_ge h
    nlinarith
  have hqNR : (q : ℝ)*(N : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast (show q*N ≤ n by nlinarith)
  have hqNpR : (q : ℝ)*((N+1 : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hqN
  have hrec : (∑ k ∈ Finset.Icc 1 q, 1/(k : ℝ)) ≤ (harmonic K : ℝ) := by
    calc
      _ ≤ ∑ k ∈ Finset.Icc 1 K, 1/(k : ℝ) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro k hk
          exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hk).1,
            (Finset.mem_Icc.mp hk).2.trans hqK⟩
        · intro k hk hnot
          positivity
      _ = _ := by simp [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv,
        Rat.cast_natCast, one_div]
  have hterm (k : ℕ) (hk : k ∈ Finset.Icc 1 q) :
      |M (n/k)-M N| ≤ A*((n : ℝ)/(k : ℝ)+(N : ℝ)) := by
    have hk0 : 0 < k := (Finset.mem_Icc.mp hk).1
    have hkR : (0 : ℝ) < k := by exact_mod_cast hk0
    have hp : k*(N+1) ≤ n :=
      (Nat.le_div_iff_mul_le (Nat.succ_pos N)).mp (Finset.mem_Icc.mp hk).2
    have hNk : N ≤ n/k := by
      have : N+1 ≤ n/k := (Nat.le_div_iff_mul_le hk0).mpr
        (by simpa [Nat.mul_comm] using hp)
      omega
    have hd : ((n/k : ℕ) : ℝ) ≤ (n : ℝ)/(k : ℝ) := by
      apply (le_div_iff₀ hkR).mpr
      exact_mod_cast Nat.div_mul_le_self n k
    calc
      _ ≤ |M (n/k)|+|M N| := by
        simpa only [sub_eq_add_neg, abs_neg] using abs_add_le (M (n/k)) (-M N)
      _ ≤ A*((n/k : ℕ) : ℝ)+A*(N : ℝ) := add_le_add (hM _ hNk) (hM _ le_rfl)
      _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left hd hA]
  have ht : |T| ≤ A*(n : ℝ)*((harmonic K : ℝ)+1) := by
    calc
      _ ≤ ∑ k ∈ Finset.Icc 1 q, |M (n/k)-M N| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ k ∈ Finset.Icc 1 q, A*((n : ℝ)/(k : ℝ)+(N : ℝ)) := Finset.sum_le_sum hterm
      _ = A*(n : ℝ)*(∑ k ∈ Finset.Icc 1 q, 1/(k : ℝ)) +
          (q : ℝ)*(A*(N : ℝ)) := by
        simp_rw [mul_add]
        rw [Finset.sum_add_distrib]
        simp only [Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel, nsmul_eq_mul]
        congr 1
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k hk
        ring
      _ ≤ A*(n : ℝ)*(harmonic K : ℝ) + A*(n : ℝ) := by
        apply add_le_add
        · exact mul_le_mul_of_nonneg_left hrec (mul_nonneg hA (Nat.cast_nonneg n))
        · nlinarith [mul_le_mul_of_nonneg_left hqNR hA]
      _ = _ := by ring
  have hc : |((N+1 : ℕ) : ℝ)*mobiusReciprocalSum N*(q : ℝ)| ≤ B*(n : ℝ) := by
    simp only [abs_mul,
      abs_of_nonneg (Nat.cast_nonneg (N+1) : (0 : ℝ) ≤ _),
      abs_of_nonneg (Nat.cast_nonneg q : (0 : ℝ) ≤ _)]
    have hp := mul_le_mul_of_nonneg_left hm (Nat.cast_nonneg (N+1) : (0 : ℝ) ≤ _)
    have hp' := mul_le_mul_of_nonneg_right hp (Nat.cast_nonneg q : (0 : ℝ) ≤ _)
    nlinarith [mul_le_mul_of_nonneg_left hqNpR hB]
  have hr : canonicalMobiusHead N n =
      1-T-((N+1 : ℕ) : ℝ)*mobiusReciprocalSum N*(q : ℝ) := by
    have hi := finite_mobius_floor_tail_identity N n (by omega) hNn.le
    rw [canonicalMobiusHead_floor_expansion]
    change 1-(∑ d ∈ Finset.Icc 1 N,
      (ArithmeticFunction.moebius d : ℝ)*((n/d : ℕ) : ℝ)) = T at hi
    change (∑ d ∈ Finset.Icc 1 N,
      (ArithmeticFunction.moebius d : ℝ)*((n/d : ℕ) : ℝ))-
        ((N+1 : ℕ) : ℝ)*mobiusReciprocalSum N*(q : ℝ) = _
    linarith
  have h1 : |1-T| ≤ 1+|T| := by
    simpa only [sub_eq_add_neg, abs_neg, abs_one] using abs_add_le (1 : ℝ) (-T)
  rw [hr]
  have hh := abs_add_le (1-T) (-(((N+1 : ℕ) : ℝ)*mobiusReciprocalSum N*(q : ℝ)))
  simp only [← sub_eq_add_neg, abs_neg] at hh
  nlinarith

theorem canonicalMobiusHilbert_linear_window_energy (N K : ℕ)
    (hN : 0 < N) (hK : 2 ≤ K) (D : ℝ)
    (hmid : ∀ j, N < j → j ≤ K*N →
      |canonicalMobiusHead N j| ≤ 1+(j : ℝ)*D) :
    ‖canonicalMobiusHilbert N‖^2/(N : ℝ) ≤ 3/(N : ℝ)+2*(K : ℝ)*D^2+4/(K : ℝ) := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hKR : (0 : ℝ) < K := by exact_mod_cast (by omega : 0 < K)
  let L := K*N-N
  have hNL : N ≤ K*N := by nlinarith
  have hL : L+N = K*N := Nat.sub_add_cancel hNL
  have hidx (k : ℕ) : (k+L)+(N+1) = k+(K*N+1) := by omega
  have hs : Summable (fun j : ℕ => positiveWeight j*canonicalMobiusHead N j^2) := by
    simpa only [canonicalMobiusHilbert_sequence] using
      hilbertSequence_square_summable (canonicalMobiusHilbert N)
  have ht := (summable_nat_add_iff (N+1)).mpr hs
  have hw := (summable_nat_add_iff (N+1)).mpr positiveWeight_summable
  have hweights : (∑ k ∈ Finset.range L, positiveWeight (k+(N+1))) ≤ 1 := by
    calc
      _ ≤ ∑' k : ℕ, positiveWeight (k+(N+1)) :=
        Summable.sum_le_tsum _ (fun k _ => positiveWeight_nonneg _) hw
      _ = 1/((N : ℝ)+1) := by
        rw [positiveWeight_tail_tsum (N+1) (Nat.succ_pos _)]; norm_cast
      _ ≤ 1 := by apply (div_le_one (by positivity)).mpr; linarith [Nat.cast_nonneg (α := ℝ) N]
  have hwj (j : ℕ) (hj : 0 < j) : positiveWeight j*(j : ℝ)^2 ≤ 1 := by
    have hjR : (0 : ℝ) < j := by exact_mod_cast hj
    have he : positiveWeight j*(j : ℝ)^2 = (j : ℝ)/((j : ℝ)+1) := by
      unfold positiveWeight
      field_simp
      <;> ring
    rw [he]
    exact (div_le_one (by positivity)).mpr (by linarith)
  have hmiddle : (∑ k ∈ Finset.range L,
      positiveWeight (k+(N+1))*canonicalMobiusHead N (k+(N+1))^2) ≤
      2+2*(K : ℝ)*(N : ℝ)*D^2 := by
    calc
      _ ≤ ∑ k ∈ Finset.range L, (2*positiveWeight (k+(N+1))+2*D^2) := by
        apply Finset.sum_le_sum
        intro k hk
        have hk' := Finset.mem_range.mp hk
        have hb := hmid (k+(N+1)) (by omega) (by omega)
        have hsq := mul_self_le_mul_self (abs_nonneg _) hb
        have hsq' : canonicalMobiusHead N (k+(N+1))^2 ≤
            2+2*((k+(N+1) : ℕ) : ℝ)^2*D^2 := by
          simp only [← pow_two, sq_abs] at hsq
          nlinarith [sq_nonneg (1-((k+(N+1) : ℕ) : ℝ)*D)]
        have hp := mul_le_mul_of_nonneg_left hsq' (positiveWeight_nonneg (k+(N+1)))
        have hweight := hwj (k+(N+1)) (by omega)
        have hp' := mul_le_mul_of_nonneg_right hweight (sq_nonneg D)
        nlinarith
      _ = 2*(∑ k ∈ Finset.range L, positiveWeight (k+(N+1)))+(L : ℝ)*(2*D^2) := by
        rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range,
          nsmul_eq_mul, Finset.mul_sum]
      _ ≤ 2+2*(K : ℝ)*(N : ℝ)*D^2 := by
        have hLR : (L : ℝ) ≤ (K : ℝ)*(N : ℝ) := by
          exact_mod_cast (show L ≤ K*N by omega)
        nlinarith [mul_le_mul_of_nonneg_right hLR (sq_nonneg D)]
  have hfar : (∑' k : ℕ, positiveWeight (k+(K*N+1))*
      canonicalMobiusHead N (k+(K*N+1))^2) ≤ 4*(N : ℝ)/(K : ℝ) := by
    have hf := (summable_nat_add_iff (K*N+1)).mpr hs
    have hwf := (summable_nat_add_iff (K*N+1)).mpr positiveWeight_summable
    calc
      _ ≤ ∑' k : ℕ, positiveWeight (k+(K*N+1))*(2*(N : ℝ))^2 := by
        apply Summable.tsum_le_tsum _ hf (hwf.mul_right _)
        intro k
        apply mul_le_mul_of_nonneg_left _ (positiveWeight_nonneg _)
        have hh := mul_self_le_mul_self (abs_nonneg _)
          (canonicalMobiusHead_abs_le_two_mul N hN (k+(K*N+1)))
        simpa only [← pow_two, sq_abs] using hh
      _ = (2*(N : ℝ))^2/((K : ℝ)*(N : ℝ)+1) := by
        rw [tsum_mul_right, positiveWeight_tail_tsum (K*N+1) (Nat.succ_pos _)]
        push_cast
        ring
      _ ≤ (2*(N : ℝ))^2/((K : ℝ)*(N : ℝ)) :=
        div_le_div_of_nonneg_left (sq_nonneg _) (mul_pos hKR hNR) (by linarith)
      _ = _ := by field_simp <;> ring
  have htotal : ‖canonicalMobiusHilbert N‖^2 ≤
      3+2*(K : ℝ)*(N : ℝ)*D^2+4*(N : ℝ)/(K : ℝ) := by
    rw [canonicalMobiusHilbert_norm_sq_split, ← ht.sum_add_tsum_nat_add L]
    simp_rw [hidx]
    have hhead : (N : ℝ)/((N : ℝ)+1) ≤ 1 := by
      apply (div_le_one (by positivity)).mpr
      linarith
    linarith
  apply (div_le_iff₀ hNR).mpr
  calc
    _ ≤ 3+2*(K : ℝ)*(N : ℝ)*D^2+4*(N : ℝ)/(K : ℝ) := htotal
    _ = _ := by field_simp <;> ring

theorem canonicalMobiusHilbert_harmonic_energy_bound (N K : ℕ)
    (hN : 0 < N) (hK : 2 ≤ K) (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hM : ∀ t : ℕ, N ≤ t → |∑ d ∈ Finset.Icc 1 t,
      (ArithmeticFunction.moebius d : ℝ)| ≤ A*(t : ℝ))
    (hm : |mobiusReciprocalSum N| ≤ B) :
    ‖canonicalMobiusHilbert N‖^2/(N : ℝ) ≤
      3/(N : ℝ)+2*(K : ℝ)*(A*((harmonic K : ℝ)+1)+B)^2+4/(K : ℝ) :=
  canonicalMobiusHilbert_linear_window_energy N K hN hK _
    (fun n hn hnK => canonicalMobiusHead_harmonic_window_bound N n K A B hA hB hn hnK hM hm)

open RiemannResearch.NumberTheory.PrimeNumberTheorem in
theorem canonicalMobiusHilbert_eventual_quantitative_energy :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ N : ℕ in atTop, ∀ K J : ℕ, 2 ≤ K → 0 < J →
      ‖canonicalMobiusHilbert N‖^2/(N : ℝ) ≤ 3/(N : ℝ)+2*(K : ℝ)*
        (1/(J : ℝ)+1/((N : ℝ)*(J : ℝ))+
          C*((harmonic K : ℝ)+(harmonic J : ℝ)+2)/Real.log (N : ℝ))^2+4/(K : ℝ) := by
  obtain ⟨C,hC,hM⟩ := exists_M_mul_log_bound_from_quantitative_PNT
  refine ⟨C,hC,?_⟩
  have hm := mobiusReciprocalSum_eventual_cutoff_bound_of_M_log_bound C hC hM
  obtain ⟨Y,hY⟩ := eventually_atTop.mp hM
  have hNY : ∀ᶠ N : ℕ in atTop, Y ≤ (N : ℝ) :=
    (tendsto_natCast_atTop_atTop : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop).eventually
      (eventually_ge_atTop Y)
  filter_upwards [hNY, hm, eventually_ge_atTop (2 : ℕ)] with N hNY hmN hN2
  have hN : 0 < N := by omega
  have hN1 : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hlogN : 0 < Real.log (N : ℝ) := Real.log_pos hN1
  have hbound : ∀ y : ℝ, (N : ℝ) ≤ y → |M y| ≤ (C/Real.log (N : ℝ))*y := by
    intro y hy
    have hy1 : 1 < y := hN1.trans_le hy
    have hlogy : 0 ≤ Real.log y := (Real.log_pos hy1).le
    have hlog : Real.log (N : ℝ) ≤ Real.log y := Real.log_le_log (by positivity) hy
    have hh := hY y (hNY.trans hy)
    rw [abs_mul, abs_of_nonneg hlogy] at hh
    have hl : |M y| *Real.log (N : ℝ) ≤ C*y :=
      (mul_le_mul_of_nonneg_left hlog (abs_nonneg _)).trans hh
    calc
      |M y| ≤ (C*y)/Real.log (N : ℝ) := (le_div_iff₀ hlogN).mpr hl
      _ = _ := by ring
  have hnat : ∀ t : ℕ, N ≤ t → |∑ d ∈ Finset.Icc 1 t,
      (ArithmeticFunction.moebius d : ℝ)| ≤ (C/Real.log (N : ℝ))*(t : ℝ) := by
    intro t hNt
    have hi := M_nat_difference 0 t (Nat.zero_le t)
    have hset : Finset.Ioc 0 t = Finset.Icc 1 t := by
      ext d
      simp only [Finset.mem_Ioc, Finset.mem_Icc]
      omega
    have hzero : M (0 : ℝ) = 0 := by
      have hz : Finset.Iic (0 : ℕ) = {0} := by ext n; simp
      simp [M, hz]
    rw [hset, Nat.cast_zero, hzero, sub_zero] at hi
    rw [← hi]
    exact hbound _ (by exact_mod_cast hNt)
  intro K J hK hJ
  have hb := canonicalMobiusHilbert_harmonic_energy_bound N K hN hK
    (C/Real.log (N : ℝ))
    (1/(J : ℝ)+1/((N : ℝ)*(J : ℝ))+C*((harmonic J : ℝ)+1)/Real.log (N : ℝ))
    (div_nonneg hC hlogN.le) ((abs_nonneg _).trans (hmN J hJ)) hnat (hmN J hJ)
  convert hb using 1 <;> ring



theorem canonicalMobiusHilbert_eventual_optimized_energy :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ N : ℕ in atTop,
      let x := (1+Real.log (Real.log (N : ℝ)+3))/Real.log (N : ℝ)
      ‖canonicalMobiusHilbert N‖^2/(N : ℝ) ≤
        3/(N : ℝ)+(4+2*(2+4*C)^2)*x+4*(2+4*C)^2*x^2 := by
  obtain ⟨C,hC,hE⟩ := canonicalMobiusHilbert_eventual_quantitative_energy
  refine ⟨C,hC,?_⟩
  filter_upwards [hE, eventually_ge_atTop (2 : ℕ)] with N he hN2
  have hN : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hN1 : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  let L := Real.log (N : ℝ)
  let Q := 1+Real.log (L+3)
  let A := 2+4*C
  let x := Q/L
  let J : ℕ := ⌊L⌋₊+1
  let K : ℕ := ⌊L/Q⌋₊+2
  have hL : 0 < L := Real.log_pos hN1
  have hQ1 : 1 ≤ Q := by
    have := Real.log_nonneg (show 1 ≤ L+3 by linarith)
    dsimp [Q]
    linarith
  have hQ : 0 < Q := by linarith
  have hA : 0 ≤ A := by dsimp [A]; linarith
  have hx : 0 < x := div_pos hQ hL
  have hJ : 0 < J := by dsimp [J]; omega
  have hK : 2 ≤ K := by dsimp [K]; omega
  have hJR : (0 : ℝ) < J := by exact_mod_cast hJ
  have hKR : (0 : ℝ) < K := by exact_mod_cast (show 0 < K by omega)
  have hJlo : L < (J : ℝ) := by
    simpa only [J, Nat.cast_add, Nat.cast_one] using Nat.lt_floor_add_one L
  have hJhi : (J : ℝ) ≤ L+1 := by
    have := Nat.floor_le hL.le
    dsimp [J]
    push_cast
    linarith
  have hKhi : (K : ℝ) ≤ L/Q+2 := by
    have := Nat.floor_le (div_nonneg hL.le hQ.le)
    dsimp [K]
    push_cast
    linarith
  have hKlo : L/Q < (K : ℝ) := by
    have := Nat.lt_floor_add_one (L/Q)
    dsimp [K]
    push_cast
    linarith
  have hQdiv : L/Q ≤ L := by
    apply (div_le_iff₀ hQ).mpr
    nlinarith
  have hKlog : Real.log (K : ℝ) ≤ Real.log (L+3) :=
    Real.log_le_log hKR (by linarith)
  have hJlog : Real.log (J : ℝ) ≤ Real.log (L+3) :=
    Real.log_le_log hJR (by linarith)
  have hharm : (harmonic K : ℝ)+(harmonic J : ℝ)+2 ≤ 4*Q := by
    have hHK := harmonic_le_one_add_log K
    have hHJ := harmonic_le_one_add_log J
    dsimp [Q] at *
    linarith
  have hJinv : 1/(J : ℝ) ≤ 1/L :=
    div_le_div_of_nonneg_left zero_le_one hL hJlo.le
  have hNJ : (J : ℝ) ≤ (N : ℝ)*(J : ℝ) := by nlinarith
  have hNJinv : 1/((N : ℝ)*(J : ℝ)) ≤ 1/L :=
    (div_le_div_of_nonneg_left zero_le_one hJR hNJ).trans hJinv
  let D := 1/(J : ℝ)+1/((N : ℝ)*(J : ℝ))+
    C*((harmonic K : ℝ)+(harmonic J : ℝ)+2)/L
  have hHK0 : 0 ≤ (harmonic K : ℝ) := by
    have he : (harmonic K : ℝ) = ∑ j ∈ Finset.Icc 1 K, 1/(j : ℝ) := by
      simp [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast, one_div]
    rw [he]
    exact Finset.sum_nonneg (fun j hj => by positivity)
  have hHJ0 : 0 ≤ (harmonic J : ℝ) := by
    have he : (harmonic J : ℝ) = ∑ j ∈ Finset.Icc 1 J, 1/(j : ℝ) := by
      simp [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast, one_div]
    rw [he]
    exact Finset.sum_nonneg (fun j hj => by positivity)
  have hD : 0 ≤ D := by
    dsimp [D]
    exact add_nonneg (add_nonneg (by positivity) (by positivity))
      (div_nonneg (mul_nonneg hC (by linarith)) hL.le)
  have hDhi : D ≤ A*x := by
    have hh := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hharm hC) hL.le
    have hQL := (div_le_div_of_nonneg_right hQ1 hL.le)
    calc
      D ≤ 1/L+1/L+C*(4*Q)/L := add_le_add (add_le_add hJinv hNJinv) hh
      _ = 2*(1/L)+C*(4*Q)/L := by ring
      _ ≤ 2*(Q/L)+C*(4*Q)/L :=
        add_le_add (mul_le_mul_of_nonneg_left hQL (by norm_num : (0 : ℝ) ≤ 2)) le_rfl
      _ = A*x := by dsimp [A,x]; ring
  have hKinv : 1/(K : ℝ) ≤ x := by
    apply (div_le_iff₀ hKR).mpr
    have hh := (div_lt_iff₀ hQ).mp hKlo
    dsimp [x]
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ hL).mpr
    nlinarith
  have hKx : (K : ℝ) ≤ 1/x+2 := by
    have hxinv : 1/x = L/Q := by dsimp [x]; field_simp
    rw [hxinv]
    exact hKhi
  have hsq : D^2 ≤ (A*x)^2 := (sq_le_sq₀ hD (mul_nonneg hA hx.le)).mpr hDhi
  have hm : 2*(K : ℝ)*D^2 ≤ 2*(1/x+2)*(A*x)^2 := by
    have hh := mul_le_mul_of_nonneg_left hsq (show 0 ≤ 2*(K : ℝ) by positivity)
    have hh' := mul_le_mul_of_nonneg_right hKx (sq_nonneg (A*x))
    nlinarith
  have hid : 2*(1/x+2)*(A*x)^2 = 2*A^2*x+4*A^2*x^2 := by
    field_simp
    <;> ring
  have hh := he K J hK hJ
  change ‖canonicalMobiusHilbert N‖^2/(N : ℝ) ≤
    3/(N : ℝ)+2*(K : ℝ)*D^2+4/(K : ℝ) at hh
  change ‖canonicalMobiusHilbert N‖^2/(N : ℝ) ≤
    3/(N : ℝ)+(4+2*A^2)*x+4*A^2*x^2
  rw [hid] at hm
  have hki : 4/(K : ℝ) ≤ 4*x := by
    calc
      _ = 4*(1/(K : ℝ)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hKinv (by norm_num)
  nlinarith



def canonicalMobiusEnergyRate (N : ℕ) : ℝ :=
  (1+Real.log (Real.log (N : ℝ)+3))/Real.log (N : ℝ)

def canonicalMobiusEnergyCeiling (C : ℝ) (N : ℕ) : ℝ :=
  3/(N : ℝ)+(4+2*(2+4*C)^2)*canonicalMobiusEnergyRate N+
    4*(2+4*C)^2*(canonicalMobiusEnergyRate N)^2

def canonicalMobiusResidualCeiling (C : ℝ) (N : ℕ) : ℝ :=
  2*canonicalMobiusEnergyCeiling C N+3/(N : ℝ)

theorem canonicalMobiusEnergyRate_tendsto_zero :
    Tendsto canonicalMobiusEnergyRate atTop (𝓝 0) := by
  have hL : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hY : Tendsto (fun N : ℕ => Real.log (N : ℝ)+3) atTop atTop :=
    tendsto_atTop_mono (fun N => by linarith) hL
  have hlog := Real.tendsto_pow_log_div_pow_atTop 1 1 (by norm_num : (0 : ℝ) < 1)
  simp only [Real.rpow_one, pow_one] at hlog
  have hi : Tendsto (fun y : ℝ => 1/y) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  have hfirst := (hi.add hlog).comp hY
  have hsecond : Tendsto (fun N : ℕ => 1+3*(1/Real.log (N : ℝ))) atTop (𝓝 1) := by
    simpa using (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).add
      ((hi.comp hL).const_mul 3)
  have hprod := hfirst.mul hsecond
  simp only [Function.comp_def, zero_add, mul_zero, add_zero, zero_mul] at hprod
  apply hprod.congr'
  filter_upwards [eventually_ge_atTop (2 : ℕ)] with N hN
  have hNR : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hL0 : 0 < Real.log (N : ℝ) := Real.log_pos hNR
  have hY0 : 0 < Real.log (N : ℝ)+3 := by linarith
  dsimp [canonicalMobiusEnergyRate]
  field_simp [hL0.ne',hY0.ne']
  <;> ring

theorem canonicalMobiusEnergyCeiling_tendsto_zero (C : ℝ) :
    Tendsto (canonicalMobiusEnergyCeiling C) atTop (𝓝 0) := by
  have hi := (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul 3
  have hx := canonicalMobiusEnergyRate_tendsto_zero
  have hh := (hi.add (hx.const_mul (4+2*(2+4*C)^2))).add
    ((hx.pow 2).const_mul (4*(2+4*C)^2))
  simp only [mul_zero, zero_add, add_zero, zero_pow (by norm_num : 2 ≠ 0)] at hh
  convert hh using 1
  ext N
  simp only [canonicalMobiusEnergyCeiling]
  ring

theorem canonicalMobiusResidualCeiling_tendsto_zero (C : ℝ) :
    Tendsto (canonicalMobiusResidualCeiling C) atTop (𝓝 0) := by
  have hh := ((canonicalMobiusEnergyCeiling_tendsto_zero C).const_mul 2).add
    ((tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul 3)
  simp only [mul_zero, zero_add] at hh
  convert hh using 1
  ext N
  simp only [canonicalMobiusResidualCeiling]
  ring

theorem canonicalMobiusEnergyRate_nonneg (N : ℕ) (hN : 2 ≤ N) :
    0 ≤ canonicalMobiusEnergyRate N := by
  have hNR : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hL : 0 < Real.log (N : ℝ) := Real.log_pos hNR
  have hY : 0 ≤ Real.log (Real.log (N : ℝ)+3) :=
    Real.log_nonneg (by linarith)
  unfold canonicalMobiusEnergyRate
  positivity

theorem canonicalMobiusEnergyCeiling_nonneg (C : ℝ) (N : ℕ) (hN : 2 ≤ N) :
    0 ≤ canonicalMobiusEnergyCeiling C N := by
  have hx := canonicalMobiusEnergyRate_nonneg N hN
  unfold canonicalMobiusEnergyCeiling
  positivity

theorem canonicalMobiusResidual_norm_sq_le (N : ℕ) :
    ‖hilbertOne-canonicalMobiusHilbert N‖^2 ≤ 2*‖canonicalMobiusHilbert N‖^2+2 := by
  have hh := mul_self_le_mul_self (norm_nonneg (hilbertOne-canonicalMobiusHilbert N))
    (norm_sub_le hilbertOne (canonicalMobiusHilbert N))
  have hone := hilbertOne_norm_sq
  have hs := sq_nonneg (‖hilbertOne‖-‖canonicalMobiusHilbert N‖)
  nlinarith

theorem canonicalMobiusResidualCeiling_lower (C : ℝ) (N : ℕ) (hN : 2 ≤ N) :
    1/((N : ℝ)+1) ≤ canonicalMobiusResidualCeiling C N := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hB := canonicalMobiusEnergyCeiling_nonneg C N hN
  have hh : 1/((N : ℝ)+1) ≤ 3/(N : ℝ) := by
    apply (div_le_div_iff₀ (by positivity) hNR).mpr
    linarith
  unfold canonicalMobiusResidualCeiling
  linarith

theorem canonicalMobiusResidualCeiling_norm_bound (C : ℝ) (N : ℕ) (hN : 2 ≤ N)
    (he : ‖canonicalMobiusHilbert N‖^2/(N : ℝ) ≤ canonicalMobiusEnergyCeiling C N) :
    ‖hilbertOne-canonicalMobiusHilbert N‖^2 ≤
      ((N : ℝ)+1)*canonicalMobiusResidualCeiling C N := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hB := canonicalMobiusEnergyCeiling_nonneg C N hN
  have hf := (div_le_iff₀ hNR).mp he
  have hr := canonicalMobiusResidual_norm_sq_le N
  have hi : 0 ≤ 3/(N : ℝ) := by positivity
  have heq : ((N : ℝ)+1)*canonicalMobiusResidualCeiling C N =
      2*(N : ℝ)*canonicalMobiusEnergyCeiling C N+
        2*canonicalMobiusEnergyCeiling C N+3+3/(N : ℝ) := by
    unfold canonicalMobiusResidualCeiling
    field_simp [hNR.ne']
    <;> ring
  rw [heq]
  nlinarith

theorem canonicalMobiusResidual_eventual_explicit_ceiling :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ N : ℕ in atTop,
      1/((N : ℝ)+1) ≤ canonicalMobiusResidualCeiling C N ∧
      ‖hilbertOne-canonicalMobiusHilbert N‖^2 ≤
        ((N : ℝ)+1)*canonicalMobiusResidualCeiling C N := by
  obtain ⟨C,hC,hE⟩ := canonicalMobiusHilbert_eventual_optimized_energy
  refine ⟨C,hC,?_⟩
  filter_upwards [hE, eventually_ge_atTop (2 : ℕ)] with N he hN
  exact ⟨canonicalMobiusResidualCeiling_lower C N hN,
    canonicalMobiusResidualCeiling_norm_bound C N hN he⟩

end RiemannResearch.RH.Pareto
