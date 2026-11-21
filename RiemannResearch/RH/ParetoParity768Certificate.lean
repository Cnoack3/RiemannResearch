import RiemannResearch.RH.ParetoParity8192Data
import RiemannResearch.RH.ParetoParityNormBounds
import RiemannResearch.RH.ParetoRawTrialPeriodicTail
import RiemannResearch.RH.ParetoUniformJordanVariance
import Mathlib.Tactic

/-! # The conductor-768 Pareto parity certificate

This proof candidate uses the coefficients from appendix B of *Orthogonal
projection of parity under the Pareto law* (20 November 2026). It adapts the
physical-site sieve and Jordan factorization in Cnoack3/RiemannResearch,
commit 20d4714f0640886c24c712b26f1dba23da0463ba. The supporting external
script prints the sixteen claimed block totals independently. The heavy Lean
reductions appear as separate declarations, so the trust boundary is visible.
-/

open scoped BigOperators
namespace RiemannResearch.RH.Pareto.PrimePowerSchur.Conductor768


private def row0 : ℕ := signedRow![
  4839505, 3214003, 146013, 1788126, -1337889, 1209098, -642, 12322,
  -738745, 713463, -57059, 589683, -494778, -479904, 1690, 423574,
  -21974, 377945, -21448, -324187, -299443, 303852, 11377, 3331,
  -246778, 4365, -24626, 224975, 190079, 200942, -3022, -194119,
  -160383, -167188, 13147, 170420, -157279, -161025, 1331, 144716,
  120951, 143669, 90, -7537, -132369, 128413, 127, -3993,
  -4942, -111005, -1854, 115524, 4396, -106840, 7916, -95975,
  -90531, 88809, 6778, 94083, -78990, -5739, 9108, -86336,
  81706, 81867, -15661, -81851, 66027, 71994, -4577, 68386,
  -72290, 38, 3952, -72272, 68973, 62920, -3, -161,
  -56334, 57648, 15305, -59693, -56431, -58119, -581, 58776,
  9992, -56872, 7355, -50262, -50073, -57883, 360, 51987,
  -1551, 5749, 718, 51297, 32589, 47820, -10034, 43812,
  -51463, 46069, -8495, 44485, 44141, -45058, 1113, 39093,
  42192, -44640, -700, -1239, -30216, -37599, -418, 4441,
  -40982, -36286, -3526, -510, 8824, 41619, -6835, -40519
]

private def row1 : ℕ := signedRow![
  38012, 34389, 1917, -35304, -34464, -84, 4252, 29836,
  29510, 34626, 6836, -29476, -34052, -33114, 6091, -27559,
  -25500, 4894, -5144, 25304, 4411, 25397, 1466, -1061,
  33915, -26535, -2652, 27102, -24734, -29136, 22, -29694,
  2202, 23841, -2778, 31989, -23017, 23609, -7480, -1453,
  19655, 1746, -7478, 26899, 18560, 722, -541, -21766,
  -30641, 24826, -1478, 26855, 21137, -23958, -6073, -25223,
  20932, -19537, -5696, 4887, 25875, 25097, -9705, 23408,
  -21343, 22560, 308, 21922, -6599, 21976, 835, -22472,
  -19039, -23823, 13769, -19675, -15453, 3853, 6125, -19314,
  -17228, 22235, 393, -16841, -14276, -20923, 1066, -19078,
  -16260, -15708, 345, -15089, 19209, 18701, -2732, 1690,
  -14035, 13707, -5987, 15862, 18492, 24628, 114, 17296,
  -1848, -21914, 5068, -20561, 12281, 16791, -2000, 12386,
  -5220, 1070, 2725, 2765, 17927, -22630, 2073, -15008,
  2649, 13480, -7586, -14951, -17212, 18113, 1992, 16274
]

private def row2 : ℕ := signedRow![
  13126, -14165, -1668, -328, -12408, 15211, -4112, -16853,
  12120, -17908, 1210, 16319, -2791, 10726, 980, 14070,
  -12741, 3497, 3303, 13328, -17209, -1424, -3848, 11406,
  9240, 12335, -177, 17716, 16752, -12911, -2124, -176,
  10407, -15347, -1000, 11424, 3056, -11094, 1984, -1963,
  -5525, -10814, -4074, -9562, -5854, -13049, -5839, -15352,
  6124, 11106, -2760, -15019, 10406, 11721, 4003, 11826,
  -12656, 3704, 1317, 11632, 9823, -14959, 2376, -12207,
  12966, -8267, 5177, -207, -12395, -11400, 2399, -10344,
  -15009, 13471, -4144, 1334, -4716, -12692, -847, 11866,
  -325, -11849, 8002, -7074, -611, 12, 797, 13850,
  -11557, 11264, -1882, 12245, 1018, -1585, -4294, 12413,
  10050, -13159, 161, 13193, -9838, 7363, -4129, 1008,
  -7747, -165, 1988, -9922, 9905, 10155, 3996, 1113,
  8733, -16009, -1176, 10799, 10570, 362, 3451, -7573,
  -5528, 6357, -3211, -11213, -12529, 10934, 4377, 6379
]

private def row3 : ℕ := signedRow![
  -9370, 2009, 2091, 7799, -12646, -6802, -473, -5430,
  -8460, -7438, -342, 6559, -7674, 6837, -2217, 5564,
  12304, -6220, -1879, 3071, 9113, -7041, -7037, 5613,
  8961, -3472, -3583, -5793, 3037, -4723, -384, -6279,
  5002, 7235, -1823, 5114, -9892, -488, 740, -2855,
  11732, -6516, -3451, 5704, 12268, 6206, -835, 4620,
  5433, 4645, -1491, -4238, 6522, 5575, -1738, -202,
  7715, 6030, 281, -6375, -9378, -5078, -132, 4730,
  -4301, -6898, 204, -2587, -5176, 5755, 451, 5671,
  -5173, 449, -675, 3466, -14518, 4533, -857, 7842,
  -8208, 6057, 1863, -4767, 10730, -3856, -3500, -7240,
  7746, 72, 2709, 792, -4471, 3731, 75, -5865,
  -3613, 6498, 1976, -5378, -3121, 6283, 520, -5236,
  -3096, 6251, -1983, -4970, 9220, -1410, -1142, -6999,
  7964, 6627, 1146, -7056, -4869, 6138, 3826, -8424,
  7009, 2143, -635, 6599, -4512, -2331, -504, -3973
]

private def row4 : ℕ := signedRow![
  -8676, -4462, 7372, -2868, 4969, -6028, 330, 1840,
  1652, 6023, -738, 1017, -6886, -4295, 3379, -4436,
  6833, -380, 3960, -3952, 11318, -1660, -2417, -5310,
  -5376, -2324, 1835, 3833, -3249, -2602, -1243, -5711,
  -4837, 4067, 3256, 21, -2285, -4179, 1064, -3997,
  -5301, 6207, 3088, 3716, 1873, -3956, -736, 2236,
  -5207, 2314, 3697, -713, -3768, -2267, -235, 3356,
  -10681, 1494, -906, -7299, 6224, 304, 2254, 5952,
  -1681, -7867, -1344, -3299, 6439, -3206, -2011, 2294,
  -4876, 6223, -3165, -4996, 5145, -4317, -25, 6887,
  3450, 556, -875, -4403, 2192, 2292, 2458, 5039,
  2900, -1602, -1050, -1593, 3822, 2486, 2366, 4912,
  7730, -3038, -3386, 1693, -6942, 3325, 1745, 4779,
  7771, 4893, 166, -2618, -6362, -4781, -965, 1282,
  -5622, 3126, -1050, -2189, -1590, 4267, -571, -3893,
  -7409, -5645, 1786, -108, 7688, -226, -830, 4283
]

private def row5 : ℕ := signedRow![
  3001, 2157, 823, 4335, 2453, 2213, -2014, -4857,
  124, 5755, 3755, 3732, 4217, -2236, -2885, -1581,
  4138, 2036, 1201, 3821, -5036, 3671, 765, 2274,
  735, -3071, -928, -4196, 5370, -3445, 2240, 2883,
  -6267, -1169, 496, 3913, 5017, -4544, -424, -4466,
  1274, 3279, 1817, -3219, 20, -2128, 1110, -3489,
  -5631, 4610, -1947, -1041, -5609, -4009, 2859, -4041,
  -6820, -2197, -8, 1623, 42, -2488, 3209, 5335,
  -7446, -3766, -3570, 3538, 7991, 2703, 2756, -2786,
  -3001, 4010, -492, -3453, -4326, 3961, 1583, -3941,
  -1529, -2369, -2208, -126, 3715, 6408, -464, 460,
  1718, -4947, -393, 3045, -4933, 307, -2442, -4636,
  -1423, 2430, 1888, 6526, 7194, 2861, 1078, -2982,
  -3143, 1324, -2026, -4094, -1501, 3477, -1624, -1624,
  3210, -3831, 3793, 3534, -3218, 714, 2744, 3982,
  4873, -4645, 1188, -64, -4905, -2106, -1621
]

private def chunks : ℕ → ℕ
  | 0 => row0 | 1 => row1 | 2 => row2
  | 3 => row3 | 4 => row4 | 5 => row5
  | _ => 0

def coeff (d : ℕ) : ℤ :=
  if 2 ≤ d ∧ d ≤ 768 then
    let i := d - 2
    let row := chunks (i/128)
    let digit : ℕ := (row >>> (31*(i%128))) % 2^31
    (digit : ℤ) - 2^30
  else 0

def support : Finset ℕ := Finset.Icc 2 768

/-- Descending integer accumulation. This is definitionally a tail call at
each site and avoids building an interval during kernel evaluation. -/
def intFold (f : ℕ → ℤ) : ℕ → ℤ → ℤ
  | 0, a => a
  | n+1, a => intFold f n (a + f n)

theorem intFold_eq (f : ℕ → ℤ) (n : ℕ) (a : ℤ) :
    intFold f n a = a + ∑ j ∈ Finset.range n, f j := by
  induction n generalizing a with
  | zero => simp [intFold]
  | succ n ih =>
    rw [intFold,ih,Finset.sum_range_succ]
    abel

theorem intFold_support (f : ℕ → ℤ) :
    intFold (fun j => f (j+2)) 767 0 = ∑ d ∈ support, f d := by
  rw [intFold_eq,zero_add]
  apply Finset.sum_bij (fun i _ => i+2)
  · intro i hi
    have := Finset.mem_range.mp hi
    exact Finset.mem_Icc.mpr ⟨by omega,by omega⟩
  · intro i hi j hj he
    omega
  · intro d hd
    obtain ⟨h2,ht⟩ := Finset.mem_Icc.mp hd
    exact ⟨d-2,Finset.mem_range.mpr (by omega),by omega⟩
  · intro i hi
    rfl

def fastSum (f : ℕ → ℤ) : ℤ := intFold (fun j => f (j+2)) 767 0

theorem fastSum_spec (f : ℕ → ℤ) : fastSum f = ∑ d ∈ support, f d :=
  intFold_support f

def residual (n : ℕ) : ℤ :=
  10^7 - ∑ d ∈ support, coeff d * ((n%d : ℕ) : ℤ)

def roundedUnit (n : ℕ) : ℕ :=
  let den := n*(n+1)
  ((residual n).natAbs ^ 2 + (den-1)) / den

def roundedHead (T : ℕ) : ℕ := ∑ i ∈ Finset.range T, roundedUnit (i+1)

def twiceMean : ℤ := 2*10^7 - ∑ d ∈ support, coeff d * ((d : ℤ)-1)

def oscillation : ℤ := ∑ d ∈ support, abs (coeff d) * (d : ℤ) * ((d : ℤ)-1)

def covariance : ℤ := ∑ d ∈ support, ∑ e ∈ support,
  coeff d * coeff e * (((d.gcd e : ℕ) : ℤ)^2-1)



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
  ∑ j ∈ Finset.range (768/k), coeff (k*(j+1))

private theorem multipleSum_spec {k : ℕ} (hk : k ∈ support) :
    (multipleSum k : ℝ) =
      ∑ d ∈ support, (coeff d : ℝ)*divisorIncidence d k := by
  have h2 := (Finset.mem_Icc.mp hk).1
  have hk0 : 0 < k := by omega
  have hinj : Function.Injective (fun j : ℕ => k*(j+1)) := by
    intro i j hij
    exact Nat.add_right_cancel (Nat.eq_of_mul_eq_mul_left hk0 hij)
  have himg : (Finset.range (768/k)).image (fun j => k*(j+1)) =
      support.filter (fun d => k ∣ d) := by
    ext d
    simp only [Finset.mem_image,Finset.mem_range,Finset.mem_filter,support,Finset.mem_Icc]
    constructor
    · rintro ⟨j,hj,rfl⟩
      refine ⟨⟨by nlinarith,?_⟩,dvd_mul_right _ _⟩
      have hq := (Nat.le_div_iff_mul_le hk0).mp (show j+1≤768/k by omega)
      simpa only [Nat.mul_comm] using hq
    · rintro ⟨⟨hd,hle⟩,m, rfl⟩
      have hm : 0 < m := by cases m with
        | zero => simp at hd
        | succ m => omega
      refine ⟨m-1, ?_,by rw [Nat.sub_add_cancel hm]⟩
      have hq := (Nat.le_div_iff_mul_le hk0).mpr (by simpa [Nat.mul_comm] using hle)
      omega
  rw [multipleSum,Int.cast_sum]
  change (∑ j ∈ Finset.range (768/k), (coeff (k*(j+1)) : ℝ)) = _
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
  have hgB : g ≤ 768 := (Nat.le_of_dvd hd0 (Nat.gcd_dvd_left d e)).trans (Finset.mem_Icc.mp hd).2
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

def jordanEnergy : ℤ := ∑ k ∈ support, (jordanFuel 10 k : ℤ)*(multipleSum k)^2

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
        (show k ≤ 2^10 by have h := (Finset.mem_Icc.mp hk).2; omega)]

private def fastMultiple (k : ℕ) : ℤ :=
  intFold (fun j => coeff (k*(j+1))) (768/k) 0

private theorem fastMultiple_spec (k : ℕ) : fastMultiple k = multipleSum k := by
  simp [fastMultiple,multipleSum,intFold_eq]

def fastJordan : ℤ :=
  fastSum (fun k => (jordanFuel 10 k : ℤ) * (fastMultiple k)^2)

theorem fastJordan_spec : fastJordan = jordanEnergy := by
  unfold fastJordan jordanEnergy
  rw [fastSum_spec]
  simp only [fastMultiple_spec]


set_option maxRecDepth 100000
set_option maxHeartbeats 100000000

theorem twiceMean_value : twiceMean = 218240 := by
  have hc : fastSum (fun d => coeff d*((d:ℤ)-1)) = 19781760 := by decide +kernel
  rw [fastSum_spec] at hc
  unfold twiceMean
  rw [hc]
  decide

theorem oscillation_value : oscillation = 658340882348 :=
  (fastSum_spec (fun d => abs (coeff d)*(d:ℤ)*((d:ℤ)-1))).symm.trans
    (by decide +kernel)

theorem covariance_value : covariance = 3118747506858140 :=
  covariance_eq_jordanEnergy.trans (fastJordan_spec.symm.trans
    (by decide +kernel : fastJordan = 3118747506858140))


def coefficientSum : ℤ := ∑ d ∈ support, coeff d

private theorem residue_succ (n d : ℕ) (hd : 2 ≤ d) :
    (((n+1)%d : ℕ) : ℤ) = (n%d : ℕ) + 1 - (if d ∣ n+1 then (d:ℤ) else 0) := by
  have hr := Nat.mod_lt n (show 0 < d by omega)
  have h : (n + 1) % d = (n % d + 1) % d := by
    rw [Nat.add_mod n 1, Nat.mod_eq_of_lt (show 1 < d by omega)]
  by_cases hwrap : n%d + 1 = d
  · have hz : (n+1)%d = 0 := by rw [h,hwrap,Nat.mod_self]
    rw [if_pos (Nat.dvd_of_mod_eq_zero hz),hz]
    omega
  · have hlt : n%d + 1 < d := by omega
    rw [Nat.mod_eq_of_lt hlt] at h
    have hnd : ¬ d ∣ n+1 := fun hdiv => by
      have hz := Nat.mod_eq_zero_of_dvd hdiv
      omega
    rw [if_neg hnd,h]
    push_cast
    ring

theorem residual_succ (n : ℕ) :
    residual (n+1) = residual n - coefficientSum +
      ∑ d ∈ support.filter (fun d => d ∣ n+1), (d:ℤ) * coeff d := by
  have hsum : (∑ d ∈ support, coeff d * (((n+1)%d : ℕ) : ℤ)) =
      (∑ d ∈ support, coeff d * ((n%d : ℕ):ℤ)) + coefficientSum -
        ∑ d ∈ support.filter (fun d => d∣n+1), (d:ℤ)*coeff d := by
    rw [coefficientSum,Finset.sum_filter,← Finset.sum_add_distrib,← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun d hd => ?_
    rw [residue_succ n d (Finset.mem_Icc.mp hd).1]
    by_cases hdiv : d ∣ n+1 <;> simp [hdiv] <;> ring
  unfold residual
  rw [hsum]
  ring

/-- Blocks starting at `length*b+1` partition the physical head exactly. -/
theorem roundedHead_eq_blocks (length blocks : ℕ) :
    roundedHead (length*blocks) =
      ∑ b ∈ Finset.range blocks, ∑ j ∈ Finset.range length,
        roundedUnit (length*b+j+1) := by
  unfold roundedHead
  induction blocks with
  | zero => simp
  | succ b ih => rw [Nat.mul_succ,Finset.sum_range_add,ih,Finset.sum_range_succ]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 100000000 in
-- The reduction reads all 8191 signed coefficient digits.
theorem coefficientSum_value : coefficientSum = 9835393 :=
  (fastSum_spec coeff).symm.trans (by decide +kernel)



private def addAt {len : ℕ} (v : Vector ℤ len) (index : ℕ) (amount : ℤ) : Vector ℤ len :=
  if h : index < len then v.set index (v[index] + amount) else v

private theorem get_addAt {len : ℕ} (v : Vector ℤ len) (index j : ℕ) (hj : j < len)
    (amount : ℤ) :
    (addAt v index amount)[j] = v[j] + if index = j then amount else 0 := by
  by_cases h : index < len
  · simp only [addAt,dif_pos h,Vector.getElem_set]
    split_ifs with hsame
    · subst j
      rfl
    · simp
  · have hn : index ≠ j := by omega
    simp [addAt,h,hn]

private def site (lo d k : ℕ) := d*(lo/d+k+1)

private theorem lt_site (lo d k : ℕ) (hd : 0 < d) : lo < site lo d k := by
  have h := Nat.lt_mul_div_succ lo hd
  exact h.trans_le (Nat.mul_le_mul_left d (by omega))

/-- Apply a conductor's updates in reverse order. The recursion is tail-recursive. -/
private def mark {len : ℕ} (lo d : ℕ) (amount : ℤ) : ℕ → Vector ℤ len → Vector ℤ len
  | 0, v => v
  | k+1, v =>
    mark lo d amount k (addAt v (site lo d k - (lo+1)) amount)

private theorem get_mark {len : ℕ} (lo d j : ℕ) (hd : 0 < d) (hj : j<len)
    (amount : ℤ) (count : ℕ) (v : Vector ℤ len) :
    (mark lo d amount count v)[j] = v[j] +
      ∑ k ∈ Finset.range count, if site lo d k = lo+j+1 then amount else 0 := by
  induction count generalizing v with
  | zero => simp [mark]
  | succ k ih =>
    rw [mark,ih,get_addAt _ _ _ hj,Finset.sum_range_succ]
    have he : site lo d k - (lo+1) = j ↔ site lo d k = lo+j+1 := by
      have := lt_site lo d k hd
      omega
    simp only [he]
    ring

private theorem sum_hits (lo len d j : ℕ) (hd : 0 < d) (hj : j<len) (amount : ℤ) :
    (∑ k ∈ Finset.range ((lo+len)/d-lo/d),
      if site lo d k = lo+j+1 then amount else 0) =
        if d ∣ lo+j+1 then amount else 0 := by
  by_cases h : d ∣ lo+j+1
  · let m := (lo+j+1)/d
    have hm : d*m = lo+j+1 := Nat.mul_div_cancel' h
    have hlow : lo/d < m := (Nat.div_lt_iff_lt_mul hd).mpr (by rw [Nat.mul_comm,hm]; omega)
    have hhigh : m ≤ (lo+len)/d := Nat.div_le_div_right (by omega)
    let k := m-lo/d-1
    have hindex : lo/d+k+1 = m := by dsimp [k]; omega
    have hsite : site lo d k = lo+j+1 := by rw [site,hindex,hm]
    have hk : k ∈ Finset.range ((lo+len)/d-lo/d) := Finset.mem_range.mpr (by dsimp [k]; omega)
    rw [if_pos h,Finset.sum_eq_single_of_mem k hk]
    · simp [hsite]
    · intro t ht htk
      have hn : site lo d t ≠ lo+j+1 := by
        intro he
        have he' := Nat.eq_of_mul_eq_mul_left hd (he.trans hsite.symm)
        change lo/d+t+1 = lo/d+k+1 at he'
        omega
      simp [hn]
  · rw [if_neg h]
    apply Finset.sum_eq_zero
    intro k hk
    have hn : site lo d k ≠ lo+j+1 := by
      intro he
      apply h
      rw [← he]
      exact dvd_mul_right d (lo/d+k+1)
    simp [hn]

private def sieveSteps {len : ℕ} (lo : ℕ) : ℕ → Vector ℤ len → Vector ℤ len
  | 0, v => v
  | k+1, v =>
    let d := k+2
    let count := (lo+len)/d-lo/d
    sieveSteps lo k (mark lo d ((d:ℤ)*coeff d) count v)

private theorem get_sieveSteps {len : ℕ} (lo j k : ℕ) (hj : j<len) (v : Vector ℤ len) :
    (sieveSteps lo k v)[j] = v[j] +
      ∑ i ∈ Finset.range k, if i+2 ∣ lo+j+1 then ((i+2:ℕ):ℤ)*coeff (i+2) else 0 := by
  induction k generalizing v with
  | zero => simp [sieveSteps]
  | succ k ih =>
    rw [sieveSteps,ih,get_mark _ _ _ (by omega) hj,sum_hits _ _ _ _ (by omega) hj,
      Finset.sum_range_succ]
    ring

private theorem sum_dictionary (f : ℕ → ℤ) :
    (∑ i ∈ Finset.range 767, f (i+2)) = ∑ d ∈ support, f d := by
  simpa only [intFold_eq,zero_add] using intFold_support f

private def physicalSteps (lo len : ℕ) : Vector ℤ len :=
  sieveSteps lo 767 (Vector.replicate len (-9835393))

private theorem physicalSteps_spec (lo len j : ℕ) (hj : j<len) :
    (physicalSteps lo len)[j] = residual (lo+j+1) - residual (lo+j) := by
  rw [physicalSteps,get_sieveSteps _ _ _ hj,Vector.getElem_replicate hj,
    sum_dictionary (fun d => if d ∣ lo+j+1 then (d:ℤ)*coeff d else 0),
    ← Finset.sum_filter,residual_succ,coefficientSum_value]
  ring

private def roundedLoss (n : ℕ) (e : ℤ) : ℕ :=
  let den := n*(n+1)
  (e.natAbs^2+(den-1))/den

private def scan {len : ℕ} (steps : Vector ℤ len) (lo : ℕ) :
    (count index : ℕ) → ℤ → ℕ → ℕ
  | 0, _, _, total => total
  | count+1, i, e, total =>
    let next := e + (steps[i]?).getD 0
    scan steps lo count (i+1) next (total + roundedLoss (lo+i+1) next)

private theorem scan_spec {len : ℕ} (lo count i acc : ℕ) (h : i+count ≤ len) :
    scan (physicalSteps lo len) lo count i (residual (lo+i)) acc =
      acc + ∑ j ∈ Finset.range count, roundedUnit (lo+i+j+1) := by
  induction count generalizing i acc with
  | zero => simp [scan]
  | succ count ih =>
    have hi : i < len := by omega
    have hnext : residual (lo+i) + ((physicalSteps lo len)[i]?).getD 0 =
        residual (lo+(i+1)) := by
      rw [Vector.getElem?_eq_getElem hi,Option.getD_some,physicalSteps_spec _ _ _ hi]
      rw [← Nat.add_assoc]
      ring
    rw [scan,hnext,ih (i+1) _ (by omega),Finset.sum_range_succ']
    simp only [Nat.add_zero,roundedLoss,roundedUnit]
    simp only [Nat.add_assoc,Nat.add_left_comm,Nat.add_comm]

private def startingResidual (lo : ℕ) : ℤ :=
  10^7 - fastSum (fun d => coeff d * ((lo%d : ℕ):ℤ))

private theorem startingResidual_spec (lo : ℕ) : startingResidual lo = residual lo := by
  unfold startingResidual residual
  rw [fastSum_spec]

/-- Executable exact integer head of sites `lo+1` through `lo+length`. -/
def sievedBlock (lo length : ℕ) : ℕ :=
  scan (physicalSteps lo length) lo length 0 (startingResidual lo) 0

theorem sievedBlock_spec (lo length : ℕ) :
    sievedBlock lo length = ∑ j ∈ Finset.range length, roundedUnit (lo+j+1) := by
  simpa [sievedBlock,startingResidual_spec] using scan_spec lo length 0 0 (show 0+length≤length by omega)


/-- A coarse block of 262144 sites comprises 1024 blocks of length 256.
The short blocks keep the intermediate vectors bounded during reduction. -/
def integerBlock (g : ℕ) : ℕ :=
  (List.range 1024).foldl
    (fun a j => a + sievedBlock (256 * (1024*g+j)) 256) 0

private theorem sum_range_foldl (f : ℕ → ℕ) (n a : ℕ) :
    (List.range n).foldl (fun t i => t+f i) a = a + ∑ i ∈ Finset.range n, f i := by
  induction n with
  | zero => simp
  | succ n ih => simp [List.range_succ,List.foldl_append,ih,Finset.sum_range_succ,Nat.add_assoc]

private theorem sum_range_groups (f : ℕ → ℕ) (length count : ℕ) :
    (∑ i ∈ Finset.range (length*count), f i) =
      ∑ g ∈ Finset.range count, ∑ j ∈ Finset.range length, f (length*g+j) := by
  induction count with
  | zero => simp
  | succ g ih => rw [Nat.mul_succ,Finset.sum_range_add,ih,Finset.sum_range_succ]



theorem roundedHead_eq_integerBlocks :
    roundedHead (2^22) = ∑ g ∈ Finset.range 16, integerBlock g := by
  rw [show (2^22 : ℕ) = 256*(1024*16) by norm_num, roundedHead_eq_blocks]
  simp_rw [← sievedBlock_spec]
  rw [sum_range_groups]
  apply Finset.sum_congr rfl
  intro g hg
  unfold integerBlock
  rw [sum_range_foldl, zero_add]

noncomputable def energyBudget : ℝ :=
  1987639569969424585050133 / 293203310455500000000000000

open CoefficientStabilization

private theorem head_term_le (n : ℕ) (hn : 0 < n) :
    positiveWeight n * (RawTrialTail.error support (fun d => (coeff d : ℝ)) (10^7) n)^2 ≤
      (roundedUnit n : ℝ) := by
  have hreal : (residual n : ℝ) =
      RawTrialTail.error support (fun d => (coeff d : ℝ)) (10^7) n := by
    simp only [residual,RawTrialTail.error,residue,Int.cast_sub,Int.cast_pow,
      Int.cast_sum,Int.cast_mul,Int.cast_natCast,Int.cast_ofNat]
  let den := n*(n+1)
  have hden : 0 < den := Nat.mul_pos hn (Nat.succ_pos n)
  have hq : (residual n).natAbs ^ 2 ≤ den * roundedUnit n := by
    have hz := Nat.lt_mul_div_succ ((residual n).natAbs^2+(den-1)) hden
    rw [Nat.mul_succ] at hz
    change (residual n).natAbs^2 ≤ den * (((residual n).natAbs^2+(den-1))/den)
    omega
  have habs : (((residual n).natAbs : ℕ) : ℝ) = |(residual n : ℝ)| := by
    have hi := congrArg (fun z : ℤ => (z : ℝ)) (Int.natCast_natAbs (residual n))
    simpa only [Int.cast_natCast,Int.cast_abs] using hi
  have hr : (((residual n).natAbs : ℝ))^2 ≤ (den:ℝ)*(roundedUnit n:ℝ) := by exact_mod_cast hq
  rw [habs,sq_abs] at hr
  rw [← hreal,positiveWeight,one_div,← div_eq_inv_mul]
  apply (div_le_iff₀ (by positivity : 0 < (n:ℝ)*((n:ℝ)+1))).mpr
  simpa [den,mul_comm] using hr

private theorem cast_roundedHead (T : ℕ) :
    (roundedHead T : ℝ) = ∑ j ∈ Finset.range T, (roundedUnit (j+1) : ℝ) := by
  simp only [roundedHead,Nat.cast_sum]

/-- Only the finite integer head appears as an input. -/
theorem limitEnergy_le_of_roundedHead
    (hhead : roundedHead (2 ^ 22) ≤ 674763337657) : limitEnergy ≤ energyBudget := by
  let c := fun d => (coeff d : ℝ)
  have hH : (∑ j ∈ Finset.range (2 ^ 22), positiveWeight (j+1) *
      (RawTrialTail.error support c (10^7) (j+1))^2) ≤ (674763337657 : ℝ) := by
    calc
      _ ≤ ∑ j ∈ Finset.range (2 ^ 22), (roundedUnit (j+1) : ℝ) :=
        Finset.sum_le_sum fun j _ => head_term_le (j+1) (Nat.succ_pos _)
      _ = (roundedHead (2 ^ 22) : ℝ) := (cast_roundedHead _).symm
      _ ≤ _ := by exact_mod_cast hhead
  have hm : RawTrialTail.mean support c (10^7) = (218240:ℝ)/2 := by
    have h := congrArg (fun x : ℤ => (x : ℝ)) twiceMean_value
    simp [twiceMean] at h
    unfold RawTrialTail.mean c
    linarith only [h]
  have ha : RawTrialTail.amplitude support c = 658340882348 := by
    have h := congrArg (fun x : ℤ => (x : ℝ)) oscillation_value
    simpa [oscillation,RawTrialTail.amplitude,c] using h
  have hg : RawTrialTail.gcdEnergy support c = 3118747506858140 := by
    have h := congrArg (fun x : ℤ => (x : ℝ)) covariance_value
    simpa [covariance,RawTrialTail.gcdEnergy,c] using h
  have h := RawTrialTail.limitEnergy_le_of_head support c (10^7) _ (2 ^ 22) (by norm_num)
    (fun d hd => (Finset.mem_Icc.mp hd).1) hH
  unfold RawTrialTail.uniformSquare RawTrialTail.discrepancy at h
  rw [hm,ha,hg] at h
  convert h using 1 <;> norm_num [energyBudget]

theorem normalizedParityCapture_exact_lower_of_roundedHead
    (hhead : roundedHead (2 ^ 22) ≤ 674763337657) :
    Real.sqrt (1 / Real.log 2 - 1 / (1-energyBudget)) ≤ normalizedParityCapture :=
  sqrt_energy_lower_le_normalizedParityCapture (limitEnergy_le_of_roundedHead hhead)
    (by norm_num [energyBudget])



theorem sieve_first_256 : sievedBlock 0 256 = 363137245152 := by decide +kernel
#print axioms twiceMean_value
#print axioms oscillation_value
#print axioms covariance_value
#print axioms sieve_first_256
#print axioms limitEnergy_le_of_roundedHead
#print axioms normalizedParityCapture_exact_lower_of_roundedHead
end RiemannResearch.RH.Pareto.PrimePowerSchur.Conductor768
