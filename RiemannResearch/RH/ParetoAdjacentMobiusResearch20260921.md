# Adjacent moment corrections and exact Möbius heads

Research derivation, 21 September 2026. Lean status must be supplied by the coordinating verification job; this note alone is not a verification receipt.

Write R_d(j)=j mod d, g_d=R_d/d, t_d=g_d−e_1/d, and w_j=1/[j(j+1)].
For odd d≥3 set r_d=d(R_d−R_(d+1))=d²t_d−d(d+1)t_(d+1).
Its reciprocal head is zero, its odd reciprocal-square moment is one, and r_d(j)=0 for j<d.

## Exact full energy and sharp elementary bounds

Let U_d=R_d−R_(d+1), L=d(d+1), H_d=∑_(k=1)^d1/k.
For 1≤k≤d, U_d is k−d−1 on k d≤j<k(d+1), and k on k(d+1)≤j<(k+1)d. The second interval is empty for k=d. Summing Pareto weights on each interval gives

E_(d,k)=(d+1−k)²/[k d(d+1)]+k(d−k)/[(d+1)(k+1)d]
       =(d+1)/(d k)−1/d−1/[d(k+1)].

Consequently

∑_(j=0)^(L−1)w_j U_d(j)² = H_d−d/(d+1).

Since |U_d(j)|≤d and ∑_(j≥L)w_j=1/L, the literal remaining sum B_d satisfies 0≤B_d≤d/(d+1). Thus

||r_d||²=d²[H_d−d/(d+1)+B_d],
d²[H_d−d/(d+1)]≤||r_d||²≤d²H_d.

For d=3, the first-period unscaled energy is 13/12. This identity uses the actual infinite energy, retaining the entire remainder; no asymptotic replacement is involved.

## Controlled normalization of actual candidates

If F_c=∑c_dt_d has odd moment J(c), set δ=1−J(c) and add δr_d. The corrected coefficient at d increases by δd² and the coefficient at d+1 decreases by δd(d+1). Then J becomes exactly one, h is unchanged, and every coordinate j<d is unchanged. The full exact energy is

||F_c+δr_d||²=||F_c||²+2δ⟨F_c,r_d⟩+δ²||r_d||².

The correction itself has energy at most δ²d²H_d. Thus a family with δ_N²d_N²H_(d_N)→0 has asymptotically negligible correction. This condition does not supply the missing full-tail-small original candidates.

## Explicit exact-head Möbius family

For n≥2 define a_n=−μ(n)+1_(2|n)μ(n/2). Its divisor sum for n≥2 is 1+1_(n=2). Hence ∑_(2≤d≤N)a_d floor(j/d)=j for 2≤j≤N.
Let κ=π²/(π²−8),
A_N=∑_(2≤d≤N)a_d/d,
B_N=∑_(3≤d≤N,d odd)a_d/d²,
H=κ(1−A_N), K=1−κB_N.
Choose an odd D>N and E=D+1. Put c_d=κa_d for 2≤d≤N, c_D=D²K, and c_E=E(H−DK), with all other coefficients zero. Then h(c)=κ, J(c)=1, f_c(1)=κ, and f_c(j)=0 for 2≤j≤N. These are finite exact identities.

For S(N)=∑_(d≤N)μ(d)/d, A_N=1−S(N)+(1/2)S(floor(N/2)). Also B_∞=1−8/π²=1/κ by the absolutely convergent Möbius Dirichlet series at 2, so K is precisely the tail odd Möbius reciprocal-square sum. This explains why κ is the required arithmetic normalization.

The full remaining energy is exactly

∑_(j>N) [κj−κ∑_(2≤d≤N)a_d floor(j/d)−D²K floor(j/D)−E(H−DK)floor(j/E)]²/[j(j+1)].

No argument that this sum tends to zero was found. Numerical finite sums do not suggest it: for N=50,100,300,1000,3000, sums through j=10^6 were respectively about 2.49436,2.25833,2.49662,2.08674,2.27798. Floating computations are exploratory, not certificates. The adjacent moment correction is small in these examples, while the remaining Möbius interpolation error persists.

The publication-safe conclusion is controlled exact normalization and its full harmonic energy bound, not a constructed small-energy family or RH. A known general caution is Baez-Duarte, Arithmetical Aspects of Beurling's Real Variable Reformulation of the Riemann Hypothesis (2000), https://arxiv.org/abs/math/0011254: natural pointwise/L1 approximants can fail in L2. This citation supports the caution, not a theorem about this particular two-boundary family.

## A bounded-family route remains possible

Nondecay of these specific candidate norms does not rule out their usefulness. Because their heads are exactly κe₁ on every fixed growing prefix, a uniform bound on their complete Hilbert norms would imply weak convergence to κe₁. The norm-closed legal subspace is weakly closed, so κe₁ would belong to it. Convex combinations would then give strong approximants. Accordingly, a uniform full-energy bound for this exact-head family is a meaningful alternative target. Neither that bound nor vanishing full energy has been proved here. The displayed partial energies cannot establish a uniform bound on the omitted infinite tails.

## Uniform-bound attempt and its exact unresolved expression

Let D be the least odd integer greater than N and E=D+1. Before repairing the odd moment, use the even-anchor interpolant

F_N^0=κ∑_(2≤d≤N)a_dt_d+EH t_E.

The full repaired vector is exactly F_N=F_N^0+K r_D. Its full norm identity is

||F_N||²=||F_N^0||²+2K⟨F_N^0,r_D⟩+K²||r_D||².

In terms of the actual full-tail Gram entries G_(d,e)=⟨t_d,t_e⟩, the base energy is exactly

||F_N^0||²=κ²∑_(d,e≤N;d,e≥2)a_da_eG_(d,e)
 +2κEH∑_(2≤d≤N)a_dG_(d,E)+(EH)²G_(E,E).

No sign or cross term is removable without further work. Using the already established elementary bound |∑_(d≤N)μ(d)/d|≤1 gives |H|≤3κ/2. Also ∑_(2≤d≤N)|a_d|≤N−1+floor(N/2). Therefore the elementary absolute-value estimate, together with the exact vanishing of the physical tail through N, yields only

||F_N^0||² ≤ κ²[N−1+floor(N/2)+(3/2)E]²/(N+1).

This grows linearly with N when E is the chosen adjacent even anchor. It does not give the desired uniform bound. The sharper harmonic estimate controls the added moment correction, but does not bound the displayed base signed Gram expression. At the ordinary-mathematics level, quantitative prime-number-theorem cancellation makes the moment correction negligible; importing that analytic result would still leave the same base-energy problem.

Critical-line zeros do not automatically refute uniform boundedness. Baez-Duarte's Proposition 4.6 establishes failure of strong L² convergence for classical exact-head natural approximants, while the discussion after Proposition 4.5 distinguishes the stronger question of unbounded norms. Those theorems have not been specialized here to the present two-boundary family. The dyadic Möbius factor 1−2^(−ρ) is nonzero on Reρ=1/2, so there is no simple cancellation of those critical modes. No theorem that the present complete norms are uniformly bounded or unbounded has been proved.
