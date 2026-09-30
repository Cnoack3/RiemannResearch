# RH consequences and the prime angular research target

Date: 2026-09-30.
Continuation of Cnoack3/RiemannResearch ea119df9b70d862a797de04f02e43bdb62aba0a8.
Modules: RH/ParetoFirstSiteRHConsequences.lean,
RH/ParetoFirstSitePrimeAngular.lean, and Analysis/WeightedScalarEnergy.lean.

The unconditional results here are exact identities, monotonicity, and an
arithmetic lower bound on the angular weight. The capacity-divergence provider
remains **Open**. No unconditional RH or divergence of an arithmetic channel
is asserted.

## What RH implies, and what Lean currently supplies

Classically, Báez-Duarte's Theorem 1.1 implies natural integer-dilation
approximation under RH. The repo already proves the complete normalization
transfer to the Pareto residue closure. Its first-point closure equivalence
and inverse-capacity identity consequently give
\[
\mathrm{RH}\ \Longrightarrow\ C_N\to\infty,\qquad
\Delta_N=\frac1{C_N+2}\to0.
\]
Hence RH implies
\[
U_N+A_N=G_N+J_N=R_N+W_N+J_N\longrightarrow\infty.
\]
It does not specify which prime or nonprime channel supplies this growth.

The analytic input is **not yet a Lean-provided theorem**. The new
RH_iff_tailCapacity_tendsto, RH_iff_prime_alignment_unbounded, and
RH_iff_prime_angular_channels retain the explicit hypothesis
\[
h_{\rm BD}:\mathrm{RiemannHypothesis}\to\mathrm{NaturalApproximation}.
\]
No external analytic axiom is introduced. The implication from capacity
divergence to Mathlib's RH needs no such hypothesis. The new
tailCapacity_tendsto_of_naturalApproximation assembles the previously checked
normalization, first-point closure, and capacity conversions.

Source for the analytic implication: L. Báez-Duarte, *A strengthening of the
Nyman--Beurling criterion for the Riemann hypothesis, 2*, Theorem 1.1:
https://arxiv.org/abs/math/0205003. This supports the classical implication,
not a claim that its analytic proof has been imported into Lean.

## Classical scale check: the fixed-fraction targets are too strong

The following is a **mathematical deduction from classical results, not a
kernel-verified capacity or source rate in this repo**. It changes which
arithmetic hypotheses are sensible research targets.

Burnol's denominator-length lower bound for constant-target approximation is
\(d_M\gg1/\sqrt{\log M}\). Transfer it to the point target as follows. Write
\(T=\frac12 D_2\), \(q=1/\sqrt2\), and
\(S_K=\sum_{k<K}T^k\). For the actual best point approximant \(f_N\), retain
the complete identity
\[
1-S_K f_N=T^K1+S_K(e_1-f_N)
\]
and its complete norm square
\[
\|1-S_Kf_N\|^2=\|T^K1\|^2+
2\langle T^K1,S_K(e_1-f_N)\rangle+
\|S_K(e_1-f_N)\|^2.
\]
Only then use
\[
d_M\le q^K+(1-q)^{-1}\sqrt{\Delta_N}.
\]
The existing dilation identity enlarges denominators by at most \(2^K\):
\(M\le(N+1)2^K\). Taking \(K=\lceil\log_2(N+1)\rceil\) yields
\(M\le2(N+1)^2\), while \(q^K\le(N+1)^{-1/2}\). Thus
\[
\Delta_N\gg1/\log(N+1),\qquad C_N=O(\log(N+1)).
\]
The centered continuous squared norm equals the Pareto squared norm exactly,
so no norm scaling is hidden in this transfer.
Source: J.-F. Burnol, *A lower bound in an approximation problem involving the
zeros of the Riemann zeta function*, Theorems 1.2--1.3:
https://arxiv.org/abs/math/0103058. The transfer just displayed is our deduction.

For a fresh prime \(p\), put \(P=(p-1)!\). The exact Euler product is
\[
M_P=\prod_{\ell\ge p,\ \ell\ {\rm prime}}(1-\ell^{-2})^{-1}.
\]
PNT and partial summation give \(M_P-1\sim1/(p\log p)\). The already checked
defect identity then gives
\[
\delta_p=\frac{M_P}{p^2(M_P-1)}\sim\frac{\log p}{p}.
\]
Together with the checked \(\sigma_p\le2/p\) and
\(\sum_{p\le x}(\log p)^2/p\sim\frac12(\log x)^2\), this yields the classical
lower estimate \(U_N\ge(\frac14-o(1))(\log N)^2\).
The PNT asymptotic assembly is **not formalized here**.

Consequently \(C_{N+1}/U_N\to0\) classically, regardless of RH. The exact
capacity identity gives \(A_N/U_N\to-1\). Also, preserving the full prime
square first,
\[
G_N=U_N+V_N+2X_N,\quad X_N^2\le U_NV_N,
\]
gives \((\sqrt{V_N}-\sqrt{U_N})^2\le G_N\le C_{N+1}\), and therefore
\(V_N/U_N\to1\), \(X_N/U_N\to-1\).
Thus the cofinal fixed-\(\theta<1\) \(A\)-saving and \(V\)-saving targets are
incompatible with this classical scale comparison. Their Lean implication
theorems remain valid, but their hypotheses should not guide the arithmetic
search. The square-root saving and fluctuation-scale alternatives are not
ruled out by this comparison.

primeSignedBudget_ratio_tendsto_of_capacity_sublinear_source kernel-verifies
the exact implication \(C_{N+1}/U_N\to0\Rightarrow A_N/U_N\to-1\), retaining
its source-rate hypothesis explicitly. It does not provide that rate.

## Exact monotone angular channel

Let \(w_n=1/\sigma_{n+1}\) at prime stages and zero otherwise,
\(u_n=w_n\delta_n^2\). For \(n\ge1\), the complete new square is
\[
\boxed{\Gamma_n=
\frac{w_n(U_n\kappa_n-X_n\delta_n)^2}{U_n(U_n+u_n)}.}
\]
The empty initial stage has \(\Gamma_0=0\), and \(W_0=W_1=0\).
Weighted regression square completion proves
\[
\boxed{W_{n+1}=W_n+\Gamma_n,\qquad W_N=\sum_{n<N}\Gamma_n.}
\]
In particular \(W_N\) is monotone. No cross term is removed in deriving this
update. The exact relative form is
\[
\Gamma_n=\frac{u_nU_n}{U_n+u_n}
\left(\frac{\kappa_n}{\delta_n}-\frac{X_n}{U_n}\right)^2.
\]
The mean channel need not be monotone; the full conservation identity is
\[
R_{n+1}+\Gamma_n=R_n+\frac{\eta_{n+1}^2}{\sigma_{n+1}}
\]
at prime stages, with zero prime gain at nonprime stages.
The capacity accounting remains
\[
\boxed{C_{N+1}=C_1+R_N+\sum_{n<N}\Gamma_n+J_N.}
\]

## Unconditional reciprocal-prime comparison

The existing fresh-prime source lower bound gives \(u_n\ge1/[8(n+3)]\)
at prime stages. The first prime gives \(U_1\ge1/24\); monotonicity then gives
\(U_n\ge1/[8(n+3)]\) for \(n\ge1\). Keeping the determinant square, the reduced
weight satisfies
\[
\frac{u_nU_n}{U_n+u_n}\ge\frac1{16(n+3)}.
\]
Define \(E_n=0\) at \(n=0\) and nonprime stages, and otherwise
\[
E_n=\frac1{n+3}
\left(\frac{\kappa_n}{\delta_n}-\frac{X_n}{U_n}\right)^2.
\]
The new kernel-checked comparison is
\[
\boxed{0\le E_n\le16\Gamma_n.}
\]
Consequently nonsummability of \(E_n\) conditionally suffices for capacity
divergence and RH. Failure of RH forces both \(\Gamma_n\) and \(E_n\) to be
summable. The sharper classical factorial weights and the capacity scale
above in fact imply that \(E_n\) is summable without RH, as deduced in
[the three-series continuation](FirstSiteKolmogorovThreeSeries20260930.md).
Those analytic rates are not kernel-imported here. The coarse conditional
endpoint remains valid, but \(E\)-nonsummability should not guide the search.

The exact screened expression inside the square is
\[
\kappa_n=b_n+\sum_{m<n}T_{nm},\quad
b_n=\langle{\rm tailInnovation}(n+1),{\rm infiniteCoprimeCertificate}(2!)\rangle,
\quad T_{nm}=\langle{\rm tailInnovation}(n+1),{\rm factorialPrimeRefinement}(m)\rangle.
\]
primeRelativeAngularEnergy_eq_screened_rows retains this full row.
The negative formula for raw unscreened rows cannot replace it. Vanishing
composite refinement columns does not discharge the nonprime gain channel.

## Weakest provider and the next arithmetic task

The exact capacity criterion is now also
\[
C_N\to\infty\quad\Longleftrightarrow\quad
(R_N\not\to0)\ \lor\ (\Gamma\ {\rm not\ summable})\
\lor\ ({\rm factorialCompositeGain}\ {\rm not\ summable}).
\]
tailCapacity_tendsto_iff_prime_angular_channels proves this without RH.
Equivalently, the weakest explicit remaining inequality is
\[
\boxed{\forall B\in\mathbb R\ \exists N\ge1:
 R_N+\sum_{n<N}\Gamma_n+J_N>B.}
\]
No one channel is asserted necessary individually. A sufficient arithmetic
subtask is unbounded partial sums of the **full** \(\Gamma_n\), retaining the
actual reduced Schur/factorial weight, every screened row, and the historical
running slope. The reciprocal-prime \(E\)-nonsummability endpoint is too strong
under the classical scale audit. No imported large-sieve upper inequality
currently provides the required full angular lower-energy assertion.

Wolfram independently checked the finite determinant update and the paired
scalar example \(\delta_n=w_n=1\),
\(\eta_{2k}=(k+1)^{-1/2}\), \(\eta_{2k+1}=-(k+1)^{-1/2}\).
At \(N=2m\), it has \(R_N=0\), \(W_N=G_N=2H_m\to\infty\),
\(V_N=U_N+G_N\), and \((V_N-U_N)^2/U_N=2H_m^2/m\to0\).
This is an abstract budget example, not the actual factorial arithmetic and
not a kernel-verified counterexample. It explains why capacity divergence
alone cannot select the previously sufficient mean or error-saving channel.

The implementation exports both new RH modules, updates the theorem catalog,
and uses only ordinary Lean/Mathlib foundations. Domain-specific hypotheses
remain visible in the exact conditional declaration types.
