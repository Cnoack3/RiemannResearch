# Fourier convex-repair continuation: verified scope

September 11, 2026. Continuation of `FourierZeroDampingVerification20260911(1).md`.

## Result

This continuation adds **17 public theorems across four modules**.

The main new conditional conclusion is that the existing uniform multiplier
and remainder-energy bounds would give **finite convex mixtures of actual
remainders with arbitrarily small norm**, using arbitrarily small positive
dampings. Individual remainder-energy tightness is unnecessary for this
mixture conclusion.

The two analytic bounds are still hypotheses. **No uniform-energy provider,
unconditional infinite-coordinate limit, legal recovery, or RH proof was
established in Lean.** This is a standard functional-analytic reduction
applied to the actual arithmetic family, not a new arithmetic estimate.

## 1. Exact signed energy across different dampings

Write
\[
R_\varepsilon=\texttt{dyadicNormalizationRemainder }\varepsilon,
\qquad
b_{\varepsilon,i}=\texttt{dyadicNormalizationBoundaryCoefficient }\varepsilon\ i,
\qquad
F_{\varepsilon,i}=\sum_{h\ne0}c_i(h)M_\varepsilon(h).
\]
The previously verified full bridge gives
\(F_{\varepsilon,i}=b_{\varepsilon,i}\in\mathbb R\) for positive damping.

For any two positive dampings, Lean now proves the convergent exact identity
\[
\langle R_\varepsilon,R_\delta\rangle
=\sum_{i\ge0}\frac14 b_{\varepsilon,i}b_{\delta,i}.
\]

More generally, for any finite index set \(s\), arbitrary real weights
\(a_k\), and positive dampings \(\varepsilon_k\) on the used indices,
\[
\boxed{
\left\|\sum_{k\in s}a_kR_{\varepsilon_k}\right\|^2
=\sum_{i\ge0}\frac14\left(\sum_{k\in s}a_kb_{\varepsilon_k,i}\right)^2
=\sum_{i\ge0}\frac14
\left|\sum_{k\in s}a_kF_{\varepsilon_k,i}\right|^2.}
\]

All displayed boundary-energy series are proved summable. Every frequency
interaction and every interaction between different dampings remains inside
the squared signed sum. Neither a frequency diagonal nor the average of
individual energies replaces the actual mixture energy. These identities
are unconditional for the stated finite positive-damping packets.

Providers include
`dyadicNormalizationRemainder_inner_eq_signed_boundary` and
`dyadicNormalizationRemainder_finite_norm_sq_eq_signed_fourier`.

## 2. From actual boundary coordinates to weak convergence

A general Hilbert-basis theorem is verified: if a family is eventually
bounded in norm and every basis pairing tends to zero, then its pairing
against every fixed Hilbert-space vector tends to zero.

The proof approximates the fixed test vector by a finite basis sum and uses
Cauchy–Schwarz only on the residual test-vector error. The approximation
cutoff is chosen before the parameter limit.

Applied to the complete actual dyadic boundary basis, this gives
\[
\left[
\|R_{\varepsilon(a)}\|\le C\text{ eventually},\quad
b_{\varepsilon(a),i}\to0\ \text{for every }i
\right]
\Longrightarrow
\langle x,R_{\varepsilon(a)}\rangle\to0\ \text{for every }x.
\]
Only eventual positive damping is required. The remainder's exact zero mean
and equality with its quotient projection are already established. Riesz
representation then supplies genuine weak convergence in the **full
physical Hilbert space**; this statement does not assert legal membership.

Providers: `HilbertBasis.inner_tendsto_zero_of_bounded_coordinates`,
`dyadicNormalizationRemainder_pairing_tendsto_zero`, and
`dyadicNormalizationRemainder_weak_tendsto_zero`.

## 3. The conditional convex-repair endpoint

The final theorem takes exactly the two existing named analytic hypotheses:

1. `DyadicUniformSignedFourierMultiplierSqrtBound`:
   \(\exists B\ge0:\ |M_\varepsilon(h)|\le B|h|^{1/2}\)
   for \(0<\varepsilon\le1/2\), \(h\ne0\).
2. `DyadicNormalizationRemainderUniformEnergyBound`:
   \(\exists C\ge0:\ \|R_\varepsilon\|^2\le C\)
   for \(0<\varepsilon\le1/2\).

Under those hypotheses, for every \(\delta,\eta>0\), Lean proves that there
are a finite index type, weights \(a_k\ge0\) with \(\sum_k a_k=1\), and
dampings \(0<\varepsilon_k<\delta\), such that
\[
\left\|\sum_k a_kR_{\varepsilon_k}\right\|<\eta,
\qquad
\sum_{i\ge0}\frac14
\left|\sum_k a_k\sum_{h\ne0}c_i(h)M_{\varepsilon_k}(h)\right|^2<\eta^2.
\]

The endpoint is
`exists_dyadicNormalizationRemainder_convex_weights_small_fourier_energy`.

The general convex-closure proof uses the equality of weak and norm closures
for convex sets, supplied by Mathlib's `Convex.toWeakSpace_closure`. This is
the standard argument behind Mazur's lemma. It yields finite mixtures in
every sufficiently small damping interval without assuming that the
individual remainder norms vanish.

The weights and dampings are existential. No effective selection algorithm
or rate is proved.

## 4. What still separates this result from RH

The actual arithmetic family satisfies the exact vector identity
\[
\sum_k a_k(V_{\varepsilon_k}-1)
=\sum_k a_kR_{\varepsilon_k}
+\sum_k a_k(C_{\varepsilon_k}-1),
\]
where \(C_\varepsilon\) is the actual normalization comparison and
\(\sum_k a_k=1\). Therefore small remainder mixtures alone do not approximate
the constant: the centered comparison still needs its appropriate control.

The projected arithmetic family has not been proved to belong to the full
legal two-seed closure. Convexity preserves membership only after the
necessary membership/recovery theorem has been supplied.

The next substantive targets remain:

- Supply the uniform multiplier provider, obtaining unconditional actual
  coordinate limits in Lean.
- Prove actual signed energy control, or construct small mixtures directly
  using the exact mixed-damping energy formula.
- Control the centered comparison and recover full legal approximants,
  retaining the complementary physical energy.

## 5. Analytic candidate retained for the next formalization

**This paragraph is an informal mathematical derivation, not a Lean provider.**

There is a classical route to the multiplier hypothesis that avoids uniform
Stirling asymptotics. Sondow–Dumitrescu's Theorem 1 gives horizontal xi-modulus
monotonicity in the unconditional region \(\Re s>1\), extending to its
boundary by continuity. Using \(\Re s>1/2\) here would be circular.
[Source for the monotonicity statement](https://arxiv.org/pdf/1005.1104).

For \(s=1-it\), \(|t|\ge1\), and \(0<\varepsilon\le1/2\), the xi–zeta
identity reduces the ratio estimate to the gamma ratio. Put
\(a=(1+\varepsilon)/2\), \(y=-t/2\). Euler's beta integral gives
\[
\left|\frac{\Gamma(a+iy)}{\Gamma(1+iy)}\right|\le\Gamma(a)\le3.
\]
The last inequality follows by splitting Euler's gamma integral at one.
[Source for the beta–gamma identity](https://dlmf.nist.gov/5.12#E1).

Gamma reflection and recurrence give
\[
\left|\frac{\Gamma(1+iy)}{\Gamma(1/2+iy)}\right|^2
=|y|\coth(\pi|y|)\le |y|+1/\pi.
\]
Thus the required gamma ratio is at most \(3\sqrt{|t|}\).
[Source for the gamma modulus identities](https://dlmf.nist.gov/5.4).

Bounding the two rational xi factors by \(3/2\) each then gives
\[
\left|\frac{\zeta(1-it)}{\zeta(1+\varepsilon-it)}\right|
\le\frac{27}{4}\sqrt{|t|}.
\]
Together with the already verified normalization and full Abel-factor bounds,
this suggests the explicit sufficient constant
\[
B=\frac{89}{4}\sqrt{\frac{2\pi}{\log2}}.
\]
This application and constant are our derivation from the cited identities.
The substantial missing Lean infrastructure is the completed-xi horizontal
comparison; the beta/gamma estimates and its exact zeta adapter must also be
formalized. None of these steps was used as an added axiom in this continuation.

## 6. Modules and decisive verification

| Module | Public theorems | Scope |
| --- | ---: | --- |
| `Analysis/HilbertBasisWeakLimit` | 1 | Bounded coordinate limits imply all pairing limits |
| `Analysis/WeakConvexRepair` | 3 | Riesz adapter and weak-to-convex norm approximation |
| `RH/DyadicSignedDampingPackets` | 8 | Exact signed mixed-damping and Fourier energies |
| `RH/DyadicRemainderConvexRepair` | 5 | Actual weak limits and conditional explicit small mixtures |

Combined source and endpoint audit:
`job_jDMXcjlyVnAiw6U4TMszPjTOWC4obP0f`.
**Succeeded; verified true; exit code 0; 4.407 seconds.**

All 17 theorem sources compiled together. Four audited endpoints depend only
on `propext`, `Classical.choice`, and `Quot.sound`. The printed final endpoint
retains both named open hypotheses. The audit output was untruncated.
No placeholder, extra axiom, or unsafe declaration was introduced.

Audit source SHA-256:
`89b67bd79c85c270505d9e7c5c5583a99a2f3c02974bf899c4cea0694f59f191`.

All verification submissions were serialized. One read-only catalog search
returned HTTP 504 and was recovered; no duplicate verification job was
submitted to work around it.

Workspace token: `ws__eykLs_HJEUiekupiRigb5Ft5hXoDngi`.

Project root:
`/home/cri_2025/lean-agent-workspaces/ws__eykLs_HJEUiekupiRigb5Ft5hXoDngi/RiemannResearch`.

Starting published commit: `02856ee260c4e598611f7b1ce62455dc57e1357f`.

The final affected-module checkpoint and published commit are recorded below
in the delivered handoff. This source note accompanies that publication.
