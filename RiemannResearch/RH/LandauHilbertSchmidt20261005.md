# Finite Hilbert–Schmidt improvement of the actual Landau residual

Research date: 2026-10-05.

## Result and comparison

Keep the complete actual multiplicity-weighted residual

\[
E_d(T)=H_d(T)-I+
 \frac{T}{2\pi N(T)}A_d,
\]

where \(A_d\) is the full integer prime-power covariance matrix. Every
integer coordinate, composite-frequency interaction and arithmetic main
term remains in this identity. Set \(Y=T+3\) and \(L=\log Y\).

For every \(T\ge9\), \(d\in\mathbb N\), and \(N(T)>0\), the existing entrywise-maximum assembly gives a numerator
\(C[d^{7/2}+d^{5/2}L^2+d^2L]\). The new finite assembly gives

\[
\boxed{\|E_d(T)\|\le \frac{C}{N(T)}
       \bigl(2d^3+2d^2L^2+3d^2L\bigr).}
\]

This uses the existing unconditional nonmaxed rational Landau provider,
not a new analytic estimate or a zero-density hypothesis.

| Consequence | Existing assembly | New assembly |
|---|---:|---:|
| Endpoint support with residual tending to zero | \(d=O(Y^{2/7})\) | \(d=O(Y^{1/3})\) |
| Full Gram lower coefficient at that endpoint | every \(h<5/7\) | every \(h<2/3\) |
| Strongest leading support budget | \(d^{7/2}/(YL)\to0\) | \(d^3/(YL)\to0\) |

The new leading-budget theorem and its logarithmic extension
\(d=O(Y^{1/3}L^b)\) for every \(b<1/3\) are also proved in Lean.
The normalized nonnegative envelope tends to zero if and only if its
leading term does. This exact iff concerns the majorant; it does not claim
necessity for the actual signed residual.

## Proof chain

For \(n>m\), use the original three positive entry envelopes

\[
A_{nm}=n^{5/2}/m^{3/2},\qquad
B_{nm}=(n/m)^{3/2},\qquad
D_{nm}=1+1/\log(n/m),
\]

reflect them symmetrically, and set their diagonal entries to zero.

1. Row Cauchy–Schwarz proves the genuine Euclidean operator certificate
   \(\|M\|^2\le\sum_{n,m}|M_{nm}|^2\).
2. A finite telescoping argument proves \(\sum_{m\le d}m^{-3}\le2\).
   Together with \(\sum_{n\le d}n^k\le d^{k+1}\), this gives
   \(\|A\|_{HS}\le2d^3\) and \(\|B\|_{HS}\le2d^2\).
3. The already proved rational-frequency separation gives \(D_{nm}\le3d\),
   hence its operator contribution is at most \(3d^2L\). This conservative
   finite bound avoids needing the sharper harmonic Schur estimate in Lean.
4. Split each actual complex residual entry into proportions
   \(A_{nm}\), \(L^2B_{nm}\), and \(LD_{nm}\) of their sum. If that sum
   is zero, the entrywise bound forces the actual entry to be zero. The
   three parts add exactly to the original entry; no actual phase is replaced.
5. Apply the two Hilbert–Schmidt certificates, the third uniform-entry
   certificate, and the operator triangle inequality.

The existing actual zero count eventually satisfies
\(N(T)\ge (64\pi)^{-1}YL\). Writing \(\ell=\log d\), the normalized
three-term envelope is exactly

\[
2e^{3\ell-L}/L+2Le^{2\ell-L}+3e^{2\ell-L}.
\]

At \(\ell\le a+L/3\), it is bounded by

\[
2e^{3a}/L+2e^{2a}Le^{-L/3}+3e^{2a}e^{-L/3}\longrightarrow0.
\]

## Actual hyperbolic-form consequence

The existing complete arithmetic form estimate is
\(|\langle f,A_df\rangle|\le(\log d+\log4+4)\|f\|^2\).
The actual zero-count asymptotic and the
new residual convergence therefore give, for \(0\le\theta\le1/3\),
\(\log d(T)\le a+\theta\log(T+3)\), and every \(h<1-\theta\),

\[
h\|f\|^2\le \operatorname{Re}\langle f,H_{d(T)}(T)f\rangle
\quad\text{eventually, uniformly in }f.
\]

The existing exact actual-row identity turns this into

\[
h\|f\|^2\le
 \|C_{T,d(T)}f\|^2-\|S_{T,d(T)}f\|^2.
\]

At the new endpoint every \(h<2/3\) is valid. This statement retains the
negative sinh norm square, the multiplicity-copy indexing, the repository's
complex sign convention and all composite interactions. It supplies the
full actual-form lower input. A shrinking good-zero mask still requires
its separate bad-row/density estimate; physical Pareto transfer and RH
are not consequences claimed here.

## Verified declarations and verification

Repository modules:

- `Analysis/EuclideanHilbertSchmidt.lean`: the three generic Euclidean
  Hilbert–Schmidt/scaled-entry certificates, in namespace `ContinuousLinearMap`.
- `Analysis/LandauHilbertSchmidtResidual.lean`: finite envelope assembly,
  concrete actual residual, support convergence, and actual-form consequences.

Main declarations:

- `exists_actualLandauResidual_hilbertSchmidt_norm_bound`
- `actualLandauResidual_norm_tendsto_zero_one_third_support`
- `eventually_landauGram_lower_power_support_one_third`
- `eventually_actualHyperbolic_rows_lower_one_third`
- `normalizedHSEnvelope_tendsto_zero_iff_leading_budget`
- `actualLandauResidual_norm_tendsto_zero_of_hs_leading_budget`
- `actualLandauResidual_norm_tendsto_zero_hs_log_power_support`

The coherent ephemeral Lean candidate was kernel-checked. Axiom reports for
the actual finite bound, actual-row endpoint, full leading-budget consumer,
and logarithmic-support specialization contain only `propext`,
`Classical.choice`, and `Quot.sound`. The support conditions are explicit
elementary growth hypotheses; no density or RH hypothesis is introduced.
Final publication uses the repository's change-aware checkpoint to validate
the saved modules, their exports, and affected reverse dependents. The Git
publication records the resulting checked source state.

Analytic provenance remains the already proved actual rational contour,
good-height, height-transfer and zero-count providers. The contour strategy
is based on [Gonek, Theorem 1 (1985)](https://www.sas.rochester.edu/mth/people/faculty/gonek-steve/assets/pdf/8-landau-form.pdf).
No published Landau estimate is imported as a new Lean assumption.
