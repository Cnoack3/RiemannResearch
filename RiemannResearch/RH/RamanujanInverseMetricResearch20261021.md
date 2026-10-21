# Ramanujan zero signals and inverse-Gram stability — 2026-10-21

> Continuation: [relaxed density and screened inverse-Gram control](RamanujanDensityRelaxationResearch20261021.md)
> strengthens the initial analytic premise in this note. The current Ramanujan
> consumers take E(T)/T -> 0. A single shrinking strip, or every positive
> exponential rate with any fixed logarithmic loss, is sufficient.
> The analytic count provider and capacity saturation remain Open.


## Status and scope

The containing commit's successful Lean-server checkpoint is the publication
certificate. Before that checkpoint, the complete three-module development
passed targeted server job
`job_rA4fzZsTPMLhf7Y-i5iUeFwZ7MF2XI72`: exit code 0,
`verified=true`, reported total elapsed time 11.843 seconds. The final packet
module itself reported a 2.5-second compilation. These figures are not the
workspace-opening or conversational waiting time. The opening request
exceeded its first 31-second response window; no kernel timing is inferred
from that delay.

The finite Hilbert and actual packet results are unconditional. The
zero-ordinate convergence and zero-cutoff specialization explicitly require
`ActualZeroOrdinate.UniformSelbergDensity (1/4)`. This is a classical
unconditional density theorem, but the repository has not formalized its
analytic provider. It remains a local hypothesis, not a new axiom and not an
RH assumption. No capacity-saturation theorem or unconditional RH proof is
claimed.

The earlier trigamma evaluation and the untruncated Chebyshev explicit formula
are mathematical context; this change does not claim new Lean proofs of those
analytic formulas. Existing project results supply the arithmetic packet
basis, exact Pareto mean, full finite Gram inverse, and Hilbert realization.

## 1. The exact measure and packet normalization

Let

```math
\begin{gathered}
P(n)=1/[n(n+1)],     Q(n)=1/[Z n^2],     Z=\zeta(2),     w(n)=n/(n+1),
\end{gathered}
```

on positive integers. The auxiliary zero coordinate has weight zero.
For every sequence for which these means are used,

```math
\begin{gathered}
L(F)=\mathbb E_P F=Z \mathbb E_Q[wF].
\end{gathered}
```

The actual packet convention is

```math
\begin{gathered}
B_q(n)=\sum_{d|q} μ(q/d)(n\bmod d) \\
      =\sum_{d|q} μ(q/d)d g_d(n),     g_d(n)=(n\bmod d)/d.
\end{gathered}
```

The existing theorem `Pareto.paretoMean_ramanujanPacket` gives
`L(B_q)=Λ(q)`. The new theorem `weightedQMean_packet` identifies exactly
the same functional in the actual inverse-square law. For squarefree q,
Λ(q) is log q for a prime q and is zero for a composite q.

The actual Gram matrix in this development is

```math
\begin{gathered}
H_{qr}=\mathbb E_P[B_q B_r]=Z \mathbb E_Q[w B_q B_r].
\end{gathered}
```

It is not the unweighted Q Gram matrix. Its finite inverse is constructed
from independence of the genuine Hilbert packets, not postulated.
`gram_entry_eq_weightedQ` retains all mixed entries and the complete tails.

## 2. Zero ordinates recover the full mean vector

For fixed q>1 define the actual, multiplicity-preserving estimator

```math
\begin{gathered}
ell_T(q)=-(2π \sqrt{q}/T) \sum_{0<\operatorname{Im} ρ≤T} \mathrm{mult}(ρ) \cos(\operatorname{Im}(ρ) \log q).
\end{gathered}
```

The cosine identity is `sampledSignal_eq_cos_sum`. Under the explicit
Selberg-density input, `sampledSignal_tendsto` proves

```math
\begin{gathered}
ell_T(q) → \Lambda(q).
\end{gathered}
```

All actual nontrivial zeros are included, irrespective of their real parts.
The imported rational Landau limit has no RH hypothesis. The passage from
Landau's real-part-sensitive terms to ordinate-only terms is where the
classical Selberg-density input enters the formalized chain.

For finite real coefficients the normalization therefore has the spectral
interpretation

```math
\begin{gathered}
\sum_p a_p \log p = 1 \\
\Longleftrightarrow \\
\lim_{T→∞} (1/T) \sum_{0<γ≤T} \sum_p a_p \sqrt{p} \cos(γ \log p) = -1/(2π).
\end{gathered}
```

This is the lower-order bias. Dividing the same finite phase sum by N(T)
instead loses the prime signal.

Source for this analytic statement and proof strategy:
Ford–Zaharescu, “On the distribution of imaginary parts of zeros of the
Riemann zeta function”, Theorem 1 and equation (3.8):
https://www.ford126.web.illinois.edu/wwwpapers/fz.pdf .
See also Ford–Meng–Zaharescu:
https://arxiv.org/abs/1511.06814 .

## 3. Literal inverse-Gram geometry

For a finite independent Hilbert family v, let S be its synthesis map and
H its actual Gram matrix. The already constructed minimum-observation map is

```math
\begin{gathered}
R(b)=S H^{-1} b.
\end{gathered}
```

The new inverse pairing and norm are

```math
\begin{gathered}
<b,c>_{H^{-1}}=<R(b),R(c)>=b^T H^{-1} c, \\
||b||_{H^{-1}}=||R(b)||.
\end{gathered}
```

The literal matrix equalities are proved in
`inversePair_eq_matrix` and `inverseNorm_sq_eq_matrix`.
Finite coordinate convergence implies convergence in this metric by
`inverseNorm_error_tendsto`. The proof uses continuity of a fixed finite
linear map; it imposes no bound uniform over different conductor sets.

## 4. Exact normalization and exact remainder

Write A=H^{-1}, ell for the true mean vector, z=ell+e for its estimate, and

```math
\begin{gathered}
κ=\ell^T A \ell>0,     ρ=\ell^T A e,     b=e^T A e.
\end{gathered}
```

The true and sampled normalized coefficient vectors are

```math
\begin{gathered}
a^*=A \ell/κ, \\
a(z)=A z/(\ell^T A z)=A(\ell+e)/(κ+ρ).
\end{gathered}
```

Whenever κ+ρ is nonzero, `normalizedCoefficients_signal` proves
`ell^T a(z)=1` exactly. In the actual squarefree application,
`coefficients_prime_signal` proves the literal sum over prime conductors
with weights log p equals one.

Define the inverse-metric orthogonal error

```math
\begin{gathered}
e_perp=e-(ρ/κ)\ell.
\end{gathered}
```

Then

```math
\begin{gathered}
<\ell,e_perp>_A=0, \\
||e_perp||_A^2=b-ρ^2/κ, \\
a(z)-a^*=A e_perp/(κ+ρ).
\end{gathered}
```

The full signed error identity is

```math
\begin{gathered}
||a(z)-a^*||_H^2 \\
  =||e_perp||_A^2/(κ+ρ)^2 \\
  =(κ b-ρ^2)/(κ(κ+ρ)^2).
\end{gathered}
```

The abstract orthogonal identity is
`SignalNormalizationStability.normalized_error_orthogonal`; the actual
inverse-Gram identity is
`FiniteGramSignalStability.normalized_error_exact`.
In particular, a purely multiplicative mean-vector error is removed by exact
normalization. The mixed square ρ^2 is retained before any upper estimate.

## 5. Quadratic stability

Suppose

```math
\begin{gathered}
||e||_A ≤ ε ||\ell||_A,     0≤ε<1.
\end{gathered}
```

Cauchy–Schwarz gives |ρ|≤εκ, so κ+ρ≥(1-ε)κ>0.
Consequently the proved bound is

```math
\begin{gathered}
||a(z)-a^*||_H^2 ≤ ε^2/[κ(1-ε)^2].
\end{gathered}
```

For the unit constant target, the exact Pythagorean completion is

```math
\begin{gathered}
||1-S a(z)||_P^2 \\
  =1/κ-1+||S(a(z)-a^*)||_P^2.
\end{gathered}
```

Therefore

```math
\begin{gathered}
||1-S a(z)||_P^2 ≤ 1/κ-1+ε^2/[κ(1-ε)^2].
\end{gathered}
```

These are `normalized_target_error_exact`,
`normalized_target_error_le`, and the concrete
`RamanujanZeroSignal.sampled_target_error_le`.

## 6. Certifying inverse-metric errors from coordinate errors

If |e_i|≤η_i, η_i≥0, the verified anisotropic majorant is

```math
\begin{gathered}
e^T A e ≤ \sum_i \sum_j |A_{ij}| η_i η_j.
\end{gathered}
```

This is `inverseNorm_sq_le_entrywise`. Thus it is enough to certify that
the right side is at most ε^2 κ. For a common coordinate tolerance δ, the
simpler sufficient budget is

```math
\begin{gathered}
δ^2 \sum_i \sum_j |A_{ij}| ≤ ε^2 κ.
\end{gathered}
```

This estimate is a sufficient certificate after the exact signed quadratic
identity; it does not replace the actual inverse Gram matrix by a diagonal
phase average.

## 7. Increasing zero cutoffs: the uniform-condition-number issue is removed

For each fixed finite stage D_j, coordinate convergence of ell_T implies

```math
\begin{gathered}
||ell_T-\ell||_{H_j^{-1}} →0.
\end{gathered}
```

For any prescribed positive ε_j, one can therefore choose strictly increasing
integer zero heights τ_j, with τ_j≥j, such that

```math
\begin{gathered}
||ell_{τ_j}-\ell||_{H_j^{-1}} ≤ ε_j ||\ell||_{H_j^{-1}}.
\end{gathered}
```

The general result is
`FiniteGramSignalStability.exists_strictMono_diagonal_relative_error`.
The actual-zero result is
`RamanujanZeroSignal.exists_strictMono_zero_cutoffs`, conditional only on
the stated Selberg input in addition to its finite-stage conditions.

No uniform bound on ||H_j^{-1}|| and no uniform-in-j equidistribution rate
is needed for this existence statement. The required heights may be extremely
large and are not given effectively. This sharpens the previous conversational
claim: uniform conditioning is a practical rate issue, not an additional
existential obstacle to sampling the exact finite optimizers.

## 8. The remaining arithmetic target

Let κ_j be the capacities of an increasing exhaustive squarefree packet
family containing conductor 2. Then 0<κ_j≤1, and the constant-closure target is

```math
\begin{gathered}
κ_j →1.
\end{gathered}
```

If that target is independently established and ε_j→0, the complete error
bound above tends to zero along the chosen sampling diagonal. Equivalent
P and Q norms then transfer the same constant approximation to the original
squarefree Q legal space, giving the established RH sufficient condition.

Sampling does not prove κ_j→1. It can reproduce finite optimizers to arbitrary
prescribed accuracy without furnishing the arithmetic estimate that forces
their limiting deficit to vanish.

Research obligations:

1. **Open formal analytic provider:** prove
   `UniformSelbergDensity (1/4)` in the actual-zero library, with its classical
   uniformity in the strip threshold. This is known mathematics, not RH.
2. **Open arithmetic estimate:** force κ_j→1 using the complete signed Gram
   form and the free squarefree-composite corrections.
3. **Effective refinement:** combine entrywise bias rates with the certified
   inverse-metric majorant to produce usable finite zero cutoffs.
4. Preserve the distinction between weighted Q/P Gram geometry and the
   unweighted Q Gram geometry throughout any subsequent optimization.

## 9. Source map and verification boundary

| Module | Main content | Substantive analytic hypotheses |
|---|---|---|
| Analysis/SignalNormalizationStability.lean | Exact orthogonal remainder, quadratic bound, normalized convergence | None |
| Analysis/FiniteGramSignalStability.lean | Actual inverse metric, literal inverse matrix, exact signal, full target-error bound, entrywise certificate, diagonal selection | None; finite independence is explicit and proved for the packet application |
| RH/RamanujanZeroSignal.lean | Weighted Q means, actual packet Gram, prime normalization, cosine estimator, actual-zero diagonal | Selberg density only for the zero-limit and zero-cutoff statements |

Representative axiom inspections in the targeted successful job reported only
`propext`, `Classical.choice`, and `Quot.sound`. These inspections do not
remove the explicit local Selberg hypothesis from the zero-limit statements.
All final publication claims remain gated by the containing commit's
successful server checkpoint.
