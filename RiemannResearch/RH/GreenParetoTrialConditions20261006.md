# Green–Pareto trial and relative-log conditions

Source: user-provided continuation, Sections 12, 17 and 18. The source supports
the theorem statements and the complete signed proof strategy. These are
conditional research reductions, not an unconditional RH proof.

## Actual physical trials

Write \(v=\texttt{twoThreeDual}\),
\(p_n=P_{\texttt{finiteSpace}(n+2)}v\),
\(Q_n=\texttt{compactHead}(n+3)\), and let
\(u_n\in\texttt{finiteSpace}(n+2)\). Put

\[
D_n=\|v-p_n\|^2,\quad E_n=\|v-Q_nu_n\|,\quad
H_n=\langle Q_n(v-p_n),v-Q_nu_n\rangle,\quad
L_n=\langle(I-Q_n)p_n,(I-Q_n)u_n\rangle.
\]

`twoThree_actual_trial_signed_identity` and
`twoThree_actual_trial_head_pair_abs_le` prove

\[
D_n=H_n+L_n,\qquad |H_n|\le\|v\|E_n.
\]

All full physical tails and signed cross terms are retained. The normal
equations are discharged by the actual finite-space orthogonal projection.
The existing projection-exhaustion theorem supplies
\(D_n\to\delta=\|v-P_Wv\|^2\ge0\).

For any cofinal map \(k:\mathbb N\to\mathbb N\), head approximation
\(E_{k_n}\to0\) implies \(L_{k_n}\to\delta\). Either of the following
providers forces \(\delta=0\) and then invokes the existing one-way RH criterion:

| Declaration in `RH/ParetoTrialTailConditions.lean` | Additional provider |
| --- | --- |
| `riemannHypothesis_of_cofinal_signed_trial_fraction` | Fixed \(\theta<1\), \(Z_n\to0\), and eventually \(L_{k_n}\le\theta D_{k_n}+Z_n\) |
| `riemannHypothesis_of_cofinal_approximate_head_tail_product` | \(\|(I-Q_{k_n})u_{k_n}\|^2\|(I-Q_{k_n})p_{k_n}\|^2\to0\) |

The signed condition uses no absolute trial-tail cap. The product condition
uses Cauchy only after identifying the signed pairing's limit. Neither theorem
requires exact head interpolation, optimizer-tail convergence, an inverse
Gram construction, monotonicity of the cofinal map, or an RH converse.

Open: construct legal trials with the required cofinal head approximation.
Open: prove either signed strict-fraction cancellation or complete tail-product
smallness for those trials. These hypotheses remain explicit in the types.

## Finite source spectral data

For arbitrary finite nonnegative weights \(w_i\) and eigenvalues
\(\lambda_i\), define

\[
T=\sum_i\frac{w_i\lambda_i}{1+\lambda_i},\quad
S=\sum_i\frac{w_i\lambda_i}{(1+\lambda_i)^2},\quad
J=\sum_iw_i\left(\frac{\lambda_i}{1+\lambda_i}\right)^2,\quad
\mathcal L=\sum_iw_i\log(1+\lambda_i).
\]

`Analysis/FiniteSpectralBudget.lean` proves the exact identity \(T=J+S\),
complete threshold comparisons, local/general moment bounds, screening bounds,
and moving logarithmic-budget consumers. In particular, for \(R>0\),

\[
T\le(1+R)S+\mathcal L/\log(1+R).
\]

`Analysis/FiniteSpectralRelativeLog.lean` proves that a positive envelope
\(0<\sigma<1\), \(S\le\sigma\), permits the choice
\(R=1/\sqrt\sigma\) and gives

\[
T\le\sigma+\sqrt\sigma+2\mathcal L/\log(1/\sigma).
\]

`limit_eq_zero_of_cofinal_relative_log_envelope` consequently proves
\(\delta=0\) from an existing correction limit \(T_n\to\delta\), a cofinal
map \(k_n\to\infty\), \(\sigma_n\to0\), an eventual positive envelope
\(S_{k_n}\le\sigma_n<1\), and
\(\mathcal L_{k_n}/\log(1/\sigma_n)\to0\).
The moment may be unbounded, and \(S_{k_n}\) itself may equal zero.

Open: identify these finite scalar sums with the actual full-conductor
whitened arithmetic spectrum and source weights in Lean.
Open: prove the arithmetic relative-log provider. This finite-source theorem
does not itself conclude RH. The sharp Jensen lower bound
\(\mathcal L\ge T\log(T/S)\) and its coefficient-one limit floor remain
paper proofs.

## Verification scope

The combined source passed the Lean kernel before repository integration.
The generic signed-fraction consumer, literal relative-log consumer, and both
actual RH consumers report only `propext`, `Classical.choice`, and `Quot.sound`
under `#print axioms`. No proof placeholder, project-local axiom, or unsafe
declaration is used. Publication additionally validates the separate modules
and their affected reverse dependents.

The earlier consolidated head-inverse/rank-one draft is not covered by this
verification claim. The newly focused modules are the source of truth for
these conditions.
