# Raw-source bounds and the unresolved positive-moment estimate

The requested uniform upper bound for the actual correction has **not been
proved**. This continuation proves unconditional source and negative-moment
bounds. It does not discharge the arithmetic hypotheses of the earlier RH
criteria and does not prove RH.

## Definitions and scope

For positive integers, use

\[
Q(n)=\frac1{\zeta(2)n^2},\quad
a(n)=\frac{n}{(8+\log n)^2},\quad a(0)=0.
\]

Let \(V_N\) be the masked squarefree stage, \(P_N\) its Q-orthogonal
projection, \(r_N=1-P_N1\), \(s_N=Br_N\), and \(b_N=P_Ns_N\), where
\(Bf(n)=f(n)/(n+1)\). Put \(e_N=\|r_N\|_Q^2\le1\), and let \(T_t\)
retain physical coordinates \(n>t\).

These results use the **raw source** \(s_N\). The preceding CRT criterion
used the conditional source \(u_N=C_LBr_N\). Their cumulative moments are
different; no raw-source assertion below is silently transferred to \(u_N\).

Define

\[
E(H,f)=\sum_{n\le H}a(n)Q(n)f(n)^2,\qquad
\mathcal E(f)=\sum_{n\ge1}a(n)Q(n)f(n)^2,
\]
\[
M_N(t)=\sum_{n\le t}Q(n)b_N(n)(s_N(n)-b_N(n)),\qquad
\Phi_N^\pm(H)=\sum_{t<H}\Delta a(t)\max(\pm M_N(t),0).
\]

## Unconditional source and negative-part bounds

For all \(N,H,t\),

\[
\boxed{\mathcal E(s_N)\le\frac{e_N}{256}\le\frac1{256}},\qquad
\boxed{\|T_ts_N\|_Q^2\le\frac{e_N}{(t+2)^2}},
\]
\[
\boxed{M_N(t)\ge-\frac{e_N}{4(t+2)^2}},\qquad
\boxed{\Phi_N^-(H)\le\frac{e_N}{1024}\le\frac1{1024}}.
\]

The source estimate holds for every input \(f\in L^2(Q)\), with
\(\mathcal E(Bf)\le\|f\|_Q^2/256\). Indeed,

\[
\frac{a(n)}{(n+1)^2}
\le\frac{n}{64(n+1)^2}\le\frac1{256}.
\]

The scalar constant is attained at \(n=1\); this does not assert sharpness
for actual projection residuals. The tail estimate follows from
\((n+1)^{-1}\le(t+2)^{-1}\) on \(n>t\).

Orthogonality gives the exact signed identities

\[
M_N(t)=\|T_tb_N\|_Q^2-\langle T_tb_N,T_ts_N\rangle_Q
=\|T_tb_N-\tfrac12T_ts_N\|_Q^2-\tfrac14\|T_ts_N\|_Q^2,
\]
\[
\|T_tb_N\|_Q^2
=2M_N(t)+\|T_ts_N\|_Q^2-\|T_t(b_N-s_N)\|_Q^2.
\]

These retain the full tails and the nonnegative square remainders.

## Exact cumulative energy accounting

Set
\[
X_H(f)=\sum_{t<H}\Delta a(t)\|T_tf\|_Q^2.
\]
The formal layer identity is
\[
\boxed{X_H(f)=E(H,f)+a(H)\|T_Hf\|_Q^2}.
\]
If \(\mathcal E(f)\) is finite, monotonicity of \(a\) yields
\(X_H(f)\le\mathcal E(f)\). Consequently the completed-square identity
gives \(\Phi_N^-(H)\le X_H(s_N)/4\le e_N/1024\).

The full signed decomposition is
\[
\boxed{X_H(b_N)=2(\Phi_N^+(H)-\Phi_N^-(H))
+X_H(s_N)-X_H(b_N-s_N)}.
\]
In particular,
\[
\boxed{E(H,b_N)\le 2\Phi_N^+(H)+\frac{e_N}{256}}.
\]
The positive variation remains on the right. This is an unconditional
inequality, **not** an unconditional uniform energy bound.

## An unconditional parity improvement of the intrinsic form

For an odd-orthogonal vector, the first internal Hilbert coordinate uses at
most one third of the energy outside the second coordinate. Combining this
with the exact reciprocal spectral split gives, for every nonempty stage,
\[
\boxed{\langle r_N,Br_N\rangle_Q+D(r_N)\le e_N/3},
\quad D(f)=\sum_{j\ge0}\left(\frac14-\frac1{j+4}\right)\widehat f(j+2)^2,
\]
where \(\widehat f(j)=f(j+1)/(\sqrt{\zeta(2)}(j+1))\) denotes the
internal Q-Hilbert coordinate. Thus \(D\ge0\). The preceding exact identity is
\[
\langle f,Bf\rangle_Q
=\|f\|_Q^2/4+\widehat f(0)^2/4+\widehat f(1)^2/12-D(f).
\]
The one-third constant is sharp on the entire odd-orthogonal space, as the
vector supported at physical site two shows. No sharpness claim is made for
the actual residuals. This strengthens the intrinsic form budget but still
does not bound the weighted projection.

## What the arithmetic attempts did and did not establish

Möbius inversion, radical-jump constraints, conductor decompositions, prime
dilations, the Q/P Gram comparison, and the compressed reciprocal resolvent
did not yield a bound for the specific forcing
\(y_N=\nu_N-J_NG_N^{-1}\mu_N\).

There is a concrete obstruction to replacing that missing argument by a
uniform weighted Gram comparison. For a prime \(d\ge3\), put
\(N=H=d-1\) and use the legal atom \(g_d(n)=(n\bmod d)/d\).
Splitting its Q norm at \(d\), using \(g_d\le(d-1)/d\), and using
\(\sum_{n\ge d}n^{-2}\le1/(d-1)\), gives
\(\|g_d\|_Q^2\le2/(\zeta(2)d)\). On the head,
\[
E(d-1,g_d)
=\frac1{\zeta(2)d^2}\sum_{n=1}^{d-1}\frac{n}{(8+\log n)^2}
\ge\frac1{3\zeta(2)(8+\log d)^2}.
\]
Thus the ratio is at least \(d/[6(8+\log d)^2]\), which is unbounded
along primes. This calculation is a paper audit, not a newly formalized
Lean theorem. It refutes a bound for **all** legal vectors, not the desired
bound for the specially coupled \(b_N\).

The actual positive-moment envelope and the cofinal uniform positive-variation
bound remain **Open**. Neither a proof nor a counterexample for the actual
sequence was obtained. Ordinary Q-norm contraction, source smoothing, and
complete CRT conditioning alone do not fill this gap.

## Formal artifacts

- `Analysis/PolylogAbelBudget.lean`: scalar reciprocal logarithmic multiplier.
- `RH/QReciprocalWeightedEnergy.lean`: complete source summability, source
  energy, and quadratic tail bounds.
- `RH/QHeadTailLayerEnergy.lean`: exact layer identity and signed split,
  negative variation, and positive-variation energy comparison.
- `RH/QSquarefreeRawSourceBounds.lean`: specialization to the actual residual
  and correction; no unresolved arithmetic hypothesis in these declarations.
- `RH/QShiftedReciprocalTail.lean` and `RH/QParityReciprocalForm.lean`:
  complete two-coordinate spectral defect and parity form bound by one third.

The exact signed results are primary. The earlier RH reductions remain
conditional research reductions. Verification uses the Lean server and the
publication checkpoint; numerical or symbolic calculations are not proof
certificates. Wolfram independently returned `True` for the scalar rational
inequality and the completed-square algebra; Lean checks the actual theorems.

Source: the user's squarefree CRT research agenda and follow-up request to
prove its bounds, 26 October 2026. These are independent formal derivations;
no claim of mathematical novelty is made.
