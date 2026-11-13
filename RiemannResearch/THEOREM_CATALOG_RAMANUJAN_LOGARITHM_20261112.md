# Ramanujan logarithm and direct atom closure

Correction, 13 November 2026: the user clarified that the intended logarithm
is the physical Pareto sequence h(n)=Lambda(n)/log(n), not the packet
coefficient synthesis studied below. This note's obstruction applies only
to the latter and does not refute legality of the physical sequence.
See THEOREM_CATALOG_PARETO_PHYSICAL_LOGARITHM_20261113.md for the corrected
investigation and the remaining legality transfer.

12 November 2026. Source: Christian Noack's request to use
log_*(mathbb 1) as a legal Ramanujan combination and prove that the
constant target belongs to the closed atom span.

## Precise distinction

For Dirichlet convolution, write epsilon for the convolution identity and
mathbb 1 for the arithmetic function identically one on positive integers.
The coefficientwise identities are
\[
 h=\log_*\mathbb 1,\quad h(p^k)=1/k,\quad h(n)=0
 \text{ otherwise},\qquad
 \exp_*h=\mathbb 1,\qquad \exp_*(-h)=\mu.
\]
They follow by taking the formal logarithm of each Euler factor:
\[
 \log(1-z)^{-1}=\sum_{k\ge1}z^k/k,\qquad
 \exp\!\left(-\sum_{k\ge1}z^k/k\right)=1-z.
\]
These are ordinary mathematical derivations, not new Lean declarations in
this change. Formal arithmetic identities do not assert continuity of
packet synthesis or exponentiation in the target Hilbert norm.

We use g_d(n)=(n mod d)/d and reserve B for multiplication by dQ/dP.
Write the integrated Ramanujan packets as
\[
 R_q(n)=\sum_{d\mid q}\mu(q/d)d\,g_d(n).
\]
Every finite packet sum is a legal finite atom combination.
The arithmetic coefficient vector h is not, by definition, the physical
sequence obtained by packet synthesis. Nor is it the inverse-Gram solution.
In the Pareto metric the correlation vector is
\(\langle1,R_q\rangle_P=\Lambda(q)\), and the finite optimal synthesis
coefficients are \(G^{-1}\Lambda\).

## Exact obstruction to raw prime-power synthesis

Let
\[
 \mathcal W_{\rm pp}
 =\overline{\operatorname{span}}^{L^2(P)}
   \{R_{p^k}:p\text{ prime},\,k\ge1\},
 \qquad P(n)=1/[n(n+1)].
\]
The continuous functional
\[
 L(f)=2f(1)-f(3)-f(5)+f(6)
\]
annihilates every raw prime-power packet and hence all of this closed span.
Its value on the target is L(1)=1. Its Riesz vector is
\[
 v=4\delta_1-12\delta_3-30\delta_5+42\delta_6,\qquad
 \|v\|_P^2=92.
\]
For every f in the entire Hilbert space, the full equality is
\[
 \boxed{\|1-f\|_P^2
 =\frac{(1-L(f))^2}{92}
 +\left\|1-f-\frac{1-L(f)}{92}v\right\|_P^2.}
\]
In particular, every f in W_pp has error at least 1/92. This lower bound
is not claimed sharp for W_pp: the repository already has a stronger
four-witness finite-coordinate bound in ParetoFiniteCertificates.

Consequently, all finite logarithmic syntheses
\[
 \ell_E=\sum_{(p,k)\in E}\frac1k R_{p^k}
\]
are legal, but none can approach one. Changing their coefficients,
normalizing them, or taking a Hilbert-space limit within the raw
prime-power span does not remove the obstruction.

The natural undamped truncations fail even to converge at the first site:
\[
 \ell_N(1)=\pi(N),\qquad
 \ell_N=\sum_{p^k\le N}\frac1k R_{p^k}.
\]
Indeed R_p(1)=1 and R_{p^k}(1)=0 for k>=2. This last pointwise computation
is an ordinary proof, not a separately formalized theorem in this change.

If f_N lies in W_pp and f_N+c_N tends to one, then L(c_N) tends to one.
Thus any successful exponential construction has to supply a nonvanishing
mixed-conductor correction; the logarithmic part alone is insufficient.

## The corrected exponential route

Use the negative convolution exponential to obtain the signed arithmetic
coefficients mu, then synthesize them in the g_d dictionary. Put
\[
 M_N=\sum_{d=1}^N\frac{\mu(d)}d,\qquad
 F_N=-\sum_{d=2}^N\mu(d)g_d+(N+1)M_Ng_{N+1}.
\]
This is a genuine finite legal family. For 1<=n<=N,
\[
 F_N(n)=1.
\]
At every n its exact floor formula, including the correction term, is
\[
 F_N(n)=\sum_{d=1}^N\mu(d)\lfloor n/d\rfloor
 -(N+1)M_N\lfloor n/(N+1)\rfloor.
\]
Existing Lean providers:
- Pareto.canonicalMobiusHead_exact,
  CanonicalMobiusConditionalHead.lean;
- Pareto.canonicalMobiusHead_floor_expansion,
  CanonicalMobiusFullEnergy.lean;
- QMobiusExactHead.exactHead_mem_legalSpan and exactHead_exact,
  QMobiusExactHead.lean.

This construction really does carry the logarithmic algebra into legal
exact heads. The complete remaining strong-convergence obligation is
\[
 \|1-F_N\|_P^2
 =\sum_{n>N}\frac{|1-F_N(n)|^2}{n(n+1)}\longrightarrow0.
\]
Pointwise stabilization and coefficientwise convolution exponentiation do
not bound this tail. An alternative sufficient target is a uniform complete
Hilbert-norm bound along a cofinal subsequence. Exact heads then give weak
convergence to one; a closed linear subspace is weakly closed. Finite convex
averages give strong legal approximants. The existing Q theorem
exists_exactHead_averages_of_uniform_bound implements the full-sequence
version, with a genuine uniform error-bound hypothesis.

Neither tail convergence nor that uniform bound has been proved here.

## Screened prime-power route

PrimePowerRamanujanClosure.lean already proves the correct equivalence
after replacing R_{p^k} by (I-P_C)R_{p^k}, where C is the closed mixed-packet
span. These corrected packets contain mixed-conductor information.
Their target closure is equivalent to full atom closure. The raw-packet
obstruction above does not refute this screened equivalence, and the
screened equivalence alone does not prove target membership.

The measures P and Q(n)=1/(zeta(2)n^2) have bounded positive density ratios,
so their closures of the same physical atom span agree. This does not
make their Gram matrices identical.

## Formal additions and status

New module: RiemannResearch/RH/RamanujanLogarithmObstruction.lean.
Namespace: RiemannResearch.RH.Pareto.RamanujanLogarithm.

| Declaration | Exact content |
|---|---|
| rawPrimePowerClosure_le_kernel | Complete raw prime-power closure lies in ker L. |
| dualSix_riesz_norm_sq | The actual Riesz vector has squared norm 92. |
| error_eq_charge_add_remainder | Exact full Hilbert error, signed charge and orthogonal remainder. |
| error_eq_obstruction_add_remainder | Exact specialization when L(f)=0. |
| rawPrimePowerClosure_error_floor | Error at least 1/92 on the entire closed raw span. |
| one_not_mem_rawPrimePowerClosure | Unconditional exclusion of one from that restricted closure. |
| logPacketCombination_mem | Finite 1/k packet synthesis belongs to the raw closed span. |
| logPacketCombination_error_floor | The same explicit error obstruction for logarithmic synthesis. |
| correction_charge_tendsto_one | Any successful correction must supply asymptotic charge one. |

These additions extend the earlier finite witnesses to an exact complete
Hilbert decomposition and closure statement. They do not establish
1 in the full atom closure or RH. Publication is gated on the server's
full Bazel/BuildBuddy checkpoint; the terminal checkpoint record supplies
the verification evidence.

Background reference: Luis Baez-Duarte, "A strengthening of the
Nyman-Beurling criterion for the Riemann Hypothesis",
https://arxiv.org/abs/math/0202141. This supports the integer-dilation
criterion and explains the significance of the closure goal; it is not
an external proof provider for any new Lean declaration.
