# RH continuation: ordered damping, finite certificates, and source prediction

Date: 2026-09-24.
Starting commit: `214f54a4dfde9dee9a0f37b11e344fbab715a8f3`.
Input: `RH_Power_Damping_and_All_Dilation_Continuation_2026-09-24(1).md`.

## Conclusion

Unconditional RH has not been proved. This continuation follows both branches of
the handoff and makes the distinction between proved analytic tools and the
actual arithmetic provider explicit.

The formal work extends ordered Abel summation, power-damped physical pairings,
finite signed dilation certificates, and the exact local divisor-box algebra.
It also identifies the actual signed source as a next-residue prediction error.
Verification and publication evidence is recorded below after the final checks.

## Exact source to attack

Use the actual first-head vector e1, actual finite legal space V_M, its
orthogonal projection P_M, and E_M = ||e1-P_M e1||². This is distinct from the
constant-vector residual r = projection of 1 onto the infinite legal
orthogonal complement.

For M>=1 put

\[
v_M=(M+2)\rho_{M+2}-(M+1)\rho_{M+1},
\qquad
p_M=P_Me_1,
\]

and let s_M be the handoff's actual signed screened source. The exact
projection identity is

\[
\boxed{
E_Ms_M
=\langle v_M,p_M\rangle
=(M+2)\langle\rho_{M+2},p_M\rangle-\frac12.
}
\]

The old atom lies in V_M, so its projected e1-moment is exactly 1/2.
Define the last expression as prediction error Delta_M. Since E_M>0,

\[
s_M=\frac{\Delta_M}{E_M}.
\]

Thus the existing harmonic source criterion becomes the concrete target

\[
\boxed{
\neg\operatorname{Summable}\left(
\frac{\Delta_M^2}{E_M^2 H_{M+1}}
\right)_{M\ge1}
\quad\Longrightarrow\quad\mathrm{RH}.
}
\]

The nonsummability assertion is **Open**. Formal verification of this
implication does not establish its hypothesis.

A possible sufficient block target is: there exist c>0 and J such that for
every j>=J,

\[
\sum_{M=2^j}^{2^{j+1}-1}\left(\frac{\Delta_M}{E_M}\right)^2\ge c.
\]

Because H_(M+1)<=1+(j+1)log 2 on that block, these bounds would force the
harmonic-weighted source series to diverge. This is an unproved sufficient
RH-strength arithmetic target, not a claimed consequence of the projection
identities or the prime number theorem.

## Ordered damping: the precise formalization improvement

A real conditionally convergent ordered series is not represented by Lean's
`Summable` or by an unrestricted `tsum`. The infinite damped approximant
is not assumed to belong to the Hilbert space.

For real sequences B,f, the new generic theorem proves the exact ordered
limit

\[
\lim_{N\to\infty}\sum_{k=0}^{N-1}(B_{k+1}-B_k)f_k
=-B_0f_0+\sum_{k\ge0}B_{k+1}(f_k-f_{k+1}),
\]

assuming only absolute summability on the primitive side and the vanishing
endpoint B_N f_N ->0. A summable-majorant specialization and damping-parameter
dominated convergence are included.

For the actual damped Mobius weight q_epsilon(n), the specialization proves

\[
|q_\varepsilon(n)|\le\frac1{n+1}
\]

and the endpoint limit from H_N/(N+2)->0. Together with the previously
verified variation bound 2/((n+1)(n+2)), it gives the natural-order physical
pairing limit. The iterated theorem first lets the physical cutoff grow for
each fixed damping parameter, and then removes damping using the existing
primitive-side limit. No diagonal limit or absolute physical summability is
asserted.

The fixed-damping absolute interchange with legal-vector pairings and the
identification of the constant mode with the derivative of 1/zeta remain
outside these formal statements.

## Finite certificate theorem

Let S be a finite set of positive divisors of Q>0, with Q in S and arbitrary
real signed weights w_h. Write

\[
A_{M+1}=\sum_{h\in S}w_hR_{(Q/h)(M+1)}.
\]

The new formal bridge proves

\[
A_{M+1}\perp V_M,\qquad
\langle A_{M+1},v_M\rangle=w_Q,
\]

and, with B_M=||v_M-P_Mv_M||²,

\[
w_Q^2\le\|A_{M+1}\|^2 B_M.
\]

The existing finite physical norm limit therefore yields the eventual
inequality B_M>c whenever

\[
c\sum_{n\ge1}\eta(n)^2<w_Q^2.
\]

Here the eta coefficients are exactly those already defined in the finite
dilation module. Their arithmetic energy is retained; it is not replaced by
one without a provider proof.

## Local divisor-box algebra

The exact local geometric summation is formalized as

\[
q+(q-1)^2\sum_{j=0}^{L-1}q^j+q^L=q^{L+1}+1.
\]

Dividing by q^(L+1), for q nonzero, gives 1+1/q^(L+1). The prime-square
specialization gives 1+p^(-2(L+1)), with the exponent exact.

These declarations prove the local algebra. They do not establish the
multiplicative coefficient calculation, infinite Euler product, or global
all-dilation lower limit by themselves.

## A stronger informal arithmetic primitive criterion

The following audited argument extends the handoff's Dini test class; it is
not yet a complete Lean theorem.



Let `f` belong to the physical Hilbert space, be orthogonal to all legal
vectors, and put

\[
C_n=\sum_{k=1}^n(f_k-L),\qquad
W_\varepsilon(m)=\sum_{d\mid m}|\mu(d)|d^{-\varepsilon}
=\prod_{p\mid m}(1+p^{-\varepsilon}).
\]

It suffices that there be positive numbers `ε_j → 0` such that, for every j,

\[
\sum_{n\ge1}
 \frac{|C_n|W_{\varepsilon_j}(n+1)}{(n+1)(n+2)}<\infty.
\tag{A}
\]

This criterion does not require a monotone pointwise envelope or
`C_N/N → 0`. It is a mathematical proof, not yet a verified Lean theorem.

Indeed `W_ε≥1`, so (A) supplies exactly the summable primitive majorant
needed by `dampedPhysicalPrimitive_pairing_tendsto`. For fixed ε, write
`b_d(n)=rho_d(n)/[n(n+1)]`. Its exact difference gives

\[
\begin{aligned}
&\sum_{d\ge2}|\mu(d)|d^{-\varepsilon}
 \sum_{n\ge1}|C_n|\,|b_d(n)-b_d(n+1)|\\
&\quad\le
3\left(\sum_{d\ge2}\frac{|\mu(d)|}{d^{1+\varepsilon}}\right)
  \sum_{n\ge1}\frac{|C_n|}{(n+1)(n+2)}
 +\sum_{n\ge1}
   \frac{|C_n|(W_\varepsilon(n+1)-1)}{(n+1)(n+2)}.
\end{aligned}
\tag{B}
\]

The first term follows from `rho_d(n)≤n/d`; the second keeps precisely
the squarefree divisor jumps. Thus (A) justifies absolute interchange.
Pointwise absolute convergence of the legal expansion identifies the
primitive kernel with the damped kernel.

For each fixed d, the original legal pairing is absolutely summable by
Hilbert-space Cauchy–Schwarz. Its Abel endpoint vanishes without (A):

\[
|C_N|\le \|f-L\|\left(\sum_{k=1}^N k(k+1)\right)^{1/2}
=\|f-L\|\sqrt{\frac{N(N+1)(N+2)}3}.
\]

Since `0≤rho_d(N)<1`, this implies `C_N b_d(N)→0`. The limiting
constant weight `1/[N(N+1)]` has the same vanishing endpoint. Therefore
all necessary physical pairings are identified; no ordered damped physical
pairing or endpoint `C_N q_ε(N)` is needed in this assembly.

After interchange, the damped primitive-side value equals `−L J(ε)`.
Dominated convergence as `ε_j→0` gives `<1,f−L>=−L`, hence `<1,f>=0`.

The handoff's monotone Dini envelope implies (A) by the same dilation
comparison already proved there. For the actual canonical residual, (A)
is still an unproved RH-strength provider. Under RH the residual is zero,
so necessity of existence is immediate. This is not unconditional RH.



## An alternative to Euler products for all dilations

The following argument is also mathematical prose, not a fully formalized
global energy provider.



For a real sequence u with sum u(n)^2 finite, let T_h u(n) equal u(n/h)
when h divides n and zero otherwise. For h,k>0, put g=gcd(h,k), a=h/g,
b=k/g. The exact inner-product identity is

    <T_h u,T_k u> = sum_{t>=1} u(bt)u(at).

It follows by reindexing the common multiples of h and k by lcm(h,k)t;
the series is absolutely convergent by Cauchy--Schwarz. If h,k divide Q,
then the reduced coprime indices of Q/h,Q/k are b,a. Therefore

    <T_h u,T_k u> = <T_(Q/h) u,T_(Q/k) u>.

Finite bilinear expansion gives the full Gram-reversal identity for any
real weights alpha_d supported on positive divisors of Q:

    ||sum_d alpha_d T_d u||_2^2
      = ||sum_d alpha_d T_(Q/d) u||_2^2.

Apply it to u(n)=mu(n)/n, u(0)=0, and alpha_d=1/d for 1<=d<=D,
where Q is any common multiple of 1,...,D. The existing physical norm
theorem in the handoff then gives, for the actual certificate

    C_(D,N) = sum_(1<=d<=D) R_(dN)/d,
    lim_(N->infinity) ||C_(D,N)||^2 = E_D,
    E_D = sum_(n>=1) T_D(n)^2,
    T_D(n) = (1/n) sum_(d|n,d<=D) mu(n/d).

For D>=1, exact Mobius inversion gives T_D(1)=1 and T_D(n)=0 for
2<=n<=D. Thus

    E_D = 1 + sum_(n>D) T_D(n)^2.

The uniform majorant |T_D(n)|<=tau(n)/n is summable after squaring.
One elementary proof uses tau(n)^2<=d_4(n). The map from pairs d,e|n to

    (gcd(d,e), d/gcd(d,e), e/gcd(d,e), n/lcm(d,e))

is injective into ordered positive factorizations of n into four factors:
its product is n, and the first three coordinates recover d and e.
Consequently Tonelli and ordinary p-series convergence give

    sum_n tau(n)^2/n^s <= zeta(s)^4 < infinity     (s>1).

In particular

    0 <= E_D-1 <= sum_(n>D) tau(n)^2/n^2 -> 0.

An optional explicit certificate-index estimate is

    E_D-1 <= D^(-1/2) zeta(3/2)^4.

The proof fixes D before sending the physical cutoff N to infinity. It
therefore introduces no uniform-cutoff assumption or diagonal exchange.



The limit E_D->1 supplies liminf B_M>=1 by the new finite certificate bridge.
Under nondensity, D_M=B_M E_(M+1)/E_M gives liminf D_M>=1.
Both remain compatible with positive limiting first-head defect.
Neither forces signed source accumulation.

## What would close RH

One must prove an actual arithmetic provider, for example:

1. The nonsummability of Delta_M²/(E_M² H_(M+1)), or the stronger block lower
   bound above.
2. The weighted squarefree-divisor primitive criterion for the actual
   constant-vector residual.
3. The handoff's centered monotone Dini envelope for that residual.

Further lower bounds on the innovation denominator do not supply these.
The constant residual and the first-head residual must remain distinct.

## Files and declarations

- `Analysis/OrderedPrimitiveAbel.lean`:
  `primitive_abel_partialSum_tendsto`,
  `primitive_abel_partialSum_tendsto_of_bound`,
  `primitiveAbelPairing_tendsto`.
- `RH/DampedMobiusOrderedPairing.lean`:
  `dampedPhysicalWeight_abs_le`,
  `dampedPhysicalWeight_primitive_boundary`,
  `dampedPhysical_ordered_pairing_tendsto`,
  `dampedPhysical_iterated_ordered_pairing_tendsto`.
- `RH/FiniteDilationInnovationCertificates.lean`:
  finite-charge orthogonality, exact pairing, innovation inequality, and
  `finiteDilationReciprocalCharge_eventually_innovation_gt`.
- `RH/DivisorBoxLocalEnergy.lean`:
  `divisorBox_local_energy_numerator`,
  `divisorBox_local_energy_normalized`,
  `divisorBox_local_energy_inverse`,
  `divisorBox_prime_local_energy`.
- `RH/ScreeningSourcePrediction.lean`:
  `firstHeadSignedSource_eq_projection_pairing`,
  `firstHeadSignedSource_eq_next_atom_prediction`,
  `firstHeadPredictionError_eq_mul_source`,
  `firstHeadPredictionError_div_error`, and the conditional
  `riemannHypothesis_of_firstHead_prediction_not_summable`.

## Literature boundary

The primary sources consulted were Calderaro, Manzur, Noor and Santos,
*Orthogonality questions in the Hardy space related to zeta-zeros*,
[arXiv:2203.05030v3](https://arxiv.org/html/2203.05030v3), and Manzur, Noor and
Quintero, *A Hardy space approximation supporting zero-free half-planes for
the zeta-function*,
[arXiv:2606.16097v1](https://arxiv.org/html/2606.16097v1).
They provide context for orthogonal regularity and Hardy approximation.
They are not treated as providers of the actual residual estimates needed
here. No historical novelty claim is made for the arguments in this note.

## Verification and publication

The coherent ordered-damping/certificate candidate passed in
`job_Cz-rrCipVa7nTsre5iKE_jQHOQ2jpeGP`, with exit_code=0,
verified=true, and no warnings.

The extended iterated-damping and local-energy candidate passed in
`job_Q1WL6Y_LkOxDljDyD3-eHHT97rd9Auk9`, with exit_code=0,
verified=true, and no warnings.

The actual source/prediction identities and their conditional RH theorem
passed in `job_0-7r3JgdqhY_hYEvXFbWlLCSouE3RSXg`, with
exit_code=0, verified=true, and no warnings.

All seven principal axiom inspections printed only `propext`,
`Classical.choice`, and `Quot.sound`. No `sorry`, `admit`,
project-local axiom, or unsafe declaration is introduced. These inspections
do not discharge the explicit hypotheses in the theorem types.

The five new Lean modules are exported from `RiemannResearch.lean`.
The required checkpoint validates the saved modules before commit and push.
For the repository copy, the publication commit is the commit containing
this report; the delivered copy appends the checkpoint result and hash.
