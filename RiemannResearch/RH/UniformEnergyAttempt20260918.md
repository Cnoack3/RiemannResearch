# Uniform-energy attempt: verified delayed-gain bound and pulse detection

Date: 2026-09-18. Project base: fdb623737dc4b00851cf711c08c22f0cab2d2c47.

**The requested uniform energy estimate is not proved.** Neither
UniformSignedSchurTarget nor a cofinal subpolynomial bound for the actual
legal exact-head energies is supplied by this continuation. RH remains unproved.

## Lean result and its precise scope

The coherent Lean candidate passed with exit_code: 0 and verified: true.
Axiom audits for the principal new bounds reported only propext,
Classical.choice, and Quot.sound. The integrated modules and their reverse
dependencies are validated by the publication checkpoint.

Six proved declarations extend existing modules:

- RH/ConditionalMeanSignedProjection.lean:
  conditionalMeanSquare_gain_eq_tail_difference,
  conditionalMeanSquare_gain_le_original_tail,
  delayed_scalar_gain_le_original_tail.
- RH/CRTDelayedProjection.lean:
  zeroMean_tail_energy_bound,
  delayed_correction_gain_bound,
  delayed_scalar_gain_bound.

For actual finite legal F and G agreeing on positive indices through M,
the exact identity is
\[
E(F)-E(G)=E_{>M}(F)-E_{>M}(G).
\]
Thus the gain is at most the original tail energy. If F has period mean
zero and its actual cumulative period defect has absolute value at most B
beyond M, then every such G satisfies
\[
E(F)-E(G)\le \frac{2}{M+2}\left(\frac{B}{M+1}\right)^2.
\]
The same upper bound applies to the exact optimized scalar gain
\(\langle \mathsf CF,\mathsf CR\rangle_J^2/E(R)\)
for every nonzero legal direction R vanishing through M. This includes any
finite combination of delayed directions, regardless of coefficients or
conductor. Existence of a finite B for each periodic F is supplied by the
existing periodDefect_exists_bound theorem. No useful uniform bound for
the B values of a growing exact-head family is claimed.

This result prevents an invalid inference from arbitrarily cheap delayed
mean cancellation to large recovery of an existing residual's energy.
It does not exclude successful corrections that operate in the necessary
earlier arithmetic range.

The existing implication
riemannHypothesis_of_uniformSignedSchurTarget was also rechecked.
Its theorem type still has the explicit unproved hypothesis
h : UniformSignedSchurTarget; its foundational axiom audit does not
discharge that hypothesis.

## Mathematical continuation and verification status

Source: the user's conditional-iid/CRT program and mathematical development
during this task. No claim of mathematical priority is made.

The qualitative strict-improvement conclusion has now been Lean-verified:
RH/ThreeGeneratorStrictImprovement.lean proves
exists_threeGenerator_strict_improvement, including existence of a
nonzero actual correlation for some d > Y. Its proof uses the exact
conditional Hilbert adjoint, first absolute moments, summable-multiples
inversion and dyadic rigidity. RH/ThreeGeneratorCorrection.lean supplies
the precise three-generator identity, optimal energy decrease, exact-head
and mean preservation, and a corrected period Q*(4*d).

The explicit Dirichlet-inverse coefficient formula and quantitative
finite-scale detection estimates below remain a written mathematical
argument. They are not claimed as Lean-verified. Their constants depend
on the current period and cumulative defect; neither the written estimates
nor the verified qualitative theorem supplies a uniform or subpolynomial
energy bound or a proof of RH.

## Statement

Let
\[
g_d(n)=\{n/d\},\quad H_d(n)=2g_{2d}(n)-g_d(n),\quad
q_t=\frac2{(t+1)(t+2)},\quad
E(F)=\sum_{t\ge1}q_t\left(\frac1t\sum_{n=1}^tF(n)\right)^2.
\]
Let \(F\) be a finite legal witness, with period \(Q\), period mean zero, and \(F(n)=1\) for \(1\le n\le Y\), where \(Y\ge1\).

Then there exists an integer \(a>Y\) with
\[
P_a:=\langle\mathsf CF,\mathsf CH_a\rangle_J\ne0.
\]
Consequently there are integers \(A>a\) and a real number \(u\) such that
\[
F+u(H_a-H_A)
\]
is legal, has mean zero, retains the exact head, and has energy strictly smaller than \(E(F)\). Thus no finite mean-zero exact-head witness minimizes energy against the full legal correction dictionary.

The stronger quantitative statement below bounds \(a\) and the energy decrease using the actual period and period-defect bound. These constants deteriorate with those quantities; no uniform bound follows.

## Exact signed transform

Write
\[
B(t)=\sum_{n=1}^tF(n),\quad x_t=\mathsf CF(t)=B(t)/t,\quad
\beta=\max_{0\le r<Q}|B(r)|.
\]
Zero period mean implies \(B(t+Q)=B(t)\), hence \(|B(t)|\le\beta\). Define
\[
a_n=\sum_{t\ge n}\frac{q_t x_t}{t},\qquad
A(m)=\sum_{n\ge m}a_n.
\]
All sums converge absolutely. Telescoping gives
\[
\sum_{t\ge n}\frac{2}{t(t+1)(t+2)}=\frac1{n(n+1)},
\]
and therefore
\[
|a_n|\le\frac{\beta}{n^2(n+1)},\qquad
|A(m)|\le\frac{\beta}{m^2}.
\tag{1}
\]
In fact, rearranging the absolutely convergent double sum gives the sharper bound \(|A(m)|\le\beta/[m(m+1)]\).
Indeed
\[
A(m)=\sum_{t\ge m}(t-m+1)\frac{q_t x_t}{t},
\]
and \(t-m+1\le t\) bounds its absolute value by
\(\beta\sum_{t\ge m}q_t/t=\beta/[m(m+1)]\).

The pulse has the exact endpoint convention
\[
H_d(n)=\sum_{k\ge1}(-1)^{k+1}\mathbf1_{n\ge kd}.
\]
Indeed its value is the parity of \(\lfloor n/d\rfloor\), so its first on-block starts at \(n=d\). Expanding the Cesaro mean and rearranging gives
\[
\begin{aligned}
P_d
&=\sum_{t\ge1}q_t x_t\frac1t\sum_{n\le t}H_d(n)\\
&=\sum_{n\ge1}a_nH_d(n)
=\sum_{k\ge1}(-1)^{k+1}A(kd).
\end{aligned}
\tag{2}
\]
The first rearrangement is justified by \(|H_d|\le1\) and \(\sum_t q_t|x_t|<\infty\). The second is justified by
\[
\sum_n|a_n|\lfloor n/d\rfloor
\le d^{-1}\sum_n n|a_n|<\infty.
\]
Every actual sign is retained in (2).

We will also need a direct correlation bound, stronger than applying the triangle inequality to the right side of (2). Since \(\mathsf CH_d(t)=0\) for \(t<d\) and \(0\le\mathsf CH_d(t)\le1\),
\[
\boxed{|P_d|\le\beta\sum_{t\ge d}\frac{q_t}{t}
=\frac{\beta}{d(d+1)}\le\frac{\beta}{d^2}.}
\tag{2a}
\]
The scalar tail identity in this display is the same telescoping identity used in (1).

## Absolute Dirichlet inversion

For \(m\) odd define
\[
\alpha(2^v m)=
\begin{cases}
\mu(m),&v=0,\\
2^{v-1}\mu(m),&v\ge1.
\end{cases}
\tag{3}
\]
Put \(\eta(k)=(-1)^{k+1}\). In terms of Dirichlet convolution,
\[
\eta=\mathbf1*(\delta_1-2\delta_2),\qquad
\alpha=\mu*\sum_{j\ge0}2^j\delta_{2^j},
\]
so \(\alpha*\eta=\delta_1\). Each coefficient in these formal convolution identities is a finite divisor sum, so the identities themselves require no analytic hypothesis.

Furthermore,
\[
\sum_{k\ge1}\frac{|\alpha(k)|}{k^2}
=\frac32\sum_{m\text{ odd}}\frac{\mu(m)^2}{m^2}
\le\frac32\sum_{m\ge1}\frac1{m^2}\le3.
\tag{4}
\]
Thus only the elementary integral-test estimate \(\sum_m m^{-2}\le2\) is needed. By (1),
\[
\sum_{k,j\ge1}|\alpha(k)|\,|A(jkd)|
\le\frac{\beta}{d^2}\left(\sum_jj^{-2}\right)
\left(\sum_k|\alpha(k)|k^{-2}\right)<\infty.
\]
We can therefore interchange and regroup (2), obtaining the exact inverse
\[
\boxed{A(d)=\sum_{k\ge1}\alpha(k)P_{kd}.}
\tag{5}
\]

If \(P_d=0\) for every \(d>Y\), (5) gives \(A(d)=0\) there. But successive differences give
\[
A(t)-2A(t+1)+A(t+2)=\frac{q_t x_t}{t}.
\tag{6}
\]
Thus \(x_t=0\) for \(t>Y\). This contradicts
\[
B(Y+Q)=B(Y)=Y>0.
\]
Hence some \(P_a\ne0\) with \(a>Y\).

## Explicit finite detection scale

Put
\[
T=Y+Q,\qquad
\delta=\frac{Y}{2T^2(T+1)(T+2)}.
\]
By (6),
\[
A(T)-2A(T+1)+A(T+2)=4\delta.
\]
For some \(d\in\{T,T+1,T+2\}\), therefore, \(|A(d)|\ge\delta\).

Choose an integer \(L\ge0\) satisfying
\[
\beta(L+4)\le\delta T^2 2^L,
\qquad K=2^L.
\tag{7}
\]
Such \(L\) exists. Two elementary estimates for (3) are
\[
\sum_{k>K}\frac{|\alpha(k)|}{k^2}
\le\frac{L+4}{2K},
\qquad
\sum_{k\le K}\frac{|\alpha(k)|}{\sqrt{k}}
\le\sqrt K(L+2).
\tag{8}
\]
For the first, separate the 2-adic valuations \(v\le L\) and \(v>L\), use \(\sum_{m>N}m^{-2}\le1/N\) for integer \(N\ge1\), and \(\sum_{m\ge1}m^{-2}\le2\). The \(v=0\) contribution is at most \(1/K\); each \(1\le v\le L\) contributes at most \(1/(2K)\); and the sum of \(v>L\) contributions is at most \(1/K\). For the second, use \(\sum_{m\le N}m^{-1/2}\le2\sqrt N\): the \(v=0\) contribution is at most \(2\sqrt K\), and each \(1\le v\le L\) contributes at most \(\sqrt K\). Dropping the oddness and squarefree restrictions only increases the bounds.

By (2a), the remainder in (5), truncated at \(K\), consequently satisfies
\[
\left|A(d)-\sum_{k\le K}\alpha(k)P_{kd}\right|
\le\frac{\beta(L+4)}{2Kd^2}\le\delta/2.
\tag{9}
\]
Every pulse has positive energy, and the existing elementary estimate gives
\[
0<E(H_a)\le\frac2{a+1}\le\frac2a.
\]
Let
\[
\Gamma=\max_{1\le k\le K}\frac{P_{kd}^2}{E(H_{kd})}.
\]
Then (8)-(9) give
\[
\frac\delta2
\le\sum_{k\le K}|\alpha(k)|\,|P_{kd}|
\le\sqrt{\frac{2\Gamma}{d}}\sqrt K(L+2).
\]
Thus for some \(a=kd\le K(T+2)\),
\[
\boxed{
\frac{P_a^2}{E(H_a)}
\ge\frac{\delta^2d}{8K(L+2)^2}
\ge\frac{\delta^2T}{8K(L+2)^2}>0.
}
\tag{10}
\]
This lower bound is for a genuine signed residual correlation. Its proof does not replace the energy matrix by entrywise absolute values; the absolute estimates only justify inversion and bound its isolated remainder.

## Legal, mean-zero energy improvement

Choose \(A>a\) sufficiently large that
\[
E(H_A)\le E(H_a),\qquad
|P_A|\le |P_a|/2.
\]
For example, the elementary bound \(E(H_A)\le2/(A+1)\) and Cauchy--Schwarz show that it suffices to take
\[
A+1\ge2/E(H_a),\qquad
A+1\ge8E(F)/P_a^2,
\]
together with \(A>a\). Let \(W=H_a-H_A\). It is legal, mean zero, and zero on the head. Its energy \(g=E(W)\) is positive: at \(t=a\), \(\mathsf CW(a)=1/a\). Put \(h=P_a-P_A\). Then
\[
E(F+uW)=E(F)+2uh+u^2g,
\qquad u_*=-h/g.
\]
The complete signed square completion gives
\[
E(F+u_*W)=E(F)-h^2/g.
\]
Since \(|h|\ge|P_a|/2\) and \(g\le4E(H_a)\), (10) gives
\[
\boxed{
E(F+u_*W)
\le E(F)-\frac{\delta^2T}{128K(L+2)^2}.
}
\tag{11}
\]
Only four residue generators are used in \(W\): \(g_a,g_{2a},g_A,g_{2A}\), with overlaps allowed. It lies in the complete mean-zero correction dictionary from the handoff.

## Exact remaining gap

Repeated finite improvement does not imply that the resulting energies become uniformly bounded as \(Y\) grows, or approach the compulsory head energy. The lower bound (11) depends on the current period \(Q\) and defect bound \(\beta\); subsequent corrections can make both grow. Consequently the guaranteed gains can form a summable series before removing the required energy.

The decisive unresolved quantitative step remains control of the cumulative signed gain for a growing sequence of actual legal witnesses. This result rules out a finite stationary obstruction, but it does not rule out a nonperiodic limiting obstruction whose decay is too weak for the absolutely convergent inversion above.

## Addendum: three generators suffice, with a finite period bound

The preceding proof has a simpler correction that is already mean zero. Define
\[
W_d=H_d-H_{2d}=3g_{2d}-g_d-2g_{4d},\qquad
R_d=\langle\mathsf CF,\mathsf CW_d\rangle_J=P_d-P_{2d}.
\]
The four consecutive blocks of length \(d\) have values \(0,1,-1,0\). Thus \(W_d\) has period \(4d\), mean zero, vanishes before \(d\), and satisfies \(|W_d|\le1\). In particular,
\[
0<E(W_d)\le\frac2{d+1}\le\frac2d,\qquad
|R_d|\le\frac{\beta}{d(d+1)}\le\frac{\beta}{d^2}.
\tag{12}
\]
Strict positivity follows from \(\mathsf CW_d(d)=1/d\).

Since \(P_{2^j d}\to0\), telescoping gives
\[
P_d=\sum_{j\ge0}R_{2^j d}.
\]
This sum is absolute by (12). Substituting it into (5) is also absolutely justified:
\[
\sum_{k\ge1}\sum_{j\ge0}|\alpha(k)|\,|R_{2^jkd}|
\le\frac{\beta}{d^2}
\left(\sum_k\frac{|\alpha(k)|}{k^2}\right)
\left(\sum_{j\ge0}4^{-j}\right)<\infty.
\]
Consequently,
\[
\boxed{A(d)=\sum_{k\ge1}\gamma(k)R_{kd},\qquad
\gamma(2^v m)=2^v\mu(m)\quad(m\text{ odd}).}
\tag{13}
\]
Indeed the coefficient at \(2^v m\) is
\(\sum_{j=0}^v\alpha(2^{v-j}m)
=[1+\sum_{i=1}^v2^{i-1}]\mu(m)=2^v\mu(m)\).
In particular, the family of already mean-zero directions \(W_d\), \(d>Y\), detects every finite mean-zero exact-head witness.
The inverse coefficients also have the explicit absolute-convergence bound
\[
\sum_{k\ge1}\frac{|\gamma(k)|}{k^2}
=2\sum_{m\text{ odd}}\frac{\mu(m)^2}{m^2}\le4.
\]
Together with (12), this proves absolute convergence directly on the right side of (13).

For an explicit gain, retain \(T,\delta\) from above, but now choose \(L\ge0\), \(K=2^L\), satisfying
\[
2\beta(L+3)\le\delta T^2K.
\tag{14}
\]
The same valuation decomposition gives
\[
\sum_{k>K}\frac{|\gamma(k)|}{k^2}\le\frac{L+3}{K},
\qquad
\sum_{k\le K}\frac{|\gamma(k)|}{\sqrt{k}}
\le2(L+1)\sqrt K.
\tag{15}
\]
For the first estimate, every \(0\le v\le L\) contributes at most \(1/K\), and the sum for \(v>L\) contributes at most \(2/K\). For the second, each \(0\le v\le L\) contributes at most \(2\sqrt K\). These use the same elementary integral estimates as (8).

For some \(d\in\{T,T+1,T+2\}\), \(|A(d)|\ge\delta\). By (12)-(15), truncating (13) at \(K\) costs at most \(\delta/2\). Put
\[
\Gamma_0=\max_{1\le k\le K}\frac{R_{kd}^2}{E(W_{kd})}.
\]
Then
\[
\frac\delta2
\le\sum_{k\le K}|\gamma(k)|\,|R_{kd}|
\le\sqrt{\frac{2\Gamma_0}{d}}\;2(L+1)\sqrt K.
\]
There is therefore an \(a=kd\le K(T+2)\) with
\[
\boxed{\frac{R_a^2}{E(W_a)}
\ge\frac{\delta^2d}{32K(L+1)^2}
\ge\frac{\delta^2T}{32K(L+1)^2}>0.}
\tag{16}
\]
Set \(u=-R_a/E(W_a)\). The full signed quadratic identity, without an additional mean repair, yields
\[
\boxed{E(F+uW_a)
=E(F)-\frac{R_a^2}{E(W_a)}
\le E(F)-\frac{\delta^2T}{32K(L+1)^2}.}
\tag{17}
\]
This corrected witness is legal, mean zero, and exact on the original head. It has a period dividing
\[
\operatorname{lcm}(Q,4a)\le4Qa\le4QK(T+2).
\]
Thus a genuine finite strict improvement is available with just three residue generators and a stated finite period bound. The dependence of (14), (16), and the new period on the current \(Q,\beta\) still leaves the uniform and subpolynomial energy estimates unresolved. None of this addendum has been Lean-verified in this task.
