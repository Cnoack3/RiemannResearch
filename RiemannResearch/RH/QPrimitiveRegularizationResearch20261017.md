# Q primitive regularization: checked framework and arithmetic continuation

Research date: 17 October 2026. Source: user-provided
Squarefree_Primitive_Energy_Regularization_2026-10-17(1).md.

Use a=1/zeta(2), Q(n)=a/n^2 for n>=1, g_d(n)=(n mod d)/d,
physical boundary F(0)=0, and Delta F(n)=F(n)-F(n-1).
Let L_M be the product of the first M primes, D_M its divisors greater
than one, V_M their real residue span, and H the Q closure of their union.
The target e_1 is the indicator of the physical site n=1.

## 1. Formal scope and verification evidence

Analysis/PrimitiveRegularization.lean contains complete objective and
penalty-change identities, coercive existence and uniqueness, Galerkin
Pythagoras, and zero_penalty_cross_identity.
RH/QPhysicalDifference.lean realizes the actual unilateral shift as a
contraction and constructs the bounded injective physical difference.
RH/QPrimitiveEnergyClosure.lean supplies bounded-difference closure,
canonical squarefree minimizer existence, and the exact equivalence
between constant closure and a uniform critical regularized objective
budget along any positive normal family with penalties tending to zero.
Its actual Mathlib RH conclusion is a conditional research reduction.

The split-module check job job_W3UVvIJkgjEBIXbpBWoCcEUKiNyBaV5j
succeeded, compiling all three modules. The additional correlation-identity
snippet job job_ERwaZLkOUisN_FTKbNffaOoBlGLswOz7 succeeded.
Axiom inspections reported propext, Classical.choice and Quot.sound only.
Publication of the final delta still requires its checkpoint validation;
these snippet results do not replace that validation.

Bagchi, https://arxiv.org/abs/math/0607733, Remark 8 supports the imported
mathematical equivalence RH iff 1 belongs to H. The implication from RH
to squarefree closure is not newly formalized here. The standard quadratic
regularization method is discussed in Albani et al.,
https://arxiv.org/abs/1511.02950, introduction and equation (1).

The following arithmetic derivations are paper proofs and exact finite
rational checks, not additional Lean-certified statements. In particular,
no complete O(lambda) arithmetic provider has been proved.

## 2. Arithmetic diagonalization of the derivative Gram

Fix a squarefree primorial \(L=L_M\), and write
\[
D=\{r>1:r\mid L\},\quad
J_2(r)=\prod_{p\mid r}(p^2-1),\quad \phi(r)=\prod_{p\mid r}(p-1).
\]
Under Q, the indicators \(I_p\) are independent Bernoulli variables of means
\(p^{-2}\). Consequently the finite divisor wavelets
\[
W_r(n)=\prod_{p\mid r}(p^2I_p(n)-1)
      =\sum_{d\mid r}\mu(r/d)d^2 I_d(n)
\]
satisfy, for \(r,s>1\),
\[
\langle1,W_r\rangle_Q=0,\qquad
\langle W_r,W_s\rangle_Q=\mathbf1_{r=s}J_2(r).
\]
All of these are actual physical Q identities. Only the finite prime-divisibility
variables have product law; no Haar model replaces the physical sequence space.

Define **legal primitive wavelets**
\[
\Psi_r=\sum_{\substack{d\mid r\\d>1}}d^2\mu(r/d)g_d.
\]
The exact jump identity gives
\[
\boxed{\Delta\Psi_r=\phi(r)\,1-W_r.}
\]
Indeed, the omitted \(d=1\) jump is zero, and
\(\sum_{d\mid r}d\mu(r/d)=\phi(r)\).
This is an identity for finite legal combinations, not a claim that \(1\) or
\(W_r\) separately belongs to the legal primitive span.

For \(F_c=\sum_{d\in D}c_dg_d\), introduce the invertible upper-divisor transform
\[
t_r=\sum_{\substack{d\mid L\\r\mid d}}\frac{c_d}{d^2},
\qquad
c_d=d^2\sum_{\substack{r\mid L\\d\mid r}}\mu(r/d)t_r.
\]
Then
\[
F_c=\sum_{r\in D}t_r\Psi_r,\quad
\Delta F_c=\left(\sum_{r\in D}\phi(r)t_r\right)1-
                 \sum_{r\in D}t_rW_r,
\]
\[
\sum_{d\in D}\frac{c_d}{d}
 =\sum_{r\in D}(\phi(r)-\mu(r))t_r.
\]
Thus the **complete derivative error** is
\[
\boxed{
\|\Delta F_c-e_1\|_Q^2
 =a-2a\sum_{r\in D}(\phi(r)-\mu(r))t_r
  +\left(\sum_{r\in D}\phi(r)t_r\right)^2
  +\sum_{r\in D}J_2(r)t_r^2.
}
\]
This retains the constant component and every covariance contribution.

Normalize by
\[
P_r=\Psi_r/\sqrt{J_2(r)},\quad x_r=\sqrt{J_2(r)}t_r,\quad
k_r=\phi(r)/\sqrt{J_2(r)},\quad h_r=\mu(r)/\sqrt{J_2(r)}.
\]
The derivative Gram is now exactly
\[
\boxed{I+kk^{\mathsf T}.}
\]
The physical primitive Gram remains
\(\Gamma(r,s)=\langle P_r,P_s\rangle_Q\). In particular the full mixed matrix is
\[
\boxed{I+kk^{\mathsf T}+\lambda\Gamma,}
\]
and
\[
\boxed{
\alpha_M(\lambda)
 =a-a^2(k-h)^{\mathsf T}
       (I+kk^{\mathsf T}+\lambda\Gamma)^{-1}(k-h).
}
\]
This is a change of coordinates in the original complete physical problem.
It does not replace \(\Gamma\) by the identity or discard its off-diagonal entries.

For \(R_\lambda=(I+\lambda\Gamma)^{-1}\), Sherman–Morrison gives the additional exact form
\[
\alpha_M(\lambda)=a-a^2\left[
 (k-h)^{\mathsf T}R_\lambda(k-h)
 -\frac{((k-h)^{\mathsf T}R_\lambda k)^2}
             {1+k^{\mathsf T}R_\lambda k}\right].
\]
The subtraction is essential. The remaining arithmetic work concerns this
complete primitive resolvent near the critical scale.

## 3. Explicit derivative-only optimizer and a divergent primitive-energy bound

Put
\[
B_M=\prod_{p\mid L_M}(1-p^{-2}),\qquad
R_M=\prod_{p\mid L_M}\frac p{p+1},\qquad
\delta_M=B_MR_M.
\]
The finite products give
\[
\|k\|^2=2^M R_M-1,\quad
\langle k,h\rangle=R_M-1,\quad
\|h\|^2=B_M^{-1}-1.
\]
Solving the diagonal-plus-rank-one system at zero penalty yields
\[
t_r^{(0)}=\frac a{J_2(r)}\left(\frac{\phi(r)}{2^M}-\mu(r)\right),
\]
\[
\boxed{c_d^{(0)}=a\left(\frac{dR_M}{2^M}-\frac{\mu(d)}{B_M}\right).}
\]
For the inverse divisor transform, use
\[
\sum_{d\mid r\mid L_M}\mu(r/d)\frac{\phi(r)}{J_2(r)}=\frac{R_M}{d},
\qquad
\sum_{d\mid r\mid L_M}\mu(r/d)\frac{\mu(r)}{J_2(r)}
 =\frac{\mu(d)}{d^2B_M}.
\]
Both follow by multiplying the one-prime factors over \(L_M/d\).
The exact minimum derivative error is therefore
\[
\boxed{
\alpha_M(0)=a-a^2\left(B_M^{-1}-2^{-M}R_M\right)
 =a\left(1-\frac a{B_M}\right)+\frac{a^2R_M}{2^M}.
}
\]
It tends to zero unconditionally because \(B_M\to a\).

Nevertheless the primitive optimizer \(F_M^{(0)}=\sum c_d^{(0)}g_d\) has a large
**ordinary period mean**. For a periodic legal F, write
\(m_L(F)=L^{-1}\sum_{n=1}^{L}F(n)\); this is not Q expectation.
Since \(m_L(g_d)=(d-1)/(2d)\),
\[
\boxed{m_{L_M}(F_M^{(0)})=\frac{aL_M}{2^{M+1}}.}
\]
For completeness, the required divisor sums are
\[
\sum_{d\mid L,\,d>1}(d-1)=\prod_{p\mid L}(p+1)-2^M,
\quad
\sum_{d\mid L,\,d>1}\mu(d)(1-d^{-1})=-\delta_M,
\]
and \(R_M\prod_{p\mid L_M}(p+1)=L_M\).

Finite Cauchy–Schwarz on a full period gives, for every such F,
\[
\|F\|_Q^2\ge\frac a{L^2}\sum_{n=1}^{L}F(n)^2
             \ge\frac aL\,m_L(F)^2.
\]
Hence
\[
\boxed{
\|F_M^{(0)}\|_Q^2\ge\frac{a^3L_M}{4^{M+1}}\longrightarrow+\infty.
}
\]
The divergence uses only \(p_j\ge5\) for \(j\ge3\), so
\(L_M/4^M\ge(6/16)(5/4)^{M-2}\).

This proves a concrete failure of the derivative-only finite optimizer. It does
not prove failure of positive-penalty minimizers or optimized packet mixtures.
The two limits \(M\to\infty\) and \(\lambda\downarrow0\) cannot be interchanged on
this basis.

## 4. A signed correlation provider for the positive-penalty problem

Let \(F_{M,\lambda}\) be the actual complete-energy minimizer and
\(F_M^{(0)}\) the derivative-only optimizer above. The normal equations give
\[
\boxed{
\alpha_M(\lambda)=\alpha_M(0)
 +\lambda\langle F_M^{(0)},F_{M,\lambda}\rangle_Q.
}
\]
There is the stronger exact decomposition
\[
\boxed{
\lambda\langle F_M^{(0)},F_{M,\lambda}\rangle_Q
 =\lambda\|F_{M,\lambda}\|_Q^2
  +\|\Delta(F_{M,\lambda}-F_M^{(0)})\|_Q^2.
}
\]
The abstract identity is the Lean declaration
`PrimitiveRegularization.zero_penalty_cross_identity`. Its specialization here
uses the finite normal equations. In particular the cross term is nonnegative;
one must still preserve its sign and cancellations in estimating it.

For any fixed finite C and positive \(\lambda\), the mixed-Gram budget is exactly
\[
\langle F_M^{(0)},F_{M,\lambda}\rangle_Q
 \le C-\frac{\alpha_M(0)}\lambda.
\]
For the original C=2 provider, one can first choose stages with
\(\alpha_M(0)\le\lambda\), which is unconditionally possible. A remaining
sufficient arithmetic target is then
\[
\langle F_M^{(0)},F_{M,\lambda}\rangle_Q\le1.
\]
This is an exact reformulation of where a signed cancellation estimate must act.
Cauchy–Schwarz with \(\|F_M^{(0)}\|_Q\) alone loses the required information,
since that norm has just been proved to diverge.

## 5. Sharpening the finite diagonal budget from 2 to 1

Under constant closure, the scalar competitor
\[
F=\frac a{a+\lambda}\,1\in H
\]
gives the strict bound
\[
\boxed{\alpha(\lambda)\le\frac{a\lambda}{a+\lambda}<\lambda.}
\]
The calculation is
\(a(t-1)^2+\lambda t^2\) with \(t=a/(a+\lambda)\).
Consequently fixed-positive-penalty stage convergence supplies a finite stage
with \(\alpha_M(\lambda)<\lambda\), not merely \(\alpha_M(\lambda)\le2\lambda\).
For \(\lambda_j=2^{-j}\), therefore,
\[
\boxed{
1\in H\iff\forall j\ge1\ \exists M_j\ge j:\quad
 a-v_{M_j}^{\mathsf T}(A_{M_j}+\lambda_jG_{M_j})^{-1}v_{M_j}<\lambda_j.
}
\]
The reverse implication is the regularized-budget closure argument with C=1.
Through the literature equivalence this is another RH criterion. It supplies no
unconditional arithmetic provider. The forward proof uses approximation at an
objective margin of order \(\lambda_j^2\), so no improved effective stage bound
is asserted.

Moreover any diagonal family satisfying this C=1 budget has
\(\|F_j\|_Q\le1\), derivative convergence, and weak limit 1. Lower semicontinuity
forces its norms to tend to 1; hence \(F_j\to1\) strongly. This last assertion is a
mathematical proof here, not a newly checked Lean limit declaration.

## 6. A repair that removes the period-mean obstruction without changing closure

Let \(\mathcal V_0\) consist of finite squarefree legal combinations with zero
ordinary period mean. Then
\[
\boxed{\overline{\mathcal V_0}^{\,Q}=H.}
\]
To prove this, fix one finite legal F of squarefree period L, and take fresh primes
\(p\to\infty\). Set
\[
F_p=F-\frac{2p\,m_L(F)}{p-1}g_p.
\]
Its period is a divisor of Lp, it is squarefree legal, and its ordinary period mean
is exactly zero. The correction coefficient stays bounded, while
\(g_p\to0\) strongly in Q. Thus \(F_p\to F\) in Q. Every finite legal vector is
therefore in the closure of \(\mathcal V_0\), proving equality of closures.

The fact \(g_p\to0\) is an established repository result in
`RH/QConductorLimits.lean`. This proof does not identify ordinary period mean with
a continuous functional on the whole Q space. In fact, the correction explains
why such a uniformly continuous extension is unavailable.

One may consequently add the exact zero-period-mean constraint to a trial family
without changing the infinite squarefree closure problem. This removes the
specific large-mean obstruction of Section 3. It does not establish bounded
primitive energy for the constrained derivative minimizers; their remaining
full signed Q-Gram is a separate problem.

## 7. Updated research agenda and precise remaining gap

1. The retained-workspace recovery, repaired appendix, physical difference
   construction, and coercive minimizer existence are now completed as described
   in Section 1. Preserve their server verification and publication evidence.
2. Formalize the arithmetic basis change of Section 2 using the existing divisor
   wavelets, then the explicit derivative optimizer and energy lower bound of
   Section 3. These paper results are not to be reported as already kernel-checked.
3. Estimate the **complete signed correlation** in Section 4 along selected
   positive penalties and growing primorial stages. The explicit small derivative
   minimum alone does not control it.
4. Test the zero-period-mean constrained derivative optimizer in the diagonal plus
   rank-one coordinates. Retain the complete primitive Gram and every constraint
   remainder; a bounded-energy conclusion still needs a proof.
5. Continue the multiple-fresh-prime packet capacity problem from source Section 10.
   Its full signed primitive Gram may contain cancellations that individual packet
   energies cannot reveal. Products of fresh primes remain available.
6. Keep the conditional off-line-zero witness as a circularity test: an estimate
   that produces the critical bounded legal family cannot be justified solely by
   derivative density, finite CRT consistency, or formal projective compatibility.

**Unresolved arithmetic obligation:** an unconditional uniform O(lambda) bound
for the complete optimized objective, or an equivalent bounded full-energy legal
provider. No theorem in this continuation proves RH.

Additional source: V. Albani, P. Elbau, M. V. de Hoop and O. Scherzer,
*Optimal Convergence Rates Results for Linear Inverse Problems in Hilbert Spaces*,
https://arxiv.org/abs/1511.02950, introduction and equation (1). This supports the
standard regularization framework, not the new arithmetic estimates or an RH claim.
