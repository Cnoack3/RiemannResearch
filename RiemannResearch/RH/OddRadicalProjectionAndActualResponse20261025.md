# Odd radical projection and the remaining actual response bound

**Date:** 25 October 2026.
**Baseline:** ff64ced471dfe112be4359a04c5010c9e4a3f233.
**Conclusion:** RH is not proved. No provider of KPS, KF, or the actual signed bound B was obtained.

This continuation attempted the actual kernel-energy and signed-response estimates in the incoming prime-square screening handoff. The new Lean result is a finite weighted-pair projection theorem with an absolute physical bound. The complete odd-radical extension below is an ordinary mathematical argument, not a formalized infinite QHilbert projection theorem.

## Formal results and their exact scope

Module: `RiemannResearch/Analysis/FinitePairBlockProjection.lean`.
Namespace: `RiemannResearch.Analysis.FinitePairBlockProjection`.

For a nonempty finite index type, positive weights a_i,b_i, and input pairs x_i,y_i, put

```text
rho_i = a_i*b_i/(a_i+b_i)
c = sum_i rho_i*(x_i-y_i) / sum_i rho_i
m_i = (a_i*x_i+b_i*y_i)/(a_i+b_i)
X_i = m_i + b_i*c/(a_i+b_i)
Y_i = m_i - a_i*c/(a_i+b_i).
```

Lean establishes:

- `block_common_difference`: X_i-Y_i=c.
- `block_mean_preserved`: a_i*X_i+b_i*Y_i=a_i*x_i+b_i*y_i.
- `block_residual_norm`: the complete finite weighted residual energy is sum_i rho_i*(x_i-y_i-c)^2.
- `block_orthogonal`: the residual is orthogonal, in the weighted pair form, to every array whose pair differences are constant.
- `block_pythagorean`: for every such comparison array (u_i,v_i), the squared weighted distance from (x,y) to (u,v) is exactly the residual energy plus the squared distance from (X,Y) to (u,v). Hence this is the weighted orthogonal minimizer.
- `block_sup_bound_of_ratios`: if both weight ratios are at most A, the output coordinates are at most (1+2A)M whenever all input coordinates are at most M in absolute value.
- `inverseSquare_pair_identities`: the exact pair ratios and harmonic weight for weights 1/(Z*j^2), 1/(Z*(j-1)^2).
- `inverseSquare_block_sup_bound`: for Z>0 and every j_i>=3, both output coordinates are bounded by (31/13)M, uniformly in block size and sites.

These are unconditional finite-array results. The Lean statements do not yet construct U, R, R_L, or their infinite projection limits below. The arithmetic identification and the passage to complete infinite odd-radical screening are ordinary arguments in this report. No domain-specific RH premise is used in the finite results, and no new conditional RH consumer was added.

The ordinary proof below explains the intended application: finite odd physical pairs with the same radical form disjoint weighted blocks, and the finite projection bound survives their strong projection limit.

## Verification record before the final publication checkpoint

- Baseline exact-type and axiom audit: job_O0S3RPxPPgA8Of1kGqNdU8Qma3M7I4r9 succeeded, verified=true; reported Lean duration 8.120 seconds.
- It rechecked the complete prime-square inequality, gain-tail bound, cutoff gap, and existing moving-head RH consumer. The latter still explicitly requires a common bound on the actual moving correction.
- Coherent new candidate and axiom audit: job___IrVsbSvVKOyUXQxgnt8Il988nMZqsB succeeded, verified=true; reported duration 4.394 seconds.
- Audited central axioms: propext, Classical.choice, Quot.sound.
- Routine earlier elaboration errors were repaired. In particular, complete summands containing addition are explicitly parenthesized; the final statements have no unintended free site parameter.
- These timings are reported verification durations, not workspace-opening or total request times. Workspace opening and some source requests were slow; some source requests timed out. Their cause and separate duration were not established.
- Final source publication is gated by the server checkpoint, including the aggregate import change. The final checkpoint ID and commit are reported in the accompanying response.

## Ordinary infinite arithmetic extension

Put Z=ζ(2), Q(n)=1/(Zn²), n≥1, and let H=ℓ²(Q). The evaluation vector e_n is normalized by ⟨f,e_n⟩=f(n). Let

\[
U=\overline{\operatorname{span}}\{
e_j-e_{j-1}-e_{\operatorname{rad}j}+e_{\operatorname{rad}j-1}:
j\ge3,\ j\text{ odd and nonsquarefree}\}.
\]

Write R=I−P_U. Then R is the orthogonal projection onto

\[
W_{\rm odd}=\{f\in H:\Delta f(j)=\Delta f(\operatorname{rad}j)
\text{ for every odd nonsquarefree }j\ge3\}.
\]

For every physically bounded f,

\[
\boxed{\|Rf\|_\infty\le \frac{31}{13}\|f\|_\infty.}
\tag{1}
\]

This is a proved upper bound, not a claim about the optimal operator norm. The simpler constant 3 also works for arbitrary positive pair weights.

For Bf(n)=f(n)/(n+1), physical evaluation gives |Bf(n)|≤√Z‖f‖_H. Consequently,

\[
\boxed{\|RBf\|_\infty\le\frac{31}{13}\sqrt Z\|f\|_H.}
\tag{2}
\]

Both statements include the complete infinite tail.

## Orthogonal pair and radical blocks

For each odd j≥3 put

\[
d_j=e_j-e_{j-1},\quad D_j=j^2+(j-1)^2,\quad
a_j=\|d_j\|_H^2=ZD_j,\quad\rho_j=a_j^{-1}.
\]

The supports {j−1,j} are pairwise disjoint over odd j≥3. Thus the d_j are mutually orthogonal. The pairs partition all physical sites n≥2; site 1 is left alone.

For each odd squarefree r≥3 let J_r={j≥3: rad(j)=r}. Every element of J_r is odd. Distinct J_r give orthogonal support blocks. The set J_r contains r.

Let D_r be the closed span of {d_j:j∈J_r}, and U_r the closed span of {d_j−d_r:j∈J_r}. The vector

\[
v_r=\sum_{j\in J_r}\frac{d_j}{a_j}
\]

converges in H, because its summands are orthogonal and

\[
\|v_r\|_H^2=S_r:=\sum_{j\in J_r}\frac1{a_j}<\infty.
\]

Here 0<S_r since r∈J_r, and finiteness follows from a_j≥Zj². Moreover ⟨v_r,d_j⟩=1 for every j∈J_r. If h∈D_r is orthogonal to all d_j−d_r, then all ⟨h,d_j⟩ equal a common c. Orthogonal expansion therefore gives h=cv_r. It follows that

\[
D_r\cap U_r^\perp=\operatorname{span}\{v_r\},
\qquad U_r=D_r\cap v_r^\perp.
\]

The remaining subspace within each pair consists of functions with equal values at its two sites. R leaves these pair-constant components unchanged. On D_r it projects onto the line spanned by v_r. R also fixes the coordinate at site 1.

## Exact physical formula

For f∈H define

\[
\delta_j=f(j)-f(j-1),\qquad
c_r=\frac{\sum_{j\in J_r}\rho_j\delta_j}{S_r},
\]

\[
m_j=\frac{Q(j)f(j)+Q(j-1)f(j-1)}{Q(j)+Q(j-1)}
=\frac{(j-1)^2f(j)+j^2f(j-1)}{D_j}.
\]

The numerator defining c_r is absolutely convergent even when f is not physically bounded. Indeed Bessel gives Σ_{j∈J_r}δ_j²/a_j≤‖f‖², while Σ1/a_j<∞; Cauchy–Schwarz then gives Σ|δ_j|/a_j<∞.

For j∈J_r,

\[
\boxed{
(Rf)(j)=m_j+\frac{j^2}{D_j}c_r,\qquad
(Rf)(j-1)=m_j-\frac{(j-1)^2}{D_j}c_r.}
\tag{3}
\]

Also (Rf)(1)=f(1). Formula (3) preserves every pair's Q-weighted mean and replaces its difference by c_r. In particular ΔRf(j)=c_r for every j∈J_r, so **all odd radical constraints** hold.

For completeness, the generic weighted-pair identity proving orthogonality is as follows. For positive w_+,w_− put

\[
m=\frac{w_+x+w_-y}{w_++w_-},\quad
x'=m+\frac{w_-}{w_++w_-}c,\quad
y'=m-\frac{w_+}{w_++w_-}c,\quad
\rho=\frac{w_+w_-}{w_++w_-}.
\]

Then x'−y'=c, the weighted mean is preserved, and for arbitrary u,v,

\[
w_+(x-x')u+w_-(y-y')v
=\rho(x-y-c)(u-v).
\tag{4}
\]

Within a block whose test vector has common difference d, summing (4) gives dΣρ(δ−c)=0, by the definition of c. Thus the displayed construction has range in the constraint space and orthogonal residual, proving it is the orthogonal projection.

## Proof of the physical bound

Suppose |f(n)|≤M for all n, with M≥0. Then |δ_j|≤2M, and c_r is a positive weighted average, so |c_r|≤2M. Likewise |m_j|≤M.

For every real j≥3,

\[
0\le\frac{j^2}{D_j}\le\frac9{13},\qquad
0\le\frac{(j-1)^2}{D_j}\le\frac9{13}.
\]

The first upper bound is equivalent to

\[
0\le5j^2-18j+9=(j-3)(5j-3).
\]

The second follows from (j−1)²≤j². Applying these bounds to (3) gives

\[
|(Rf)(j)|,\ |(Rf)(j-1)|\le M+\frac9{13}(2M)=\frac{31}{13}M.
\]

Site 1 is unchanged. This proves (1). In arbitrary positive pair weights the two weight ratios are at most 1, giving the universal constant 3 instead.

## Complete screening-energy formula

For every f∈H,

\[
\boxed{
\|P_Uf\|_H^2
=\sum_{\substack{r\ge3\\r\text{ odd squarefree}}}
\left[
\sum_{j\in J_r}\frac{\delta_j^2}{a_j}
-\frac{\left(\sum_{j\in J_r}\delta_j/a_j\right)^2}
{\sum_{j\in J_r}1/a_j}
\right].}
\tag{5}
\]

Every bracket is nonnegative by weighted Cauchy–Schwarz. The whole sum converges and is at most ‖f‖², by orthogonality and Bessel. Formula (5) accounts for the full Gram projection within each radical block. It is not a sum of independent rowwise gains within a block.

## Entirely finite version and the limiting argument

For an integer L≥3 use J_{r,L}=J_r∩{3,…,L}. Nonempty blocks contain their squarefree anchor r. Define U_L as the finite span of d_j−d_rad(j) for odd nonsquarefree j≤L, and R_L=I−P_{U_L}.

In (3), replace c_r by

\[
c_{r,L}=\frac{\sum_{j\in J_{r,L}}\rho_j\delta_j}
{\sum_{j\in J_{r,L}}\rho_j}.
\]

Use that formula only on selected pairs j∈J_{r,L}; leave all other sites unchanged. A singleton block is unchanged because c_{r,L}=δ_r. The finite weighted identity (4) proves that this is exactly R_L. The same argument gives the **uniform-in-L** bound

\[
\|R_L f\|_\infty\le(31/13)\|f\|_\infty.
\]

The finite projector enforces precisely the selected constraints. It does **not** in general enforce an unselected constraint in the same radical block. If f already satisfies every odd radical constraint, all finite R_L fix f.

The U_L increase, and the closure of their union is U by construction. The standard increasing-subspace projection theorem gives P_{U_L}f→P_Uf strongly, hence R_Lf→Rf strongly. Physical evaluation is continuous at every fixed site, so the uniform physical bound passes to R. Every fixed constraint is eventually selected, so the limiting Rf satisfies all constraints. Alternatively, (3) follows by the absolutely convergent block sums above.

For a generic finite weighted-pair Lean formalization, use positive weights w_{i,+},w_{i,−}, harmonic weights ρ_i=w_{i,+}w_{i,−}/(w_{i,+}+w_{i,−}), weighted difference c=(Σρ_i(x_i−y_i))/(Σρ_i), and (4). The finite candidate can establish range, weighted-mean preservation, orthogonal residual, and the physical bound without any arithmetic or infinite sums. The actual Q specialization uses ratios j²/D_j and (j−1)²/D_j; Z cancels from c.

## Application to the actual squarefree stages — and the remaining gap

For squarefree d, Δg_d(j)=1/d−1_{d|j}; since d|j iff d|rad(j), every legal atom lies in W_odd. The constant target also lies there. Thus V_N⊂W_odd, r_N=1−P_N1∈W_odd, and

\[
RP_N=P_NR=P_N,\qquad
U\subseteq V_N^\perp\cap1^\perp.
\]

For k_{N,n}=P_Ne_n the completely odd-radical-screened kernel is

\[
s_{N,n}=(R-P_N)Bk_{N,n}.
\]

Its exact energy is

\[
\|s_{N,n}\|^2
=\|Bk_{N,n}\|^2-\|P_NBk_{N,n}\|^2-\|P_UBk_{N,n}\|^2,
\]

and residual orthogonality gives

\[
|b_N(n)|^2\le\varepsilon_N\|s_{N,n}\|^2.
\]

The new physical bound gives a uniformly bounded intermediate vector

\[
f_N=RBr_N,\qquad
\|f_N\|_\infty\le(31/13)\sqrt Z,
\qquad b_N=P_N f_N.
\]

**The unresolved step is the further actual projection P_N.** A physical bound on f_N does not bound P_Nf_N without an additional theorem about these particular stages and inputs. The present proof does not establish uniform physical boundedness of P_N, does not prove the required error-weighted surviving-energy bound, and does not prove RH.

Odd and even radical constraints overlap on physical sites. The independent odd-block argument cannot simply be repeated and added to even-block gains. Alternating bounded projections without a uniform iteration bound likewise does not yield a bound for their intersection.


## Actual stages examined with complete moment formulas

The numerical diagnostics use the actual squarefree conductors 2<=d<=N+1. Inactive masked coordinates are omitted for the numerical solve; the resulting subspace is unchanged. Every inner product has a complete infinite-tail formula; special functions and linear solves are evaluated in floating point. These are not certified bounds.

Let L=lcm(d,e), r=1,...,L, x=r/L, y=(r+1)/L, and Z=zeta(2). The residue-product coefficient is g_d(r)g_e(r). The period weights for G=<g_d,g_e>, H=<Bg_d,g_e>, and J=<Bg_d,Bg_e> are respectively

```text
G: psi_1(x)/(Z L^2)
H: [psi_1(x)/L^2 + (psi(x)-psi(y))/L]/Z
J: [(psi_1(x)+psi_1(y))/L^2 + 2*(psi(x)-psi(y))/L]/Z.
```

They follow by summing the rational weights 1/n^2, 1/[n^2(n+1)], and 1/[n^2(n+1)^2] over each residue class. The same single-conductor formulas give h=<1,g_d> and s=<B1,g_d>. For the head evaluation vector v_n:

```text
c = G^{-1}h
epsilon = 1-h^T c
kernel coefficients x_n = G^{-1}v_n
unscreened energy = x_n^T (J-H G^{-1}H) x_n
b_N(n) = v_n^T G^{-1}(s-Hc).
```

Both original Schur terms are retained. Prime-square gains were summed over odd primes through 997. The inherited theorem bounds the exact omitted gain by 4*Z*n^2/997^4. Floating-point evaluation errors remain separate and uncertified.

| N | epsilon_N | Maximum prime-square screened energy on 1<=n<=N | epsilon_N times maximum | Maximum absolute b_N |
|---:|---:|---:|---:|---:|
| 16 | 0.01167427 | 0.08322498 | 0.00097159 | 0.00990097 |
| 32 | 0.00912754 | 0.11189044 | 0.00102128 | 0.01549382 |
| 64 | 0.00755325 | 0.17536467 | 0.00132457 | 0.01897713 |
| 128 | 0.00633207 | 0.47362850 | 0.00299905 | 0.03836078 |

The exact signed normal decomposition was also evaluated:

| N and site n | Leading A_N K_N(n,1) | Forcing remainder | Total b_N(n) |
|---|---:|---:|---:|
| 32, 31 | 0.00767697 | 0.00781685 | 0.01549382 |
| 64, 58 | -0.00564172 | -0.01333541 | -0.01897713 |
| 128, 95 | -0.00489274 | -0.03346804 | -0.03836078 |

The observed terms reinforce rather than cancel. This is a diagnostic against assuming favorable signs, not a rigorous sign certificate.

All nonsquarefree radical rows through cutoff R were tested with their **full Gram matrix**, including odd and even rows and their overlaps. Corrected values at N=128:

| R | Maximum surviving energy | epsilon_N times maximum | Maximizing site |
|---:|---:|---:|---:|
| 512 | 0.3449204276193247 | 0.0021840596987345285 | 95 |
| 1024 | 0.3441496476881494 | 0.002179179067581736 | 95 |

Exact integer assertions checked that every generated row annihilates the constant and every active legal residue vector. Radical factorization must include the residual prime factor; a fixed prime list bounded by 997 is insufficient when R=1024. The values above use corrected factorization. The floating Gram solve is still not a proof.

These finite tables establish neither boundedness nor divergence. They suggest that adding local rows alone does not explain away the principal surviving component.

## Why abstract projection structure and the dichotomy are insufficient

The following is an ordinary countermodel to an abstract shortcut, not to the actual squarefree estimate.

In the same H_Q choose q(n)=n^alpha with 0<alpha<1/2, V=q-perp, and

```text
V_N = {f supported on 1,...,N+1 : <f,q>_Q=0}.
```

The spaces are nested, finite dimensional, and generated by bounded finite-support vectors. Their union is dense in V: truncate f in V, then correct its vanishing limiting q-pairing by a multiple of the first coordinate.

Writing sums below over n<=N+1, let

```text
a_N = sum Q(n)q(n) / sum Q(n)q(n)^2,
d_N = sum Q(n)q(n)^2/(n+1) / sum Q(n)q(n)^2.
```

Direct projection gives r_N(n)=a_N q(n) on the head and r_N(n)=1 outside. Its smoothed moving correction is

```text
b_N(n)=a_N(1/(n+1)-d_N)q(n) on the head, and zero outside.
```

Both a_N and d_N converge to strictly positive constants. Thus |b_N(N)| is asymptotic to a positive constant times N^alpha and is unbounded.

Nevertheless V-perp is spanned by q, every nonzero annihilator has nonzero mean, and

```text
H * ||tail_H q||_Q^2 ~ H^(2*alpha) / [Z*(1-2*alpha)] -> infinity.
```

So nested projections, bounded finite generators, the same smoothing multiplier, projection of the constant target, and this annihilator tail dichotomy can coexist with failure of B. The arithmetic structure of the actual legal span remains essential.

## Remaining research agenda

1. **Primary signed target remains Open:** find C>=0 with |P_N B r_N(n)|<=C for every 1<=n<=N. The new ordinary factorization b_N=P_N(RBr_N) supplies a uniformly bounded intermediate family satisfying all odd radical constraints. It does not supply stability of P_N on that family.
2. **Surviving-energy target remains Open:** bound epsilon_N times the complete prime-square screened energy, or select a finite omitted-coordinate family meeting KF. Keep the full Schur subtraction and overlap Gram terms.
3. Investigate the actual forcing remainder in the signed normal equation, using its dependence on r_N. Do not replace it by a bare coefficient-response norm or assume cancellation with the leading term.
4. If the odd-radical projection formula is useful to that estimate, formalize the arithmetic finite-family embedding, strong limit, and full QHilbert operator R. The finite algebra and physical constant are now available; this assembly has not been completed.
5. Do not infer a bound for the projection onto all radical constraints by alternating odd and even projections without a uniform bound on the iterates.
6. Assemble an assumption-free theorem of exact type RiemannHypothesis only after a genuine provider passes Lean. The existing moving-head consumer is already sufficient.

A relevant external comparison was [Manzur and Noor, A Hardy-space operator acting on zeta-zeros, arXiv:2610.03568v1](https://arxiv.org/html/2610.03568v1). Section 5 formulates RH through invariance of the full-conductor Hardy legal closure. That paper does not establish the required invariance, and no transfer here supplies the missing squarefree regularity estimate.

Wolfram independently simplified the elementary weighted-pair energy identity to True. That calculation is diagnostic; the finite identities above were checked separately by Lean.

## Retained workspace

```text
workspace_token: ws_WVVQ_Rp9qSUC9afF2Orx6DfamIRxdQDj
project_root: /home/cri_2025/lean-agent-workspaces/ws_WVVQ_Rp9qSUC9afF2Orx6DfamIRxdQDj/RiemannResearch
```

Resume this workspace or any continuation returned by the final checkpoint. Preserve newer published work. Keep Lean submissions serialized across agents.
