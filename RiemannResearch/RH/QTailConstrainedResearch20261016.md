# Complete-tail Gram reduction and conductor-gap arithmetic

Date: 16 October 2026.

Source: the user-provided rank-one head-removal deduction and priority 2 of
[QLCMConstrainedMinimumResearch20261016.md](QLCMConstrainedMinimumResearch20261016.md),
building on commit
[1b7ceeebaf66be0f6dad0a23b7b403191b4b8caf](https://github.com/Cnoack3/RiemannResearch/commit/1b7ceeebaf66be0f6dad0a23b7b403191b4b8caf).
The source supports the head decomposition, periodicity proof strategy, and
requested capacity identities. The source update, exact error accounting,
and conductor-gap statements below are continuations of that argument.

## Actual tail geometry and inverses

Work in the real Hilbert space with
\[
 Q(n)=\frac1{\zeta(2)n^2},\qquad
 g_d(n)=\frac{n\bmod d}{d}\quad(n\ge1).
\]
Choose finitely many distinct conductors \(d_i>1\), all greater than \(H\).
Squarefreeness is needed for the squarefree RH application, not for the
tail Gram independence or the rank-one algebra. Put
\[
 w_i=d_i^{-1},\quad a=H/\zeta(2),\quad A_x=\sum_i x_i g_{d_i}.
\]
The restriction retains the original Q weights and every site beyond H:
\[
 \langle u,v\rangle_T=\frac1{\zeta(2)}
       \sum_{n>H}\frac{u(n)v(n)}{n^2},\qquad
 T_{ij}=\langle g_{d_i},g_{d_j}\rangle_T.
\]
Lean implements this as a shift of weighted l2 coordinates, not as an
unweighted shift of the physical sequence. Its coordinate n corresponds
to the original physical site \(n+H+1\).
The declaration tailGram_entry identifies the implemented matrix with the
complete physical sum above.

**Established: T is positive definite.** If the tail synthesis vanishes,
choose a positive common period L for the finitely many conductors.
For every n, \(n+(H+1)L>H\), and periodicity gives \(A_x(n)=0\).
Full-Q residue independence now gives \(x=0\). Thus the tail inverse is
constructed from actual independence; its existence is not a hypothesis.
No uniform conditioning estimate follows from finite positive definiteness.

Let f have the linear head \(f(n)=ns\), \(1\le n\le H\). The exact identities are
\[
 K=T+aww^{\mathsf T},\qquad
 \beta=\beta_T+asw,\qquad
 \|f\|_Q^2=\|f\|_T^2+as^2.
\]
More generally, for every coefficient vector, feasible or not,
\[
 \boxed{\|f-A_x\|_Q^2=\|f-A_x\|_T^2+a(s-w^{\mathsf T}x)^2.}
\]
In particular, the complete and tail errors agree exactly under
\(w^{\mathsf T}x=s\).

For a nonempty free family define
\[
 u=T^{-1}w,\quad C_T=w^{\mathsf T}u>0,\quad D=1+aC_T.
\]
The complete inverse, on every source y, satisfies
\[
 K^{-1}y=T^{-1}y-
       \frac{a\,w^{\mathsf T}T^{-1}y}{D}\,u.
\]
Consequently
\[
 \boxed{C_Q=\frac{C_T}{1+aC_T},\qquad
        \frac1{C_Q}=a+\frac1{C_T}.}
\]
These are now Lean theorems, including an actual matrix-inverse mulVec
identity, rather than informal deductions from an assumed inverse.

## Exact optimizer and full source accounting

Set
\[
 v=T^{-1}\beta_T,\quad B_T=w^{\mathsf T}v,\quad
 \delta_T=s-B_T.
\]
The tail-only constrained coefficients are exactly
\[
 \boxed{x^*=v+\frac{\delta_T}{C_T}u.}
\]
They satisfy the normalization constraint. They are coefficientwise equal
to the already implemented complete-Q constrained optimizer. Their complete
error is exactly
\[
 \boxed{\mathcal E=
      \|f\|_T^2-\beta_T^{\mathsf T}T^{-1}\beta_T+
                 \frac{(s-w^{\mathsf T}T^{-1}\beta_T)^2}{C_T}.}
\]
For every feasible x, the complete tail completion is
\[
 \|f-A_x\|_T^2=\mathcal E+\|A_{x-x^*}\|_T^2.
\]
It includes every signed Gram cross term inside the squared norm. The
optimizer is unique by tail independence, equivalently by the existing
complete-Q uniqueness theorem and coefficient equality.

Removing the head changes the unconstrained source solution:
\[
 K^{-1}\beta=v+\frac{a\delta_T}{D}u,\qquad
 m_Q=s-w^{\mathsf T}K^{-1}\beta=\frac{\delta_T}{D}.
\]
Writing
\[
 E_{0,T}=\|f-A_v\|_T^2,\qquad
 E_{0,Q}=\|f-A_{K^{-1}\beta}\|_Q^2,
\]
the exact error accounting is
\[
 E_{0,Q}=E_{0,T}+\frac{a\delta_T^2}{D},\qquad
 \frac{m_Q^2}{C_Q}=\frac{\delta_T^2}{C_TD},
\]
\[
 \boxed{E_{0,Q}+\frac{m_Q^2}{C_Q}
       =E_{0,T}+\frac{\delta_T^2}{C_T}.}
\]
In particular, a smaller complete-Q mismatch alone does not reduce the
complete minimum. Its suppression factor is accompanied by an exact
transfer into the unconstrained residual. The signed expansion is
\[
 \frac{\delta_T^2}{C_T}
    =\frac{s^2}{C_T}-\frac{2sB_T}{C_T}+\frac{B_T^2}{C_T}.
\]
Discarding the middle term would change the arithmetic problem.

For the actual application,
\[
 F_H^0=-\sum_{d\le H}\mu(d)g_d,\quad
 s=S_H=\sum_{d\le H}\frac{\mu(d)}d,\quad f=1-F_H^0.
\]
The d=1 atom and nonsquarefree coefficients vanish. The existing legality
and exact-head theorems apply to the tail optimizer through its proved
equality with the complete optimizer. The minimumError_tail_formula refers
to the original actual minimumError, not to a newly postulated energy.

## Stronger restrictions from the first free conductor

Suppose every free conductor exceeds \(J\ge H\). A normalized synthesis
with \(w^{\mathsf T}x=1\) equals n for every \(n\le J\). If
\(A\) is the synthesis of \(C_T^{-1}T^{-1}w\), the exact identity is
\[
 \boxed{\frac1{C_T}=\frac{J-H}{\zeta(2)}+\|A\|_{Q,n>J}^2.}
\]
Therefore, when \(J>H\),
\[
 \boxed{C_T\le\frac{\zeta(2)}{J-H}.}
\]
This is a capacity ceiling, not the lower bound needed to control a
normalization penalty.

**Established squarefree consequence:** if H+1 is nonsquarefree, every
squarefree free family above H actually lies above H+1. Thus
\[
 \boxed{\neg\operatorname{Squarefree}(H+1)\ \Longrightarrow\ C_T\le\zeta(2).}
\]
Hence divergence of C_T along every growing head is not a viable universal
goal for these squarefree families. For example, the elementary sequence
\(H=k^2-1,\ k\ge2\), satisfies the antecedent at every stage. This
last subsequence observation is an ordinary arithmetic consequence;
the Lean declaration is the displayed conditional inequality.

A further analytical deduction, not a separate Lean theorem in this change:
for any R, choose distinct primes \(p_1,\ldots,p_R\) and use CRT to choose
arbitrarily large H with \(H+r\equiv0\pmod{p_r^2}\), \(1\le r\le R\).
Then H+1,...,H+R are all nonsquarefree. Applying the proved gap ceiling
with J=H+R gives \(C_T\le\zeta(2)/R\), uniformly over every squarefree
free family at that head. Choosing the CRT representatives strictly
increasing gives a cofinal sequence of heads with capacities tending to
zero. Thus a uniform positive lower bound over all heads is also
incompatible with this geometry. This does not rule out a useful selected
subsequence or direct control of the coupled error.

There is also a coefficient-independent physical residual before the
first free wrap. Define the signed floor defect
\[
 R_H(n)=1-\sum_{d\le H}\mu(d)\left\lfloor\frac nd\right\rfloor.
\]
For every feasible x and every positive \(n\le J\),
\[
 \boxed{1-(F_H^0+A_x)(n)=R_H(n).}
\]
Consequently, with the full remainder retained,
\[
 \boxed{\|1-F_H^0-A_x\|_Q^2
       =\frac1{\zeta(2)}\sum_{n=1}^{J}\frac{R_H(n)^2}{n^2}
         +\|1-F_H^0-A_x\|_{Q,n>J}^2.}
\]
This applies to the actual optimizer and gives a rigorous necessary lower
bound for its complete minimum.

For \(H<n\le2H+1\), each omitted conductor \(H<d\le n\) has
\(\lfloor n/d\rfloor=1\). The finite Möbius floor identity yields
\[
 \boxed{R_H(n)=\sum_{H<d\le n}\mu(d)=M(n)-M(H),}
 \qquad M(n)=\sum_{d\le n}\mu(d).
\]
The exact first-window equality is formalized; no Mertens cancellation
estimate is assumed. Conductors chosen far above H leave an unavoidable
initial block of signed Mertens increments. Whether that block is useful
for an upper bound still requires a separate argument controlling the
complete remaining tail.

## Finite numerical probe: evidence, not a bound

Floating calculations used all squarefree conductors H<d<=M, the actual
signed Möbius seed, and complete-Q pairings. Repeated-period reciprocal
weights were evaluated in double precision by SciPy; physical tails were
not cut off. No interval certification or Lean numerical certificate is
claimed. The small finite values do not imply a cofinal estimate.

| H | M | Free atoms | C_T | delta_T | E_0,T | delta_T^2/C_T | Complete minimum |
|---:|---:|---:|---:|---:|---:|---:|---:|
| 2 | 4 | 1 | 3.40245244 | 0.03608093 | 0.07028181 | 0.00038262 | 0.07066443 |
| 4 | 8 | 3 | 1.74742942 | 0.03267045 | 0.01702407 | 0.00061082 | 0.01763488 |
| 4 | 16 | 8 | 8.17318623 | 0.12229065 | 0.01123016 | 0.00182976 | 0.01305992 |
| 8 | 16 | 5 | 0.54296236 | -0.00857218 | 0.01636890 | 0.00013534 | 0.01650423 |
| 8 | 32 | 14 | 1.11550893 | 0.00506920 | 0.01197495 | 0.00002304 | 0.01199798 |
| 16 | 32 | 9 | 0.55284611 | 0.03705304 | 0.01410379 | 0.00248338 | 0.01658717 |
| 16 | 64 | 28 | 3.33344624 | 0.07608516 | 0.00927050 | 0.00173663 | 0.01100713 |
| 32 | 64 | 19 | 0.31177891 | -0.02169538 | 0.01399497 | 0.00150969 | 0.01550466 |

Across these cases, tail condition numbers ranged from 1 to about 1200.
Full and tail coefficient formulas agreed within 1.4e-14 in maximum
coordinate error, and the two complete energies within 4e-17.
At H=4, enlarging M increases both the absolute mismatch and its penalty
while decreasing the complete minimum. This illustrates why the full
signed accounting must remain primary.

The reproducible exploratory script is appended below. It uses NumPy
2.3.5 and SciPy 1.17.0 in this session; its output is not a formal proof.

## Lean declarations, assumptions, and verification

- Analysis/FiniteGramRankOne.lean: general actual-inverse rank-one identities,
  simultaneous source update, mismatch and penalty identities, coefficient
  equality, and residual_rank_one_value.
- RH/QTailGram.lean: actual complete tail restriction, periodicity-based
  independence, tailGram_posDef, physical entries, head Gram/source splits,
  and exact residual energy.
- RH/QTailConstrainedMinimum.lean: full_inverse_mulVec_eq_tail,
  full_capacity_eq_tail, inverse_full_capacity_eq_tail,
  tailCoefficients_eq_full, tailOptimizer_eq_full,
  minimumError_tail_formula, and complete tail completion.
- RH/QTailConductorGap.lean: inverse_tail_capacity_gap,
  tailCapacity_le_gap, tailCapacity_le_zetaTwo_of_next_not_squarefree,
  seedResidual_minus_linear, floorDefect_first_window,
  and the actual optimizer's forced physical block.

The assembled main development passed Lean-server snippet
job_pTST6NvTyI1WbXhq9qqOH81HRC4p0FAm, exit code 0.
Axiom inspection of positive definiteness, the actual matrix inverse,
optimizer equality, minimum formula, arithmetic block, first-window
identity, and squarefree capacity ceiling reported only propext,
Classical.choice, and Quot.sound.

The four saved Lean modules passed server check
job_r4Pmyl4fHKgLQHGM8sHej9MBIuVgGG9C, exit code 0. This check imported the
actual saved modules, built the new modules using the retained dependency
artifacts, and inspected the listed key declarations' axioms, including
the actual Q unconstrained-error update and optimizer Mertens window.
Only the same standard foundations were reported. Final publication
additionally requires the checkpoint's source audit and dependency
validation; its terminal result and published commit are reported with
this record.

All independence, inverse, and finite-energy identities above are
unconditional under the displayed finite conductor conditions.
**Open:** a uniform bound for the actual complete minimum along a
suitable family of growing heads. No RH assumption, equivalent arithmetic
bound, or project-local axiom is introduced as a proved theorem.

## Research agenda

1. Estimate the coupled pair \(E_{0,T}\) and \(\delta_T^2/C_T\) on a specified
   family. A lower bound for C_T alone cannot control either source
   cancellation or the unconstrained error.
2. Use the exact floor block to evaluate conductor gaps. In particular,
   account for forced Mertens increments on the first dyadic window before
   attempting any estimate for the later complete physical tail.
3. Replace universal tail-capacity divergence by an argument compatible
   with the proved nonsquarefree-successor ceiling. If using a selected
   subsequence of heads, prove its cofinality and supply the full error
   bound there. Formalize the CRT construction of long nonsquarefree gaps
   to record the analytical subsequence obstruction above.
4. Derive arithmetic identities for the signed source pairing
   \(w^{\mathsf T}T^{-1}\beta_T\) and its dependence on stage enlargement.
   The H=4 computation cautions against assuming monotonicity of either
   the mismatch or normalization penalty.
5. Produce certified finite upper bounds for trial feasible coefficients
   with an explicit complete-tail remainder. Compare them with the exact
   optimum; retain conditioning data and every signed mixed term.

## Reproducible exploratory calculation

For a common period L, the program groups the infinite sum using
\[
 \sum_{k\ge0}\frac1{(r+kL)^2}
       =L^{-2}\psi_1(r/L).
\]
This is used only to evaluate finite test cases, not as a convergence
criterion or a proof of any asymptotic estimate.


```python
import math
from functools import lru_cache
import numpy as np
from scipy.special import polygamma

Z = math.pi**2 / 6
def mobius(n):
    sign = 1
    p = 2
    while p*p <= n:
        if n % p == 0:
            n //= p
            sign = -sign
            if n % p == 0:
                return 0
            while n % p == 0:
                n //= p
        p += 1
    if n > 1:
        sign = -sign
    return sign

@lru_cache(None)
def weights(L):
    a = np.arange(1, L, dtype=np.float64)
    return a, polygamma(1, a/L)/(Z*L*L)

@lru_cache(None)
def mean(d):
    a, wt = weights(d)
    return (a/d) @ wt

@lru_cache(None)
def gram(d,e):
    L = math.lcm(d,e)
    a, wt = weights(L)
    return ((a % d)/d * (a % e)/e) @ wt

print("H M count C_tail mismatch_tail E0_tail penalty_tail E_min cond_tail coeff_gap energy_gap")
for H, ratio in [(2,2),(4,2),(8,2),(16,2),(32,2),(4,4),(8,4),(16,4)]:
    M=ratio*H
    free=np.array([d for d in range(H+1,M+1) if mobius(d)])
    low=[d for d in range(2,H+1) if mobius(d)]
    mu=np.array([mobius(d) for d in low])
    s=sum(mobius(d)/d for d in range(1,H+1))
    G0=np.array([[gram(d,e) for e in low] for d in low]).reshape(len(low),len(low))
    m0=np.array([mean(d) for d in low])
    f2=1+2*m0@mu+mu@G0@mu
    K=np.array([[gram(int(d),int(e)) for e in free] for d in free])
    cross=np.array([[gram(int(d),e) for e in low] for d in free])
    beta=np.array([mean(int(d)) for d in free])+cross@mu
    w=1/free
    a=H/Z
    T=K-a*np.outer(w,w)
    bt=beta-a*s*w
    f2t=f2-a*s*s
    u=np.linalg.solve(T,w)
    x0=np.linalg.solve(T,bt)
    C=w@u
    delta=s-w@x0
    E0=f2t-bt@x0
    penalty=delta*delta/C
    xt=x0+delta/C*u
    uf=np.linalg.solve(K,w)
    xf0=np.linalg.solve(K,beta)
    Cf=w@uf
    xf=xf0+(s-w@xf0)/Cf*uf
    Ef=f2-2*beta@xf+xf@K@xf
    print(H,M,len(free),*[f"{v:.9g}" for v in (C,delta,E0,penalty,E0+penalty,np.linalg.cond(T),np.max(np.abs(xf-xt)),abs(Ef-E0-penalty))])
```
