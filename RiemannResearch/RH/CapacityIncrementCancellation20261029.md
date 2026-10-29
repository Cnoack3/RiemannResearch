# Capacity increments and prime-supported cancellation

**Date:** 29 October 2026
**Starting commit:** 47299c1afe5e27db9bb3b43dd59cc56fdd8a29a4.
**Source:** continuation of the user-provided moving-prediction cancellation agenda.
The arguments below were developed from the actual complete-Q normal equations;
no mathematical novelty claim is made.

**Status:** RH is not proved. This continuation strengthens the gain inequality,
retains an additional nonnegative cancellation term, identifies the prime support
of dictionary changes, and gives exact paper-level counterexamples to proposed
pointwise sign shortcuts. The growth provider remains **Open**.

## 1. Actual family and new capacities

Retain exactly the agenda's family:
\[
U_i=\operatorname{span}\{g_d:1<d\mid\mathfrak P(2i+2)\},\quad
F_i=\operatorname{minimumAt}(2i,i+1),\quad
Z_i=\operatorname{minimumAt}(2i+2,i+1).
\]
Set \(n=i+2\), \(a_i=1-F_i(n)\), \(b_i=1-Z_i(n)\),
\(D_i=F_i-Z_i\), \(G_i=\|D_i\|_Q^2\), and \(E_i=\|F_i\|_Q^2\).

Let \(T_i^-=U_i\cap\{f:f(1)=\cdots=f(i+1)=0\}\) be the old tangent,
and let \(k_i\) be the existing next-site stepNormal in the enlarged tangent
\(T_i^+\). Its squared norm is \(\kappa_i\). Define
\[
k_i^-=P_{T_i^-}k_i,\qquad
\ell_i=k_i-k_i^-,\qquad
K_i=\|k_i^-\|_Q^2,\qquad h_i=\|\ell_i\|_Q^2.
\]
These use the actual finite-dimensional complete-Q projection, not assumed
inverses or an external capacity estimate. The exact decomposition is
\[
\kappa_i=K_i+h_i,\qquad 0\le h_i\le\kappa_i.
\]
For \(u\in T_i^-\), the projection property and the enlarged Riesz equation
give \(\langle u,k_i^-\rangle_Q=u(n)\). Thus \(K_i\) is precisely the
capacity of the old tangent for the same next-site observation. The definition
remains valid when this capacity is zero, without choosing an old anchor.

## 2. Stronger gain completion

Both minima are orthogonal to the old tangent, so \(D_i\perp T_i^-\).
Consequently
\[
\langle D_i,\ell_i\rangle_Q=\langle D_i,k_i\rangle_Q=b_i-a_i.
\]
Cauchy--Schwarz yields the stronger unconditional estimate
\[
\boxed{(b_i-a_i)^2\le h_iG_i,\qquad h_i\le\kappa_i.}
\]
The previous result used \(\kappa_iG_i\).

Define
\[
R_i^{\mathrm{new}}
=D_i-\frac{b_i-a_i}{h_i}\ell_i.
\]
The complete equality is
\[
\boxed{G_i=\frac{(b_i-a_i)^2}{h_i}+\|R_i^{\mathrm{new}}\|_Q^2.}
\]
At \(h_i=0\), the checked inequality forces \(b_i=a_i\).
The displayed identity then means \(G_i=\|D_i\|_Q^2\);
Lean's totalized real division returns zero. No positivity is silently assumed.

At squarefree \(n\), \(\kappa_i>0\), and therefore
\[
E_{i+1}-E_i
=\frac{b_i^2}{\kappa_i}-\frac{(b_i-a_i)^2}{h_i}
 -\|R_i^{\mathrm{new}}\|_Q^2
=\boxed{\frac{a_i(2b_i-a_i)-(K_i/h_i)(b_i-a_i)^2}{\kappa_i}
 -\|R_i^{\mathrm{new}}\|_Q^2.}
\]
This equality also covers \(h_i=0\) with the convention just explained.
At nonsquarefree sites the existing exact transition is \(-G_i\);
we never assert positive next-site capacity there.

When \(K_i,h_i>0\), another paper-level rearrangement is
\[
E_{i+1}-E_i
=\frac{a_i^2}{K_i}
 -\frac{(K_i b_i-\kappa_i a_i)^2}{K_i h_i\kappa_i}
 -\|R_i^{\mathrm{new}}\|_Q^2.
\]
Wolfram checked the two scalar rearrangements symbolically, returning zero
differences. The main displayed refinement is also included in the Lean development.

## 3. Smaller literal budget

Let
\[
\widetilde p_i=
\left[a_i(2b_i-a_i)-\frac{K_i}{h_i}(b_i-a_i)^2\right]_+.
\]
Then \(0\le\widetilde p_i\le p_i\).
With exactly the previous nearest-squarefree gap weight \(w_i\), set
\[
\widetilde S_N=\sum_{i<N}
\min\left\{\frac{4b_i^2}{\zeta(2)(i+1)},\ \widetilde p_iw_i\right\}.
\]
The unconditional estimates are
\[
0\le\widetilde S_N\le S_N\le T_N,\qquad
E_N\le E_0+\widetilde S_N,
\]
\[
\|1-F_N\|_Q^2\le2+2E_0+2\widetilde S_N.
\]
The refined budget can retain cancellation discarded by the previous budget.
No strict all-stage inequality between budgets is asserted.

The new conditional consumer is
\[
\lim_{N\to\infty}\frac{\log(1+\widetilde S_N)}{\log(N+2)}=0
\quad\Longrightarrow\quad\mathrm{RH}.
\]
It applies the existing exact-head subpolynomial consumer directly. It does
not incorrectly infer a bound for the larger budget from a bound for the smaller one.

## 4. Exact arithmetic support of dictionary gains

The old and new cutoffs are \(2n-2\) and \(2n\). The even endpoint
\(2n\ge4\) is composite. Hence, if \(2n-1=2i+3\) is not prime,
the primorials and dictionaries coincide. Seed independence identifies the
actual minimizers, giving
\[
D_i=0,\quad G_i=0,\quad b_i=a_i,\quad h_i=0.
\]
If \(n\) is also nonsquarefree, \(E_{i+1}=E_i\).

These are exact arithmetic statements, with no prime distribution hypothesis.
They show that enlargement cancellation is supported only at the prime steps.
They do not bound the positive head costs between those steps.

**Further paper-level localization.** At a prime step \(p=2n-1\), every new
conductor is \(pd\), \(d\mid L_{\rm old}\). For \(n\ge3\), the old primorial
exceeds \(p\). To see this, put \(m=2n-2\ge4\), \(L=\mathfrak P(m)\ge6\).
If \(L-1\le m\), a prime divisor of \(L-1\) would divide both \(L\) and \(L-1\).
Thus \(L-1>m\). Using old anchor \(L\), every new raw compensated direction
vanishes through \(2n-2\). Subtracting its projection onto the old tangent can
reintroduce next-site values. Raw support alone therefore does not supply an
angle bound, conditioning bound, or Bessel estimate for the moving family.

## 5. Exact first-stage obstructions (paper-level)

This section is an ordinary complete-Q derivation, not an additional Lean
identification theorem for the period-six minimizer.

For residues modulo six put
\[
A=\sum_{j\ge0}Q(6j+2),\quad C=\sum_{j\ge0}Q(6j+3),\quad
D=\sum_{j\ge0}Q(6j+4),\quad E=\sum_{j\ge0}Q(6j+5),\quad S=C+D+E.
\]
All these masses are strictly positive. The stage-zero minimizer is
\(F_0=2g_2=\mathbf1_{\rm odd}\). In the enlarged old-head tangent choose
\(v_2=g_2-\tfrac32g_3\), \(v_6=g_6-\tfrac12g_3\). Their values on
residues \(2,3,4,5\) are respectively
\[
(-1,\tfrac12,-\tfrac12,-\tfrac12),\qquad
(0,\tfrac12,\tfrac12,\tfrac12).
\]
All other residue contributions to these Gram entries are zero. Thus
\[
\Gamma=\begin{pmatrix} A+S/4&(C-D-E)/4\\
(C-D-E)/4&S/4\end{pmatrix},\qquad
z=\binom{(C-E)/2}{(C+E)/2}.
\]
The literal Schur quantities and distinguished coefficient are
\[
s=A+\frac{C(D+E)}S,\quad t=\frac{CD}S,\quad
\gamma_2=\frac{CD}{AS+C(D+E)}.
\]
Termwise comparison gives \(A>C>0\), and
\[
AS+C(D+E)-2CD=AC+AE+CE+D(A-C)>0.
\]
Therefore
\[
0<\gamma_2<\tfrac12,\quad a_0=1,\quad b_0=1-\gamma_2>\tfrac12,
\quad p_0=1-2\gamma_2>0.
\]
The proposed alignment \(a_i\gamma_n\ge a_i^2/2\) cannot hold at every stage.

There is also an actual positivity obstruction. Every period-six dictionary
vector with first two values equal to one has period values
\[
(1,1,x,x,1+x,0).
\]
The part of its complete energy depending on \(x\) is
\((C+D)x^2+E(1+x)^2\). Its unique minimizer is \(x=-E/S\), so
\[
F_1(3)=F_1(4)=-E/S<0,\qquad a_1=1+E/S>1.
\]
Thus neither \(F_i\ge0\) nor \(|a_i|\le1\) is universally valid.

In fact the first net energy increment is strictly positive:
\[
E_1-E_0=A-C-E^2/S>\frac1{100\zeta(2)}>0.
\]
For a purely symbolic bound, use unnormalized masses
\[
A^*\ge\tfrac14,\quad C^*=\zeta(2)/12\le\tfrac16,\quad
E^*\le\tfrac1{25}+\int_0^\infty(6x+5)^{-2}\,dx=\tfrac{11}{150}.
\]
The integral comparison is valid for a positive decreasing function;
\(\zeta(2)\le2\) follows from the usual integral bound.
Thus \(A-C-E\ge1/(100\zeta(2))\), while \(E^2/S<E\).

These finite-prefix counterexamples do not rule out eventual alignment,
averaged cancellation, subpolynomial growth, or RH.

## 6. What the attempted block argument still lacks

Embedding every dictionary of a finite block into the last dictionary
is legitimate. It does not make the corresponding old-head tangents
nested: dictionary enlargement adds directions while increasing the head
removes directions. The innovation normals for different prediction sites
therefore are not automatically orthogonal.

The new inequalities hold separately at every stage. Summing them still
requires a quantitative theorem controlling the actual moving family.
Prime support and delayed raw directions do not provide that theorem.
No unconditional dyadic estimate was obtained in this session.

The most precise remaining positive-budget target is
\[
\boxed{\forall\varepsilon>0\ \exists C_\varepsilon>0\ \forall M\ge1:
\sum_{M\le i+2<2M}
\min\left\{\frac{4b_i^2}{\zeta(2)(i+1)},\widetilde p_iw_i\right\}
\le C_\varepsilon M^\varepsilon.}
\]
Dyadic summation would give the growth hypothesis of the new RH consumer.
Alternatively, bound the complete signed transition sum while retaining
\(\|R_i^{\mathrm{new}}\|^2\) and nonsquarefree gains.

Next work should estimate the screened new-prime Gram block against the
old next-site Riesz vector. Any proposed angle or frame constant must be
proved for those actual blocks. A finite sign failure cannot replace a
cofinal estimate, and a positive-definite matrix alone supplies no
uniform inverse bound.

## 7. Formal modules and status

- Analysis/OrthogonalObservationInnovation.lean: zero-safe scalar observation
  completion, exact projection-residual energy, sharper Cauchy--Schwarz,
  and scalar refined-transition algebra.
- RH/QSquarefreeHeadStep.lean: stepNormal_pairing identifies the actual
  normal with physical next-site evaluation on the entire tangent.
- RH/QCRTInnovationGain.lean: actual old-tangent orthogonality,
  capacity decomposition, innovation_gain_completion,
  prediction_shift_sq_le_innovation_gain, and dense_refined_signed_transition.
- RH/QCRTDensePrimeSupport.lean: nonprime equality of dictionaries and actual
  minima; zero gain, prediction shift, and innovation capacity; exact energy
  plateau when the head site is also nonsquarefree.
- RH/QCRTInnovationBudget.lean: refined positive part, literal smaller budget,
  complete energy/error estimates, and the conditional RH consumer.

The actual-family gain inequalities are unconditional. The signed transition
assumes only squarefreeness of the next site, where capacity positivity is
proved. The RH theorem additionally assumes the displayed asymptotic limit,
which remains **Open**. The period-six counterexample and further
new-prime localization in Sections 4--5 remain paper-level.

## 8. Verification record and limits

- Combined development candidate: job_Wzv9eIxUHe1VsGjf35C6l_U99wgFQs3L,
  succeeded without proof placeholders.
- Saved-source import and ten-declaration axiom audit:
  job_Z7Y8xGYjwouCm71Wml9dK3WiPDRyv93E, succeeded.
  The audited declarations depend only on propext, Classical.choice, and Quot.sound.
  The audit also prints the RH consumer's exact type, including its unresolved
  subpolynomial-growth hypothesis.
- The server reported 47.530 seconds for that saved-source verification job,
  including its required dependency/module work; this is not kernel-only time.
  Workspace-opening duration and queue/polling overhead were not separately measured.
- Publication is gated by the subsequent server checkpoint, which validates
  the aggregate project and changed child modules before pushing.
  Its terminal job and published commit are reported in the session's final response.

Wolfram independently simplified both signed scalar rearrangements to zero,
verified the period-six distinguished coefficient and its strict interval
(0,1/2) under A>C>0, D>0, E>0, and returned the exact squared remainder
S(x+E/S)^2 for the period-six minimization. These symbolic checks supplement
the written derivations; they are not Lean identifications of the actual masses.

The agenda's general arbitrary-size Schur block interface was not separately
formalized here. The work instead formalizes the stronger capacity-increment
completion and its actual-family budget application. Neither development
discharges the open arithmetic growth provider.
