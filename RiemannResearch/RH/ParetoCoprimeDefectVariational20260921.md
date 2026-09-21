
## Continuation: exact odd-moment variational problem

Date: 21 September 2026. Starting published commit:
`3e0729293c426a788a20a95000195f33b172b277`.

This continuation turns the screened odd source into an exact finite
interpolation and variational problem. It does not establish the open
small-energy witness condition or prove RH.

### The finite inverse-Gram energy

Use all tail atoms `t_0,...,t_(n-1)`, corresponding to moduli
`2,...,n+1`. Let `G_n` be their actual full tail Gram matrix,
`b_i=1/(i+2)`, and `z=z_2` the fixed infinite coprime certificate.
Write
\[
H_i=\operatorname{coprimeObservationDefect}(2,i+2),\qquad
Q_n=H_n^T G_n^{-1}H_n.
\]
The new `coprimeDefectMinimum n` is the actual minimum Hilbert vector
with observations H on this finite dictionary. Its squared norm is Q_n.
For every feasible Hilbert vector x, Lean proves the exact completion
\[
\|x\|^2=Q_n+\|x-y_n\|^2.
\]
Nested minima also satisfy
\[
\|y_n-y_m\|^2=Q_n-Q_m\quad(m\le n).
\]
In particular Q_n is nonnegative and nondecreasing.

The already proved all-modulus observation identity gives
\[
H_i=b_i-\langle t_i,z\rangle.
\]
If u_n is the original reciprocal-source minimum, C_n its squared norm,
and P_n the projection onto the full finite tail dictionary, then
\[
\boxed{y_n=u_n-P_nz,\qquad
Q_n=C_n-2\langle u_n,z\rangle+\|P_nz\|^2.}
\]
Every mixed term remains explicit. The general source-translation module
also proves the useful finite comparisons
\[
Q_n\le 2C_n+2\|z\|^2,\qquad
C_n\le 2Q_n+2\|z\|^2.
\]
These are genuine bounds, not asymptotic replacements for the exact identity.

### Exact relationship to the remaining screened-energy problem

Lean proves, without an RH or density hypothesis,
\[
\boxed{
\begin{aligned}
\sup_n Q_n<\infty
&\iff \sup_n C_n<\infty\\
&\iff \exists x\in\mathcal H\quad
        \langle t_k,x\rangle=H_k\ \text{for every }k\\
&\iff \sum_n\mathcal E_n<\infty.
\end{aligned}}
\]
Here \(\mathcal E_n\) is the existing full signed factorial cross-Gram
row energy. The equivalence with its summability uses the established
Schur-capacity telescope and finite-base invariance.

Thus the summable raw scalar source H need not have a finite-energy
Hilbert interpolant. Excluding such an interpolant is precisely an open
form of the arithmetic obstruction; the new theorem does not exclude it.

The checked direction \(\neg\mathrm{RH}\Rightarrow\sup_nQ_n<\infty\)
uses no RH-to-density provider. Consequently unbounded Q_n implies RH.
The reverse implication from RH remains dependent on the previously
explicit classical density input unless a separate provider is proved.

### A concrete normalized odd-moment target and its exact optimizer

Put
\[
\kappa=1+\frac{\|z_2\|^2}{2}
       =\frac{\pi^2}{\pi^2-8},
\qquad
J_n(c)=\sum_{\substack{0\le i<n\\i+2\text{ odd}}}
              \frac{c_i}{(i+2)^2}.
\]
Lean proves the exact pairing \(c^TH_n=\kappa J_n(c)\).
For n>=2, Q_n is strictly positive and the actual coefficients
\[
\boxed{c_n^*=\frac{\kappa}{Q_n}G_n^{-1}H_n}
\]
satisfy \(J_n(c_n^*)=1\). Their complete tail energy is
\[
\boxed{\left\|\sum_i(c_n^*)_it_i\right\|^2
       =\frac{\kappa^2}{Q_n}.}
\]
For every signed coefficient vector c with J_n(c)=1, the stronger
completion holds:
\[
\boxed{
\left\|\sum_i c_it_i\right\|^2
=\frac{\kappa^2}{Q_n}
 +\left\|\sum_i(c_i-(c_n^*)_i)t_i\right\|^2.}
\]
This is an attained exact minimum, not a diagonal estimate.

Unbounded Q_n is equivalent to the following concrete witness condition:
for every epsilon>0 there is a finite legal combination with odd moment
one and full tail squared norm less than epsilon. The checked theorem
`riemannHypothesis_of_oddMoment_small_tail` proves that this condition
implies RH. Its arithmetic premise is **Open**.

Even-modulus coefficients do not occur in J_n, but their vectors remain
available in the combination and affect its norm and the optimizer.
Odd composite moduli also remain. Omitting either class changes the
variational problem and is not justified by these results.

### Research conclusion

The new result supplies an explicit moment normalization, a genuine
finite optimizer, an exact minimum, and a precise equivalence with the
previous screened-energy obstruction. It has not produced a family whose
minimum tends to zero. Proving Q_n unbounded, or constructing the stated
small-energy witnesses independently of the unknown inverse-Gram growth,
remains the substantive RH step.

### Lean modules and verification

New modules:

- `Analysis/FiniteGramSourceTranslation.lean`: exact translation of the
  minimum and capacity by the observations of a fixed Hilbert vector,
  with finite two-sided comparisons.
- `RH/ParetoCoprimeDefectVariational.lean`: defect interpolation,
  nested minimum energies, boundedness alternatives, exact odd-moment
  optimizer and completion, and the conditional RH endpoint.

Verification and publication receipt follows after the single final checkpoint.

The combined source candidate passed with exit code 0 and no warnings in
about 40 seconds. Its five key axiom audits report only
`[propext, Classical.choice, Quot.sound]`. The addition contains 29 proved
theorems and four definitions. It introduces no admitted proof,
project-local axiom, unsafe declaration, or new density/zero provider.

Verified candidate: `job_IQMYGshYeGgfaqvBF5DnydPrlyicoQ1E`.
Final installed-module acceptance is the publishing checkpoint.
