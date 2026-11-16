# M06 closed: uniform Hurwitz growth and explicit modulus bounds

Prepared 16 November 2026, America/Los_Angeles.

## Status and scope

**M06 — an actual Hurwitz strip-growth provider without a supplied growth
premise — is proved.** The original provider was published in
[3d680d8f17efd6161958ac0c688baf282d1d6fc1](https://github.com/Cnoack3/RiemannResearch/commit/3d680d8f17efd6161958ac0c688baf282d1d6fc1).
The selected “Open” label is stale relative to that repository source.

This continuation strengthens parameter uniformity and exposes the complete
modulus dependence. The proofs use Mathlib's actual
`HurwitzZeta.hurwitzZeta`, not an abstract function supplied with a growth axiom.

New modules:

- `Analysis/HurwitzUniformStripBounds.lean`.
- `Analysis/ConreyBaluyotEstermannUniformGrowth.lean`.

The inspected starting commit was
`d414397c292ff465a2c3351929b22d942ff848a2`.

## Exact identity underlying the estimates

For $0<q\le1$, $\Re s>-1$ and $\Im s\ne0$, the existing checked provider gives

$$
\zeta(s,q)=q^{-s}\left(\frac12+\frac{q}{s-1}\right)
-\frac{s(s+1)}2\int_q^\infty
  \{\!x-q\!\}\bigl(\{\!x-q\!\}-1\bigr)x^{-s-2}\,dx .
$$

Both endpoint contributions and the complete integral remainder are retained
in `HurwitzEulerMaclaurin.eulerMaclaurinValue`. The new estimates are
consequences of this identity. They do not replace it by a purported density
or cancellation theorem.

The corrected classical formula is
[NIST DLMF 25.11.6](https://dlmf.nist.gov/25.11.E6).
The actual identification, integrability and continuation are already proved
in `HurwitzEulerMaclaurin.lean`; the current results do not assume them as
unproved premises.

## 1. Uniform positive Hurwitz parameters

Define
$$
R(a,b)=\max(|a|,|b|),\qquad
C(a,b)=\frac32+\frac{(R(a,b)+1)(R(a,b)+2)}{8(a+1)},\qquad
p(b)=\max(b,0)+1.
$$

For $a>-1$, $r\in[a,b]$, $|t|\ge1$, and $0<\delta\le q\le1$:

$$
\boxed{|\zeta(r+it,q)|\le C(a,b)\,\delta^{-p(b)}|t|^2.}
$$

The sharper parameter-dependent version replaces $\delta$ by $q$.
The constant is positive and independent of the particular $q,r,t$.

Declarations, in `RiemannResearch.Analysis.HurwitzUniformStripBounds`:

- `stripConstant`, `stripConstant_pos`.
- `parameterExponent`, `parameterExponent_pos`.
- `norm_hurwitzZeta_parameter_bound`.
- `norm_hurwitzZeta_uniform_parameter_bound`.

## 2. Uniform complex shifts

Let $\Re\alpha\in[A,B]$ and $a+A>-1$. Put
$$
H=\frac94\,C(a+A,b+B),\qquad p=p(b+B).
$$

For every $r\in[a,b]$ and $|t|\ge2(1+|\Im\alpha|)$:

$$
\boxed{|\zeta(r+it+\alpha,q)|\le H\,\delta^{-p}|t|^2,
\qquad \delta\le q\le1.}
$$

The same $H$ works for all shifts in the given real interval.
There is **no dependence of $H$ on $\Im\alpha$**; the imaginary shift appears
in the height threshold. The estimate uses
$1\le|t+\Im\alpha|\le\frac32|t|$.

Declaration: `norm_hurwitzZeta_uniform_shift_bound`.

## 3. Explicit rational-modulus dependence

For every positive integer $K$ and every class $j\in\mathbb Z/K\mathbb Z$,
Lean constructs a representative $q\in[1/K,1]$. The zero class is represented
by $q=1$, not by an inadmissible positive-parameter formula at $q=0$.

Consequently,
$$
\boxed{
|\operatorname{Hz}(j/K,r+it+\alpha)|\le H K^p |t|^2.
}
$$

Here $\operatorname{Hz}$ denotes Mathlib's additive-circle version.
At the zero class it is the usual Riemann zeta function.

Declarations:

- `exists_positive_representative`.
- `norm_hurwitzZeta_rational_uniform_shift_bound`.

The modulus is universally quantified; it is not fixed before choosing $H$.
This is an explicit weighted uniform bound, not a bound independent of $K$.

## 4. Actual Estermann growth for all moduli

Assume $\Re\alpha,\Re\beta\in[A,B]$, $a+A>-1$, and put
$$
E=-2a-2A+2(p+1),\qquad
T_{\alpha,\beta}
=\max\{2(1+|\Im\alpha|),\,2(1+|\Im\beta|)\}.
$$

For every $K\ge1$, every numerator class $h\bmod K$ (including nonunits),
$r\in[a,b]$, and $|t|\ge T_{\alpha,\beta}$:

$$
\boxed{
|E_h(r+it+\alpha,r+it+\beta)|\le H^2 K^E |t|^4.
}
$$

This follows from the repository's complete finite Hurwitz/character identity
before taking norms. The two finite sums each have exactly $K$ terms.
The bound is deliberately elementary; no arithmetic cancellation or
optimality in the exponent of $K$ is asserted.

Declarations, in `RiemannResearch.Analysis.ConreyBaluyot`:

- `uniformModulusExponent`.
- `norm_estermann_uniform_modulus_bound`.

## 5. Uniform damped Mellin tail after the explicit modulus factor

For fixed $\lambda$ with $\Re\lambda>0$ and $a+A>-1$, Lean proves

$$
\exists D\ge0\ \forall K\ge1\ \forall h\bmod K\
\forall\alpha,\beta\text{ with }\Re\alpha,\Re\beta\in[A,B]:
$$
$$
\boxed{
|\Gamma(r+it)\lambda^{-r-it}
 E_h(r+it+\alpha,r+it+\beta)|
 \le D\,K^E(1+t^2)^{-1}
}
$$
whenever $r\in[a,b]$ and $|t|\ge T_{\alpha,\beta}$.

The constant $D$ is chosen before the modulus, numerator class and individual
shifts. It depends only on the fixed damping and interval endpoints.
Unlike the earlier tail provider, this theorem does not need $a>-1$:
an arbitrarily high Gamma recurrence order handles any fixed real strip.
The two shifted Hurwitz real parts must still stay above $-1$.

Declaration:
`exists_estermannMellinKernel_uniform_modulus_tail`.

This strengthens the tail estimate only. It does not extend a contour
identity across additional Gamma poles without their residue accounting.

## Remaining obligations

M06 should no longer be listed as open. The following are separate:

1. Domination for both actual Gaussian rays when damping approaches its
   boundary, including endpoints and all sum/integral interchanges.
   The fixed-positive-damping constant $D$ is not proved uniform in that limit.
2. Sharp estimates for the complete arithmetic sums with their modulus, gcd,
   coefficient and parameter dependence. The displayed power $K^E$ is explicit,
   but does not by itself provide the savings required for a mollified moment.
3. The cofinal uniform Gaussian/dyadic mollified-zeta moment and the required
   separate density inputs. No UniformSelbergDensity or RH conclusion is
   supplied by this strip-growth theorem.

## Verification and sources

The coherent Hurwitz and Estermann candidate passed Bazel/BuildBuddy:
`job_FWmEhwjgnc_H9a8ARfG1PGGUSyLlOxmm`, server build time 40.319 seconds.
[BuildBuddy record](https://app.buildbuddy.io/invocation/787c7887-0db4-4c52-b1b0-68b09f3d0a2e).

The persisted modules include four guarded axiom audits for the uniform
Hurwitz, rational Hurwitz, Estermann, and Mellin-tail theorems.
The allowed list is exactly `propext`, `Classical.choice`, and `Quot.sound`.
Their geometric and parameter hypotheses are visible in the theorem types;
there is no supplied growth premise.

Focused persisted-file acceptance, including both modules and all four guards,
passed in `job_tfr9x8A8Q6v13RQU6eUELfhDtXtFSCiQ`; server build time 38.209 seconds.
[BuildBuddy record](https://app.buildbuddy.io/invocation/242643fa-9553-4aef-a851-ac3d6427160d).
The final application-file SHA-256 is
`cf0069d3d50d93815d06b6f898db2ac512fef04660d03fc7bea387703d876782`.

The final managed checkpoint validates the full exported project before
publication. The terminal verification job and exact commit are reported
with the completed change.

The finite Estermann identity and contour setting follow Baluyot,
*On the Zeros of Riemann's Zeta-function* (2017), equation (3.1.7) and
Lemma 3.1.3, pp. 95–97:
[author's dissertation](https://urresearch.rochester.edu/fileDownloadForInstitutionalItem.action?itemFileId=183460&itemId=33320).
The new uniformity estimates are elementary formal consequences of the
existing exact identities, not a claim of a new result in the literature.
