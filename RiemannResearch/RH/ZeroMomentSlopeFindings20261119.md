# Horizontal moments and density slopes

Write $L=\log T$, $\ell=\log L$, $d_\rho=\vert \Re\rho-1/2\vert $, and $M_k(v)=\sum_{0<\Im\rho\le T}d_\rho^k e^{v d_\rho}$, counting analytic multiplicity. A density slope $a$ in the repository's convention gives the two-sided tail bound $2CT L e^{-aLt}$.

| Comparison | Bound or declaration | Scope |
|---|---|---|
| Even horizontal Taylor coefficient | $2CL(\vert u\vert /(aL))^{2j+2}$ | The factorial moment cancels the Taylor factorial. In the earlier rational-mode specialization $a=1/4$, the order-dependent factor drops from $8^k/3$ to $4^k$. |
| Full signed Taylor remainder | $2CL r^{2J+2}/(1-r^2)$ for $r=\vert u\vert /(aL)<1$ | The complete open frequency range uses one provider and all orders. |
| Positive tilted moment | $M_k(v)/T\le 2CL k!q/(q-v)^{k+1}$ for $q=aL$, $0\le v<q$, $k\ge1$ | Exact half-line constant for the supplied exponential majorant. |
| Finite off-line count cap | $M_k(v)\le K[B^k e^{-(q-v)B}+q\int_d^B t^k e^{-(q-v)t}\,dt]$ | $B=1/2$, $0\le v$, $F\ge\#\{d_\rho>0\}$, $K e^{-qd}=F$, and $0\le d\le B$. The expression integrates the pointwise minimum of the cap and the exponential envelope exactly. At $v=q$ the remaining integral is $(B^{k+1}-d^{k+1})/(k+1)$. |
| Critical-line proportion at sublinear tilts | $M_k(v)/T\le D\,\ell^k/L^{k-1}$ eventually for $0\le v\le BL/\ell$ and every $D>e^{3B/2}(3/2)^k z$ | $z$ is an upper limiting coefficient of the strict off-line count divided by $TL$. A cumulative distinct critical proportion $\kappa$ supplies $z=(1-\kappa)/(2\pi)$. |
| Exact Ingham crossing at linear tilt | $M_k(\lambda L)/T\le C(4/3)L^{(3/2)\lambda-(k-1)}P_k((2-(3/2)\lambda)\ell)/(4/3-\lambda)^{k+1}$ | For $0\le\lambda<4/3$, $P_k(x)=k!\sum_{j=0}^k x^j/j!$. The unconditional density proof allows the central and tail caps to cross precisely at $(3/2)\ell/L$. This removes the exponent slack from a cutoff coefficient strictly larger than $3/2$. |
| Critical Ingham tilt | $M_k((4/3)L+r\sqrt L)/T\ll_{k,r} L^{(7-k)/2}$ for fixed $r$ | The nonlinear Ingham curve contributes at least $(8/9)d^2$ beyond its $4d/3$ tangent. Orders $k\ge8$ tend to zero. |
| Fixed-slope zero support | $\vert \Re\rho-1/2\vert \le1/a$ | Remains true with an arbitrary fixed real logarithmic loss. Improvement over the ordinary strip requires $a>2$. Improvement over the exact continuum contact requires $a>1/(B_*-1/2)=2.678481583880647807110182550204092347620\ldots$. |
| Cofinal slopes | ${\rm RH}\iff\forall A\,\exists a>A\ {\rm UniformSelbergDensity}(a)$ | Constants and starting heights may depend on the slope. The weaker condition allowing an arbitrary finite logarithmic loss at each slope is also equivalent to RH. |
| Logarithmic loss floor | $b\ge1$ in a global inclusive $CT(\log T)^b e^{-aL(\sigma-1/2)}$ | Reflection and Riemann–von Mangoldt give the necessary loss at the central cutoff. At every slope with a Selberg provider, every $b\ge1$ is admissible. |

The exponential-moment and compensated formulas measure improvements over earlier estimates for the same finite zero multisets. They do not establish a literature priority claim for elementary Mellin or incomplete-gamma identities. The repository's open Conrey–Baluyot range $a<8/7$ gives stronger inverse-logarithmic moments than the internal Ingham route below that frequency. No excluded endpoint $a=8/7$ is used.

## Analytic references

- S. A. C. Baluyot, *On the Zeros of Riemann's Zeta-function*, Theorem 1.2.1, 2017. [University of Rochester](https://urresearch.rochester.edu/fileDownloadForInstitutionalItem.action?itemFileId=183460&itemId=33320)
- K. Ford and A. Zaharescu, *On the distribution of imaginary parts of zeros of the Riemann zeta function*, Lemma 2 and equation (3.8). [Article](https://arxiv.org/abs/math/0405459)
- T. Chourasiya and A. Simonič, *An explicit form of Ingham's zero density estimate*, Theorem 1. [Preprint](https://arxiv.org/abs/2507.15184)
