# Sharp pair-energy windows when the reflected groups absorb their cost

With $B_0(T,c)$ and $N(T)$ as in the fixed-gap note, the table bounds $\liminf B_0(T,c)/N(T)$ for every fixed $0<c\le C$. These windows use the actual pair-energy asymptotic and angular inequalities. The deductions require no horizontal stop-loss or n-point interaction input. The angular and numerical obligations are independently replayed with outward-rounded interval arithmetic. The aggregate finite-frame and pair-energy input is explicit in Lean. The underlying unconditional pair-correlation theorem is published. The new isolation and variational arguments are repository derivations. [Finite frame proof](FixedGapIsolation20261119.md) · [Conditional Lean consumer](../Analysis/ActualVariationalIsolation.lean) · [Independent directed replay](BoundCertificateReplays20261119.md#verify_variational_isolationpy) · [Baluyot–Goldston–Suriajaya–Turnage-Butterbaugh, Acta Arithmetica (2024)](https://doi.org/10.4064/aa230612-20-3)

| Upper gap parameter $C$ | Outward lower proportion |
|---|---:|
| $0.49+10^{-8}$ | $0.32175415$ |
| $1/2+10^{-8}$ | $0.30187816$ |
| $11/20+10^{-8}$ | $0.18901531$ |
| $3/5+10^{-8}$ | $0.05214801$ |
| $0.61+10^{-8}$ | $0.02184040$ |
| $0.61701890$ | $0.00000001$ |

The rows with a $10^{-8}$ margin also apply at the indicated fraction of the local mean spacing. Riemann–von Mangoldt makes the proportion of indices below $T^{c/C}$ tend to zero, and the common-height cutoff at $C$ then bounds the local cutoff at $c$. The numerical lower bound $10^{-8}$ at the last row uses the common height. [Counting conventions](IsolatedZeroStopLoss20261119.md)

## Absorbing the off-line price

Write $K(v)=\int_{-1/2}^{1/2}f(t)\cos(2\pi vt)\,dt$, $k=K(C)$, $d=K(2C)$ and $p=1-k^2$. The finite grouping, spectral price $g(s)=4-(2-s)_+^2$ and the pure-pair contribution are established in the companion note. A reflected pair accompanied by one assigned singleton has weak eigenvalue at most one. Its signed price after allowance for its three occurrences is at most $g(1)-2-3p=1-3p$. With two assignments at distance $\Delta\le2C$, let $s=K(\Delta)\ge d>0$. The difference frame has weight $1-s$. The weak eigenvalue of the remaining sum-frame Gram is at most its diagonal entry $1+s$. Monotonicity of $g$ and the identity
$$
g(1+s)+g(1-s)=6-2s^2
$$
bound the signed additional price by $2(1-d^2)-4p$. Thus if $3p\ge1$ and $2p\ge1-d^2$, every nonreal group pays its full $(2-p)$ budget per occurrence, at every horizontal displacement. The other groups are controlled by the same finite estimates. Jensen gives $\operatorname{tr}\varphi_2(P_{\rm isolated})\ge n$ for the real isolated block. For a normalized window with pair-energy coefficient $E(f)$, the resulting lower proportion is
$$
 \frac{2-E(f)-p}{1-p}=1-\frac{E(f)-1}{K(C)^2}.
\tag{1}
$$
The directed certificate checks the strict angular inequalities required for smoothing. [Angular grouping and height limit](FixedGapIsolation20261119.md)

## Exact variational calculation

Let $I=[-1/2,1/2]$, $m(f)=\int_I f$, and write $\langle f,h\rangle=\int_I fh$. Define the symmetric bilinear form
$$
\mathcal E(f,h)=\langle f,h\rangle+\iint_{I^2}|s-t|f(s)h(t)\,ds\,dt,\qquad
\mathcal B(f,h)=\mathcal E(f,h)-m(f)m(h).
$$
For a unit-mass density $E(f)=\mathcal E(f,f)$. Write $f_0(t)=\cos(\sqrt2\,t)/(\sqrt2\sin(1/\sqrt2))$ for the Montgomery–Taylor density, $E_0=1/2+\cot(1/\sqrt2)/\sqrt2$ and $e=E_0-1>0$. Its stationary equation is $\mathcal E(f,f_0)=E_0m(f)$, also obtained from (2) at frequency $r=1/(\sqrt2\pi)$. The form $\mathcal B$ is positive definite. Indeed, on writing $f=m(f)f_0+g$ with $m(g)=0$, the cross term vanishes. For $G(x)=\int_{-1/2}^xg$ integration by parts twice gives $\mathcal E(g,g)=\lVert g\rVert_2^2-2\int_I G^2$. Both endpoints have $G=0$. Hence $|G(x)|^2\le\min(x+1/2,1/2-x)\lVert g\rVert_2^2$. Integration gives $\mathcal E(g,g)\ge\lVert g\rVert_2^2/2$ and $\mathcal B(f,f)\ge e m(f)^2+\lVert g\rVert_2^2/2$.

Set $s_C=\sin(\pi C)/(\pi C)$, $h_C(t)=\cos(2\pi Ct)$ and $K_0(C)=\langle f_0,h_C\rangle$. For $x\in I$, direct integration gives
$$
\int_I |x-t|h_C(t)\,dt=D_C-\frac{h_C(x)}{2\pi^2 C^2},
\qquad D_C=\frac{s_C}{2}+\frac{\cos(\pi C)}{2\pi^2 C^2}.
\tag{2}
$$
Its second derivative and boundary value at $x=1/2$ verify this formula; evenness fixes the linear integration constant. For each cutoff in the table define
$$
 b_C=\frac{e C^2}{K_0(C)(C^2-r^2)},\qquad
 f_C=(1-b_Cs_C)f_0+b_C h_C,\qquad
 K_C(v)=\langle f_C,h_v\rangle .
$$
This function has unit mass. From (2) and stationarity, $E_0s_C=D_C+(1-r^2/C^2)K_0(C)$. The coefficient of $m(f)$ therefore cancels in the following exact identity,
$$
 \mathcal B(f,f_C)=\frac{e}{K_0(C)}\langle f,h_C\rangle .
\tag{3}
$$
At $f=f_C$ it gives $E(f_C)-1=eK_C(C)/K_0(C)$. Cauchy–Schwarz in $\mathcal B$ proves that $f_C$ attains the maximum of $K(C)^2/(E(f)-1)$ over all unit-mass real $L^2$ functions. The certificate shows that $b_C$ and $1-b_Cs_C$ are positive. Both component cosines decrease on $[0,1/2]$, and the endpoint value of $f_C$ is strictly positive. Thus the extremum is attained by a positive probability density eligible for the spectral argument. Its sharp value in (1) is
$$
 1-\frac{e}{K_0(C)K_C(C)} .
\tag{4}
$$
This is sharpness of the specific pair-energy coefficient (1). The exact finite grouping, other interaction rewards, and actual zero isolation can have stronger bounds.

## Endpoint and numerical checks

The transform is elementary. For $\operatorname{sinc}(v)=\sin(\pi v)/(\pi v)$ with the continuous value at zero,
$$
 K_0(v)=\frac{\cos(\pi v)-\sqrt2\pi v\cot(1/\sqrt2)\sin(\pi v)}{1-2\pi^2v^2},
\qquad
 K_C(v)=(1-b_Cs_C)K_0(v)+
 \frac{b_C}{2}\{\operatorname{sinc}(C-v)+\operatorname{sinc}(C+v)\}.
$$
The compact angular certificate checks $k,d>0$, the triple Rayleigh inequality, and the two zero-price inequalities. For $2C>1$ a 128-cell directed secant bound proves $K_C'<0$ on $[1,2C]$. An independent calculation of $E(f_C)$ from (2) agrees with the extremal value in (3). Strict margins permit the same smoothing and height limits as in the finite-gap argument.

The optimized coefficient (4) is positive at $C=0.61701890$ and negative at $C=0.61701891$. At the latter point the upper bound from Cauchy–Schwarz applies to every positive unit-mass density. Since $K_f(v)$ decreases on $[0,1]$ for every such density, every larger $C\le1$ with $K_f(C)>0$ also has nonpositive value in (1). The largest cutoff producing a positive coefficient by this argument lies in **$[0.61701890,0.61701891]$**. Solving $K_0(C)K_C(C)=e$ numerically gives $0.61701890381713789068\ldots$ inside the certified bracket. [Outward numerical certificate](BoundCertificateReplays20261119.md#verify_variational_isolationpy)
