# Exact qutrit counterexamples to Conjecture 1 of Das and Mori

**Dehao Lin**  
School of Physics, Sun Yat-sen University, Guangzhou, China

Das and Mori's Conjecture 1 proposes the two-sided hierarchy (their Eq. (4))
in the conventions of the full manuscript:

$$
\mathcal C_S\bigl(\Psi_\rho^{U^*}(t)\bigr)
\le \mathcal C_K\bigl(\rho(t)\bigr)
\le \mathcal C_K\bigl(\Psi_\rho^I(t)\bigr).
$$

The two sides are violated by two separate strictly full-rank qutrit witnesses,
given below. No single displayed state is claimed to violate both sides.
These are the frozen results of Propositions 3.1 and 3.2, not new results.

Write $S_{U^*}=\mathcal C_S(\Psi_\rho^{U^*}(t))$,
$C_{\mathrm M}=\mathcal C_K(\rho(t))$, and $K_I=\mathcal C_K(\Psi_\rho^I(t))$.
Here $\rho(t)=e^{-itH}\rho e^{itH}$ and $P=\operatorname{Tr}\rho^2$.
Operator complexity uses the Hilbert--Schmidt inner product and normalized mixed
seed $\rho/\sqrt P$. For $s=\operatorname{vec}_{\mathrm r}\sqrt\rho$,
the purification generators are $G_I=H\otimes I$ and
$G_{U^*}=H\otimes I-I\otimes\overline H$.
The rightmost quantity $K_I$ is the operator complexity of the rank-one density
matrix $ss^\dagger$ under $[G_I,\cdot]$, not its vector spread complexity.

## A. Lower-side counterexample

$$
H_L=\operatorname{diag}(2,0,1),\qquad
\rho_L=\frac1{42}\begin{pmatrix}32&0&0\\0&5&3\\0&3&5\end{pmatrix}.
$$

Its spectrum is $16/21,4/21,1/21$, all positive. The square root and purity are

$$
\sqrt{\rho_L}=\frac1{2\sqrt{21}}
\begin{pmatrix}8&0&0\\0&3&1\\0&1&3\end{pmatrix},\qquad P_L=\frac{13}{21}.
$$

Only levels two and three carry coherence, with energy gap one.
In the energy basis, the mixed and spread spectral weights are respectively
$|\rho_{ab}|^2/P$ and $|(\sqrt\rho)_{ab}|^2$ at $E_a-E_b$.
Both measures therefore have the three-atom form
$\nu_\mu=(1-\mu)\delta_0+(\mu/2)(\delta_{-1}+\delta_1)$, with

$$
\mu_S=\frac1{42},\qquad \mu_K=\frac3{182},\qquad
S_{U^*}(t)=F(\mu_S;t),\quad C_{\mathrm M}(t)=F(\mu_K;t).
$$

Lemma 2.1 gives the exact three-atom formula, for $0<\mu<1$,

$$
F(\mu;t)=\mu\sin^2t+8\mu(1-\mu)\sin^4(t/2).
$$

For a direct check, the three Krylov amplitudes are
$(1-\mu+\mu\cos t,\,-i\sqrt\mu\sin t,\,\sqrt{\mu(1-\mu)}(\cos t-1))$;
their squared moduli, weighted by indices $0,1,2$, give $F$.
At $t=\pi$ this yields the exact contradiction

$$
S_{U^*}(\pi)=\frac{82}{441},\qquad
C_{\mathrm M}(\pi)=\frac{1074}{8281},\qquad
\frac{82}{441}-\frac{1074}{8281}=\frac{4192}{74529}>0.
$$

Thus $S_{U^*}(\pi)>C_{\mathrm M}(\pi)$, violating the lower side of the proposed hierarchy.

## B. Upper-side counterexample

$$
\rho_R=\frac1{26}\operatorname{diag}(16,1,9),\qquad
H_R=\begin{pmatrix}0&1&0\\1&0&0\\0&0&0\end{pmatrix}.
$$

This state is strictly full rank, with purity $P_R=1/2$ and square root
$\operatorname{diag}(4,1,3)/\sqrt{26}$. The two operator problems have the following
spectral measures; each weight corresponds to the support entry in the same position:

$$
\begin{array}{c|c|l}
 &\text{ordered support}&\text{ordered weights}\\ \hline
C_{\mathrm M}&(-2,0,2)&(225/1352,\ 451/676,\ 225/1352)\\[3pt]
K_I&(-2,-1,0,1,2)&(289/2704,\ 153/676,\ 451/1352,\ 153/676,\ 289/2704)
\end{array}
$$

For $K_I$, the purified vector has energy weights $17/52,9/26,17/52$
on $-1,0,1$; their difference convolution gives the second row.
All weights are positive, so the Krylov chains have exact lengths three and five.

To check the evolution from either row, orthonormalize $1,x,x^2,\ldots$
against its spectral measure $\nu$ to obtain real polynomials $p_n$.
The frozen spectral prescription and complexity definition are

$$
\varphi_n(t)=\int p_n(x)e^{-itx}\,d\nu(x),\qquad
C(t)=\sum_{n=0}^{m-1}n\,|\varphi_n(t)|^2.
$$

For additional checks on this finite calculation, the squared nonzero Lanczos
coefficients are $(225/169,451/169)$ for $C_{\mathrm M}$ and
$(17/13,43/26,1377/1118,451/559)$ for $K_I$; all diagonal coefficients vanish.
At $t=\pi/3$, Appendix A gives the complete probabilities in increasing Krylov index:

$$
\begin{aligned}
p^{\mathrm M}&=\left(\frac{458329}{1827904},\frac{675}{2704},\frac{913275}{1827904}\right),\\[3pt]
p^{K,I}&=\left(\frac{1500625}{7311616},\frac{62475}{140608},
\frac{45778977}{157199744},\frac{7803}{140608},\frac{1173051}{314399488}\right).
\end{aligned}
$$

Each row sums to one. Its index-weighted sum gives, exactly,

$$
C_{\mathrm M}(\pi/3)=\frac{1141425}{913952},\qquad
K_I(\pi/3)=\frac{2967537}{2456246},\qquad
C_{\mathrm M}(\pi/3)-K_I(\pi/3)=\frac{1600683}{39299936}>0.
$$

Thus $C_{\mathrm M}(\pi/3)>K_I(\pi/3)$, violating the upper side.
As an independent sanity check, the frozen short-time coefficients are

$$
C_{\mathrm M}(t)=\frac{225}{169}t^2+O(t^4),\qquad
K_I(t)=\frac{221}{169}t^2+O(t^4).
$$

The full manuscript also certifies failure throughout $0<t<1/2704$.

## Minimality and scope

Both displayed states are strictly full rank; they are separate witnesses for
separate sides. Theorem 3.3 states: For every qubit density matrix, every
time-independent Hermitian Hamiltonian, and every real time,
$S_{U^*}(t)\le C_{\mathrm M}(t)\le K_I(t)$. Consequently, physical dimension three
is minimal for failure of either side of the source hierarchy.

---

This note is a communication derivative of the full manuscript
*Exact limits of Krylov-complexity comparisons under purification*.
The complete proof context, AI-contribution disclosure, exact certificates, audits,
and reproducibility materials are provided in the accompanying repository.

