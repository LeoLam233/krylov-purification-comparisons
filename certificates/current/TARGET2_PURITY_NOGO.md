# Fixed dimension, fixed purity, fixed Hamiltonian: no purity-only ratio control

**Classification:** B-P = T2-NOGO. **Provenance:** this uses the internally verified fixed-purity family already supplied in the left-bound handoff. The present run verifies that its quantity is exactly the main Conjecture-2 ratio, reconstructs the needed identities and records the resulting source-grounded no-go interpretation. The family is not claimed as newly constructed here.

For 0<epsilon<5/18, define
\[
a_\pm=\frac{1-\epsilon\pm\sqrt{2\epsilon-59\epsilon^2/25}}2,
\quad
\rho_\epsilon=\operatorname{diag}(a_+,a_-)
\oplus\frac\epsilon{10}\begin{pmatrix}5&3\\3&5\end{pmatrix},
\quad H=\operatorname{diag}(2,3,0,1).
\]
Its eigenvalues are a_+,a_-,4epsilon/5,epsilon/5. They are strictly positive: the radicand is positive, 1-epsilon>0 and
\[
(1-\epsilon)^2-(2\epsilon-59\epsilon^2/25)
=(1-14\epsilon/5)(1-6\epsilon/5)>0
\]
on the stated interval. Direct algebra gives
\[
\operatorname{Tr}\rho_\epsilon=1,
\qquad P=\operatorname{Tr}\rho_\epsilon^2=\frac12.
\]
Thus d=4, P=1/2 and H are fixed throughout the entire family.

Only the last two energy levels carry coherence, with gap one. With the source's seeds rho/sqrt(P) and vec(sqrt(rho)), the nonzero-gap total weights are
\[
\mu_K=\frac{9\epsilon^2}{25},\qquad
\mu_S=\frac\epsilon{10}.
\]
A three-point normalized measure (1-mu)delta_0+(mu/2)(delta_1+delta_-1) has exact complexity
\[
F(\mu;t)=\mu\sin^2t+8\mu(1-\mu)\sin^4(t/2).
\]
Indeed the chain has b1^2=mu, b2^2=1-mu, terminates at b3=0, and its three amplitudes are 1-mu+mu cos t, -i sqrt(mu) sin t and sqrt(mu(1-mu))(cos t-1). Squaring gives both F and probability conservation without a numerical approximation.

For x=sin^2(t/2), the main source ratio is therefore
\[
r_\epsilon(t)=\frac{C_S(\Psi_\rho^{U^*}(t))}{C_K(\rho(t))}
=\frac5{18\epsilon}
\frac{1+(1-\epsilon/5)x}{1+(1-18\epsilon^2/25)x}.
\]
At common recurrences t in 2pi Z use the removable limit 5/(18epsilon). The denominator in the displayed reduced expression is positive everywhere. Because 0<epsilon<5/18, the fractional-linear expression decreases with x, giving the uniform bounds
\[
\boxed{
\frac5{18\epsilon}(1-\epsilon/10)
\le r_\epsilon(t)\le\frac5{18\epsilon}.
}
\]
Both the ratio and its recurrence-period mean therefore diverge to infinity while d,P,H stay fixed. The reciprocal q and the rescaled reciprocal Pq tend to zero uniformly. Comparing with the explicit same-purity anchor epsilon=1/10,
\[
\rho_{1/10}=\frac1{100}
\begin{pmatrix}66&0&0&0\\0&24&0&0\\0&0&5&3\\0&0&3&5\end{pmatrix},
\]
shows arbitrarily large multiplicative differences among admissible ratios at the same dimension, purity and Hamiltonian.

This refutes any universal finite purity-only upper control on r or its temporal mean, and any universal positive purity-only lower control on q or Pq. It does not refute the weak statement that purity can influence a ratio, or the particular trends measured within the one-parameter Werner family. It is not asserted that the source posited an exact identity r=f(P).

**Verification:** the transferred verifier passed once; the present target-specific checks are `verify_target2_exact.py` and `verify_target2_numerical.py`. They verify full rank, trace, purity, exact spectral weights, equality to the actual purification state-vector complexity, direct commutator evolution, recurrence behavior and the rational anchor. No minimal dimension is claimed for the fixed-purity strengthening. The two-point/qubit ordering separately explains why the original Eq.(4) violations require at least dimension three.

**Not implied:** a universal classification of all possible purity dependence, an exact universal time-average formula, or a refutation of every qualitative reading of Conjecture 2. This is source-matched prior internal work, not independently human-audited or novelty-cleared.
