# Temporal concentration: two exact four-dimensional no-go families

**Classification:** A-r = T2-NOGO; A-q = T2-NOGO. These refute explicit source-motivated universal concentration strengthenings selected in `TARGET2_SOURCE_CONTRACT.md`. They are not a claim that the authors literally asserted a universal 5% CV theorem. The small-CV Werner observations remain example-specific observations.

For each state, define r=CS(Psi_U*)/CK(rho), q=1/r and R=Pq, with the source's normalized seeds and generators. Average over the common recurrence period 2pi:
\[
\langle f\rangle_T=(2\pi)^{-1}\int_0^{2\pi}f(t)\,dt,
\qquad \mathrm{CV}(f)^2=\frac{\langle f^2\rangle_T}{\langle f\rangle_T^2}-1.
\]
All ratios below have positive numerator and denominator away from common recurrences and have removable finite positive limits at those recurrences. Each epsilon is strictly positive: no rank-deficient limiting object is itself used as a counterexample.

## 1. A comparison lemma, independent of explicit Lanczos coefficients

A normalized finite Krylov chain of length m with return amplitude A has
\[
1-|A|^2\le C\le(m-1)(1-|A|^2).
\]
This follows by bounding the index n between 1 and m-1 in the nonzero-node probability sum. For the operator flows of a positive matrix O, the normalized return amplitude Tr(O(t)O)/Tr(O^2) is real and lies in [0,1]. Set D=1-A. If m<=5,
\[
D\le C\le8D.
\]
For rho and sqrt(rho), the corresponding quantities are
\[
D_K=1-\frac{\operatorname{Tr}(\rho(t)\rho)}{P},\qquad
D_S=1-\operatorname{Tr}(\sqrt{\rho(t)}\sqrt\rho).
\]
The latter is exactly the state-vector return amplitude of the U* purification, not its purified operator return amplitude. Thus
\[
\frac18\frac{D_S}{D_K}\le r\le8\frac{D_S}{D_K},\qquad
\frac18\frac{D_K}{D_S}\le q\le8\frac{D_K}{D_S}.
\]
The following states have only the five frequencies 0,+-1,+-2. Every listed frequency has nonzero weight for the stated open parameter ranges, so the chains really have length 5.

## 2. A-r: unbounded CV of the main-text ratio

Fix once and for all
\[
B=\frac1{10}\begin{pmatrix}5&3\\3&5\end{pmatrix},\quad
\sqrt B=\frac1{2\sqrt5}\begin{pmatrix}3&1\\1&3\end{pmatrix},\quad
H=\operatorname{diag}(0,2,3,4).
\]
For 0<epsilon<=1/4 take
\[
\rho_\epsilon=(1-\epsilon)B\oplus\epsilon B.
\]
Its eigenvalues are 4(1-epsilon)/5, (1-epsilon)/5, 4epsilon/5, epsilon/5. Therefore it is trace one and full rank. Write D0=(1-epsilon)^2+epsilon^2; then P=(17/25)D0.

With A=1-cos(2t) and B_t=1-cos t, direct matrix autocorrelation gives
\[
D_S=\frac{(1-\epsilon)A+\epsilon B_t}{10},\qquad
D_K=\frac9{34D_0}[(1-\epsilon)^2A+\epsilon^2B_t].
\]
Set c=cos^2(t/2), so A=4c B_t. The comparison ratio, extended over the removable zeros, is
\[
f_\epsilon=\frac{D_S}{D_K}
=\frac{17D_0}{45}
\frac{4(1-\epsilon)c+\epsilon}{4(1-\epsilon)^2c+\epsilon^2}.
\]
An exact decomposition is
\[
f_\epsilon=\frac{17D_0}{45(1-\epsilon)}
\left[1+\frac{\epsilon(1-2\epsilon)}{4(1-\epsilon)^2c+\epsilon^2}\right].
\]
The elementary identity
\[
\left\langle\frac1{a\cos^2(t/2)+b}\right\rangle_T
=\frac1{\sqrt{b(a+b)}}\quad(a,b>0)
\]
follows by tangent substitution on a half-period. Consequently
\[
\langle f_\epsilon\rangle_T=
\frac{17D_0}{45(1-\epsilon)}
\left[1+\frac{1-2\epsilon}{\sqrt{4(1-\epsilon)^2+\epsilon^2}}\right]
\le\frac{68}{81}<1.
\]
Here D0<=1, 1-epsilon>=3/4 and the square-root denominator is at least 2(1-epsilon). Thus \(\langle r\rangle_T\le8\).

On the nonrecurrence window |t-pi|<=epsilon, c<=epsilon^2/4. Since D0>=1/2,
\[
f_\epsilon\ge\frac{17}{180\epsilon},\qquad
r\ge\frac{17}{1440\epsilon}.
\]
The window has length 2epsilon, so
\[
\langle r^2\rangle_T\ge\frac{289}{2073600\pi\epsilon},
\qquad
\boxed{\mathrm{CV}(r)^2\ge\frac{289}{132710400\pi\epsilon}-1\longrightarrow\infty.}
\]
For the explicit rational state epsilon=10^-10, the elementary bound pi<22/7 proves CV(r)>80. This finite-state certificate is independent of numerical quadrature.

The mechanism is a partial recurrence of the heavier block at t=pi. The remaining light block contributes at order epsilon to the sqrt(rho) measure but at order epsilon^2 to the normalized rho measure. The global state has not recurred at t=pi.

## 3. A-q: unbounded CV of the actual supplemental reciprocal ratio

Concentration does not survive inversion automatically, so a separate construction is necessary. Keep the same H. Let epsilon=eta^2 and 0<epsilon<=1/16. Define the positive matrix
\[
A_\eta=\eta\begin{pmatrix}2&1\\1&2\end{pmatrix}
\oplus\begin{pmatrix}1&\eta^3\\\eta^3&1\end{pmatrix},
\quad \rho_\eta=\frac{A_\eta^2}{N},
\]
\[
N=2+10\epsilon+2\epsilon^3,\qquad
T=\operatorname{Tr}A_\eta^4=2+82\epsilon^2+12\epsilon^3+2\epsilon^6.
\]
The eigenvalues of A_eta are 3eta, eta, 1+eta^3, 1-eta^3, all strictly positive. Thus rho has trace one, full rank, purity P=T/N^2 and positive square root A_eta/sqrt(N). For rational eta the density matrix is rational.

Direct autocorrelation gives
\[
D_S=\frac{2\epsilon}{N}A+\frac{2\epsilon^3}{N}B_t,
\qquad
D_K=\frac{32\epsilon^2}{T}A+\frac{8\epsilon^3}{T}B_t.
\]
Hence
\[
g_\epsilon=\frac{D_K}{D_S}
=\frac{4N\epsilon}{T}\frac{16c+\epsilon}{4c+\epsilon^2},
\]
\[
\langle g_\epsilon\rangle_T=
\frac{4N\epsilon}{T}\left[4+\frac{1-4\epsilon}{\sqrt{4+\epsilon^2}}\right]
\le27\epsilon.
\]
For the stated domain, 2<=N,T<=3, so 2/3<=N/T<=3/2. The bracket is at most 9/2. Thus \(\langle q\rangle_T\le216\epsilon\).

On |t-pi|<=epsilon, c<=epsilon^2/4, giving g_epsilon>=2N/T>=4/3 and q>=1/6. Therefore
\[
\langle q^2\rangle_T\ge\frac{\epsilon}{36\pi},
\qquad
\boxed{\mathrm{CV}(q)^2\ge\frac1{1679616\pi\epsilon}-1\longrightarrow\infty.}
\]
For the rational input eta=1/100000 (epsilon=10^-10), pi<22/7 proves CV(q)>40. Multiplication by the positive time-independent purity leaves CV unchanged, so the same theorem covers the supplemental quantity R=Pq.

Here the temporal mean of q becomes small but its narrow excursions remain finite. A decreasing absolute standard deviation is not concentration relative to the mean; the source explicitly uses the relative measure CV. This distinction is essential to the construction.

## 4. Zeros, recurrence and parameter endpoints

In both families the normalized return losses are positive combinations of 1-cos t and 1-cos 2t. They vanish simultaneously only at 2pi integers. The positive-matrix return amplitude excludes A=-1, so zero complexity has the same locus. At these common recurrences both complexities have positive quadratic curvature and their ratio has a finite positive removable limit. At t=pi, the gap-one block remains active for every positive epsilon, so this is NOT a common recurrence or a fake 0/0 counterexample. Every integral is finite for each fixed positive parameter. Divergence is proved by explicit uniform inequalities as the parameter varies; no exchange of a singular limit and a temporal integral is assumed.

## 5. Independent verification and limits of the result

`verify_target2_exact.py` squares the proposed roots, checks trace/purity identities, and independently computes the full matrix autocorrelation as a Laurent polynomial of the phase. It verifies the comparison-function identities, domain-bound constants and rational finite-witness CV lower bounds. `verify_target2_numerical.py` separately computes full state-space U* purification Lanczos and mixed matrix-commutator Lanczos, checks a third sqrt(rho) matrix representation, reconstructs the exact reduced cubic complexity polynomials and compares all channels. It checks recurrence cancellation symbolically and 70-digit evaluations near the narrow peaks. Numerical CV integrals are labelled numerical, not proofs.

No minimum dimension for these temporal no-go phenomena is claimed; exact examples are dimension four. The results do not falsify the Werner data, establish typicality, require that all states fluctuate strongly, or prove the authors' unquantified sentence false under every conceivable interpretation. They prove that the selected uniform finite-CV strengthenings are impossible even at fixed dimension and fixed nondegenerate Hamiltonian. Novelty is NOT CLEARED; independent external audit is NOT PERFORMED.
