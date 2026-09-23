# Right-bound details, independent channels and structural bootstrap

Source conventions are fixed in `sources/V4_INSPECTED_SOURCE_EXTRACT.md`. The small certificate is `RIGHT_BOUND_ONE_PAGE.md`. All results here concern time-independent Hermitian Hamiltonians, the paper's normalized Hilbert–Schmidt operator complexity, and its time-independent purification.

## 1. Exact spectral data for the displayed qutrit

For rho=diag(16,1,9)/26 and H coupling the first two levels, the normalized mixed-operator measure on (-2,0,2) has weights
\[
(225/1352,\ 451/676,\ 225/1352).
\]
The pure-state energy measure of s=vec(sqrt(rho)) under H tensor I has masses 17/52 at each of -1,+1 and 9/26 at zero. The rank-one density matrix therefore has the energy-difference measure on (-2,-1,0,1,2) with weights
\[
(289/2704,\ 153/676,\ 451/1352,\ 153/676,\ 289/2704).
\]
Both measures have total mass one and strictly positive displayed weights. Their distinct finite supports prove exact chain lengths 3 and 5; no numerical termination threshold is used.

The nonzero squared Lanczos coefficients are, respectively,
\[
(225/169,451/169),\qquad
(17/13,43/26,1377/1118,451/559),
\]
with all diagonals zero. Exact probability vectors at t=pi/3 are preserved in `results/target1r_exact.json`. Each sums exactly to one.

**Channel A:** weighted monomial Gram–Schmidt on the scalar spectral measure, followed by exact sine/cosine evolution.

**Channel B:** matrix-valued commutator Lanczos starting from rho and from R=s s^dagger, with direct U rho U^dagger or (U tensor I)R(U^dagger tensor I) evolution. The seed norms and every Krylov-vector norm are retained explicitly. Channel B never receives Channel A's measure, polynomials or recurrence coefficients. The implementations agree on all probabilities and b_n^2, not merely the final inequality.

## 2. Necessary short-time condition and an open failure set

For every finite-dimensional rho,H,
\[
k_K=\frac{2[\operatorname{Tr}(\rho^2H^2)-\operatorname{Tr}(\rho H\rho H)]}{P},
\qquad k_I=2[\operatorname{Tr}(\rho H^2)-(\operatorname{Tr}\rho H)^2].
\]
The proposed all-time right bound requires k_K<=k_I. A strict violation of this necessary condition suffices for a small-time counterexample, with analyticity in finite dimension. It is not asserted to characterize all finite-time violations.

For rho=diag(p,q,r), p,q,r>0 and p+q+r=1, with the same active sigma_x Hamiltonian, this reduces to
\[
(p-q)^2>P(p+q).
\]
This is an open algebraic condition, not an isolated fine-tuned point.

The phenomenon does not require a common active/spectator decomposition. Keep rho=diag(16,1,9)/26 but choose
\[
H_\delta=\begin{pmatrix}0&1&\delta\\1&0&2\delta\\\delta&2\delta&0\end{pmatrix}.
\]
Exact commutator algebra gives
\[
k_K-k_I=\frac{4-540\delta^2}{169}>0
\quad(0<|\delta|<1/\sqrt{135}).
\]
Because rho has simple spectrum and all off-diagonal entries of H_delta are nonzero, the pair has no nontrivial common reducing projection. At delta=1/20 the curvature gap is 53/3380. Since ||H_delta||<=11/10 and each operator chain has at most seven gap atoms, Taylor's theorem gives at t=1/20000 the exact positive lower bound
\[
\Delta(t)\ge\frac{378247}{21125000000000000}>0.
\]
Eight random complex common-unitary conjugations also preserve the original finite-time gap numerically. Commands: `python scripts/verify_1r_bootstrap.py`.

## 3. Minimum physical-system dimension

Dimension one is stationary. For an arbitrary qubit choose the energy basis, put z=(p1-p2)^2 in [0,1] and c=cos(theta)^2 in [0,1]. The source's formulas can also be independently obtained from a three-atom measure:
\[
F(\mu;\tau)=\mu\sin^2\tau+8\mu(1-\mu)\sin^4(\tau/2),
\]
\[
\mu_I=(1-zc)/2,\quad \mu_K=z(1-c)/(1+z).
\]
Both lie in [0,1/2], where F is nondecreasing for every time, and
\[
\mu_I-\mu_K=\frac{(1-z)(1+zc)}{2(1+z)}\ge0.
\]
Thus the right bound holds for every qubit state, Hamiltonian and time, including pure, maximally mixed, stationary and zero-gap cases by direct limiting/terminated-chain evaluation. The qutrit certificate is therefore minimum-dimensional. This is the physical-system dimension, not the dimension of the purification or operator space.

## 4. Historical lead comparison and provenance

The clean-room baseline first found rational violations (13,1,5)/19 and (14,1,4)/19 using Fraction arithmetic before `UNVERIFIED_LEADS.md` was opened. The displayed square-spectrum point is a later in-run exactification, not claimed to have been frozen before that opening.

Only after the baseline was written were the two old leads inspected. Both survive independent checks without repair:
- historical R1, diag(3/5,1/100,39/100): curvature gap 17829/128050;
- historical R2, diag(7/10,1/20,1/4): at pi/3 the gap is 153775/4906496, matching the old candidate.
Neither lead was treated as a proved premise before the independent checks. These confirmations are not described as new discovery of the old candidates.

## 5. Not implied

This does not show that every mixed state violates the bound, that violations occur at every time, that the two sides of Eq.(4) fail on the same state, or that either factor-two inequality is false. It supplies no model-independent corrected multiplicative constant for the right bound. Novelty remains NOT CLEARED; no independent external audit has been performed.
