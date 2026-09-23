# Exact full-rank qutrit falsification of the right side of Eq. (4)

**Statement.** Under arXiv:2408.00826v4's normalized Hilbert–Schmidt conventions, the universal inequality
\(C_K(\rho(t))\le C_K(|\Psi_\rho^{\mathbb I}(t)\rangle)\) is false.

Take
\[
\rho=\frac1{26}\operatorname{diag}(16,1,9),\qquad
H=\begin{pmatrix}0&1&0\\1&0&0\\0&0&0\end{pmatrix}.
\]
The state is strictly positive, has trace one and purity \(P=1/2\), and
\(\sqrt\rho=\operatorname{diag}(4,1,3)/\sqrt{26}\).
The two operator seeds are \(\rho/\sqrt P\) and
\(R=|s\rangle\langle s|\), where \(s=\operatorname{vec}\sqrt\rho\).
Their generators are \([H,\cdot]\) and \([H\otimes I,\cdot]\).
In particular, the second seed is the **density matrix of the purification**, not its state vector.

For any normalized Hermitian seed \(O\), the first Lanczos coefficient gives
\(C(t)=\|[G,O]\|_{HS}^2t^2+O(t^3)\).
For a rank-one seed \(R\), this coefficient equals \(2\operatorname{Var}_sG\). Hence
\[
k_K=\frac{\|[H,\rho]\|_{HS}^2}{P}=\frac{225}{169},
\qquad
k_I=2\operatorname{Var}_\rho H=\frac{17}{13}=\frac{221}{169}.
\]
Thus the difference has strictly positive quadratic coefficient \(4/169\).

**Explicit rigorous interval.** The mixed chain has spectral support \(\{0,\pm2\}\), so its Krylov number operator has norm 2. The purified-operator chain has support \(\{0,\pm1,\pm2\}\), so its number operator has norm 4. Both Liouvillians have norm at most 2. For an evolved expectation of a number operator \(N\),
\[
|C'''(t)|\le (2\|L\|)^3\|N\|.
\]
Taylor's theorem therefore yields
\[
C_K(\rho(t))-C_K(R(t))\ge\frac4{169}t^2-64t^3>0
\quad\text{for }0<t<\frac1{2704}.
\]
No limiting rank-deficient state or numerical approximation is used.

**Independent finite-time certificate.** At \(t=\pi/3\), exact spectral-polynomial reconstruction and direct matrix-commutator Lanczos independently give
\[
C_K(\rho(t))=\frac{1141425}{913952},\qquad
C_K(R(t))=\frac{2967537}{2456246},
\]
\[
\boxed{C_K(\rho(t))-C_K(R(t))=\frac{1600683}{39299936}>0.}
\]

**Verification:** `python scripts/verify_1r.py`. This is an internally verified exact certificate, not an external human audit or a novelty/priority certification. The physical-system dimension 3 is minimal, as proved from the arbitrary-qubit reduction in `RIGHT_BOUND_DETAILS.md`.
