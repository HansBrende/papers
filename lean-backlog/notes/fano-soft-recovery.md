# The Fano inequality with paid recovery errors

Hans Brende and GPT-6 Astra, 14 November 2026.
**Status: written proof with exact finite accounting, not Lean-verified.**
This extracts a conditional form of the
[33-term Fano certificate](fano-shannon-certificate.md). It specifies what
must be paid when some helpers are outside a proposed application. It
does not supply such applications on arbitrary growing hosts, and makes
no literature novelty claim.

## 1. Statement

Let W be the 28 nonincident point-line cells of the Fano plane. Let X_v,
v∈W, and Z be jointly distributed finite random variables, with entropies
measured in one fixed base. Write C_ℓ for the four cells of column ℓ and
H_ℓ for the twelve cells in its three incident point rows. Put

$$
s_v=H(X_v\mid Z),\qquad
\delta_\ell=H(X_{C_\ell}\mid X_{H_\ell},Z),\qquad
\epsilon_v=H(X_v\mid X_{H_{\operatorname{col}(v)}},Z).
$$

**Paid Fano inequality.** Without any independence, alphabet-uniformity,
linearity or recovery assumption,

$$
H(X_W\mid Z)\le \frac23\sum_{v\in W}s_v
                   +\frac{41}{84}\sum_\ell\delta_\ell, \tag{1}
$$

$$
H(X_W\mid Z)\le \frac23\sum_{v\in W}s_v
                   +\frac13\sum_{v\in W}\epsilon_v. \tag{2}
$$

Both inequalities hold; their error terms need not dominate each other.
The coefficient 41/84 is the charge from the present certificate, with
no optimality claim. The coefficient 1/3 in (2), with the singleton
coefficient fixed at 2/3, is best possible: independent nonconstant X_v
make the left side, the singleton sum and the error sum equal.

Equivalently, (2) bounds the information each cell shares with its
helper union by three times the conditional total correlation:

$$
\sum_{v\in W} I(X_v;X_{H_{\operatorname{col}(v)}}\mid Z)
\le 3\left(\sum_{v\in W}H(X_v\mid Z)-H(X_W\mid Z)\right).
$$

All steps below use only Shannon inequalities. Thus the statements also
hold for normalized monotone submodular functions and their contractions,
with conditional entropies interpreted as rank increments.

## 2. Keep each closure error

Write h(S)=H(X_S|Z). Let cl(S) be the **combinatorial** closure obtained
by adjoining a column whenever its entire helper union is included. The
random variables need not satisfy those recoveries. Instead define

$$
\kappa(S)=h(\operatorname{cl}(S))-h(S)
         =H(X_{\operatorname{cl}(S)}\mid X_S,Z).
$$

Let G=GL₃(F₂) act on points by M and line normals by M^(−T), and put
$\bar\kappa(S)=|G|^{-1}\sum_{g\in G}\kappa(gS)$.
This averages entropy functions; it imposes no symmetry on the original
distribution. Closure commutes with these 168 host automorphisms.

For each term i of the published certificate, let n_i be its integer
weight. Define U_i=S_i∪T_i for types S and J, and U_i=R_{A_i} for type B,
where R_A is the union of the residual rows in A. Types I and N require
no closure error. The following finer bound is the direct certificate:

$$
H(X_W\mid Z)\le\frac23\sum_v s_v
 +\frac1{264}\sum_{i\text{ of type S,J,B}}n_i\bar\kappa(U_i). \tag{3}
$$

To prove it, replace every exact-recovery use in the original proof.
For a type-S term, ordinary submodularity gives

$$
h(S\cap T)+h(\operatorname{cl}(S\cup T))-h(S)-h(T)
 \le\kappa(S\cup T).
$$

For type J, adjoining actual coordinates and then closing gives

$$
h(\operatorname{cl}(S\cup T))-h(S)
 \le\sum_{v\in T\setminus S}s_v+\kappa(S\cup T).
$$

For type B, purchase the rows and the remaining coordinates:

$$
h(S)\le\sum_{v\in R_A}s_v+\kappa(R_A)
              +\sum_{v\in S\setminus\operatorname{cl}(R_A)}s_v.
$$

Type I retains the ordinary increment bound with its actual singleton
entropies; type N is unchanged. Average these inequalities over G and
combine them with the same weights. Their entropy coefficients still
cancel to 264h(W). The singleton price is uniform because G is transitive
on W. Its total is 4928/264=56/3, so every cell has price
(56/3)/28=2/3. This proves (3). No entropy equality between a seed and
its combinatorial closure was assumed.

## 3. Bound the closure errors

Use a closure derivation that fires a column ℓ only when H_ℓ⊆P, where P
is the current set, and C_ℓ∖P is nonempty. The exact entropy added at
that step is

$$
H(X_{C_\ell\setminus P}\mid X_P,Z)
 \le\delta_\ell,
\qquad
H(X_{C_\ell\setminus P}\mid X_P,Z)
 \le\sum_{v\in C_\ell\setminus P}\epsilon_v. \tag{4}
$$

The increments telescope to κ of the starting set. Each column fires
productively at most once. Every column containing a new closure cell
must fire, since only its own rule can add that cell. Thus the number of
productive firings does not depend on their order; newly added cells
are counted exactly once.

Only eleven terms can incur a closure error. The term numbers refer to
the published [certificate](../tools/fano-shannon/certificate.json).

| Term | Weight n_i | Column firings | New cells |
|---:|---:|---:|---:|
| 3 | 39 | 1 | 4 |
| 4 | 63 | 1 | 4 |
| 5 | 15 | 1 | 4 |
| 8 | 42 | 1 | 4 |
| 13 | 88 | 1 | 4 |
| 18 | 77 | 1 | 2 |
| 24 | 99 | 1 | 2 |
| 26 | 14 | 1 | 1 |
| 27 | 77 | 2 | 2 |
| 31 | 215 | 1 | 4 |
| 33 | 96 | 1 | 1 |

The weighted totals are 902 column firings and 2464 new cells. Transport
each derivation by all automorphisms. Their action is transitive on the
seven columns and on W. Substitution of (4) into (3) therefore gives

$$
\frac{902}{264\cdot7}\sum_\ell\delta_\ell
 =\frac{41}{84}\sum_\ell\delta_\ell,
\qquad
\frac{2464}{264\cdot28}\sum_v\epsilon_v
 =\frac13\sum_v\epsilon_v,
$$

proving (1) and (2). The contextual errors in (3) can be smaller than
either of these coarser invoices.

The [accounting checker](../tools/fano-shannon/closure_charge.py)
reconstructs every derivation, its conditioning set and its added cells.
It also transports the charges by all 168 automorphisms and checks their
uniformity and all three coefficients, including the singleton price.
Its [receipt](../tools/fano-shannon/closure-charge-receipt.json) is exact.
From the repository root, with assertions enabled:

```sh
python3 lean-backlog/tools/fano-shannon/verify_certificate.py
python3 lean-backlog/tools/fano-shannon/closure_charge.py
```

Both commands use only the standard library. The second recomputes and
compares the saved receipt; `--output PATH` regenerates it. Neither runs
a solver or verifies the proof in Lean.

## 4. Outside helpers and shared advice

If column C_ℓ is determined by X_{H_ℓ}, Z and an outside variable B_ℓ,
then δ_ℓ≤H(B_ℓ|X_{H_ℓ},Z). This pays for missing helpers in (1).
Equation (3) can charge less when information is already present in a
later closure context.

If **one shared variable B** makes all seven recoveries exact, condition
on (Z,B) and apply the zero-error inequality. The chain rule gives

$$
H(X_W\mid Z)\le\frac23\sum_v s_v
 +I(X_W;B\mid Z)-\frac23\sum_v I(X_v;B\mid Z)
 \le\frac23\sum_v s_v+H(B\mid Z). \tag{5}
$$

This charges the record once, regardless of how many recoveries use it.
If B=X_T is a coordinate subtuple within W, the correction in (5) is at
most H(B|Z)/3: I(X_W;B|Z)=H(B|Z), while the sum of singleton mutual
informations is at least Σ_{v∈T}H(X_v|Z)≥H(B|Z).

For the full 49-cell host, first condition on its 21 incident cells,
apply the residual inequality, and add their joint entropy once. They
cannot simply be dropped: full recoveries may use them.

## 5. What a larger application must supply

For conditional singleton bounds s_v≤b, (1) improves on the residual
order price 20b whenever Σ_ℓδ_ℓ<(112/41)b. Equation (2) suffices when
Σ_vε_v<4b. These are sufficient charges from this certificate, not
optimized necessary conditions.

A growing host must still supply labelled templates with controlled
recovery defects. A fractional cover permits conditional Shearer to
combine their inequalities, but its overlap and the weighted error sum
must be paid. Common outside advice can instead be conditioned on once
when such a small record actually exists. Neither small defects nor a
useful cover follows from bounded window alone. This note supplies a
local inequality and its exact invoice, not a common whole-row deficit
or a new native-machine exclusion.
