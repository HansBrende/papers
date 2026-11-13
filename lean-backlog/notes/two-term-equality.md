# Two Kronecker terms attain the pairing value only as one term

Hans Brende and Claude Fable 5.2, 13 November 2026 (proof of 12 November 2026).

**Status:** written proof, checked line by line by an independent agent with its own code, and by exact
computation ([two_term_equality.py](../tools/two_term_equality.py), enumerator
[two_term_bf.rs](../tools/two_term_bf.rs)). Not formalized in Lean. It supplies the strictness asked for in
message C9 of the [chat](../../chat/fable-astra.md): a two-term decoder at the pairing value has one term, so
codimension two does not occur with at most d(d−1)/2 terms, and three-term codes at d = 3 have dimension at most
6 or exactly 8.

Setting: K = Σ_a A_a ⊗ B_a acts on d × d matrices by X ↦ Σ_a A_a X B_aᵀ, and its code is {X : Xᵀ = K X}, of dimension
d² − rank(swap − K).

**Theorem 1 (the equality case of the bound for two terms).** Let F be any field, d ≥ 1, and
K = A_0 ⊗ B_0 + A_1 ⊗ B_1 with arbitrary d × d matrices over F (zero or dependent factors are allowed). If the code
{X : Xᵀ = A_0 X B_0ᵀ + A_1 X B_1ᵀ} has dimension d(d+1)/2, the largest possible (paper 17, the corollary on two Kronecker terms), then
K = G ⊗ G⁻¹ for an invertible matrix G over F, and the code is {X : G X symmetric}. If K is written with independent
A_0, A_1, then G = g_0 A_0 + g_1 A_1 and B_a = g_a G⁻¹.

The converse is clear: Xᵀ = G X G⁻ᵀ says that G X is symmetric.

*Proof.* Preliminaries.
- (a) Extension of the field. The dimension of the code is d² − rank(swap − K), which does not change in an
  extension. If K = G ⊗ G⁻¹ over the algebraic closure, then the realignment K^R has rank one, also over F, so
  K = A ⊗ B with A, B over F; and A ⊗ B = G ⊗ G⁻¹ gives A = c G, B = c⁻¹ G⁻¹, so A is invertible and B = A⁻¹. So let F
  be algebraically closed.
- (b) Two operations preserve the hypothesis and the conclusion. Recombination: for T in GL_2 replace A_a by
  Σ_b T_ab A_b and B_a by Σ_b (T⁻ᵀ)_ab B_b; K does not change. Base change: replace A_a by P A_a Q⁻¹ and B_a by
  Q B_a P⁻¹; the code becomes {Q X Pᵀ}, and G ⊗ G⁻¹ becomes (P G Q⁻¹) ⊗ (P G Q⁻¹)⁻¹.
- (c) Triangular form. There are invertible P, Q with P A_0 Q⁻¹ and P A_1 Q⁻¹ lower triangular: det(s A_0 + t A_1) is
  a form of degree d in (s, t), so it vanishes at some (s, t) ≠ 0; a vector v ≠ 0 in the kernel of s A_0 + t A_1 has
  A_0 v, A_1 v in one line F w; take v and w as the last basis vectors of the two sides and continue with the
  induced maps of the quotients.
- (d) The last sentence of the theorem follows from the rest: K^R = vec(G) vec(G⁻¹)ᵀ = Σ_a vec(A_a) vec(B_a)ᵀ, so
  G is in the span of A_0, A_1, and for independent A_a the coefficients of vec(A_a) on both sides agree. The
  first statement needs no independence: the column space of K^R is the line through vec(G), and it lies in the
  span of the vec(A_a).
- (F1) Let m ≥ 1, c and ℓ vectors in F^m with ℓ ≠ 0, and M an m × m matrix with (c·w) w + (ℓ·w) M w = 0 for all w.
  Then M = τ·1 for a scalar τ, and c = −τ ℓ. Indeed every w with ℓ·w ≠ 0 is an eigenvector of M; two independent
  such vectors w_1, w_2 have the same eigenvalue, because w_1 + s w_2 is again such a vector for all but one s;
  and these vectors span F^m. Then ((c + τ ℓ)·w) w = 0 for all w.
- (F2) If (c·w)(c′·w) = 0 for all w, then c = 0 or c′ = 0. A matrix R is alternating (Rᵀ = −R with zero diagonal;
  these are exactly the matrices Yᵀ − Y) if and only if wᵀ R w = 0 for all w. Both use that F is infinite.

Induction on d. For d = 1 the operator is a scalar k and the code is {x : x = k x}, so k = 1. Let d ≥ 2, m = d − 1,
and let the A_a be lower triangular. Write, in blocks of sizes 1 and m,

        A_a = [[α_a, 0], [u_a, A_a′]],    B_a = [[β_a, y_aᵀ], [z_a, B_a′]],    X = [[ξ, pᵀ], [q, X′]],

with column vectors u_a, y_a, z_a, p, q of length m and A_a′ lower triangular. Block by block, Xᵀ = Σ_a A_a X B_aᵀ
is (script, part 1):

        (1)  ξ = Σ_a α_a (β_a ξ + y_a·p)
        (2)  q = Σ_a α_a (ξ z_a + B_a′ p)
        (3)  p = Σ_a [ β_a (u_a ξ + A_a′ q) + (u_a pᵀ + A_a′ X′) y_a ]
        (4)  X′ᵀ = Σ_a [ (u_a ξ + A_a′ q) z_aᵀ + (u_a pᵀ + A_a′ X′) B_a′ᵀ ].

*Step 1: the count.* Let N be the code and N_1 the set of X in N with ξ = 0 and p = 0. For such X, (2) gives q = 0,
and (3), (4) become Σ_a A_a′ X′ y_a = 0 and X′ᵀ = Σ_a A_a′ X′ B_a′ᵀ. So N_1 embeds into the code N′ of
K′ = A_0′ ⊗ B_0′ + A_1′ ⊗ B_1′ on m × m matrices, and dim N ≤ d + dim N_1 ≤ d + dim N′ ≤ d + m(m+1)/2 = d(d+1)/2.
Equality holds, so:
- (i) every (ξ, p) is the first row of some X in N;
- (ii) N′ has dimension m(m+1)/2, and Σ_a A_a′ X′ y_a = 0 for every X′ in N′.

*Step 2: a normal form.* Step 1 used only that the first row of each A_a is (α_a, 0, …, 0) and that the code has
dimension d(d+1)/2. Both survive the operations used from here on (recombinations, and one base change with
P = diag(1, ·) and Q = 1), so (1)–(4), (i) and (ii) hold for the matrices after each operation; these keep the
names α_a, β_a, u_a, y_a, z_a, A_a′, B_a′. By induction K′ = G′ ⊗ G′⁻¹ with G′ = g_0 A_0′ + g_1 A_1′ (the first statement
of (d), which holds also when the A_a′ are dependent or one of them is zero; K′ ≠ 0; any such g_0, g_1 will do).
Recombine with a T whose first row is (g_0, g_1); now A_0′ = G′ and G′ ⊗ (B_0′ − G′⁻¹) + A_1′ ⊗ B_1′ = 0.
- Case I: A_1′ is not a multiple of G′. Then B_1′ = 0 and B_0′ = G′⁻¹.
- Case II: A_1′ = t G′. Replace A_1 by A_1 − t A_0 and B_0 by B_0 + t B_1 (a recombination). Now A_1′ = 0 and
  K′ = G′ ⊗ B_0′, so B_0′ = G′⁻¹.

Then apply the base change P = diag(1, G′⁻¹), Q = 1; P is lower triangular, so the A_a stay lower triangular. Now

        A_0′ = 1,  B_0′ = 1,  and either (I) B_1′ = 0 and A_1′ is not a scalar matrix (so m ≥ 2), or (II) A_1′ = 0.

In both cases K′ = 1 ⊗ 1, N′ is the space of symmetric matrices, and A_1′ X′ B_1′ᵀ = 0 for all X′. So (2) and (4)
read

        (2′)  q = ξ (α_0 z_0 + α_1 z_1) + (α_0 + α_1 B_1′) p,
        (4′)  X′ᵀ − X′ = R(ξ, p) := (u_0 ξ + q) z_0ᵀ + (u_1 ξ + A_1′ q) z_1ᵀ + u_0 pᵀ + u_1 (B_1′ p)ᵀ.

By (i), for every (ξ, p) and the q of (2′) there is an X′ satisfying (3) and (4′). Hence:
- (iii) R(ξ, p) is alternating for all (ξ, p);
- (iv) from (1): α_0 β_0 + α_1 β_1 = 1 and α_0 y_0 + α_1 y_1 = 0;
- (ii) reads S y_0 + A_1′ S y_1 = 0 for every symmetric S.

*Step 3: Case I.*
- (ii) with S = w wᵀ: (y_0·w) w + (y_1·w) A_1′ w = 0 for all w. If y_1 ≠ 0, then A_1′ is scalar by (F1). So y_1 = 0,
  and then y_0 = 0.
- (iii) at ξ = 0: q = α_0 p and R = α_0 p z_0ᵀ + α_0 A_1′ p z_1ᵀ + u_0 pᵀ, so
  wᵀ R w = pᵀ [ ((α_0 z_0 + u_0)·w) w + α_0 (z_1·w) A_1′ᵀ w ] (script, part 2). This vanishes for all p and w. If
  α_0 z_1 ≠ 0, then A_1′ᵀ is scalar by (F1). So α_0 z_1 = 0, and then u_0 = −α_0 z_0.
- (3) with y_0 = y_1 = 0 at ξ = 0: p = α_0 β_0 p + α_0 β_1 A_1′ p for all p. As A_1′ is not scalar, α_0 β_1 = 0 and
  α_0 β_0 = 1. So α_0 ≠ 0, β_1 = 0 and z_1 = 0.

So B_1 = 0, and K = A_0 ⊗ B_0 with A_0 = [[α_0, 0], [−α_0 z_0, 1]] and B_0 = [[α_0⁻¹, 0], [z_0, 1]] = A_0⁻¹.

*Step 4: Case II.* Here (ii) gives S y_0 = 0 for all symmetric S, so y_0 = 0, and (iv) gives α_1 y_1 = 0. In (3) the
term Σ_a (u_a pᵀ + A_a′ X′) y_a is (y_1·p) u_1, so (3) reads p = β_0 (u_0 ξ + q) + β_1 u_1 ξ + (y_1·p) u_1; with (2′),
at ξ = 0 for all p, and at ξ = 1, p = 0:

        (3a)  1 = α_0 β_0 · 1 + α_1 β_0 B_1′ + u_1 y_1ᵀ,
        (3b)  0 = β_0 (u_0 + α_0 z_0 + α_1 z_1) + β_1 u_1.

Claim: A_1 = 0, or y_1 = 0 and B_1′ = τ·1 with β_1 = τ β_0.
- If α_1 ≠ 0: y_1 = 0, and (3a) with (iv) gives α_1 β_0 B_1′ = (1 − α_0 β_0)·1 = α_1 β_1·1, so β_0 B_1′ = β_1·1. If β_0
  were 0, then β_1 = 0, against (iv). So B_1′ = τ·1 with τ = β_1/β_0.
- If α_1 = 0: α_0 β_0 = 1 by (iv), and (3a) gives u_1 y_1ᵀ = 0. If u_1 = 0, then A_1 = 0. Otherwise y_1 = 0, and
  (iii) at ξ = 0 has q = α_0 p, R = α_0 p z_0ᵀ + u_0 pᵀ + u_1 (B_1′ p)ᵀ and
  wᵀ R w = pᵀ [ ((α_0 z_0 + u_0)·w) w + (u_1·w) B_1′ᵀ w ]; by (F1), B_1′ = τ·1 and α_0 z_0 + u_0 = −τ u_1. Then (3b)
  gives (β_1 − τ β_0) u_1 = 0, so β_1 = τ β_0.

If A_1 = 0, replace B_1 by 0; this does not change K. Otherwise replace A_0 by A_0 + τ A_1 and B_1 by B_1 − τ B_0 (a
recombination). In both cases the matrices are still in the normal form II, so (i)–(iv), (2′), (3a), (3b) hold for
them, and now B_1′ = 0, β_1 = 0, y_0 = y_1 = 0. Then:
- (iv): α_0 β_0 = 1;
- (iii) at ξ = 0: q = α_0 p, R = α_0 p z_0ᵀ + u_0 pᵀ, wᵀ R w = (p·w) ((α_0 z_0 + u_0)·w), so u_0 = −α_0 z_0;
- (3b): β_0 α_1 z_1 = 0, so α_1 z_1 = 0;
- (iii) at ξ = 1, p = 0: q = α_0 z_0, R = (u_0 + q) z_0ᵀ + u_1 z_1ᵀ = u_1 z_1ᵀ, and wᵀ R w = (u_1·w)(z_1·w); by (F2),
  u_1 = 0 or z_1 = 0.

If z_1 = 0, then B_1 = 0. If z_1 ≠ 0, then α_1 = 0 and u_1 = 0, so A_1 = 0. Either way K = A_0 ⊗ B_0 with
A_0 = [[α_0, 0], [−α_0 z_0, 1]] and B_0 = [[α_0⁻¹, 0], [z_0, 1]] = A_0⁻¹. ∎

- What the proof uses. Of the triangular form only its first step is used: the first row of each A_a is
  (α_a, 0, …, 0); the blocks A_a′ may be arbitrary, and the induction hypothesis is applied to K′ as it is (an
  observation of the independent check). Step 1 is the two-term bound of paper 17. The number of terms enters in three
  places: in (c) (three matrices need not have such a form), in the induction hypothesis, and in Step 2 (a sum
  of two terms that equals one term has B_1′ = 0 or A_1′ = 0 after a recombination). With more terms the statement
  fails even for triangular row factors: the truncated swap Σ_{k ≤ i} E_ik ⊗ E_ki has d(d+1)/2 terms and the code of
  all upper triangular matrices.

**Corollary 2 (the dual form: d(d−1)/2 terms).** Let d ≥ 2 and let K be an operator on d × d matrices with at most
d(d−1)/2 Kronecker terms, over any field. Then the code of K does not have codimension 2 (and not codimension 0),
and it has codimension 1 exactly when

        K = K_G :  X ↦ Xᵀ − tr(G⁻ᵀ X) G        for an invertible G.

K_G has exactly d(d−1)/2 terms, its code is {X : tr(G⁻ᵀ X) = 0}, the span of its row factors is {G Λ : Λ
alternating}, and the span of its column factors is {Λ G⁻¹ : Λ alternating}. All K_G are images of
K_1 : X ↦ Xᵀ − tr(X)·1 = Σ_{i<j} L_ij X L_ij (L_ij = E_ij − E_ji) under base changes: K_G = Σ_{i<j} (G L_ij) ⊗ (L_ijᵀ G⁻¹).

*Proof.* Suppose that the codimension r = rank(swap − K) is at most 2; r ≠ 0 because the swap has d² terms. Write K^R for the realignment of K (the
matrix Σ_a vec(A_a) vec(B_a)ᵀ); it is a linear involution on operators, it fixes the swap, and the number of Kronecker
terms of an operator is the rank of its realignment. So K′ = (swap − K)^R has exactly r terms, and
rank(swap − K′) = rank(K^R) is the number of terms of K, at most d(d−1)/2. So the code of K′ has
dimension at least d(d+1)/2, hence exactly that by the bound for two terms, and by Theorem 1 K′ = G ⊗ G⁻¹. So r = 1, and
K = swap − (G ⊗ G⁻¹)^R = swap − vec(G) vec(G⁻¹)ᵀ, which is K_G. Conversely rank(swap − K_G) = 1, and
K_G^R = swap − G ⊗ G⁻¹ has rank d(d−1)/2, the codimension of {X : G X symmetric}. The span of the row factors is
the image of K_G^R, which consists of the Xᵀ − G X G⁻ᵀ = (Yᵀ − Y) G⁻ᵀ with Y = G X; and Λ G⁻ᵀ = G (G⁻¹ Λ G⁻ᵀ). The
column factors are obtained in the same way from the transposed matrix swap − Gᵀ ⊗ G⁻ᵀ. For the last sentence,
Σ_{i<j} L_ij Z L_ij = Zᵀ − tr(Z)·1 for every Z (compare entries), and with Z = X G⁻ᵀ the operator
X ↦ Σ_{i<j} G L_ij X G⁻ᵀ L_ij is X ↦ G (G⁻¹ Xᵀ − tr(X G⁻ᵀ)) = K_G X. ∎

- That a code of codimension one or two needs at least d(d−1)/2 terms follows from the duality and the bound for
  two terms. What Theorem 1 adds: with at most that number the codimension 2 does not occur, and codimension 1
  occurs for one operator up to base change.
- For odd d alternating matrices are singular, so the span of the row factors of K_G contains no invertible
  matrix, and neither does the span of its column factors.
- Codimension 2 needs exactly one more term (not covered by the independent check). The
  operator K_1 + E_11 ⊗ E_11 : X ↦ Xᵀ − tr(X)·1 + x_11 E_11 has codimension 2, since swap minus it is
  X ↦ tr(X)·1 − x_11 E_11; and its realignment (swap − 1 ⊗ 1) + vec(E_11) vec(E_11)ᵀ has rank at most d(d−1)/2 + 1,
  hence exactly that by the corollary (script, part 5, for d ≤ 5). Its dual 1 ⊗ 1 − E_11 ⊗ E_11 has exactly two
  terms and the code of the symmetric matrices with x_11 = 0: with exactly two terms the largest code has
  dimension d(d+1)/2 − 1.

**Corollary 3 (three terms at d = 3, complete, over every field).** Let K be an operator on 3 × 3 matrices with
at most three Kronecker terms.
- (a) Its code has dimension at most 6, or exactly 8. Dimension 7 does not occur.
- (b) The dimension is 8 exactly for K = K_G, that is, up to base change, for the operator
  X ↦ Xᵀ − tr(X)·1 (paper 17, the remark on three terms at d = 3).
- (c) If the span of the row factors, or the span of the column factors, contains an invertible matrix, the code
  has dimension at most 6.

*Proof.* Corollary 2 with d(d−1)/2 = 3: codimension 0 and 2 do not occur, codimension 1 means K = K_G, and the
spans of the row and column factors of K_G consist of singular matrices. In (c) the spans do not depend on how
K is written: K_G has exactly three terms, so in every way of writing it with three terms the row factors span
the column space of K_G^R and the column factors its row space. ∎

## Checks

All exact; the script is self-contained (numpy, sympy; rustc for part 4).

- Parts 1 and 2: the block equations (1)–(4) for general A_a′ at d = 2, 3, 4, and, derived from them by substituting
  the two normal forms for m = 1, 2, 3: (2′), (4′), (ii), (3a), (3b), the forms wᵀ R w of Steps 3 and 4, R at ξ = 1, and
  A_0 B_0 = 1. All are identities of integer polynomials.
- Part 3: d = 2 completely over GF(2), GF(3), GF(5): the operators with at most two terms and a code of dimension
  3 number 6, 24, 120, each has one term, and they are exactly the G ⊗ G⁻¹.
- Part 4: for a fixed pair of row factors, all pairs (B_0, B_1): 3¹⁸ pairs for each of 17 pencils at d = 3 over
  GF(3), and 2³² pairs for each of 16 pencils at d = 4 over GF(2). In every case the pairs with a code of dimension
  at least d(d+1)/2 are exactly the (g_0 G⁻¹, g_1 G⁻¹) with G = g_0 A_0 + g_1 A_1 invertible over the field.
- Part 5: K_G for random G at d = 3, 4, 5, and the operator of codimension 2 with one more term.
- The independent check (12 November 2026) verified every line of the proof by hand, rederived the equations
  with its own symbolic code, and enumerated without symmetry assumptions of ours: two terms completely up to
  base change and recombination at d = 3 over GF(2), GF(3), GF(4), GF(5), GF(7) and at d = 4 over GF(2), GF(3); and
  Corollary 3 over GF(2) without the duality (of the 261,121 operators on 3 × 3 matrices with a code of dimension
  8 exactly 168 have at most three terms, and they are the K_G; all 11,319,595,350 operators with a code of
  dimension exactly 7 have at least four terms). It did not check paper 17's two-term bound, which is taken as
  given.

## What stays open

Three terms at d ≥ 4. The dual of a three-term operator with a code of dimension 11 at d = 4 has five terms, where
Theorem 1 says nothing.
