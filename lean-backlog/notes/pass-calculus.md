# Passes in the one-hop model: two counts, and the identity that needs both

Hans Brende and Claude Fable 5.2, 13 November 2026.

**Status:** short written proofs, not formalized; one identity, a table of ranks and a count of fixed points
checked by computation ([pass_layers.py](../tools/pass_layers.py), [pass_parity.py](../tools/pass_parity.py)).
Revised on 13 November 2026 after the [scope review](pass-calculus-scope-review.md) by GPT-6 Astra, whose
corrections are folded in; section 5.1 was added at the same time and has not been reviewed. Proposition 2 is
the reduction of Harvey and van der Hoeven read in the one-hop model; no novelty is claimed for it. The
question was the third attack of message C2 of the [chat](../../chat/fable-astra.md): which decoders a
schedule of boundedly many passes can produce.

## 0. Summary

A linear pipeline is K = K_t ∘ ⋯ ∘ K_1 on d × d matrices (row index first), and D(K) = dim{X : KX = Xᵀ}. Two kinds
of stage generate everything used below:

- **row-controlled**: C = Σ_r E_rr ⊗ U_r (row r is replaced by U_r applied to it); its *repertoire* is dim span{U_r};
- **uniform**: A ⊗ B (the rows are combined by A, and every row is mapped by B).

1. **Two counts.** Paper 17 counts the coset width of the uniform stages (Proposition "Stages"): row-controlled
   stages are free, and width t gives at most (d² + 2^t d)/2, for all codes. The Kronecker rank counts the
   repertoire of the row-controlled stages: uniform stages are free, whatever they cost on a tape, and
   repertoires M_1, …, M_a give D ≤ (1 − 1/(2 ΠM_i)) d² + d/2 over every field (Proposition 1). Over ℂ the bound is
   (½ + η)d² + C·d when the product of the weights of all stages stays bounded; a product stage A ⊗ B has rank one
   but weight ‖A‖‖B‖, so this needs a bound on the product stages too.
2. **Each count is defeated by one cheap or one free stage.** A row shear (row r shifted by r) is one
   linear-time operation of repertoire d. A DFT along the row index is uniform, of full coset width.
3. **The swap is five such stages** (Proposition 2): Xᵀ = N T⁻¹ (F⁻¹ ⊗ 1) M (F ⊗ 1) T⁻¹ X, with T the row shear, F the
   DFT, M the entrywise multiplication by ω^{tc} and N the reversal of the columns. Three row-controlled
   stages of repertoire d and two uniform stages; fewer than five alternating stages do not suffice
   (Proposition 3).
4. **Consequences.** (a) A machine is not forced into a bounded repertoire, so the fixed-term problem does not
   bound machines; it bounds pipelines whose row-dependent maps come from a bounded list, and for those the
   count is complete at the top end: exact transposition needs ΠM_i ≥ d², that is 2 log_M d stages, even if every
   product operator is free. (b) A pipeline of boundedly many stages above the pairing rate needs coset width
   about log₂ d (paper 17, all codes) and, over ℂ, a product of stage weights that grows with d. That the
   repertoire itself must grow is proved only at the top end; at the rate one half it is the fixed-term
   problem, open over ℂ too. (c) No
   quantity that is subadditive over stages and vanishes on both kinds of stage is positive on the swap, so
   the quantity asked for in Problem 9.5 of paper 17 has to charge the DFT along one index, which is a
   question about sequences, not matrices.

## 1. The rank count

kr(K) denotes the Kronecker rank of K with respect to rows ⊗ columns: the least M with K = Σ_{a ≤ M} A_a ⊗ B_a.

**Proposition 1 (every field).**
(a) kr(K₂K₁) ≤ kr(K₂) kr(K₁); kr(A ⊗ B) ≤ 1; kr(Σ_r E_rr ⊗ U_r) = dim span{U_r}; kr(swap) = d².
(b) D(K) ≤ (1 − 1/(2 kr(K))) d² + d/2 for K ≠ 0.
(c) So for a pipeline with stages of Kronecker rank M_1, …, M_t: it transposes every matrix only if ΠM_i ≥ d², and
    D ≤ (1 − 1/(2 ΠM_i)) d² + d/2 in general.
(d) Over ℂ, if stage i has projective weight γ_i, then D ≤ (½ + η)d² + C(η, Πγ_i) d (item A4 of the backlog; the
    weight is submultiplicative).

*Proof.* (a) Products of sums of tensors; the blocks of a row-controlled operator; the d² matrices E_sr of
swap = Σ E_sr ⊗ E_rs are independent. (b) Theorem FL of paper 17 with any complete flag: g(i) ≤ min(d, M i), and
Σ_i min(d, M i) ≤ d² − d²/(2M) + d/2. ∎

- Ranks of stages: any product operator 1 (a scan (1 − σ)⁻¹ ⊗ 1 over the rows, a DFT along the rows, any
  permutation of the rows or of the columns); the exchange of one binary digit of the row address with one of
  the column address 4; a row-controlled stage with M distinct blocks at most M; a row shear d.
- The recursion by digit exchanges has t = log₂ d stages of rank 4, so (c) is attained: among pipelines whose
  stages have bounded Kronecker rank, with every product operator free, the folklore count is optimal for
  exact transposition, over every field. (A digit exchange is not a row-controlled stage; tightness inside
  the narrower class of row-controlled and uniform stages is not claimed.) For rates the statement is weak (rate 1 − ε needs ΠM_i ≥ 1/(2ε)); the
  half bound for such pipelines is (d) over ℂ and the fixed-term problem over finite fields.
- The intermediate stores may be any tensor products V_i ⊗ W_i; the statements use only the two ends.

## 2. The swap in five stages

Let F have a primitive d-th root of unity ω, and d ≠ 0 in F. Index positions by (r, c).

- T: the entry at (r, c) moves to (r, c + r) (row shear; row-controlled with blocks σ^r).
- U: the entry at (r, c) moves to (r + c, c) (column shear).
- N: the entry at (r, c) moves to (r, −c).
- F ⊗ 1: (Y)_{t,c} = Σ_r ω^{tr} X_{r,c}; M: multiplication of the entry (t, c) by ω^{tc} (row-controlled with blocks Ω^t,
  Ω = diag(ω^c)).

**Proposition 2.** N T⁻¹ U T⁻¹ is the transposition, and U = (F⁻¹ ⊗ 1) M (F ⊗ 1). Hence

  Xᵀ = N T⁻¹ (F⁻¹ ⊗ 1) M (F ⊗ 1) T⁻¹ X.

*Proof.* As maps of positions, T⁻¹: (r, c) ↦ (r, c − r), then U: ↦ (c, c − r), then T⁻¹: ↦ (c, −r), then N: ↦ (c, r). For
the second statement, ((F ⊗ 1)X)_{t,c} = Σ_r ω^{tr} X_{r,c}; after M it is Σ_r ω^{t(r+c)} X_{r,c}; and the inverse transform at
(r′, c) is (1/d) Σ_t ω^{−tr′} Σ_r ω^{t(r+c)} X_{r,c} = X_{r′−c, c} = (UX)_{r′,c}. ∎

- Checked numerically for d = 3, 4, 5, 8, 9 (error below 2·10⁻¹⁴).
- This is the reduction of transposition to DFTs (Harvey and van der Hoeven) in the notation of the one-hop
  model. On a tape the three row-controlled stages cost O(L) operations of the coefficient ring (a shift of
  each row, a multiplication of each entry by a power of ω computed incrementally); the cost is in F ⊗ 1, a
  DFT of length d whose coefficients are whole rows, that is one cyclic convolution of the whole tape with
  a kernel supported on the multiples of d (Bluestein).
- In the index plane the transposition is a rotation followed by a reflection, and a rotation is three
  shears. A row-major tape makes the shears along the rows cheap; the shear in the other direction is the
  conjugate of a cheap one by the Fourier transform along the rows. The same holds one level down: the DFT
  is the rotation of the time–frequency plane, multiplication by a chirp is the cheap shear, and convolution
  with a chirp is the other one.

**Proposition 3 (five stages are needed).** For d ≥ 2 the swap is not a product of at most four stages that
alternate between row-controlled operators and operators A ⊗ 1, all intermediate arrays being d × d. (With d²
intermediate rows three stages suffice: spread row j over the rows (i, j), apply E_ji in row (i, j), and add up
over j; pointed out by GPT-6 Astra.) (Factors 1 ⊗ B are row-controlled and adjacent
row-controlled stages merge, so this covers all products of at most four stages of the two kinds.)

*Proof.* The block (r, s) of the swap is E_sr = e_s e_rᵀ. For A₂ C A₁ the blocks are Σ_t A²_{rt} A¹_{ts} U_t, in a space of
dimension at most d, and the d² blocks of the swap are independent. For C₂ (A ⊗ 1) C₁ the blocks are A_{rs} U_r V_s; the
row spaces force V_s to be invertible and the column spaces force U_r to be, and then the block has rank d. For
(A₂ ⊗ 1) C₂ (A₁ ⊗ 1) C₁ the blocks are W_{rs} U_s with W_{rs} in the span of the d blocks of C₂; U_s is invertible as before,
and the matrices W_{rs} = e_s e_rᵀ U_s⁻¹ are d² independent matrices. For C₂ (A₂ ⊗ 1) C₁ (A₁ ⊗ 1) the blocks are U_r W′_{rs} with
W′_{rs} in the span of the d blocks of C₁; U_r is invertible, and the matrices U_r⁻¹ e_s e_rᵀ are independent. ∎

**Corollary 4.** Let Q be a function on operators with Q(K₂K₁) ≤ Q(K₂) + Q(K₁) that vanishes on row-controlled
operators and on product operators. Then Q(swap) = 0 over every field with a primitive d-th root of unity.

- The coset width of paper 17 vanishes on row-controlled operators and is log₂ d on F ⊗ 1. log kr vanishes on
  product operators and is log₂ d on a shear. Each is attained by digit exchanges inside its own class, and
  the identity of Proposition 2 uses both resources at full strength, three times and twice.

## 3. Ranks at every split of the address

For d = 2^k a cell of the row-major tape has an address of 2k bits. For 1 ≤ m < 2k let kr_m(K) be the Kronecker
rank with respect to the top 2k − m bits against the low m bits (m = k is rows against columns). It is
submultiplicative at every m.

Computed for d = 4 and d = 8 (`pass_layers.py`; m = 1, …, 2k − 1):

| Operator | d = 8 | Pattern |
|---|---|---|
| swap | 4, 16, 64, 16, 4 | 4^{min(m, 2k − m)} |
| column shear U | 2, 4, 8, 4, 2 | 2^{min(m, 2k − m)} |
| row shear T | 3, 7, 8, 4, 2 | at most 2 · 2^{min(m, 2k − m)} |
| prefix sum over the rows | 1, 1, 1, 2, 2 | at most 2 |
| perfect unshuffle of the rows | 1, 1, 1, 4, 4 | at most 4 |
| DFT along the rows | 1, 1, 1, 4, 4 | 4^{min(m − k, 2k − m)} for m > k |

- At every split the swap has the square of the rank of the column shear, and the row shear has at least
  that rank. So by this profile one linear-time operation, the row shear, does half of the swap at all scales
  at once: the profile is not the quantity of Problem 9.5 either. It does separate what the coset width
  cannot: a scan and an unshuffle are cheap at every contiguous split, and a DFT is maximal inside its own
  index. For a scan this holds in every order by permuted digits (the comparison of two addresses has rank at
  most k + 1 across any set of digits). For an unshuffle it does not hold across arbitrary sets of digits: a
  cyclic permutation of four address bits has rank 16 across {0, 2} | {1, 3}.
- The profiles of the two shears differ (3, 7, 8, 4, 2 against 2, 4, 8, 4, 2), and the cheap one dominates the one
  that is as hard as the transposition. So no aggregate of these ranks that increases in every coordinate can
  charge the column shear more than the row shear; other functions of the profile are not excluded. What
  separates the two is whether the control is in the high bits of the address or in the low ones.

## 4. What this says about the bridge to machines

1. The premise of the third attack was that a machine might be forced into a bounded repertoire. It is not: a
   counter gives row-dependent shifts, one linear-time operation of repertoire d. What a bounded-repertoire
   theorem would exclude is pipelines whose row-dependent maps span a space of bounded dimension, with
   product operators in between. What is proved: the top end over every field (Proposition 1(c)), and the
   half bound over ℂ when the weights of all stages, product stages included, have a bounded product (a
   unitary DFT has weight one; a prefix sum does not). Without the bound on the weights the half bound is the
   fixed-term problem.
2. For whole-row stages the bridge is already in paper 17 (Proposition "Stages" and the proposition on
   expanding row relations): boundedly many forward passes realize row relations for which the order method
   stays above one half, with row maps that are not affine (given the strings that mark the maps; their
   generation in linear time is left open there). Together with 1, a family that no count reaches is:
   expanding row maps with blocks of unbounded repertoire (shears and their compositions with a bounded
   list). That is Problem 9.4(c), and with diagonal blocks the stronger form of 9.4(b); it is the family of
   the second attack. It is a target, not a proved description of everything that is left.
3a. The operation counts of section 2 are counts of operations of the coefficient ring. Whether a
   multiplication by a root of unity or by a chirp is linear in bit time on a tape of fixed alphabet is part
   of the question, not settled here.
3. A count for all scales has to be found for the DFT of length d along one index: subadditive over the
   operations on a sequence, large at every scale for the DFT, and small for a scan, an unshuffle, a local map
   and a multiplication by a chirp. The rank profile of section 3 has the first three properties and fails the
   last: a chirp has half the profile of the DFT at every split (the cross term ω^{2^m t_h t_l}).

## 5. Which sheared relations have a parity

The other agent asked which family of sheared one-class relations to compute first. The answer needs the
exact place where the trace argument stops.

Take helper maps that are affine with integer data, g_m(c, r) = (a_m r + u_m, c + b_m r + v_m), a_m = ±1, reduced
modulo a prime d. The linear part is M_m = [[0, a_m], [1, b_m]] ∈ GL₂(ℤ): P T^{b} for a = 1 and S T^{b} for a = −1, where
P = [[0, 1], [1, 0]], S = [[0, −1], [1, 0]], T = [[1, 1], [0, 1]].

GL₂(ℤ) has exactly three characters of order two: the determinant; ε, the sign of the permutation that the
reduction modulo 2 induces on the three nonzero vectors of 𝔽₂²; and their product. On the generators:
det = −a, and ε = −1 exactly when b is even (the reduction is then a transposition, otherwise a 3-cycle).

**Proposition 5.** Suppose one of the following holds: (i) every a_m = 1; (ii) every b_m is even; (iii) b_m is
odd when a_m = 1 and even when a_m = −1. Then, over ℂ, every linear code on the relation whose coefficients
have absolute value at most κ has dimension at most (½ + o(1)) d² as d → ∞ through the primes, with w, κ and the
b_m fixed. More generally it is enough that some character of order two of the subgroup generated by the
linear parts is −1 on every generator.

*Proof.* A character χ as above is −1 on every generator and on every inverse, so a word W of odd length k in
the g_m^{±1} has a linear part M_W ≠ 1 over ℤ. Its entries are at most (2 + max|b_m|)^k, so for
k ≤ k₀ = log d / log(2 + max|b_m|) − 1 it is not the identity modulo d, and W has at most d fixed points among the
d² positions. Let T = Σ_m D_m Π_m with diagonal D_m of entries at most κ and Π_m the permutation of the positions
by g_m; the code is contained in ker(1 − T), ‖T‖ ≤ wκ, and for odd k ≤ k₀ every word of length k in T, T* has a
trace of absolute value at most (wκ)^k d. The proof of A3 of the backlog (the code is counted by the eigenvalues
of the Hermitian part that are at least 1, and an odd polynomial bounds their number through odd traces) uses only
these two facts: choose the polynomial first, then d large for its degree. This variant is not among the Lean
statements. ∎

- The three conditions are sufficient, not necessary (GPT-6 Astra): {P, S T³} generates an infinite dihedral
  group with a character that is −1 on both, and {P, S T³, S T⁶} has one through the reduction modulo 3, although
  none of the three characters of GL₂(ℤ) works. A relation of odd length is certain when (a, b) = (−1, −1) is
  present: that linear part M has 1 + M + M² = 0, so every affine map with it has order three. The family
  without a parity used below (pairing, S T⁻¹, S T²) is of this kind.
- The statement is asymptotic. Modulo an odd prime p the parity does not survive for long words (every
  affine S T² has p-th power the identity), and the cut-off k₀ is below 1 at p = 7, 11, 13. It predicts nothing
  about exact values at such sizes.
- For helper maps that are not affine and have no structure the same count applies with a random-like
  number of fixed points, so the open case over ℂ is the algebraic one with relations of odd length, not
  row-dependent offsets as such. Item (ii) of message C2 of the chat should be read with this.
- Over a finite field nothing of this is available in either family.
- **The first computation** therefore compares two families at the same d and window: one with a parity, say
  the pairing with S T², S T⁻², and one without, the pairing with S T⁻¹, S T². Proposition 5 predicts no gain
  for the first over ℂ with bounded coefficients; a difference between the two would be a sign that the
  relations of odd length carry a code.

### 5.1 Without a parity: the bound holds below a threshold on the coefficients

Proposition 5 is the case θ = 0 of a general statement. Let the relations have n positions, n → ∞, with at most w
helpers per position and at most w positions helped by each; a step is a helper edge in either direction.
Let c_k be the limit superior of (number of closed walks of length k)/n, and θ = limsup over odd k of c_k^{1/k}; so
0 ≤ θ ≤ 2w.

**Proposition 6 (ℂ).** Linear codes on these relations whose coefficients have modulus at most κ have rate
½ + o(1) whenever κθ < 2.

*Proof.* T = Σ_m D_m Π_m, H = (T + T*)/2, and D ≤ n₊, the number of eigenvalues of H that are at least 1. A word of
length k in T, T* has a trace of modulus at most κ^k times the number of closed walks that follow it, so
|tr H^k| ≤ (κ/2)^k · #closed walks of length k. Let μ be a weak limit of the normalized spectral measures of H,
supported in [−wκ, wκ]. Its odd moments are bounded by r^k for every r > κθ/2, so the odd signed measure μ(x) − μ(−x)
has moments of that growth and is supported in [−κθ/2, κθ/2] (a compactly supported signed measure vanishes
outside the radius of growth of its moments). If κθ/2 < 1, then μ[1, ∞) = μ(−∞, −1] ≤ ½, and limsup n₊/n ≤ μ[1, ∞). ∎

- θ = 0 when odd closed walks of each length are o(n): locally bipartite relations (paper 4, Theorem A), the
  affine families with a parity, relations with random maps.
- For helper maps that generate a group Γ acting with few fixed points, θ ≤ 2w·ρ, where ρ is the spectral
  radius of the random walk on Γ with these steps (Kesten). It is below 2w exactly when Γ is not amenable.
- For the family without a parity of the computation (pairing, S T⁻¹, S T²): closed walks per position at
  p = 101 are 2.3, 77, 2042 for k = 3, 5, 7, so θ is about 5.2 to 5.7 and the bound holds for κ below about 0.36.
  A code needs the moduli of a row to sum to at least 1, so κ ≥ 1/3: the proposition covers a narrow band, and
  coefficients of modulus near 1 are open.
- The proof above is not quantitative (a weak limit), and an odd polynomial close to the clipping function
  cannot be small on the disc of radius r. A polynomial certificate exists all the same. By duality, n₊/n is
  at most ½ + η + Σ_k |q_k| (κ/2)^k F_k/n for every odd polynomial q with ½ − η ≤ q ≤ ½ + η on [1, wκ] and |q| ≤ ½ + η on
  [0, 1), where F_k is the number of closed walks of length k. Take q(x) = x p(x²) with p uniformly close to 0 on
  a disc of radius above (κθ/2)² and to a continuous function on [0, (wκ)²] that vanishes near 0 and equals
  ½ y^{−1/2} on [1, (wκ)²] (Mergelyan's theorem); the coefficient sum is then small by Cauchy's estimates. So
  the counts F_k of a finite instance give a rigorous finite bound by linear programming (the finite test
  proposed by GPT-6 Astra), with no rate of convergence known.
- A code above the pairing rate over ℂ with bounded coefficients therefore needs odd closed walks through a
  positive share of the positions, growing at a rate θ > 2/κ.

**Two thresholds (correction, 13 November 2026, after a theorem of GPT-6 Astra).** Even moments bound the code
directly: D ≤ n₊ ≤ tr H^{2k} ≤ (κ/2)^{2k} · #closed walks of length 2k. So if Λ is the growth rate of the closed walks of
even length per position, there is **no code of positive rate when κΛ < 2**, and Proposition 6 has content only
where θ < Λ, that is where odd closed walks grow more slowly than even ones (θ = 0 with a parity). For the
family pairing, S T⁻¹, S T² the other agent proves Λ ≤ √(32 + 2√3) from the regular representation (two of the
products of generators are free), hence rate zero for κ < 0.3358, with an explicit finite bound
(`shear-small-coefficient-bound.md` in the same folder of the papers repository). Three statements above
need this correction: the estimate "θ about 5.2 to 5.7" from counts at one prime bounds nothing in the limit
(the limits in the length and in p cannot be exchanged), and θ ≥ 2√5 for this family, so the criterion κθ < 2
cannot reach κ > 1/√5; the threshold is strict only when loops have vanishing density (T = 1 has rate one at
κθ = 2); and what remains open for the family without a parity is every κ from about 0.34 up, in particular
κ = 1.

## 6. Open

- Is five the least number of stages for every pattern (Proposition 3 excludes four)? Not needed.
- A pipeline with two row-controlled stages of full repertoire and uniform stages: can it transpose a set of
  rate above one half? The rank count allows it (d · d = d²), Proposition 3 excludes the exact swap in four stages.
