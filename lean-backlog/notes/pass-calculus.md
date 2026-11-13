# Passes in the one-hop model: two counts, and the identity that needs both

Hans Brende and Claude Fable 5.2, 13 November 2026.

**Status:** short written proofs, not refereed and not formalized; one identity, a table of ranks and a count
of fixed points checked by computation ([pass_layers.py](../tools/pass_layers.py),
[pass_parity.py](../tools/pass_parity.py)). Proposition 2 is the reduction of Harvey and van der Hoeven read
in the one-hop model; no novelty is claimed for it. The question was the third attack of message C2 of the
[chat](../../chat/fable-astra.md): which decoders a schedule of boundedly many passes can produce.

## 0. Summary

A linear pipeline is K = K_t ∘ ⋯ ∘ K_1 on d × d matrices (row index first), and D(K) = dim{X : KX = Xᵀ}. Two kinds
of stage generate everything used below:

- **row-controlled**: C = Σ_r E_rr ⊗ U_r (row r is replaced by U_r applied to it); its *repertoire* is dim span{U_r};
- **uniform**: A ⊗ B (the rows are combined by A, and every row is mapped by B).

1. **Two counts.** Paper 17 counts the coset width of the uniform stages (Proposition "Stages"): row-controlled
   stages are free, and width t gives at most (d² + 2^t d)/2, for all codes. The Kronecker rank counts the
   repertoire of the row-controlled stages: uniform stages are free, whatever they cost on a tape, and
   repertoires M_1, …, M_a give D ≤ (1 − 1/(2 ΠM_i)) d² + d/2 over every field (Proposition 1), and
   (½ + η)d² + C·d over ℂ when the blocks have bounded norm.
2. **Each count is defeated by one cheap or one free stage.** A row shear (row r shifted by r) is one
   linear-time operation of repertoire d. A DFT along the row index is uniform, of full coset width.
3. **The swap is five such stages** (Proposition 2): Xᵀ = N T⁻¹ (F⁻¹ ⊗ 1) M (F ⊗ 1) T⁻¹ X, with T the row shear, F the
   DFT, M the entrywise multiplication by ω^{tc} and N the reversal of the columns. Three row-controlled
   stages of repertoire d and two uniform stages; fewer than five alternating stages do not suffice
   (Proposition 3).
4. **Consequences.** (a) A machine is not forced into a bounded repertoire, so the fixed-term problem does not
   bound machines; it bounds pipelines whose row-dependent maps come from a bounded list, and for those the
   count is complete at the top end: exact transposition needs ΠM_i ≥ d², that is 2 log_M d stages, even if every
   product operator is free. (b) A pipeline of boundedly many stages above the pairing rate must combine
   row-dependent maps of unbounded repertoire with uniform operations of coset width about log₂ d. (c) No
   quantity that is subadditive over stages and vanishes on both kinds of stage is positive on the swap, so
   the quantity asked for in Problem 9.5 of paper 17 has to charge the DFT along one index, which is a
   question about sequences, not matrices.

## 1. The rank count

kr(K) denotes the Kronecker rank of K with respect to rows ⊗ columns: the least M with K = Σ_{a ≤ M} A_a ⊗ B_a.

**Proposition 1 (every field).**
(a) kr(K₂K₁) ≤ kr(K₂) kr(K₁); kr(A ⊗ B) ≤ 1; kr(Σ_r E_rr ⊗ U_r) = dim span{U_r}; kr(swap) = d².
(b) D(K) ≤ (1 − 1/(2 kr(K))) d² + d/2.
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
  exact transposition, over every field. For rates the statement is weak (rate 1 − ε needs ΠM_i ≥ 1/(2ε)); the
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
alternate between row-controlled operators and operators A ⊗ 1. (Factors 1 ⊗ B are row-controlled and adjacent
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

- At every split the swap has the square of the rank of a shear. So by this profile one linear-time
  operation, the row shear, does half of the swap at all scales at once: the profile is not the quantity of
  Problem 9.5 either. It does separate what the coset width cannot: scans and unshuffles are cheap at every
  split, in every order by permuted digits (the comparison of two addresses has rank at most k + 1 across
  any set of digits), and a DFT is maximal inside its own index.
- The row shear and the column shear have the same profile, and the second is as hard as the transposition.
  So no function of this profile separates cheap from expensive stages; what separates them is whether the
  control is in the high bits of the address or in the low ones.

## 4. What this says about the bridge to machines

1. The premise of the third attack was that a machine might be forced into a bounded repertoire. It is not: a
   counter gives row-dependent shifts, one linear-time operation of repertoire d. What a bounded-repertoire
   theorem (the complex one, or the fixed-term problem over a finite field) excludes is pipelines whose
   row-dependent maps come from a bounded list, with arbitrary product operators in between, DFTs included.
2. For whole-row stages the bridge is already in paper 17 (Proposition "Stages" and the proposition on
   expanding row relations): boundedly many forward passes realize row relations for which the order method
   stays above one half, with row maps that are not affine. Together with 1, the family that no count
   reaches is: expanding row maps with blocks of unbounded repertoire (shears and their compositions with a
   bounded list). That is Problem 9.4(c), and with diagonal blocks the stronger form of 9.4(b); it is the
   family of the second attack.
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
are bounded by κ has dimension (½ + o(1)) d² as d → ∞ through the primes, with w, κ and the b_m fixed.

*Proof.* A character χ as above is −1 on every generator and on every inverse, so a word W of odd length k in
the g_m^{±1} has a linear part M_W ≠ 1 over ℤ. Its entries are at most (2 + max|b_m|)^k, so for
k ≤ k₀ = log d / log(2 + max|b_m|) − 1 it is not the identity modulo d, and W has at most d fixed points among the
d² positions. Let T = Σ_m D_m Π_m with diagonal D_m of entries at most κ and Π_m the permutation of the positions
by g_m; the code is contained in ker(1 − T), ‖T‖ ≤ wκ, and for odd k ≤ k₀ every word of length k in T, T* has a
trace of absolute value at most (wκ)^k d. The proof of A3 of the backlog (the code is counted by the eigenvalues
of the Hermitian part that are at least 1, and an odd polynomial bounds their number through odd traces) uses only
these two facts, with a polynomial of degree at most k₀. This variant is not among the Lean statements. ∎

- Where no such character exists the argument gives nothing: with (a, b) = (−1, −1) the map has order three,
  and in general the generators satisfy relations of odd length (S T^{b} with b odd reduces to a 3-cycle).
  Examples without a parity: the pairing together with S T⁻¹; any set that contains S T^{b}, S T^{b′} with b odd
  and b′ even together with the pairing.
- For helper maps that are not affine and have no structure the same count applies with a random-like
  number of fixed points, so the open case over ℂ is the algebraic one with relations of odd length, not
  row-dependent offsets as such. Item (ii) of message C2 of the chat should be read with this.
- Over a finite field nothing of this is available in either family.
- **The first computation** therefore compares two families at the same d and window: one with a parity, say
  the pairing with S T², S T⁻², and one without, the pairing with S T⁻¹, S T². Proposition 5 predicts no gain
  for the first over ℂ with bounded coefficients; a difference between the two would be a sign that the
  relations of odd length carry a code.

## 6. Open

- Is five the least number of stages for every pattern (Proposition 3 excludes four)? Not needed.
- A pipeline with two row-controlled stages of full repertoire and uniform stages: can it transpose a set of
  rate above one half? The rank count allows it (d · d = d²), Proposition 3 excludes the exact swap in four stages.
