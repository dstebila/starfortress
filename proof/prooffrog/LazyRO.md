# Lazy Random-Oracle Helpers: `HashInputPacking`, `LazyROTwoViewsExcluded`, `LazyROTwoViewsExcludedProgrammed`

This note explains three building blocks that show up whenever a proof needs
to treat one random oracle as if it were two. It is aimed at a
cryptographer who is familiar with game-hopping proofs but not with the
internals of ProofFrog.

The idea, in paper terms, is the standard *lazy sampling* argument: a random
oracle $H$ can equivalently be answered by a table that is filled in on
demand. These helpers do exactly that, but they also support a very common
proof pattern in which **the adversary has two views onto the same hash
oracle**:

1. a *direct* view `Direct(m)`, where $m$ is a raw hash input, and
2. an *indirect* view `Indirect(q)`, answered as $H(\mathsf{Pack}(\mathsf{st}, q))$,

where $\mathsf{Pack}$ is an injective packing of a (state, query) pair into
the hash input space, supplied by the proof designer. Decryption /
decapsulation oracles typically look like this: given a ciphertext $c$, the
oracle computes a session key $H(\dots \| c \| \dots)$ — the adversary
never sees the full hash input directly, only "what is $H$ on this
ciphertext?".

The three pieces fit together as follows:

- `HashInputPacking` — the **interface**: a primitive the helpers use to
  talk to $\mathsf{Pack}$ abstractly. You instantiate it with a scheme
  that realises the actual hash-input construction of your protocol.
- `LazyROTwoViewsExcluded` — the **clean lazy-sampling lemma**: both views
  are answered by a single random function; switching to two
  cross-patched lazy maps is indistinguishable. The `Excluded` suffix
  signals that `Indirect` forbids one distinguished query $q^\ast$ (the
  caller supplies it in `Initialize`).
- `LazyROTwoViewsExcludedProgrammed` — the same thing, but with one hash
  input *programmed* to a caller-chosen value. This is what you use when
  one specific $H(m^*)$ has to be a fresh, externally chosen string
  (e.g., the challenge shared secret).

Both helpers are **statistical** (unconditional): no cryptographic
assumption is consumed. Injectivity of $\mathsf{Pack}$ alone is enough.

The `Excluded` in the helper names leaves `LazyROTwoViews` and
`LazyROTwoViewsProgrammed` free for a future no-$q^\ast$ sibling variant.

---

## 1. `HashInputPacking`

```frog
Primitive HashInputPacking(Set StateSpace, Set QuerySpace, Int M) {
    Set State = StateSpace;
    Set Query = QuerySpace;
    Int M = M;

    deterministic injective BitString<M> Pack(State st, Query q);
}
```

LaTeX analog:

$$
\mathsf{Pack} : \mathsf{State} \times \mathsf{Query} \to \{0,1\}^M,
\qquad
\text{for each fixed } \mathsf{st}, \; q \mapsto \mathsf{Pack}(\mathsf{st}, q)
\text{ is injective.}
$$

The two modifiers matter to the engine:

- `deterministic` — same inputs always produce the same output (so the
  engine can treat `Pack(st, q)` as a value, not a fresh sample).
- `injective` — distinct $q$'s map to distinct outputs (at a fixed
  $\mathsf{st}$). This is what makes the lemmas unconditional.

In your proof you never use `HashInputPacking` as a concrete object: you
define a *scheme* that extends this primitive and realises `Pack` with the
actual hash-input construction of your protocol. For UG-KEM, the packing
wraps the ciphertext with the rest of the KDF input — see
`schemes/UGHashEncoding.scheme`.

---

## 2. `LazyROTwoViewsExcluded`

Setup. The helper is parameterised by a `HashInputPacking` $P$ and an
output length $n$. It exposes three oracles:

- `Initialize(st, q*)` — fix the packing state and one "excluded" query
  $q^\ast$.
- `Direct(m)` — $H(m)$ on any raw input.
- `Indirect(q)` — if $q = q^\ast$, return $\bot$; else return
  $H(\mathsf{Pack}(\mathsf{st}, q))$.

### Honest side (eager)

```frog
Function<BitString<P.M>, BitString<n>> RF;    // sampled in Initialize

Indirect(q): if q == q* return None; else return RF(Pack(st, q))
Direct(m):   return RF(m)
```

LaTeX:

$$
\mathcal{G}_{\text{Honest}} :\quad
H \twoheadleftarrow \mathsf{Funcs}(\{0,1\}^M, \{0,1\}^n);
\qquad
\mathsf{Direct}(m) = H(m);
\qquad
\mathsf{Indirect}(q) = H(\mathsf{Pack}(\mathsf{st}, q))\ \text{for}\ q \ne q^\ast.
$$

### Lazy side (on demand, two tables)

Two lazy maps, one per view, with **cross-patching**:

```frog
Direct(m):
    if m in HT: return HT[m]
    for (q, y) in QT:
        if Pack(st, q) == m:          // route a prior Indirect hit into HT
            HT[m] = y; return y
    sample r; HT[m] = r; return r

Indirect(q):
    if q == q*: return None
    if q in QT: return QT[q]
    m = Pack(st, q)
    for (m', y) in HT:
        if m' == m:                   // route a prior Direct hit into QT
            QT[q] = y; return y
    sample s; QT[q] = s; return s
```

### Why the two sides are equivalent

The `Honest` side answers both views from the same random function $H$,
so in particular $\mathsf{Indirect}(q)$ and $\mathsf{Direct}(\mathsf{Pack}(\mathsf{st}, q))$ always
agree. On the `Lazy` side they also agree, because every new entry is
cross-checked against the other table under $\mathsf{Pack}$. Injectivity
is what guarantees the cross-check cannot produce a false alias: if
$\mathsf{Pack}(\mathsf{st}, q) = \mathsf{Pack}(\mathsf{st}, q')$, then $q = q'$.

Intuitively,

$$
\Pr[\mathcal{A}^{\mathsf{Honest}} = 1] = \Pr[\mathcal{A}^{\mathsf{Lazy}} = 1].
$$

It is a statistical (in fact *information-theoretic*) statement about how a
random function can be simulated with two views.

---

## 3. `LazyROTwoViewsExcludedProgrammed`

Identical to `LazyROTwoViewsExcluded`, with one addition: `Initialize`
takes an extra pair $(m^\ast, y^\ast)$ and the `Honest` side returns
$H(m^\ast)$ as its initialisation output, while the `Lazy` side simply
returns $y^\ast$ and pretends that $H(m^\ast) = y^\ast$.

On the `Lazy` side, `Direct` has an extra priority branch:

```frog
Direct(m):
    if m == mProgrammed: return yProgrammed   // <-- programmed point
    if m in HT: return HT[m]
    ...  // (same cross-patching as above)
```

LaTeX:

$$
\mathcal{G}_{\text{Honest}}^{\text{prog}} :\quad
H \twoheadleftarrow \mathsf{Funcs}, \quad y^\ast := H(m^\ast);
\qquad
\mathcal{G}_{\text{Lazy}}^{\text{prog}} :\quad
y^\ast \twoheadleftarrow \{0,1\}^n,\ H(m^\ast) \text{ defined to be } y^\ast.
$$

Again, the equivalence is unconditional: by injectivity of $\mathsf{Pack}$, no
`Indirect(q)` with $q \ne q^\ast$ can induce a hash input equal to $m^\ast$
(provided the caller chose $m^\ast$ outside the image of $\mathsf{Pack}(\mathsf{st}, \cdot)$
at points other than $q^\ast$; this is the usual setup in applications).

`LazyROTwoViewsExcludedProgrammed` is typically used at the *start* of the
bad-event portion of a proof; `LazyROTwoViewsExcluded` is used at the
*end* to switch back to the clean form.

---

## 4. How to use them in a proof

Both helpers are meant to be applied as assumption hops, so each use
follows the standard four-step pattern (see `CLAUDE.md`, "Standard
four-step pattern"):

```
1. G_A                                  // equiv to Helper.Side1 compose R
2. Helper.Side1 compose R                // equiv (bridge)
3. Helper.Side2 compose R                // by assumption  <-- the real content
4. G_B                                   // equiv to Helper.Side2 compose R
```

Here `R` is a **wrapper reduction** whose job is to translate between the
adversary's interface (which typically has a bunch of KEM/group-specific
setup in `Initialize`) and the helper's very generic interface (which is
parameterised only by the packing $P$ and the output length $n$).

In the Starfortress UG-KEM-CCA proof, these wrappers are
`R_Wrap_Prog` (for `LazyROTwoViewsExcludedProgrammed`) and `R_Wrap_NoAbort`
(for `LazyROTwoViewsExcluded`). Their `Initialize` sets up the KEM and
nominal-group state, then calls `challenger.Initialize(...)`; their `Hash`
and `Decaps` oracles just forward to `challenger.Direct` and
`challenger.Indirect`.

### A simplified example

Suppose we have a toy encryption scheme where decryption computes
$K := H(c \| \mathsf{sk})$ and you want to prove IND-CCA in the ROM by
replacing the challenge $K^\ast$ with a fresh random string. Structure the
proof like this:

Let the packing be
$\mathsf{Pack}(\mathsf{sk}, c) := c \| \mathsf{sk}$ (injective in $c$ for fixed $\mathsf{sk}$).
Let $m^\ast := c^\ast \| \mathsf{sk}$, and let $q^\ast := c^\ast$ be the
challenge ciphertext.

1. **Intro `LazyROTwoViewsExcludedProgrammed`.** Wrap the CCA game into a
   reduction $R$ that forwards `Decaps(c)` to `challenger.Indirect(c)` and
   every RO query to `challenger.Direct(m)`. Hop:

   - $G_0 = \mathsf{INDCCA}^{\text{Real}}$
   - $\mathsf{LazyROTwoViewsExcludedProgrammed}.\mathsf{Honest} \circ R$ — equiv to $G_0$
     (both answer from the same $H$, with $K^\ast = H(m^\ast)$).
   - $\mathsf{LazyROTwoViewsExcludedProgrammed}.\mathsf{Lazy} \circ R$ — by assumption; now
     $K^\ast$ is a fresh $y^\ast$, and the two oracles are on lazy maps.

2. **Do the bad-event analysis.** Between the Lazy forms, it is easy to argue
   that if the adversary never queries $\mathsf{Direct}$ on the programmed
   input, its view is independent of $K^\ast$. Typically this is where a
   computational assumption (SDH, DDH, ...) is applied via a separate
   reduction.

3. **Wind back with `LazyROTwoViewsExcluded`.** After the bad-event hop,
   $K^\ast$ is uniformly random and independent, so the programmed branch is
   no longer needed. Use `LazyROTwoViewsExcluded` to collapse the two lazy
   maps back into a single eager random function, and then unwrap:

   - $\mathsf{LazyROTwoViewsExcluded}.\mathsf{Lazy} \circ R'$
   - $\mathsf{LazyROTwoViewsExcluded}.\mathsf{Honest} \circ R'$ — by assumption.
   - $G_n = \mathsf{INDCCA}^{\text{Random}}$.

Concretely in the Starfortress proof, these four applications occur as
steps 8–13 of the main games list (`LazyROTwoViewsExcludedProgrammed` on the
left, SDH in the middle, `LazyROTwoViewsExcluded` on the right); see the
commented sequence at the top of `UG-KEM-CCA-SDH.proof`.

### Practical tips

- **Pick the packing carefully.** `Pack(st, q)` must be injective for
  *every* state $\mathsf{st}$ the reduction ever produces. The easiest way
  to achieve this is to make $\mathsf{Pack}$ contain $q$ as a contiguous
  slice of its output, so $q$ can be recovered by projection.
- **The wrapper reduction holds the protocol-specific setup.** The helper
  games are deliberately generic — they only know about $P$, $n$,
  $q^\ast$, and (for the programmed version) $m^\ast, y^\ast$. Everything
  else (key generation, encapsulation, the exact shape of the KDF input)
  lives in your wrapper. This keeps the helpers reusable across
  proofs.
- **The assumption hop is the one piece of content.** The two flanking
  interchangeability hops should canonicalise without fuss; if they don't,
  the wrapper is usually inconsistent with how the adversary-facing game
  builds its hash input. When in doubt use `get_step_detail` /
  `inlined-game` to compare canonical forms.
- **Programmed vs. plain.** Use `LazyROTwoViewsExcludedProgrammed` whenever
  you need $H(m^\ast)$ to *be* the challenge output (e.g., to make a
  computational reduction's challenge embed there). Use
  `LazyROTwoViewsExcluded` whenever you just need two-view lazy sampling
  without any programmed point, typically to get back to an honest
  random-oracle form.
