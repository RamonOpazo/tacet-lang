# Design note — the denotational functor `⟦−⟧ : 𝒮 → ℋ`

**Status: NOT chapter text. Not proven. A specification to study against.**

This note lays out what a denotational functor for Tacet would have to be, why each
choice is the natural one, and — for every piece — the concept to go learn and whether
the paper already contains the work. Treat every "is" below as "would need to be shown
to be." Nothing here should enter the manuscript until the corresponding item is
understood and checked. The goal is to make the target legible so the mathematics can
be studied deliberately, one piece at a time.

A one-line version of the destination, to keep in view while reading:

> `𝒮` is a symmetric-monoidal category (the linear contexts); `ℋ` is the Kleisli
> category of a _disposition-graded monad_ `W`; `⟦−⟧ : 𝒮 → ℋ` is a strong monoidal
> functor whose functoriality is the substitution lemma we already prove for
> Preservation; and _honesty_ is the statement that closed top-level morphisms factor
> through `V ⊎ W₀`.

Do not try to absorb that sentence yet — it is the finish line. The sections below are
the route.

---

## Part 0 — What a functor commits you to

A functor `F : 𝒮 → ℋ` is three promises: it sends objects to objects and morphisms to
morphisms; it preserves identities (`F(id) = id`); and it preserves composition
(`F(g ∘ f) = F(g) ∘ F(f)`). The last is the one with teeth. If `⟦−⟧` is to be a functor,
`⟦e[e'/x]⟧` must equal `⟦e⟧` composed with `⟦e'⟧` — denotation of a substitution is
composition of denotations. Keep this test in your pocket: every time you are unsure
whether something is "categorical," ask whether it respects composition.

- **Concept to learn:** category, functor, the three functor laws.
- **Where to read:** any gentle category-theory intro; Awodey _Category Theory_ ch. 1,
  or Leinster _Basic Category Theory_ ch. 1, or Milewski _Category Theory for
  Programmers_ (free, programmer-facing) for the first pass.
- **Already in the paper?** The composition law is _morally_ the substitution lemma
  invoked in the Preservation proof (Ch. 3, Thm 1). You have not stated it as a functor
  law, but the content exists. This is the single biggest reason the functor is
  "mostly organization, not new proof."

---

## Part 1 — The syntactic category `𝒮`

**Objects.** Types `τ`, or more precisely typing contexts. Because Tacet has two
contexts (`Γ` unrestricted, `Δ` linear), an object is a pair, or you fix `Γ` and let
objects be the linear part.

**Morphisms.** A morphism `A → τ` is a well-typed term `Γ; Δ ⊢ e : τ`, taken _up to some
equivalence_ (see the open decision below). Composition is substitution; identities are
variables.

**The catch — `𝒮` is not cartesian, it is monoidal.** The linear context forbids
copying and discarding, so `𝒮` does not have the "duplicate/delete any value freely"
structure of ordinary typed lambda calculus. Instead:

- the **multiplicative split** `Δ = Δ₁, Δ₂` (sequential subterms, Ch. 2 §2.5) is a
  **tensor product** `⊗` — this is what makes `𝒮` _monoidal_;
- the **additive branch rule** `T-Branch` (alternatives share `Δ`) is the **additive**
  connective (`&` / `⊕` in linear logic);
- the unrestricted `Γ` alongside the linear `Δ` is the shape of **dual intuitionistic
  linear logic (DILL)** / **Benton's LNL** (linear/non-linear) adjunction.

So the precise thing to say is: **`𝒮` is a symmetric monoidal category** (very likely
symmetric monoidal closed), with an additional comonad/adjunction carrying the
unrestricted `Γ`.

- **Concepts to learn, in order:** monoidal category → symmetric monoidal → symmetric
  monoidal _closed_ → linear logic's multiplicative/additive distinction →
  DILL / LNL models.
- **Where to read:** for monoidal categories, Coecke–Paquette or the nLab entry as a
  map, then a text; for the linear-logic side, Benton "A mixed linear and non-linear
  logic" (the LNL paper) and Melliès "Categorical semantics of linear logic" (long but
  the standard survey).
- **Already in the paper?** The _ingredients_ are all there and named correctly
  (multiplicative vs additive, `Γ` vs `Δ`). What is missing is the sentence "these
  assemble into a symmetric monoidal category," plus the check that `⊗` is associative
  and unital _up to the coherence isomorphisms_ (the coherence conditions are the part
  people underestimate).

---

## Part 2 — The disposition-graded monad `W`

This is the heart, and the place your existing disposition algebra becomes categorically
load-bearing.

**The idea.** An ordinary monad `T` models "computations returning a value" — `T(A)` is
"a computation of an `A`." A **graded monad** `T_m(A)` is indexed by a _grade_ `m` drawn
from a monoid `(𝕄, ⊗, 1)`: `T_m(A)` is "a computation of an `A` _with effect grade `m`_."
The monoid laws mirror the monad laws: the unit `1` grades the pure `return`, and grades
multiply along `bind` (`T_m(A)` then `T_n(B)` gives grade `m ⊗ n`).

**Your instance.** The grade monoid _is_ your disposition algebra:

- carrier: the admissible dispositions (the faces of the flag complex);
- unit `1`: `Total = ∅` (the empty witnessing type — this is _why_ `Total` is the unit,
  and why it maps to `V`);
- `⊗`: your composition of dispositions, _partial_ because of the exclusion relation
  (the forbidden joins). A partial operation means you likely have a **graded monad over
  a partial monoid**, or a monad graded by a _category/poset_ rather than a monoid —
  worth checking which, because the partiality is a real subtlety, not a footnote.

Then:

- `W_∅(A) = A` — the `Total` grade is pure values (`V`);
- `W_S(A)` for `S` a non-empty face carrying linear obligations = `W_L` witnesses of
  disposition `S`;
- the renounced grades (`Unbounded₀`, `Awaited₀`) — where the `W₀` bookkeeping lives —
  are the grades with _null obligation_, and "absorbs into `Total`" is the statement that
  they map to the unit at the top level.

**`expose` is the graded structure map**, and its `𝒫_fin(L_f)` codomain is why several
obligations attach to one grade. `reify`/`defer` are the algebra operations that _lower_
the grade (discharge), which is the graded analogue of a handler.

- **Concepts to learn, in order:** monad (Kleisli triple) → the monad laws → monad _for
  effects_ (Moggi) → **graded monad** → graded monad over a _partial_/poset-indexed base.
- **Where to read:** Moggi "Notions of computation and monads" (the origin of monads-as-
  effects; essential and readable); then Katsumata "Parametric effect monads and
  semantics of effect systems" (the graded-monad paper — this is the one that will most
  directly match what you have); Milewski's chapters on monads for the gentle on-ramp.
- **Already in the paper?** The disposition monoid, the unit `Total`, the composition
  `⊗`, the flag-complex constraint, and `expose`/`reify`/`defer` are all present and
  correct. What is _not_ done: identifying them as a graded monad, and — the genuinely
  new mathematical work — handling the **partiality of `⊗`** rigorously. Do not claim
  "graded monad" until you have read Katsumata and decided how the exclusions are
  modelled. This is the one place there may be real theorem-shaped work, not just
  repackaging.

---

## Part 3 — The semantic category `ℋ`

Once `W` is a graded monad, `ℋ` is its **Kleisli category**:

- objects: value types (the `V` world);
- a morphism `A → B` in `ℋ` is a map `A → W_S(B)` in the base — "a function from `A` that
  produces a `B` with disposition `S`." That is _exactly_ a Tacet function: input to
  output-with-obligations.

This is why Kleisli, not Eilenberg–Moore: Kleisli morphisms _are_ effectful functions,
which is what programs are. (Eilenberg–Moore is the category of _handlers/algebras_ — it
shows up when you study `reify` systematically, so keep it in your back pocket, but the
programs live in Kleisli.)

`select_f`, `eval`, `expose`, and the reifiers from Figure 2.1 are then the images under
`⟦−⟧` of the corresponding syntax — which is the precise sense of your phrase "a functor
that takes the syntactic function evaluation."

- **Concepts to learn:** Kleisli category of a monad; then Eilenberg–Moore (for context
  on handlers); the graded versions of both.
- **Where to read:** the Kleisli construction is in every monad reference above; for the
  handler/algebra side, Plotkin–Pretnar "Handlers of algebraic effects."
- **Already in the paper?** Figure 2.1's maps are the would-be generators. Nothing is
  stated as Kleisli yet.

---

## Part 4 — The functor `⟦−⟧ : 𝒮 → ℋ` and its laws

With `𝒮` monoidal and `ℋ` Kleisli-of-`W`, the functor must be **strong monoidal**: it
preserves the tensor (`⟦Δ₁, Δ₂⟧ ≅ ⟦Δ₁⟧ ⊗ ⟦Δ₂⟧`) up to coherent isomorphism, sends
identities to identities, and sends composition to composition.

Each law and where it comes from:

| Functor obligation                          | Discharged by                              | Status                           |
| ------------------------------------------- | ------------------------------------------ | -------------------------------- |
| objects → objects                           | the typing judgment's types                | trivial                          |
| morphisms → morphisms                       | well-typed terms are Kleisli maps          | needs the Kleisli identification |
| `F(id) = id`                                | denotation of a variable is `return`       | small lemma                      |
| `F(g∘f) = Fg ∘ Ff`                          | **the substitution lemma of Preservation** | _content exists_ (Ch. 3)         |
| monoidal: `F(⊗) ≅ F ⊗ F`                    | multiplicative split respects denotation   | needs coherence check            |
| graded: grade of `⟦e⟧` = disposition of `e` | Admissibility Preservation (Lemma 1)       | _content exists_ (Ch. 3)         |

The reassuring pattern: the two hard-looking laws (composition, grading) are _already_
your metatheorems (substitution/Preservation, and Admissibility Preservation) wearing
categorical clothes. The genuinely new work is the monoidal **coherence** conditions and
the graded-monad **partiality**, not the functor laws per se.

- **Concept to learn:** (strong/lax) monoidal functor; coherence.
- **Where to read:** monoidal-functor definition in any monoidal-category reference;
  Mac Lane's coherence theorem is the classical source but read a modern exposition first.

---

## Part 5 — The elaboration boundary (do not skip)

`tacet` is your `⇝` — "not an ordinary semantic morphism." A functor is a _total,
structure-preserving_ map, so a raw `tacet` arrow would break functoriality if `⟦−⟧` had
to act on it directly. **Resolution: factor the semantics.**

```
    𝒮  ──elab──▶  𝒮′  ──⟦−⟧──▶  ℋ
        (squiggle)      (clean functor)
```

- `elab : 𝒮 → 𝒮′` is _elaboration_ — a syntactic translation that interprets `tacet` (and
  symbol-constructs generally). The squiggle `⇝` lives **here and only here**.
- `⟦−⟧ : 𝒮′ → ℋ` is the clean denotational functor, acting on already-elaborated terms,
  where every arrow _is_ an ordinary morphism.

This keeps "`tacet` is not an ordinary morphism" honest **and** gives you full
functoriality downstream. Do not try to make one functor swallow both; the composite is
fine to call "the semantics," but the two steps have different characters and should stay
separate.

- **Concept to learn:** syntactic translation / elaboration as a functor between term
  models; (optionally) the idea of a _2-categorical_ or _fibrational_ account if you want
  elaboration itself to be structured — but that is well beyond what the paper needs.

---

## Part 6 — Honesty, restated as a functor property

The payoff. Your honesty theorem (Ch. 3, Thm 4) currently reads operationally: outcomes
coincide with the declared type up to declared capabilities. As a functor property it
becomes a _factorization_ statement:

> For a closed, top-level program `p`, the morphism `⟦p⟧` factors through the subobject
> `V ⊎ W₀ ↪ V ⊎ W` — every `W_L` grade has been discharged, leaving only value plus
> null-obligation bookkeeping.

That is cleaner than the operational statement and lives in the same categorical
language as everything else. It is the same theorem; the functor just gives it a better
sentence. Prove it _after_ the functor is solid, not before.

---

## The three decisions that gate everything

Nothing above is well-defined until these are fixed. Study toward them; decide them
before any of this becomes prose.

1. **Morphism equivalence in `𝒮`.** What makes two terms the _same_ morphism — α-equivalence
   only? β? full observational/contextual equivalence? Recommendation: observational
   (contextual) equivalence, because it is what makes the functor's equations meaningful
   and is standard for denotational adequacy. Learn: contextual equivalence, adequacy,
   full abstraction (aspirational, not required).

2. **Kleisli vs Eilenberg–Moore for `ℋ`.** Recommendation: **Kleisli** — programs are
   effectful maps. Revisit E–M only when formalizing handlers.

3. **Elaboration factoring.** Recommendation: **`𝒮 →elab 𝒮′ →⟦−⟧ ℋ`**, squiggle on the
   first arrow only (Part 5).

---

## Suggested study order (shortest path to understanding, not to a proof)

1. Functor + the three laws (Part 0). Small, do first.
2. Monads as effects — **Moggi**. This unlocks everything downstream.
3. Kleisli category (Part 3). Follows immediately from 2.
4. **Graded monads — Katsumata.** The keystone; match it against your disposition algebra.
5. Monoidal categories + linear-logic models — **Benton LNL**, then skim **Melliès**.
6. Only then: assemble the functor (Part 4) and re-read your own Ch. 3 proofs as functor
   laws — you will recognize the substitution lemma as composition-preservation.

Two references will do the most work for you specifically: **Moggi** (monads-as-effects,
the foundation) and **Katsumata** (graded monads, the exact shape of your system).
Everything else is context around those two.

---

## What to hold onto while studying

- You are not inventing new mathematics; you are _recognizing_ that constructions you
  already have (disposition algebra, `expose`, the substitution lemma) are instances of
  known categorical structure. The exception is the **partiality of `⊗`** (Part 2),
  which may be genuinely new work — flag it, do not bluff it.
- Do not write a word of functor prose into the chapters until Parts 2 and 4 feel
  _obvious_ to you rather than intimidating. A denotational-semantics section you can
  defend is worth a great deal; one you cannot is a liability.
- When ready, this becomes a **short dedicated chapter or a closing section**, pitched at
  the one-line summary at the top — never shoehorned into Chapter 2.
