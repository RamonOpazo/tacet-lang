# Chapter 2 · Formal semantics

We now develop the calculus sketched in the introduction. Its organizing idea is a separation between *values* and *computational obligations*: the value a computation produces is kept distinct from the obligations its evaluation incurs, so that a strong value space can be maintained under an honest signature.

The chapter proceeds in five steps. Section 2.1 fixes the result domain into which evaluation lands, together with the small-step reduction relation — equipped with a fuel discipline — on which the metatheory of Chapter 3 depends. Section 2.2 introduces *dispositions*, the small algebra that governs which computational phenomena may co-occur. Section 2.3 characterizes witnesses and the obligations they expose, distinguishing the stateful witness from the nominal obligation. Section 2.4 gives the introduction forms through which obligations enter the linear context, and connects the semantic account of obligations to their syntactic bookkeeping. Section 2.5 gives the discharge rules through which obligations are consumed. The metatheory these definitions support — culminating in the honesty theorem — is developed separately in Chapter 3.

## 2.1 Function evaluation, the result domain, and reduction

### Two-stage evaluation

Given a function $f$, let $A$ denote its input-value domain, $B$ the universe of branches, and $B_f \subseteq B$ the set of branches occurring in the body of $f$. Evaluation proceeds in two stages: an input first determines the branch to be executed, and that branch is then evaluated,

$$
A \;\xrightarrow{\;\mathrm{select}_f\;}\; B_f \;\xrightarrow{\;\mathrm{eval}\;}\; R.
$$

The selection stage captures the control-flow structure of $f$: for an input $a \in A$, $\mathrm{select}_f$ identifies the branch $b \in B_f$ whose execution $a$ determines. Concretely, $\mathrm{select}_f$ is the language's match construct, written `|>`, which dispatches over the arms of $f$ by matching the scrutinee along whichever axis its arms use — *truthiness*, *structure*, *content*, or *morphology*. Binary decision is the degenerate case rather than a separate primitive: Tacet has no boolean atom, only Church booleans, the total selectors $\mathsf{true} = x\,y \mapsto x$ and $\mathsf{false} = x\,y \mapsto y$, and a two-arm truthiness match is exactly such a selector applied to its arms.

Selection is *total and obligation-free by construction*. Matching only chooses an arm; it never itself raises, and — because a Church boolean is a total value in $V$ — the decision axis lives wholly inside the value space. There is no implicit "non-exhaustive match" failure: if no arm should produce a value, the programmer writes that arm explicitly as $\mathsf{tacet}$, so even the gap in a match is a disclosed obligation rather than a silent error. Every obligation in the system therefore enters through introduction (Section 2.4), never through branch selection. The evaluation stage then reduces the chosen branch $b$ to an element of the *result domain* $R$.

The inclusion of $B_f$ into the general branch universe,

$$
B_f \hookrightarrow B,
$$

lets the semantics reason about the branches of a particular function without identifying them with the entire syntactic universe of possible branches. The structure of $B_f$ determines which branch-specific phenomena can arise during the evaluation of $f$.

### The result domain

The result domain is partitioned into values and witnesses,

$$
R \;=\; V \;\uplus\; W .
$$

Here $V$ is the domain of ordinary language values and $W$ is the domain of witnessed outcomes — obligation-bearing results, each carrying a witness type. The disjointness is deliberate: a witnessed outcome is not a language value and cannot be used interchangeably with an element of $V$. Ordinary evaluation has the form $b \mapsto v \in V$, while a branch that leaves an obligation has the form $b \mapsto w \in W$. Thus $R$ is the complete range of branch-evaluation outcomes, and $V$ is the sub-range consisting of ordinary values.

The value domain is moreover kept apart from the bottom element,

$$
\bot \notin V .
$$

Bottom is not an ordinary value and is never produced as the outcome of a successful evaluation. In particular there is no null, none, or nothing inhabiting any value type: absence is never a value but a $\mathsf{Reify}$ obligation, reached only through $\mathsf{tacet}$ (Section 2.4). This matters because the semantics does not model the phenomena carried by witnesses as ordinary bottom-valued computation; such phenomena are represented explicitly, as elements of $W$ (Section 2.3). We will shortly strengthen $\bot \notin V$ to $\bot \notin R$, which holds unconditionally, in every evaluation regime.

### Reduction with fuel

To state progress, preservation, and — above all — honesty, we need a reduction relation to reason about, not merely the input–output map $\mathrm{eval}$. We equip evaluation with a *fuel* budget that bounds the depth of self-referential computation.

A **configuration** is a pair $\langle e, \varphi \rangle$ consisting of an expression $e$ and a fuel value

$$
\varphi \in \mathbb{N} \cup \{\infty\}.
$$

Reduction is a relation $\langle e, \varphi \rangle \to \langle e', \varphi' \rangle$ on configurations, governed by two disciplines.

**(Fuel.)** The two reduction forms that can recur without structurally shrinking the expression — the unfolding of a recursive call and the deferral reifier $\mathsf{reify}_L$ (Section 2.5) — each draw one unit of fuel:

$$
\frac{\varphi > 0}{\langle \mathcal{R}[e],\, \varphi \rangle \to \langle \mathcal{R}'[e],\, \varphi - 1 \rangle}
\qquad(\text{recursion / defer}),
$$

with the convention $\infty - 1 = \infty$. When such a redex is reached at $\varphi = 0$, it does not become stuck and does not diverge; it introduces a $\mathsf{Bound}$ obligation — the obligation of an $\mathsf{Unbounded}$ witness (Section 2.2) — recording that the budget was exhausted:

$$
\frac{}{\langle \mathcal{R}[e],\, 0 \rangle \to \langle \mathsf{obl}_{\mathsf{Bound}},\, 0 \rangle}.
$$

Every other reduction step leaves the fuel value unchanged.

**(Capability.)** A function evaluates with $\varphi = \infty$ if and only if it declares the $\mathsf{Unbounded}^{-}$ capability in its signature; otherwise it evaluates with a finite budget $\varphi \in \mathbb{N}$. Thus the two regimes are one relation at two fuel settings, and the capability reads semantically as the lifting of the fuel bound. Because $\mathsf{Unbounded}^{-}$ is recorded in the signature, the choice of regime is disclosed to every caller.

### Boundedness and totality

The result domain never contains bottom:

$$
\bot \notin R,
$$

unconditionally, in either fuel regime. Tacet does not model non-termination as a value; what the two regimes differ in is only whether reduction is *guaranteed to halt*.

In the default regime, $\varphi \in \mathbb{N}$ is finite. Because recursion and deferral strictly decrease $\varphi$ and every other step leaves it fixed, no configuration admits an infinite reduction sequence: fuel exhaustion converts would-be divergence into a finite reduction ending in a $\mathsf{Bound}$ obligation. Evaluation therefore always halts, $\mathrm{eval}$ is *total* on $B_f$, and every branch reduces to some element of $R$. The fuel-exhaustion outcome is not $\bot$; it is an ordinary $\mathsf{Bound}$ obligation, typed as an $\mathsf{Unbounded}$ witness in $W$. Like every obligation, it is discharged through the single reification API (Section 2.5); its *default resolution*, $\mathsf{Bound}$, is precisely the fuel discipline just described. Section 2.2 fixes these per-kind default resolutions, and Section 2.5 the uniform reifiers that can override them.

In the renounced regime, $\varphi = \infty$, the fuel argument no longer forces termination, and reduction of such a branch may continue without end. This does *not* reintroduce $\bot$. The possibility of non-termination is disclosed by the $\mathsf{Unbounded}^{-}$ capability in the signature; when such a computation does halt, its result is absorbed into $\mathsf{Total}$ — an ordinary value — leaving no residual witness or obligation. A computation that fails to halt produces no semantic value at all, but it produces no bottom either: $\bot$ remains outside $R$, and the risk it runs is exactly the one its capability announced. This is the governing principle in its sharpest form: honesty is the *disclosure of the risk*, never the production of $\bot$.

The overall shape of function evaluation is summarized in Figure 2.1; the internal structure of $V$ and $W$ indicated there is developed in the sections that follow.

```
                          A
                          │  select_f
                          ▼
              B_f ───────────────────► B          (B_f ↪ B)
               │  eval
               ▼
               R  =  V  ⊎  W                       (⊥ ∉ R, unconditionally)
                     │      │
                     ▼      ▼
                   values  witnesses         (non-termination under Unbounded⁻
                                              is a disclosed risk, not a value)
```

*Figure 2.1.* Function evaluation. An input selects a branch from $B_f$, which evaluates to an element of the result domain $R = V \uplus W$; bottom is never an element of $R$. In the default (finite-fuel) regime evaluation is guaranteed to halt. Declaring $\mathsf{Unbounded}^{-}$ sets $\varphi = \infty$: reduction may then run without end, but that possibility is disclosed by the capability, and any value it does produce is absorbed into $\mathsf{Total}$ — never a bottom value. The internal structure of $V$ and $W$ is developed in Sections 2.2–2.3.

## 2.2 Dispositions and their composition

### The disposition of an outcome

The partition of the result domain in Section 2.1 is not primitive; it is induced by the *disposition* of a branch evaluation — the collection of computational phenomena its evaluation realizes. The default disposition is $\mathsf{Total}$: a branch that realizes no phenomenon beyond producing a value is $\mathsf{Total}$, and its outcome is an ordinary value in $V$. $\mathsf{Total}$ is the identity disposition — the absence of any witnessed phenomenon. Its canonical inhabitants are the Church booleans $\mathsf{true} = x\,y \mapsto x$ and $\mathsf{false} = x\,y \mapsto y$: total functions that select between two values already held, raising nothing. The *decision* axis of the language thus lives wholly in $V$ as $\mathsf{Total}$ values, disjoint from the *absence* axis, which lives wholly in $L$ and is reached only through $\mathsf{tacet}$; the two are never conflated in a single degenerate inhabitant.

When evaluation realizes a phenomenon that is not an ordinary value — a possible failure, an unbounded recursion, an asynchronous wait, an intrinsically infinite loop — the branch acquires a corresponding *witness kind*. The linear kinds are

$$
\mathcal{K}_L \;=\; \{\, \mathsf{Partial},\ \mathsf{Unbounded},\ \mathsf{Awaited},\ \mathsf{Loop} \,\}.
$$

This set is closed and exhaustive. Its four kinds are the orthogonal axes along which a computation can depart from producing a value — *partiality*, *boundedness*, *effectfulness*, and *loop productivity* — and no further axis inhabits the space. The metatheory of Chapter 3 is defined over exactly these four.

Each linear kind, when realized, causes its witness to *expose* a named obligation:

| Witness | Exposes | Domain |
|---|---|---|
| `Total`       | —        | `V`   |
| `Partial`     | `Reify`  | `W_L` |
| `Unbounded`   | `Bound`  | `W_L` |
| `Awaited`     | `Sync`   | `W_L` |
| `Loop`        | `Break`  | `W_L` |

The obligation's name is its entire content. Consistent with the thin-obligation ontology of Section 2.3, a $\mathsf{Bound}$ obligation records nothing but the nominal fact that an unboundedness occurred and must be answered; a $\mathsf{Reify}$ obligation, that a partiality occurred; and so on. $\mathsf{Total}$ exposes nothing, because it is already a value.

The partition of Section 2.1 now reads off the disposition. A $\mathsf{Total}$ branch lands in $V$; a branch that exposes at least one obligation lands in $W_L$. These are the two fibres of the disposition — so $R = V \uplus W$ with $W = W_L$ — not primitive buckets. There is no third fibre: as the next subsection shows, a renounced phenomenon is absorbed into $\mathsf{Total}$ rather than surviving as an obligation-free witness, so every witness that persists exposes an obligation.

### Renunciation

Two of the linear kinds admit a *renounced* form, written with a superscript minus — the witness with its obligation removed:

$$
\mathsf{Unbounded}^{-} \qquad \mathsf{Awaited}^{-}
$$

Renunciation removes the phenomenon from the linear domain entirely. Rather than exposing an obligation, a renounced phenomenon is *absorbed into* $\mathsf{Total}$ after evaluation: an $\mathsf{Unbounded}^{-}$ recursion that halts, or an $\mathsf{Awaited}^{-}$ effect that is launched, resolves to an ordinary value and leaves no witness behind. The phenomenon is not answered but *accepted*, and the acceptance is disclosed as a capability in the function's signature (Section 2.1).

Because a renounced form is thus the identity disposition, it composes trivially, and no admissibility question arises. A computation that is both failable and renounced-unbounded has disposition $\{\mathsf{Partial}\} \otimes \mathsf{Total} = \{\mathsf{Partial}\}$; the renounced axis contributes nothing. This is why the exclusions of the composition algebra (below) constrain only *live* linear kinds — the pairs $\{\mathsf{Unbounded}, \mathsf{Awaited}\}$ and the like — and never a renounced form, which is already $\mathsf{Total}$.

Renunciation is available only for $\mathsf{Unbounded}$ and $\mathsf{Awaited}$ — the phenomena whose obligation one may legitimately decline: an unbounded recursion may be allowed to run, and an asynchronous effect may be launched without awaiting it (the fire-and-forget sink). Partiality and looping have no renounced form. A failure must be answered and a productive loop must be broken, so $\mathsf{Reify}$ and $\mathsf{Break}$ obligations cannot be declined — only discharged.

### Non-termination without bottom

Three kinds bear on non-termination, and all three obey the principle that Tacet produces no bottom (Section 2.1); they differ only in how the possibility of non-termination is accounted for.

- $\mathsf{Unbounded}$ is fuel-bounded by default. Evaluation is guaranteed to halt; on budget exhaustion it introduces its $\mathsf{Bound}$ obligation. No unbounded run occurs.
- $\mathsf{Unbounded}^{-}$ renounces the bound. Evaluation may run without end, disclosed by the capability; any value it does produce is absorbed into $\mathsf{Total}$, and non-termination is never a bottom value.
- $\mathsf{Loop}$ exposes a $\mathsf{Break}$ obligation. A loop is intrinsically infinite: it does not draw on the fuel budget (a fuel-limited loop could not run forever, which would defeat the purpose of a productive one), and it iterates productively until its $\mathsf{Break}$ obligation is discharged. Uniquely among the kinds, a $\mathsf{Break}$ is discharged *out-of-band* — by an explicit break originating outside the loop body, either an interrupt ($\mathtt{Ctrl}$-$\mathtt{C}$) or a call to a breaking function — rather than within the forward flow of evaluation. Until that break lands the branch does not complete; a loop never broken runs productively forever. This is not bottom: the branch simply never yields a value, and the $\mathsf{Break}$ obligation discloses, statically, that completion is contingent on an explicit break.

In every case the possibility of non-termination is reified — as a fuel bound, a renounced capability, or a $\mathsf{Break}$ obligation — and never as an element of $R$.

### Composition

Dispositions compose. A single computation may realize several phenomena at once — an asynchronous computation that can also fail, say — so its disposition is in general a *set* of linear kinds. Composition is orthogonal: writing a branch's disposition as $S \subseteq \mathcal{K}_L$, the disposition algebra is

$$
(\mathcal{D},\ \otimes,\ \mathsf{Total}), \qquad \mathsf{Total} = \varnothing, \qquad S \otimes S' = S \cup S',
$$

a commutative, associative, idempotent operation with $\mathsf{Total}$ as identity — a bounded join-semilattice — made *partial* by the fact that not every combination is admissible.

The inadmissible combinations are exactly the four pairs

$$
\{\mathsf{Loop}, \mathsf{Unbounded}\}, \quad
\{\mathsf{Loop}, \mathsf{Awaited}\}, \quad
\{\mathsf{Loop}, \mathsf{Partial}\}, \quad
\{\mathsf{Unbounded}, \mathsf{Awaited}\}.
$$

Admissibility is determined entirely by pairs and is downward closed, so the admissible dispositions are exactly the *cliques* of the compatibility graph $G$ whose edges are the surviving pairs:

```
        Unbounded          Awaited
              \              /
               \            /
                \          /
                 Partial                 Loop
                                       (isolated)
```

$G$ is a two-leaf star centred on $\mathsf{Partial}$, together with an isolated $\mathsf{Loop}$. Because inadmissibility lives entirely in pairs, the admissible dispositions form a **flag (clique) complex**, with seven faces,

$$
\varnothing\ (\mathsf{Total}), \quad
\{\mathsf{Partial}\},\ \{\mathsf{Unbounded}\},\ \{\mathsf{Awaited}\},\ \{\mathsf{Loop}\}, \quad
\{\mathsf{Partial}, \mathsf{Unbounded}\},\ \{\mathsf{Partial}, \mathsf{Awaited}\},
$$

whose three maximal faces are the only maximal effect-profiles a computation may inhabit:

$$
\underbrace{\{\mathsf{Partial}, \mathsf{Unbounded}\}}_{\text{failable recursion}} \qquad
\underbrace{\{\mathsf{Partial}, \mathsf{Awaited}\}}_{\text{failable async}} \qquad
\underbrace{\{\mathsf{Loop}\}}_{\text{productive loop}}
$$

Every non-$\mathsf{Total}$ computation is thus a face of one of three maximal simplices. $\mathsf{Partial}$ (failability) is the universal companion, pairing with either $\mathsf{Unbounded}$ or $\mathsf{Awaited}$ but never both; $\mathsf{Loop}$ is sealed, composing with nothing, because a productive loop answers its own failures internally rather than exposing them upward.

### Discharge is uniform

Whatever obligation a $W_L$ witness exposes — $\mathsf{Reify}$, $\mathsf{Bound}$, $\mathsf{Sync}$, or $\mathsf{Break}$ — it is discharged through the single reification interface of Section 2.5: the three reifiers $\mathsf{reify}_T$, $\mathsf{reify}_\forall$, $\mathsf{reify}_L$. There is no per-kind discharge machinery to tabulate. The name of an obligation records where it came from; the reifiers say, uniformly, how it may leave — into a value of the same type, a value of another type, or a fresh obligation. This uniformity is precisely what allows one small interface to answer partiality of every kind.

## 2.3 Witnesses and obligations

Sections 2.1 and 2.2 have spoken of witnesses and of the obligations they expose as though these were the same kind of thing seen twice. They are not. A witness and an obligation stand in a definite ontological asymmetry, and making it explicit is what lets the linear bookkeeping of Section 2.5 sit consistently atop the semantic account given here.

### Thick witnesses, thin obligations

A **witness** is *thick*. It is a *type*: the type carried by an obligation-bearing occurrence, recording everything statically known about it. It carries two things — the payload type $T$ of the value that was expected, and the disposition $S \subseteq \mathcal{K}_L$, the face recording which phenomena the occurrence realizes — so its type is indexed by both,

$$
\mathsf{Witness}_S(T),
$$

and is fixed at the point where the obligation is introduced, because the state that determines it is present there. A witness type knows what it is. It is what appears in a function's contract, at a call boundary, and as the annotation on an occurrence in $\Delta$; it is never a separate runtime object floating alongside the value.

An **obligation** is *thin*. It carries no payload and no state; its entire content is its own identity. An obligation is a *signal* — a nominal token whose message is simply that a computation has left the value space at a definite point and must be brought back. The obligation exposed by a $\mathsf{Partial}$ witness is a $\mathsf{Reify}$ obligation, that exposed by an $\mathsf{Unbounded}$ witness a $\mathsf{Bound}$ obligation, and so on; the name *is* the meaning. Nothing about the recovered value's type lives in the obligation — that lives in the witness.

The two are bridged by exposure, and the direction of the asymmetry is exactly that a thick witness gives rise to thin obligations, never the reverse.

### Exposure

A witness exposes one obligation occurrence per active axis of its disposition:

$$
\mathrm{expose} : W_L \longrightarrow \mathcal{P}_{\mathrm{fin}}(L_f),
\qquad
\mathrm{expose}(w) \;=\; \{\, l_\kappa : \kappa \in S(w) \,\}.
$$

For a witness of singleton disposition — say $S = \{\mathsf{Partial}\}$ — this is a single $\mathsf{Reify}$ occurrence. For a composed witness — the only non-trivial admissible cases being $\{\mathsf{Partial}, \mathsf{Unbounded}\}$ and $\{\mathsf{Partial}, \mathsf{Awaited}\}$ (Section 2.2) — it is two occurrences at once, one per axis, each of which must be discharged independently. Exposure is thus in general one-to-many; that a single witness may raise several obligations is precisely why the codomain is a finite powerset of $L_f$ rather than $L_f$ itself.

### Occurrences, not names: the Grothendieck reading of $L_f$

The obligations of a function are collected across its branches. For each branch $b \in B_f$, let $\mathrm{obligations}(b)$ denote the occurrences arising in $b$ — those `tacet` introduces directly, together with those exposed by any witness types received at a call within $b$. The obligations of $f$ are then the disjoint union

$$
L_f \;=\; \coprod_{b \in B_f} \mathrm{obligations}(b).
$$

The disjoint union is doing real work: $L_f$ tracks *occurrences*, not the distinct obligation names that occur. This is the total space of the family $\mathrm{obligations} : B_f \to \mathbf{Set}$ — its Grothendieck construction $\int \mathrm{obligations}$ — whose elements are pairs $(b, l)$ of a branch and an occurrence within it. It comes with two canonical maps:

$$
B_f \;\xleftarrow{\;\pi\;}\; L_f \;\xrightarrow{\;\mathrm{name}\;}\; L,
$$

the fibration $\pi$ recording *which branch* an occurrence arose in, and the naming map $\mathrm{name}$ recording *which* underlying obligation it is an occurrence of, within the universe $L$ of all obligations.

The point of the construction is that $\mathrm{name}$ need not be injective. If two distinct branches $b_1, b_2 \in B_f$ each raise an occurrence of the same underlying obligation $l \in L$, those occurrences are nevertheless distinct elements of $L_f$ — distinguished by their fibres under $\pi$ — even though $\mathrm{name}$ identifies them in $L$. Branch structure is thereby preserved when the obligations of a function are collected, and this is exactly why $L_f$ is associated with the function while $L$ is the universe: $L$ describes the possible obligation names, whereas $L_f$ records the particular occurrences the branches of $f$ induce. (The original presentation wrote $L_f \hookrightarrow L$; the inclusion is too strong, since it would force distinct occurrences of one name to collapse. The correct arrow is the generally non-injective $\mathrm{name} : L_f \to L$.)

### The linear context, by inheritance

The bridge to the syntactic bookkeeping of Section 2.5 is now short. The linear context $\Delta$ tracks occurrences of $L_f$, and an entry $l : \mathsf{Witness}(T)$ in $\Delta$ does not assert that the obligation *is* a witness. It records the occurrence $l$ together with the payload type $T$ *inherited from the witness that exposed it* — so that a reifier knows the type of the value its handler will receive. The obligation contributes its identity through $\mathrm{name}$; the witness contributes the type through $\mathrm{expose}$. There is no tension between the semantic separation of $W_L$ from $L_f$ and the syntactic annotation of occurrences with witness types: the annotation is simply the image of a witness under $\mathrm{expose}$, read together with the witness's own payload.

### The force of a dropped obligation

An obligation's message is: *rectify here, or produce no value.* In Tacet the second alternative is not a silent $\bot$ but an explicit, terminal, loudly surfaced failure. This is the semantic force behind treating obligations linearly. An unconsumed obligation cannot decay into a quiet default, because its only alternative to being discharged is a visible error — never a bottom, and never an implicit fallback. The linear discipline of Section 2.5, and the Global Branch Totality it enforces, is precisely the static guarantee that a well-typed branch never reaches that alternative: every occurrence in $L_f$ that a branch raises is, in well-typed code, discharged before the branch completes.

## 2.4 Introduction

Section 2.3 characterized obligations and the domain $L_f$ that collects them, but not how an obligation comes to be there in the first place. This section gives the *introduction* forms — the constructs through which a witness is raised and its obligations enter the linear context — and connects the semantic collection $L_f$ to the syntactic context $\Delta$ that the discharge rules of Section 2.5 will consume.

### Symbols, and `tacet` as obligation introduction

Obligations are not values: they live in $L$, outside the value space entirely, and so cannot be named, passed, or matched on directly in code. To let a program *refer* to an obligation without ever *holding* one, the language provides value-level proxies. A **symbol** is such a proxy — a value that stands in for an obligation as its avatar, carrying only the obligation's semantic meaning and none of its linear substance. A **symbol-construct** is a set of symbols. Symbols are what code manipulates; the obligations they name stay in $L$.

A symbol-construct is a signal to the type interpreter, which reads it as a type-level operation against $\Gamma$ or $\Delta$: a check on values, a declaration of witnesses, or the production of an obligation. Symbol-constructs serve several roles in the language; module loading and creation ($\mathsf{Load}$, $\mathsf{Module}$) are introduced in a later chapter. Here we are concerned with the two that bear on obligations: the `tacet` keyword, which *introduces* obligations, and the function contract, which *declares* witnesses.

The `tacet` keyword is the most universal of the obligation-introducing rules, because it is simply the introduction written directly in the code. Applied to a symbol-construct, `tacet` signals that the branch produces the linear obligation the symbols name, and introduces that obligation into $\Delta$. It can introduce *any* obligation the language admits, with a single exception: it cannot introduce $\mathsf{Break}$. A $\mathsf{Break}$ is never raised by code — it is produced solely by a decision the user makes while the computation runs, an interrupt or a call to a breaking function — so no symbol introduces it. Every other obligation is within `tacet`'s reach.

The essential discipline is that `tacet` lands **purely in $L$**. It consumes a symbol — a value — and emits an obligation, which is not a value; the symbol is the avatar that carries the semantic meaning across this boundary, leaving the obligation itself wholly outside the value world. `tacet` never produces a witness. What it does do, beyond depositing the obligation in $\Delta$, is *force an implicit witness in the contract*: a branch that raises an obligation via `tacet` obliges the function's contract to carry the corresponding witness (below). Witnesses ($W$) thus remain the concern of the interface, obligations ($L$) the concern of the body, and `expose` (Section 2.3) is the map between them at the call boundary — the two domains never merge, which is exactly why they are kept separate. Writing the elaboration with a squiggle, to mark that it is not an ordinary semantic morphism,

$$
\mathsf{tacet} : \mathrm{Sym} \rightsquigarrow L_f,
$$

we cross the value/obligation boundary exactly once, and nothing of $L$ leaks back into the value space.

### How each obligation arises

Each of the four obligations reaches the type system by its own route, and the routes are deliberately not uniform.

- **$\mathsf{Reify}$** enters through `tacet` and through $\mathsf{reify}_L$ (Section 2.5): `tacet` raises it where a computation declares it may fail to produce a value, and $\mathsf{reify}_L$ threads it forward as the $\mathsf{Partial}$ successor of a deferral.
- **$\mathsf{Bound}$** enters through `tacet` and through recursion under the fuel discipline (Section 2.1): budget exhaustion produces it, and a recursive computation that may not terminate carries it.
- **$\mathsf{Sync}$** is a deliberate special case. It should be *completely transparent* to the user — Tacet does not want two colours of function, one synchronous and one not. Asynchrony is therefore expressed only by calling the language's primitive effectful functions, which are lifted into progressively richer effectful ones; the introduction rule for $\mathsf{Sync}$ is a function, not a keyword, and an asynchronous function is syntactically indistinguishable from a synchronous one.
- **$\mathsf{Break}$** cannot be introduced in code at all. It is produced only by the user's runtime decision, so the $\mathsf{Loop}$ phenomenon it belongs to reaches the type system solely through the contract, as the next subsection explains.

### Introduction rules

An introduction deposits a fresh obligation occurrence into the linear context, guarded by admissibility: the new kind must be compatible with those already live. Writing $\mathrm{kinds}(\Delta)$ for the witness kinds live in $\Delta$ and $\mathcal{X}$ for the flag complex of admissible dispositions (Section 2.2):

$$
\textbf{(T-Intro}_\kappa\textbf{)}\qquad
\frac{\;\Gamma; \Delta \vdash e : T \qquad \mathrm{kinds}(\Delta) \cup \{\kappa\} \in \mathcal{X} \qquad \kappa^{-} \notin \mathrm{caps}(f)\;}
     {\;\Gamma;\ \Delta,\, l : \mathsf{Witness}(T) \vdash \mathrm{intro}_\kappa(e) : \mathsf{Witness}(T)\;}
\quad (l\ \text{fresh})
$$

The rule covers the obligations `tacet` can introduce — $\mathsf{Reify}$ and $\mathsf{Bound}$ directly, and $\mathsf{Sync}$ through the effectful primitives; $\mathsf{Break}$ has no introduction rule and enters only through the contract. The admissibility premise is what makes the "impossible combinations" of Section 2.2 a typing fact rather than prose: an introduction that would leave the flag complex simply has no derivation. The capability premise $\kappa^{-} \notin \mathrm{caps}(f)$ selects the *live* case for the renounceable kinds $\mathsf{Unbounded}$ and $\mathsf{Awaited}$; the renounced case is the following rule.

When the corresponding capability is declared, the same introduction form is *transparent*: it raises no witness, touches no obligation, and its phenomenon is absorbed into $\mathsf{Total}$ (Section 2.2):

$$
\textbf{(T-Absorb}_\kappa\textbf{)}\qquad
\frac{\;\Gamma; \Delta \vdash e : T \qquad \kappa^{-} \in \mathrm{caps}(f)\;}
     {\;\Gamma; \Delta \vdash \mathrm{intro}_\kappa(e) : T'\;}
\qquad \kappa \in \{\mathsf{Unbounded}, \mathsf{Awaited}\}.
$$

The result type $T'$ is $T$ for a renounced recursion ($\mathsf{Unbounded}^{-}$ in the contract), which yields the value it would have computed, and the trivial type for a renounced asynchronous launch ($\mathsf{Awaited}^{-}$), which returns immediately as a fire-and-forget sink. The linear context is unchanged: renunciation adds nothing to $\Delta$, exactly as its status as the identity disposition requires. Because asynchrony enters only through primitive effectful functions, $\mathsf{Awaited}^{-}$ renounces the $\mathsf{Sync}$ obligation those primitives would otherwise raise.

### The witness contract

Where `tacet` introduces *obligations* in the body, a function's contract declares the *witnesses* it exposes in its interface. The two are the syntactic faces of the thick/thin distinction of Section 2.3: obligations are the thin occurrences that live in $\Delta$; witnesses are the thick objects the signature advertises. A declaration may append a symbol-construct after the return type,

$$
f : A \to \tau \;\; \kappa_1 \cdots \kappa_n ,
$$

naming the witnesses the body exposes. This contract is the function's set of capabilities, and $\mathrm{caps}(f)$ is the subset of renounced symbols within it — those written $\kappa^{-}$, a witness with its obligation removed. The contract must *comply with the body*: the witnesses it declares must match the obligations the branches raise, up to renunciation. Left empty, it is inferred — the function is linearly typed by the evaluation of its branches. The intent is to be *always explicit about obligations*, which the body's `tacet`s make unavoidable, while *opting in to witnesses*, which the contract makes a deliberate part of the interface, since the witness API is itself something the programmer defines.

$\mathsf{Loop}$ is the one witness that can *only* be declared, never introduced. Because its $\mathsf{Break}$ cannot be raised in code, a loop reaches the type system solely by adding $\mathsf{Loop}$ to the contract, which must be made explicit and must comply with the function's main branch. This matches the isolation of $\mathsf{Loop}$ in the flag complex (Section 2.2): a loop stands alone as a witness, separated from every other, so a $\mathsf{Loop}$ contract admits no companion. Renunciation is declared the same way — $\mathsf{Unbounded}^{-}$ or $\mathsf{Awaited}^{-}$ in the contract absorbs the corresponding obligation into $\mathsf{Total}$ (Section 2.2), which is how a programmer opts into possible unboundedness or a fire-and-forget effect.

### The correspondence $L_f \leftrightarrow \Delta$

The semantic collection of Section 2.3 and the syntactic context here are two views of one object. For a branch $b \in B_f$, the introduction rules accumulate exactly the occurrences of $\mathrm{obligations}(b)$ as linear hypotheses; write $\Delta_b$ for that context. The discharge rules of Section 2.5 transform $\Delta_b$. A branch is **complete** when it is typeable with an empty residual context,

$$
\Gamma;\ \cdot \vdash \mathrm{body}_b : \tau,
$$

i.e. every occurrence in $\mathrm{obligations}(b)$ has been discharged. Collecting over branches recovers

$$
L_f \;=\; \coprod_{b \in B_f} \mathrm{obligations}(b)
$$

as the total space of occurrences the type system must drive to empty. **Global Branch Totality** is precisely the requirement that every branch of a well-typed function admit such a derivation: no branch completes into $V$ while an obligation remains, and — by the fuel discipline of Section 2.1 — no branch defers indefinitely. The introduction rules populate $\Delta$; the discharge rules drain it; a well-typed branch is one for which the draining is complete.

## 2.5 Discharge

Introduction populates the linear context; discharge drains it. This section gives the interface through which every obligation leaves $\Delta$ — a single family of three reifiers, uniform across all witness kinds — and the rules that combine subterms and branches.

### The two contexts

Judgments have the form $\Gamma;\, \Delta \vdash e : \tau$ with two environments of different character:

- $\Gamma$, the **lexical context**, maps immutable identifiers to ordinary value types. It is unrestricted: weakening and contraction are admissible.
- $\Delta$, the **linear context**, is a multiset of active, unconsumed obligation occurrences, $\Delta = \{\, l_1 : \mathsf{Witness}(T_1),\ l_2 : \mathsf{Witness}(T_2),\ \dots \,\}$. It admits neither weakening nor contraction: an occurrence can be neither discarded nor duplicated.

Sequential subterms — subterms both of which are evaluated — split the linear context **multiplicatively**, $\Delta = \Delta_1, \Delta_2$, distributing the active obligations disjointly between them. Alternatives combine additively, as the branch rule below records.

### The three reifiers

Whatever obligation a witness exposes, it is discharged by one of three reifiers, distinguished only by *where the result lands*:

$$
\mathsf{reify}_T : W \to V(T) \qquad
\mathsf{reify}_\forall : W \to V(U) \qquad
\mathsf{reify}_L : W \to W_L .
$$

All three consume a witness. $\mathsf{reify}_T$ and $\mathsf{reify}_\forall$ reify it into the value space — into a value of the witness's own type, or of an arbitrary target type. $\mathsf{reify}_L$ reifies it into the linear space instead, producing a fresh obligation. There is no per-kind discharge machinery: a single interface answers partiality of every kind, which is the point of collapsing the witness taxonomy onto one reification API.

$$
\textbf{(T-Reify}_T\textbf{)}\qquad
\frac{\;\Gamma; \Delta_1 \vdash e_w : \mathsf{Witness}(T) \qquad \Gamma, x{:}T;\, \Delta_2 \vdash e_h : T\;}
     {\;\Gamma;\ \Delta_1, \Delta_2 \vdash \mathsf{reify}_T(e_w,\, x.\,e_h) : T\;}
$$

$$
\textbf{(T-Reify}_\forall\textbf{)}\qquad
\frac{\;\Gamma; \Delta_1 \vdash e_w : \mathsf{Witness}(T) \qquad \Gamma, x{:}T;\, \Delta_2 \vdash e_h : U\;}
     {\;\Gamma;\ \Delta_1, \Delta_2 \vdash \mathsf{reify}_\forall(e_w,\, x.\,e_h) : U\;}
$$

$$
\textbf{(T-Reify}_L\textbf{)}\qquad
\frac{\;\Gamma; \Delta_1 \vdash e_w : \mathsf{Witness}(T) \qquad \Gamma, x{:}T;\, \Delta_2 \vdash e_d : \mathsf{Witness}(U)\;}
     {\;\Gamma;\ \Delta_1, \Delta_2 \vdash \mathsf{reify}_L(e_w,\, x.\,e_d) : \mathsf{Witness}(U)\;}
$$

In each rule the witness $e_w$ carries an obligation $l \in \Delta_1$, and the handler consumes the payload variable $x : T$. In $\textbf{T-Reify}_T$ and $\textbf{T-Reify}_\forall$ the obligation is discharged into a value and no residue remains. In $\textbf{T-Reify}_L$ the obligation is consumed and a fresh successor $l' : \mathsf{Witness}(U)$ is threaded into the context; the successor is always $\mathsf{Partial}$, so deferral, whatever kind of witness it consumes, hands forward an ordinary reification obligation.

### The type discipline of reification

$\mathsf{reify}_T$ and $\mathsf{reify}_\forall$ differ not operationally but in the discipline they commit to, and the difference is deliberately visible in the syntax. $\mathsf{reify}_T$ is **type-preserving** (endomorphic): it obliges the handler to return a value in the witness's own type, so reification lands back in the domain the computation was expected to inhabit. $\mathsf{reify}_\forall$ is **type-transforming** (polymorphic): it permits projection into an arbitrary target $U$, allowing a branch to leave that domain. Although $\mathsf{reify}_T$ coincides with $\mathsf{reify}_\forall$ at $U := T$, the two are kept distinct precisely because their distinctness is *statically legible*.

Call a branch **codomain-coherent** when all of its reifications are type-preserving, and **codomain-divergent** when it uses at least one type-transforming reification. This predicate is decidable by inspection of the discharge sites, and it measures how tightly a branch stays within the domain fixed by its structure. It feeds signature honesty directly: a function whose branches are all codomain-coherent has honest codomain $\tau$, whereas each $\mathsf{reify}_\forall$ site widens the honest codomain to include its escape type — and because the widening is marked by a distinct construct, the true codomain is statically recoverable rather than inferred. Type-preserving reification is the default that keeps a function within one declared codomain; type-transforming reification is the explicit, analyzable act of leaving it.

### Deferral chains

Because $\mathsf{reify}_L$ yields a fresh obligation, obligations may be threaded through successive deferrals before a value is produced:

$$
l^{(0)} \xrightarrow{\ \mathsf{reify}_L\ } l^{(1)} \xrightarrow{\ \mathsf{reify}_L\ } \cdots \xrightarrow{\ \mathsf{reify}_L\ } l^{(k)} \xrightarrow{\ \mathsf{reify}_{T\,|\,\forall}\ } v \in V .
$$

Two independent properties govern such a chain. **Local linearity** is a property of $\Delta$: each $\mathsf{reify}_L$ step consumes its obligation $l^{(i)}$ exactly once, producing the successor $l^{(i+1)}$ — no occurrence is duplicated or dropped. **Chain finiteness** is a property of the fuel discipline: each $\mathsf{reify}_L$ draws one unit of fuel (Section 2.1), so in the default regime the length $k$ is bounded and the chain is finite. A finite chain terminates either by reaching a value-producing reifier, or by exhausting fuel — in which case the residue is itself an $\mathsf{Unbounded}$ witness, handled by the same discipline. The two properties are orthogonal — linearity is enforced by the context, finiteness by the fuel — and together they establish that no branch defers forever and none completes with an obligation outstanding.

### Additive branch combination

The multiplicative split governs subterms that both execute. Alternatives are different: since $\mathrm{select}_f$ executes exactly one branch, the branches *share* the incoming linear context and are each typed against it independently:

$$
\textbf{(T-Branch)}\qquad
\frac{\;\Gamma;\, \Delta \vdash \mathrm{body}_b : \tau \quad\text{for every } b \in B_f\;}
     {\;\Gamma;\, \Delta \vdash \mathrm{select}_f : \tau\;}
$$

Each branch introduces and discharges its own occurrences internally, so no occurrence from one branch is ever live during another. The collected space $L_f = \coprod_{b} \mathrm{obligations}(b)$ is thus a *disjunction* of admissible faces — one per branch — never their union. This is what forbids a function whose outcome space conflates disciplines the composition rules keep apart. Under multiplicative combination a function with an $\mathsf{Unbounded}$ branch and an $\mathsf{Awaited}$ branch would accumulate the inadmissible face $\{\mathsf{Unbounded}, \mathsf{Awaited}\}$ and fail to typecheck, though no single execution realizes both; additivity records each branch's disposition as an independent alternative, so a function may *span* several maximal profiles across its branches while every individual outcome remains a single admissible face. Domain segregation is enforced at the granularity of branches, not smeared across them.

### Summary of linear-context transformations

$$
\begin{aligned}
\textbf{T-Reify}_T &:\quad \Delta,\, l : \mathsf{Witness}(T) \;\longrightarrow\; \Delta \\
\textbf{T-Reify}_\forall &:\quad \Delta,\, l : \mathsf{Witness}(T) \;\longrightarrow\; \Delta \\
\textbf{T-Reify}_L &:\quad \Delta,\, l : \mathsf{Witness}(T) \;\longrightarrow\; \Delta,\, l' : \mathsf{Witness}(U) \quad (l'\ \mathsf{Partial})
\end{aligned}
$$

Every obligation $l \in L_f$ is therefore either discharged into the value space $V$ or transformed into a successor obligation $l'$; none can be silently dropped. Together with the introduction rules of Section 2.4, these judgments establish the invariant on which the whole calculus rests: a well-typed branch drives its linear context to empty.

This invariant is asserted here but not yet proved. Establishing it — and, through it, the honesty that the calculus was built to guarantee — is the work of the next chapter, which develops the metatheory of the system defined in Sections 2.1–2.5.
