# Chapter 2 · Formal semantics

We now develop the calculus sketched in the introduction. Its organizing idea is a separation between _values_ and _computational obligations_: the value a computation produces is kept distinct from the obligations its evaluation incurs, so that a strong value space can be maintained under an honest signature.

The chapter proceeds in six steps. Section 2.1 fixes the result domain into which evaluation lands, together with the small-step reduction relation — equipped with a fuel discipline — on which the later metatheory depends. Section 2.2 introduces _dispositions_, the small algebra that governs which computational phenomena may co-occur. Section 2.3 characterizes witnesses and the obligations they expose, distinguishing the stateful witness from the nominal obligation. Section 2.4 gives the introduction forms through which obligations enter the linear context, and connects the semantic account of obligations to their syntactic bookkeeping. Section 2.5 gives the discharge rules through which obligations are consumed. Section 2.6 states the metatheory, culminating in the honesty theorem.

## 2.1 Function evaluation, the result domain, and reduction

### Two-stage evaluation

Given a function $f$, let $A$ denote its input-value domain, $B$ the universe of branches, and $B_f \subseteq B$ the set of branches occurring in the body of $f$. Evaluation proceeds in two stages: an input first determines the branch to be executed, and that branch is then evaluated,

$$
A \;\xrightarrow{\;\mathrm{select}_f\;}\; B_f \;\xrightarrow{\;\mathrm{eval}\;}\; R.
$$

The selection stage captures the control-flow structure of $f$: for an input $a \in A$, $\mathrm{select}_f$ identifies the branch $b \in B_f$ whose execution $a$ determines. The evaluation stage then reduces $b$ to an element of the _result domain_ $R$.

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

Here $V$ is the domain of ordinary language values and $W$ is the domain of witnesses produced during evaluation. The disjointness is deliberate: a witness is not a language value and cannot be used interchangeably with an element of $V$. Ordinary evaluation has the form $b \mapsto v \in V$, while evaluation may instead produce a witness, $b \mapsto w \in W$. Thus $R$ is the complete range of branch-evaluation outcomes, and $V$ is the sub-range consisting of ordinary values.

The value domain is moreover kept apart from the bottom element,

$$
\bot \notin V .
$$

Bottom is not an ordinary value and is never produced as the outcome of a successful evaluation. This matters because the semantics does not model the phenomena carried by witnesses as ordinary bottom-valued computation; such phenomena are represented explicitly, as elements of $W$ (Section 2.3). We will shortly strengthen $\bot \notin V$ to $\bot \notin R$ for the default evaluation regime.

### Reduction with fuel

To state progress, preservation, and — above all — honesty, we need a reduction relation to reason about, not merely the input–output map $\mathrm{eval}$. We equip evaluation with a _fuel_ budget that bounds the depth of self-referential computation.

A **configuration** is a pair $\langle e, \varphi \rangle$ consisting of an expression $e$ and a fuel value

$$
\varphi \in \mathbb{N} \cup \{\infty\}.
$$

Reduction is a relation $\langle e, \varphi \rangle \to \langle e', \varphi' \rangle$ on configurations, governed by two disciplines.

**(Fuel.)** The two reduction forms that can recur without structurally shrinking the expression — the unfolding of a recursive call and the deferral of an obligation (Section 2.5) — each draw one unit of fuel:

$$
\frac{\varphi > 0}{\langle \mathcal{R}[e],\, \varphi \rangle \to \langle \mathcal{R}'[e],\, \varphi - 1 \rangle}
\qquad(\text{recursion / defer}),
$$

with the convention $\infty - 1 = \infty$. When such a redex is reached at $\varphi = 0$, it does not become stuck and does not diverge; it reduces instead to a witness of kind $\mathsf{Unbounded}$ (Section 2.2), recording that the budget was exhausted:

$$
\frac{}{\langle \mathcal{R}[e],\, 0 \rangle \to \langle \mathsf{witness}_{\mathsf{Unbounded}},\, 0 \rangle}.
$$

Every other reduction step leaves the fuel value unchanged.

**(Capability.)** A function evaluates with $\varphi = \infty$ if and only if it declares the $\mathsf{Unbounded!}$ capability in its signature; otherwise it evaluates with a finite budget $\varphi \in \mathbb{N}$. Thus the two regimes are one relation at two fuel settings, and the capability reads semantically as the lifting of the fuel bound. Because $\mathsf{Unbounded!}$ is recorded in the signature, the choice of regime is disclosed to every caller.

### Boundedness and totality

The result domain never contains bottom:

$$
\bot \notin R,
$$

unconditionally, in either fuel regime. Tacet does not model non-termination as a value; what the two regimes differ in is only whether reduction is _guaranteed to halt_.

In the default regime, $\varphi \in \mathbb{N}$ is finite. Because recursion and deferral strictly decrease $\varphi$ and every other step leaves it fixed, no configuration admits an infinite reduction sequence: fuel exhaustion converts would-be divergence into a finite reduction ending in an $\mathsf{Unbounded}$ witness. Evaluation therefore always halts, $\mathrm{eval}$ is _total_ on $B_f$, and every branch reduces to some element of $R$. The fuel-exhaustion witness is not $\bot$; it is an ordinary $\mathsf{Unbounded}$ witness in $W$. Like every witness that exposes an obligation, it is discharged through the single reification API (Section 2.5); its _default resolution_, $\mathsf{Bound}$, is precisely the fuel discipline just described. Section 2.2 fixes these per-kind default resolutions, and Section 2.5 the uniform reifiers that can override them.

In the renounced regime, $\varphi = \infty$, the fuel argument no longer forces termination, and reduction of such a branch may continue without end. This does _not_ reintroduce $\bot$. The possibility of non-termination is disclosed by the $\mathsf{Unbounded!}$ capability in the signature; when such a computation does halt, its result is absorbed into $\mathsf{Total}$ — an ordinary value — leaving no residual witness or obligation. A computation that fails to halt produces no semantic value at all, but it produces no bottom either: $\bot$ remains outside $R$, and the risk it runs is exactly the one its capability announced. This is the governing principle in its sharpest form: honesty is the _disclosure of the risk_, never the production of $\bot$.

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
                   values  witnesses         (non-termination under Unbounded!
                                              is a disclosed risk, not a value)
```

_Figure 2.1._ Function evaluation. An input selects a branch from $B_f$, which evaluates to an element of the result domain $R = V \uplus W$; bottom is never an element of $R$. In the default (finite-fuel) regime evaluation is guaranteed to halt. Declaring $\mathsf{Unbounded!}$ sets $\varphi = \infty$: reduction may then run without end, but that possibility is disclosed by the capability, and any value it does produce is absorbed into $\mathsf{Total}$ — never a bottom value. The internal structure of $V$ and $W$ is developed in Sections 2.2–2.3.

## 2.2 Dispositions and their composition

### The disposition of an outcome

The partition of the result domain in Section 2.1 is not primitive; it is induced by the _disposition_ of a branch evaluation — the collection of computational phenomena its evaluation realizes. The default disposition is $\mathsf{Total}$: a branch that realizes no phenomenon beyond producing a value is $\mathsf{Total}$, and its outcome is an ordinary value in $V$. $\mathsf{Total}$ is the identity disposition — the absence of any witnessed phenomenon.

When evaluation realizes a phenomenon that is not an ordinary value — a possible failure, an unbounded recursion, an asynchronous wait, an intrinsically infinite loop — the branch acquires a corresponding _witness kind_. The linear kinds are

$$
\mathcal{K}_L \;=\; \{\, \mathsf{Partial},\ \mathsf{Unbounded},\ \mathsf{Awaited},\ \mathsf{Loop} \,\}.
$$

Each linear kind, when realized, causes its witness to _expose_ a named obligation:

| Witness     | Exposes | Domain |
| ----------- | ------- | ------ |
| `Total`     | —       | `V`    |
| `Partial`   | `Reify` | `W_L`  |
| `Unbounded` | `Bound` | `W_L`  |
| `Awaited`   | `Sync`  | `W_L`  |
| `Loop`      | `Break` | `W_L`  |

The obligation's name is its entire content. Consistent with the thin-obligation ontology of Section 2.3, a $\mathsf{Bound}$ obligation records nothing but the nominal fact that an unboundedness occurred and must be answered; a $\mathsf{Reify}$ obligation, that a partiality occurred; and so on. $\mathsf{Total}$ exposes nothing, because it is already a value.

The partition of Section 2.1 now reads off the disposition. A $\mathsf{Total}$ branch lands in $V$; a branch that exposes at least one obligation lands in $W_L$. These are the two fibres of the disposition — so $R = V \uplus W$ with $W = W_L$ — not primitive buckets. There is no third fibre: as the next subsection shows, a renounced phenomenon is absorbed into $\mathsf{Total}$ rather than surviving as an obligation-free witness, so every witness that persists exposes an obligation.

### Renunciation

Two of the linear kinds admit a _renounced_ form, written with a bang:

$$
\mathsf{Unbounded!} \qquad \mathsf{Awaited!}
$$

Renunciation removes the phenomenon from the linear domain entirely. Rather than exposing an obligation, a renounced phenomenon is _absorbed into_ $\mathsf{Total}$ after evaluation: an $\mathsf{Unbounded!}$ recursion that halts, or an $\mathsf{Awaited!}$ effect that is launched, resolves to an ordinary value and leaves no witness behind. The phenomenon is not answered but _accepted_, and the acceptance is disclosed as a capability in the function's signature (Section 2.1).

Because a renounced form is thus the identity disposition, it composes trivially, and no admissibility question arises. A computation that is both failable and renounced-unbounded has disposition $\{\mathsf{Partial}\} \otimes \mathsf{Total} = \{\mathsf{Partial}\}$; the renounced axis contributes nothing. This is why the exclusions of the composition algebra (below) constrain only _live_ linear kinds — the pairs $\{\mathsf{Unbounded}, \mathsf{Awaited}\}$ and the like — and never a renounced form, which is already $\mathsf{Total}$.

Renunciation is available only for $\mathsf{Unbounded}$ and $\mathsf{Awaited}$ — the phenomena whose obligation one may legitimately decline: an unbounded recursion may be allowed to run, and an asynchronous effect may be launched without awaiting it (the fire-and-forget sink). Partiality and looping have no renounced form. A failure must be answered and a productive loop must be broken, so $\mathsf{Reify}$ and $\mathsf{Break}$ obligations cannot be declined — only discharged.

### Non-termination without bottom

Three kinds bear on non-termination, and all three obey the principle that Tacet produces no bottom (Section 2.1); they differ only in how the possibility of non-termination is accounted for.

- $\mathsf{Unbounded}$ is fuel-bounded by default. Evaluation is guaranteed to halt; on budget exhaustion the witness exposes a $\mathsf{Bound}$ obligation. No unbounded run occurs.
- $\mathsf{Unbounded!}$ renounces the bound. Evaluation may run without end, disclosed by the capability; any value it does produce is absorbed into $\mathsf{Total}$, and non-termination is never a bottom value.
- $\mathsf{Loop}$ exposes a $\mathsf{Break}$ obligation. A loop is intrinsically infinite: it does not draw on the fuel budget, and it iterates productively until its $\mathsf{Break}$ obligation is discharged. Uniquely among the kinds, a $\mathsf{Break}$ is discharged _out-of-band_ — by an explicit break originating outside the loop body, either an interrupt ($\mathtt{Ctrl}$-$\mathtt{C}$) or a call to a breaking function — rather than within the forward flow of evaluation. Until that break lands the branch does not complete; a loop never broken runs productively forever. This is not bottom: the branch simply never yields a value, and the $\mathsf{Break}$ obligation discloses, statically, that completion is contingent on an explicit break.

In every case the possibility of non-termination is reified — as a fuel bound, a renounced capability, or a $\mathsf{Break}$ obligation — and never as an element of $R$.

### Composition

Dispositions compose. A single computation may realize several phenomena at once — an asynchronous computation that can also fail, say — so its disposition is in general a _set_ of linear kinds. Composition is orthogonal: writing a branch's disposition as $S \subseteq \mathcal{K}_L$, the disposition algebra is

$$
(\mathcal{D},\ \otimes,\ \mathsf{Total}), \qquad \mathsf{Total} = \varnothing, \qquad S \otimes S' = S \cup S',
$$

a commutative, associative, idempotent operation with $\mathsf{Total}$ as identity — a bounded join-semilattice — made _partial_ by the fact that not every combination is admissible.

The inadmissible combinations are exactly the four pairs

$$
\{\mathsf{Loop}, \mathsf{Unbounded}\}, \quad
\{\mathsf{Loop}, \mathsf{Awaited}\}, \quad
\{\mathsf{Loop}, \mathsf{Partial}\}, \quad
\{\mathsf{Unbounded}, \mathsf{Awaited}\}.
$$

Admissibility is determined entirely by pairs and is downward closed, so the admissible dispositions are exactly the _cliques_ of the compatibility graph $G$ whose edges are the surviving pairs:

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

A **witness** is _thick_. It is produced from inside a computation and captures the evaluation state at the point of witnessing. In particular it carries two things: the payload type $T$ of the value that was expected, and the disposition $S \subseteq \mathcal{K}_L$ — the face recording which phenomena it realizes. Its type is accordingly indexed by both,

$$
\mathsf{Witness}_S(T),
$$

and is fully determined at the moment of production, because the state that determines it is present there. A witness knows what it is.

An **obligation** is _thin_. It carries no payload and no state; its entire content is its own identity. An obligation is a _signal_ — a nominal token whose message is simply that a computation has left the value space at a definite point and must be brought back. The obligation exposed by a $\mathsf{Partial}$ witness is a $\mathsf{Reify}$ obligation, that exposed by an $\mathsf{Unbounded}$ witness a $\mathsf{Bound}$ obligation, and so on; the name _is_ the meaning. Nothing about the recovered value's type lives in the obligation — that lives in the witness.

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

The obligations of a function are collected across its branches. For each branch $b \in B_f$, let $\mathrm{obligations}(b)$ denote the occurrences arising in $b$ — the union of $\mathrm{expose}(w)$ over the witnesses $w$ produced there. The obligations of $f$ are then the disjoint union

$$
L_f \;=\; \coprod_{b \in B_f} \mathrm{obligations}(b).
$$

The disjoint union is doing real work: $L_f$ tracks _occurrences_, not the distinct obligation names that occur. This is the total space of the family $\mathrm{obligations} : B_f \to \mathbf{Set}$ — its Grothendieck construction $\int \mathrm{obligations}$ — whose elements are pairs $(b, l)$ of a branch and an occurrence within it. It comes with two canonical maps:

$$
B_f \;\xleftarrow{\;\pi\;}\; L_f \;\xrightarrow{\;\mathrm{name}\;}\; L,
$$

the fibration $\pi$ recording _which branch_ an occurrence arose in, and the naming map $\mathrm{name}$ recording _which_ underlying obligation it is an occurrence of, within the universe $L$ of all obligations.

The point of the construction is that $\mathrm{name}$ need not be injective. If two distinct branches $b_1, b_2 \in B_f$ each raise an occurrence of the same underlying obligation $l \in L$, those occurrences are nevertheless distinct elements of $L_f$ — distinguished by their fibres under $\pi$ — even though $\mathrm{name}$ identifies them in $L$. Branch structure is thereby preserved when the obligations of a function are collected, and this is exactly why $L_f$ is associated with the function while $L$ is the universe: $L$ describes the possible obligation names, whereas $L_f$ records the particular occurrences the branches of $f$ induce. (The original presentation wrote $L_f \hookrightarrow L$; the inclusion is too strong, since it would force distinct occurrences of one name to collapse. The correct arrow is the generally non-injective $\mathrm{name} : L_f \to L$.)

### The linear context, by inheritance

The bridge to the syntactic bookkeeping of Section 2.5 is now short. The linear context $\Delta$ tracks occurrences of $L_f$, and an entry $l : \mathsf{Witness}(T)$ in $\Delta$ does not assert that the obligation _is_ a witness. It records the occurrence $l$ together with the payload type $T$ _inherited from the witness that exposed it_ — so that a reifier knows the type of the value its handler will receive. The obligation contributes its identity through $\mathrm{name}$; the witness contributes the type through $\mathrm{expose}$. There is no tension between the semantic separation of $W_L$ from $L_f$ and the syntactic annotation of occurrences with witness types: the annotation is simply the image of a witness under $\mathrm{expose}$, read together with the witness's own payload.

### The force of a dropped obligation

An obligation's message is: _rectify here, or produce no value._ In Tacet the second alternative is not a silent $\bot$ but an explicit, terminal, loudly surfaced failure. This is the semantic force behind treating obligations linearly. An unconsumed obligation cannot decay into a quiet default, because its only alternative to being discharged is a visible error — never a bottom, and never an implicit fallback. The linear discipline of Section 2.5, and the Global Branch Totality it enforces, is precisely the static guarantee that a well-typed branch never reaches that alternative: every occurrence in $L_f$ that a branch raises is, in well-typed code, discharged before the branch completes.

## 2.4 Introduction

Section 2.3 characterized obligations and the domain $L_f$ that collects them, but not how an obligation comes to be there in the first place. This section gives the _introduction_ forms — the constructs through which a witness is raised and its obligations enter the linear context — and connects the semantic collection $L_f$ to the syntactic context $\Delta$ that the discharge rules of Section 2.5 will consume.

### The `tacet` construct

Linear obligations are not values the language produces directly. The language instead offers the `tacet` construct as the syntactic means by which a computation raises a $\mathsf{Partial}$ witness deliberately.

Tags form a distinguished class of values, and among them a subclass admits interpretation by `tacet`:

$$
V_{T} \hookrightarrow V, \qquad V_{Te} \hookrightarrow V_{T}.
$$

During evaluation, a `tacet` expression whose tag lies in $V_{Te}$ is interpreted as a $\mathsf{Partial}$ witness:

$$
\mathsf{tacet} : V_{Te} \rightsquigarrow W_L.
$$

The squiggle is deliberate. `tacet` is not an ordinary semantic morphism from values to witnesses; it is an _elaboration_ step — the interpretation of a syntactic construct during evaluation. We do not compose across it as though it were a morphism in the semantic category. Everything downstream of the witness it produces — `expose`, and the discharge maps of Section 2.5 — is an ordinary semantic map and composes normally. The full path from a tacet-able tag to an obligation is therefore

$$
V_{Te} \;\rightsquigarrow\; W_L \;\xrightarrow{\;\mathrm{expose}\;}\; \mathcal{P}_{\mathrm{fin}}(L_f),
$$

with the elaboration boundary crossed exactly once, at the squiggle. This preserves the separation of the value domain from the obligation domain: $V_{Te} \subseteq V$ does not import $L$ into $V$. The tag remains a value; its interpretation produces a witness; and only the witness exposes the obligation.

### The four introduction sites

`tacet` is the sole introducer of $\mathsf{Partial}$. The other three linear kinds are introduced by built-in language constructs, one apiece:

- recursion introduces $\mathsf{Unbounded}$;
- the dedicated asynchronous construct introduces $\mathsf{Awaited}$;
- an intrinsically-infinite loop introduces $\mathsf{Loop}$.

Write $\mathrm{intro}_\kappa$ for the corresponding form, so that $\mathrm{intro}_{\mathsf{Partial}}$ is `tacet`. Each raises a witness of its kind, which then exposes the obligation named for that kind (Section 2.2).

### Introduction rules

An introduction deposits a fresh obligation occurrence into the linear context, guarded by admissibility: the new kind must be compatible with those already live. Writing $\mathrm{kinds}(\Delta)$ for the witness kinds live in $\Delta$ and $\mathcal{X}$ for the flag complex of admissible dispositions (Section 2.2):

$$
\textbf{(T-Intro}_\kappa\textbf{)}\qquad
\frac{\;\Gamma; \Delta \vdash e : T \qquad \mathrm{kinds}(\Delta) \cup \{\kappa\} \in \mathcal{X} \qquad \kappa! \notin \mathrm{caps}(f)\;}
     {\;\Gamma;\ \Delta,\, l : \mathsf{Witness}(T) \vdash \mathrm{intro}_\kappa(e) : \mathsf{Witness}(T)\;}
\quad (l\ \text{fresh})
$$

The admissibility premise is what makes the "impossible combinations" of Section 2.2 a typing fact rather than prose: an introduction that would leave the flag complex simply has no derivation. For $\kappa = \mathsf{Loop}$ it forces $\mathrm{kinds}(\Delta) = \varnothing$, since $\mathsf{Loop}$ composes with nothing — a loop cannot be introduced while any other obligation is live. The capability premise $\kappa! \notin \mathrm{caps}(f)$ is vacuous for the non-renounceable kinds $\mathsf{Partial}$ and $\mathsf{Loop}$, and selects the _live_ case for $\mathsf{Unbounded}$ and $\mathsf{Awaited}$; the renounced case is the following rule.

When the corresponding capability is declared, the same introduction form is _transparent_: it raises no witness, touches no obligation, and its phenomenon is absorbed into $\mathsf{Total}$ (Section 2.2):

$$
\textbf{(T-Absorb}_\kappa\textbf{)}\qquad
\frac{\;\Gamma; \Delta \vdash e : T \qquad \kappa! \in \mathrm{caps}(f)\;}
     {\;\Gamma; \Delta \vdash \mathrm{intro}_\kappa(e) : T'\;}
\qquad \kappa \in \{\mathsf{Unbounded}, \mathsf{Awaited}\}.
$$

The result type $T'$ is $T$ for a renounced recursion ($\mathsf{Unbounded!}$), which yields the value it would have computed, and the trivial type for a renounced asynchronous launch ($\mathsf{Awaited!}$), which returns immediately as a fire-and-forget sink. The linear context is unchanged: renunciation adds nothing to $\Delta$, exactly as its status as the identity disposition requires. (The asynchronous construct and its precise typing remain to be fixed; the rule above records its shape.)

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

Whatever obligation a witness exposes, it is discharged by one of three reifiers, distinguished only by _where the result lands_:

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

$\mathsf{reify}_T$ and $\mathsf{reify}_\forall$ differ not operationally but in the discipline they commit to, and the difference is deliberately visible in the syntax. $\mathsf{reify}_T$ is **type-preserving** (endomorphic): it obliges the handler to return a value in the witness's own type, so reification lands back in the domain the computation was expected to inhabit. $\mathsf{reify}_\forall$ is **type-transforming** (polymorphic): it permits projection into an arbitrary target $U$, allowing a branch to leave that domain. Although $\mathsf{reify}_T$ coincides with $\mathsf{reify}_\forall$ at $U := T$, the two are kept distinct precisely because their distinctness is _statically legible_.

Call a branch **codomain-coherent** when all of its reifications are type-preserving, and **codomain-divergent** when it uses at least one type-transforming reification. This predicate is decidable by inspection of the discharge sites, and it measures how tightly a branch stays within the domain fixed by its structure. It feeds signature honesty directly: a function whose branches are all codomain-coherent has honest codomain $\tau$, whereas each $\mathsf{reify}_\forall$ site widens the honest codomain to include its escape type — and because the widening is marked by a distinct construct, the true codomain is statically recoverable rather than inferred. Type-preserving reification is the default that keeps a function within one declared codomain; type-transforming reification is the explicit, analyzable act of leaving it.

### Deferral chains

Because $\mathsf{reify}_L$ yields a fresh obligation, obligations may be threaded through successive deferrals before a value is produced:

$$
l^{(0)} \xrightarrow{\ \mathsf{reify}_L\ } l^{(1)} \xrightarrow{\ \mathsf{reify}_L\ } \cdots \xrightarrow{\ \mathsf{reify}_L\ } l^{(k)} \xrightarrow{\ \mathsf{reify}_{T\,|\,\forall}\ } v \in V .
$$

Two independent properties govern such a chain. **Local linearity** is a property of $\Delta$: each $\mathsf{reify}_L$ step consumes its obligation $l^{(i)}$ exactly once, producing the successor $l^{(i+1)}$ — no occurrence is duplicated or dropped. **Chain finiteness** is a property of the fuel discipline: each $\mathsf{reify}_L$ draws one unit of fuel (Section 2.1), so in the default regime the length $k$ is bounded and the chain is finite. A finite chain terminates either by reaching a value-producing reifier, or by exhausting fuel — in which case the residue is itself an $\mathsf{Unbounded}$ witness, handled by the same discipline. The two properties are orthogonal — linearity is enforced by the context, finiteness by the fuel — and together they establish that no branch defers forever and none completes with an obligation outstanding.

### Additive branch combination

The multiplicative split governs subterms that both execute. Alternatives are different: since $\mathrm{select}_f$ executes exactly one branch, the branches _share_ the incoming linear context and are each typed against it independently:

$$
\textbf{(T-Branch)}\qquad
\frac{\;\Gamma;\, \Delta \vdash \mathrm{body}_b : \tau \quad\text{for every } b \in B_f\;}
     {\;\Gamma;\, \Delta \vdash \mathrm{select}_f : \tau\;}
$$

Each branch introduces and discharges its own occurrences internally, so no occurrence from one branch is ever live during another. The collected space $L_f = \coprod_{b} \mathrm{obligations}(b)$ is thus a _disjunction_ of admissible faces — one per branch — never their union. This is what forbids a function whose outcome space conflates disciplines the composition rules keep apart. Under multiplicative combination a function with an $\mathsf{Unbounded}$ branch and an $\mathsf{Awaited}$ branch would accumulate the inadmissible face $\{\mathsf{Unbounded}, \mathsf{Awaited}\}$ and fail to typecheck, though no single execution realizes both; additivity records each branch's disposition as an independent alternative, so a function may _span_ several maximal profiles across its branches while every individual outcome remains a single admissible face. Domain segregation is enforced at the granularity of branches, not smeared across them.

### Summary of linear-context transformations

$$
\begin{aligned}
\textbf{T-Reify}_T &:\quad \Delta,\, l : \mathsf{Witness}(T) \;\longrightarrow\; \Delta \\
\textbf{T-Reify}_\forall &:\quad \Delta,\, l : \mathsf{Witness}(T) \;\longrightarrow\; \Delta \\
\textbf{T-Reify}_L &:\quad \Delta,\, l : \mathsf{Witness}(T) \;\longrightarrow\; \Delta,\, l' : \mathsf{Witness}(U) \quad (l'\ \mathsf{Partial})
\end{aligned}
$$

Every obligation $l \in L_f$ is therefore either discharged into the value space $V$ or transformed into a successor obligation $l'$; none can be silently dropped. Together with the introduction rules of Section 2.4, these judgments establish the invariant that a well-typed branch drives its linear context to empty, which is the content of the metatheory to come.

## 2.6 Metatheory

We now state the properties that make the honesty claim precise. Statements are given in full; proofs are sketched, with the details deferred to a companion development. Throughout, reduction is the relation on configurations $\langle e, \varphi \rangle$ of Section 2.1, with recursion and $\mathsf{reify}_L$ the only fuel-drawing steps; $\mathsf{Loop}$ iteration does not draw fuel. We write $\mathrm{kinds}(\Delta)$ for the witness kinds live in $\Delta$, $\mathcal{X}$ for the flag complex of admissible dispositions (Section 2.2), and $\mathrm{caps}(e)$ for the capabilities declared in $e$'s signature.

### Structural lemmas

**Lemma 1 (Admissibility preservation).** _If $\Gamma; \Delta \vdash e : \tau$ with $\mathrm{kinds}(\Delta) \in \mathcal{X}$, and $\langle e, \varphi \rangle \to \langle e', \varphi' \rangle$, then $\Gamma; \Delta' \vdash e' : \tau$ with $\mathrm{kinds}(\Delta') \in \mathcal{X}$._

_Proof sketch._ Introduction is the only rule that enlarges $\mathrm{kinds}(\Delta)$, and $\textbf{T-Intro}_\kappa$ fires only when $\mathrm{kinds}(\Delta) \cup \{\kappa\}$ is a face. Discharge by $\mathsf{reify}_T$ or $\mathsf{reify}_\forall$ only shrinks the live kinds; $\mathsf{reify}_L$ replaces an occurrence by a $\mathsf{Partial}$ successor, and $\mathsf{Partial}$ is compatible with every non-$\mathsf{Loop}$ face, so it never leaves $\mathcal{X}$. Hence reachable contexts stay admissible. $\qquad\blacksquare$

**Lemma 2 (Strong normalization of the bounded, loop-free fragment).** _If $\cdot;\, \cdot \vdash e : \tau$ with $\mathrm{caps}(e) = \varnothing$ and $e$ contains no $\mathsf{Loop}$, then no infinite reduction issues from $\langle e, \varphi \rangle$ for any $\varphi \in \mathbb{N}$._

_Proof sketch._ Order configurations by the pair $(\varphi,\, \lVert e \rVert)$ lexicographically, where $\lVert \cdot \rVert$ is structural size. Recursion and $\mathsf{reify}_L$ strictly decrease $\varphi$; every other reduction leaves $\varphi$ fixed and strictly decreases $\lVert e \rVert$. Since $\mathbb{N} \times \mathbb{N}$ under the lexicographic order is well-founded, no infinite descent exists. The two excluded features are exactly the two that escape this measure: $\mathsf{Unbounded!}$ sets $\varphi = \infty$, and $\mathsf{Loop}$ iterates without drawing fuel. $\qquad\blacksquare$

Lemma 2 is the technical core of honesty: on the fragment that declares no capability and runs no intrinsic loop, evaluation genuinely terminates, so $\bot$ is absent by construction rather than by fiat.

### Preservation and progress

**Theorem 1 (Preservation).** _If $\Gamma; \Delta \vdash e : \tau$ and $\langle e, \varphi \rangle \to \langle e', \varphi' \rangle$, then $\Gamma; \Delta' \vdash e' : \tau$, where $\Delta'$ is related to $\Delta$ by exactly one of_

$$
\begin{aligned}
\textbf{intro:} &\quad \Delta' = \Delta,\, l{:}\mathsf{Witness}(T) &&(\mathrm{kinds}(\Delta)\cup\{\kappa\} \in \mathcal{X}) \\
\textbf{reify}_{T},\ \textbf{reify}_\forall: &\quad \Delta' = \Delta \setminus \{l\} && \\
\textbf{reify}_L: &\quad \Delta' = (\Delta \setminus \{l\}),\, l'{:}\mathsf{Witness}(U) &&(l'\ \mathsf{Partial}) \\
\textbf{other:} &\quad \Delta' = \Delta, &&
\end{aligned}
$$

_with $\varphi' \le \varphi$ always and $\varphi' < \varphi$ on recursion and $\mathsf{reify}_L$._

_Proof sketch._ Induction on the typing derivation, with the standard substitution lemmas — unrestricted substitution for $\Gamma$, multiplicative for $\Delta$. Each reduction form corresponds to one rule of Sections 2.4–2.5, and the context bookkeeping is read off that rule; the fuel bound follows from the reduction relation of Section 2.1. $\qquad\blacksquare$

**Theorem 2 (Progress).** _If $\cdot; \Delta \vdash e : \tau$, then either $e$ is a value in $V(\tau)$, or $\langle e, \varphi \rangle$ steps._

_Proof sketch._ By canonical forms on the type of the head redex. No well-typed closed term is stuck: fuel exhaustion is a reduction step to an $\mathsf{Unbounded}$ witness rather than a stuck state (Section 2.1), and a $\mathsf{Loop}$ iterates productively (and may additionally take an out-of-band break step). Discharge cannot be misapplied, because a reifier requires a $\mathsf{Witness}(T)$ argument; a renounced phenomenon has already been absorbed into $\mathsf{Total}$ and is an ordinary value, so there is no obligation-free witness for a reifier to fail on. $\qquad\blacksquare$

### Conservation and totality

**Theorem 3 (Conservation).** _If $\cdot; \Delta \vdash v : \tau$ and $v$ is a value, then $\Delta = \cdot$. Consequently every obligation introduced along a reduction is either discharged into $V$ or deferred to a unique $\mathsf{Partial}$ successor, exactly once — never duplicated, never dropped._

_Proof sketch._ A value inhabits $V$, and $V$ is the $\mathsf{Total}$ (empty-disposition) fibre of the result domain (Section 2.2). Linearity forbids discarding a live hypothesis, so no occurrence can survive into a value; the transformation summary of Section 2.5 shows each occurrence is consumed exactly once. $\qquad\blacksquare$

**Corollary (Global Branch Totality).** _Every complete branch of a well-typed function is typeable as $\Gamma;\, \cdot \vdash \mathrm{body}_b : \tau$. The "no value" outcome — the loud, terminal failure of Section 2.3 — is unreachable in well-typed code._

### Honesty

**Theorem 4 (Honesty).** _Let $\cdot;\, \cdot \vdash e : \tau$._

_(i) Bounded honesty. If $\mathrm{caps}(e) = \varnothing$ and $e$ contains no $\mathsf{Loop}$, then evaluation terminates and $\llbracket e \rrbracket \in V(\tau)$ — a value of exactly the declared type. No witness escapes (Conservation), no exceptional outcome escapes ($E$ is reified as $\mathsf{Partial}$ obligations and discharged), and no divergence occurs (Lemma 2). The gap of Chapter 1 collapses completely:_

$$
\llbracket f \rrbracket : A \to \tau + E + \{\bot\}
\qquad\text{reduces to}\qquad
f : A \to \tau .
$$

_(ii) General honesty. Without those restrictions, the semantic outcome space is uniformly_

$$
\llbracket e \rrbracket \in \tau + W, \qquad \bot \notin R \ \text{(unconditionally)},
$$

_and every non-value outcome is disclosed. Exceptional termination is reified into $W$ as $\mathsf{Partial}$ obligations, all discharged in well-typed code. Non-termination arises only under a declared $\mathsf{Unbounded!}$ capability — visible in the signature — or within a $\mathsf{Loop}$ branch — visible in that branch's disposition; in neither case is a bottom value produced. Bottom never appears anywhere in the outcome space._

_Proof sketch._ Part (i) is Conservation (no escaping witness, no escaping $E$) together with Lemma 2 (no divergence). For part (ii), Preservation and Lemma 1 confine every reduction to the admissible fragment; the only steps not covered by the bounded argument are those enabled by a declared capability ($\mathsf{Unbounded!}$, $\mathsf{Awaited!}$), whose phenomena are absorbed into $\mathsf{Total}$, and $\mathsf{Loop}$ iteration, whose non-termination is carried by a $\mathsf{Break}$ obligation. Each such source is recorded either in $\mathrm{caps}(e)$ or in a branch's disposition, both of which the signature carries. Since $\bot \notin R$ holds unconditionally (Section 2.1), no reduction ever produces a bottom value. $\qquad\blacksquare$

This is the sense in which Tacet is honest: **honesty is disclosure, not the absence of $\bot$.** Whatever a well-typed function can do beyond returning a value of its declared type — fail, defer, run unboundedly, loop — is exactly what its signature and its branch dispositions announce, and nothing a function can do is left to a silent bottom, a hidden exception, or an implicit default.
