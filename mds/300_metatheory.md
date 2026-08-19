# Chapter 3 · Metatheory

Chapter 2 defined the calculus and closed with an invariant it did not prove: that a well-typed branch drives its linear context to empty, so that no obligation is ever silently dropped. This chapter establishes that invariant and, through it, the property the calculus was designed to guarantee — that a function's signature tells the whole truth about what its evaluation can do. Statements are given in full and with full rigor; proofs are sketched, with the remaining details deferred to a companion development. The sketches are written to be read, not merely certified: each is meant to make clear *why* the result holds, so that the honesty theorem is understood before its proof is consulted.

## 3.1 What we prove, and why it matters

The results of this chapter are not independent; they form a short dependency chain, and seeing the chain first makes the individual statements legible.

```
   Admissibility preservation (Lemma 1)         Normalization (Lemma 2)
              │                                          │
              ▼                                          │
      Preservation (Thm 1) ───► Progress (Thm 2)         │
              │                                          │
              ▼                                          │
      Conservation (Thm 3) ───► Global Branch Totality   │
              │                                          │
              └───────────────────┬──────────────────────┘
                                  ▼
                            Honesty (Thm 4)
```

Two structural lemmas underwrite everything. *Admissibility preservation* says reduction never leaves the algebra of admissible dispositions; *normalization* says the fuel-bounded, loop-free fragment always terminates. On the first rest *preservation* and *progress* — the usual syntactic-soundness pair, guaranteeing that types are stable under reduction and that a well-typed program is never stuck. Preservation in turn yields *conservation*: a value carries no outstanding obligation, so every obligation raised is answered exactly once. Conservation is Global Branch Totality restated, and together with normalization it delivers the capstone, *honesty*.

Informally, honesty is the following. A mainstream signature $f : A \to \tau$ oversells: evaluation may also throw or diverge, invisibly. In Tacet, once a function is well-typed, its signature and the dispositions of its branches disclose *every* way evaluation can depart from returning a value of type $\tau$ — failure, deferral, unbounded recursion, productive looping — and nothing is left to a silent exception, a hidden default, or a bottom value. Honesty is disclosure, not the elimination of everything that could go wrong.

## 3.2 The formal system, recalled

For self-containment we recall the notation of Chapter 2; nothing here is new.

**Configurations and fuel.** Reduction acts on configurations $\langle e, \varphi \rangle$ with a fuel value $\varphi \in \mathbb{N} \cup \{\infty\}$. Exactly two reduction forms draw one unit of fuel — the unfolding of a recursive call and the deferral $\mathsf{reify}_L$ — and at $\varphi = 0$ such a redex introduces a $\mathsf{Bound}$ obligation (typed as an $\mathsf{Unbounded}$ witness) rather than becoming stuck. Every other step leaves $\varphi$ fixed. An intrinsically-infinite $\mathsf{Loop}$ does *not* draw fuel. A function evaluates with $\varphi = \infty$ exactly when it declares the $\mathsf{Unbounded}^{-}$ capability, recorded in $\mathrm{caps}(f)$.

**The result domain.** Branch evaluation lands in $R = V \uplus W$, where $V$ is the value domain and $W = W_L$ the witnesses, each of which exposes at least one obligation. Bottom is never an element: $\bot \notin R$, unconditionally. A renounced phenomenon is absorbed into the identity disposition $\mathsf{Total}$ and hence into $V$.

**The two contexts.** Judgments $\Gamma;\, \Delta \vdash e : \tau$ carry an unrestricted lexical context $\Gamma$ (weakening and contraction admissible) and a linear context $\Delta$ — a multiset of unconsumed obligation occurrences, admitting neither. Sequential subterms split $\Delta$ multiplicatively; alternative branches share it additively.

**Dispositions.** The live witness kinds of a context, $\mathrm{kinds}(\Delta) \subseteq \mathcal{K}_L = \{\mathsf{Partial}, \mathsf{Unbounded}, \mathsf{Awaited}, \mathsf{Loop}\}$, must at all times form a face of the flag complex $\mathcal{X}$, whose maximal faces are $\{\mathsf{Partial}, \mathsf{Unbounded}\}$, $\{\mathsf{Partial}, \mathsf{Awaited}\}$, and $\{\mathsf{Loop}\}$.

**The rules.** Introduction ($\textbf{T-Intro}_\kappa$, guarded by admissibility; $\textbf{T-Absorb}_\kappa$ for the renounced case) deposits occurrences into $\Delta$; the three reifiers $\mathsf{reify}_T$, $\mathsf{reify}_\forall$, $\mathsf{reify}_L$ discharge them — the first two into $V$, the third into a fresh $\mathsf{Partial}$ successor; $\textbf{T-Branch}$ combines alternatives additively.

## 3.3 Structural lemmas

**Lemma 1 (Admissibility preservation).** *If $\Gamma; \Delta \vdash e : \tau$ with $\mathrm{kinds}(\Delta) \in \mathcal{X}$, and $\langle e, \varphi \rangle \to \langle e', \varphi' \rangle$, then $\Gamma; \Delta' \vdash e' : \tau$ with $\mathrm{kinds}(\Delta') \in \mathcal{X}$.*

*Proof sketch.* The live kinds change only at introduction and discharge. Introduction is guarded: $\textbf{T-Intro}_\kappa$ fires only when $\mathrm{kinds}(\Delta) \cup \{\kappa\}$ is a face, so it cannot leave $\mathcal{X}$. Type-preserving and type-transforming reification remove an occurrence, and a face minus a vertex is again a face, since $\mathcal{X}$ is downward closed. Deferral replaces an occurrence by a $\mathsf{Partial}$ successor; $\mathsf{Partial}$ is compatible with every face except those containing $\mathsf{Loop}$, and $\mathsf{Loop}$ never co-occurs with a live obligation in the first place (its introduction demands an empty $\Delta$). Every reachable context is therefore admissible. $\qquad\blacksquare$

The lemma is what turns Chapter 2's "impossible combinations" from prose into an operational fact: the type system cannot even transiently reach a disposition outside the complex.

**Lemma 2 (Normalization of the bounded, loop-free fragment).** *If $\cdot;\, \cdot \vdash e : \tau$ with $\mathrm{caps}(e) = \varnothing$ and $e$ contains no $\mathsf{Loop}$, then every reduction sequence from $\langle e, \varphi \rangle$, for any $\varphi \in \mathbb{N}$, is finite.*

*Proof sketch.* Assign to each configuration the pair $(\varphi, \lVert e \rVert)$, where $\lVert e \rVert$ is the structural size of $e$, and compare pairs lexicographically. The two fuel-drawing steps — recursion and $\mathsf{reify}_L$ — strictly decrease the first component. Every other reduction leaves the first component untouched and strictly decreases the second, since it removes a redex without introducing unbounded regeneration. A strictly descending sequence in $\mathbb{N} \times \mathbb{N}$ under the lexicographic order cannot be infinite, because that order is well-founded. Hence no infinite reduction exists.

The measure also explains precisely which programs are excluded. The first component can fail to decrease only when $\varphi = \infty$, which is the $\mathsf{Unbounded}^{-}$ capability; the second can fail to decrease only when a construct regenerates itself without consuming fuel, which is exactly an intrinsic $\mathsf{Loop}$. These are the two — and only two — sources of legitimate non-termination in the calculus, and both are disclosed. $\qquad\blacksquare$

## 3.4 Syntactic soundness

**Theorem 1 (Preservation).** *If $\Gamma; \Delta \vdash e : \tau$ and $\langle e, \varphi \rangle \to \langle e', \varphi' \rangle$, then $\Gamma; \Delta' \vdash e' : \tau$, where $\Delta'$ is related to $\Delta$ by exactly one of*

$$
\begin{aligned}
\textbf{intro:} &\quad \Delta' = \Delta,\, l{:}\mathsf{Witness}(T) &&(\mathrm{kinds}(\Delta)\cup\{\kappa\} \in \mathcal{X}) \\
\textbf{reify}_{T},\ \textbf{reify}_\forall: &\quad \Delta' = \Delta \setminus \{l\} && \\
\textbf{reify}_L: &\quad \Delta' = (\Delta \setminus \{l\}),\, l'{:}\mathsf{Witness}(U) &&(l'\ \mathsf{Partial}) \\
\textbf{other:} &\quad \Delta' = \Delta, &&
\end{aligned}
$$

*and $\varphi' \le \varphi$ in every case, with $\varphi' < \varphi$ on recursion and $\mathsf{reify}_L$.*

*Proof sketch.* Induction on the typing derivation, using the substitution lemmas appropriate to each context — weakening-and-contraction substitution for $\Gamma$, multiplicative (occurrence-splitting) substitution for $\Delta$. Each reduction rule of the operational semantics corresponds to one typing rule of Sections 2.4–2.5; matching them gives the type $\tau$ unchanged and the stated transformation of $\Delta$, read directly off the rule. The fuel inequality is immediate from the reduction relation, in which only recursion and $\mathsf{reify}_L$ decrement $\varphi$. $\qquad\blacksquare$

The theorem records the one fact the rest of the chapter leans on: reduction changes $\Delta$ only in the four disciplined ways listed, so the linear context is never altered behind the type system's back.

**Theorem 2 (Progress).** *If $\cdot;\, \Delta \vdash e : \tau$, then either $e$ is a value in $V(\tau)$, or $\langle e, \varphi \rangle$ takes a step.*

*Proof sketch.* By canonical forms on the type of the leftmost redex. The two situations that might otherwise strand a computation both fail to arise. Fuel exhaustion is not a stuck state: a fuel-drawing redex at $\varphi = 0$ steps to a $\mathsf{Bound}$ obligation. And a reifier applied to a value with no obligation cannot occur in well-typed code, because a reifier demands an occurrence of witness type $\mathsf{Witness}(T)$; a renounced phenomenon has already been absorbed into $\mathsf{Total}$ and so presents as an ordinary value, carrying no obligation for a reifier to fail on. A $\mathsf{Loop}$, finally, is always able to iterate, and may additionally receive an out-of-band break. $\qquad\blacksquare$

## 3.5 Linear soundness

**Theorem 3 (Conservation).** *If $\cdot;\, \Delta \vdash v : \tau$ and $v$ is a value, then $\Delta = \cdot$. Consequently every obligation raised along a reduction is either discharged into $V$ or deferred to a unique $\mathsf{Partial}$ successor — exactly once, never duplicated, never dropped.*

*Proof sketch.* A value inhabits $V$, and $V$ is the $\mathsf{Total}$ fibre of the result domain, whose disposition is empty. So a value has no live obligation, i.e. $\Delta = \cdot$. That every obligation is consumed exactly once is then the content of the linear-context transformation summary of Section 2.5, read cumulatively: introduction adds an occurrence, the two value-reifiers remove one, deferral swaps one for a successor, and linearity forbids any rule that would silently discard a live occurrence. $\qquad\blacksquare$

**Corollary (Global Branch Totality).** *Every complete branch of a well-typed function is typeable as $\Gamma;\, \cdot \vdash \mathrm{body}_b : \tau$: it reaches a value only with an empty linear context. The "no value" outcome — the loud, terminal failure of Section 2.3 — is therefore unreachable in well-typed code.*

This corollary is the precise form of the invariant Chapter 2 asserted. A branch cannot slip into the value domain while owing an obligation, and it cannot defer forever (Lemma 2); so its only route to completion is to answer every obligation it raised.

## 3.6 Honesty

Everything above converges here.

**Theorem 4 (Honesty).** *Let $\cdot;\, \cdot \vdash e : \tau$.*

*(i) Bounded honesty. If $\mathrm{caps}(e) = \varnothing$ and $e$ contains no $\mathsf{Loop}$, then evaluation terminates and $\llbracket e \rrbracket \in V(\tau)$: a value of exactly the declared type. No witness escapes, by Conservation; no exceptional outcome escapes, since $E$ is reified as $\mathsf{Partial}$ obligations and discharged; and no divergence occurs, by Lemma 2. The gap opened in Chapter 1 closes entirely,*

$$
\llbracket f \rrbracket : A \to \tau + E + \{\bot\}
\qquad\text{reduces to}\qquad
f : A \to \tau .
$$

*(ii) General honesty. Without those two restrictions, the semantic outcome space is uniformly*

$$
\llbracket e \rrbracket \in \tau + W, \qquad \bot \notin R \ \text{unconditionally},
$$

*and every non-value outcome is disclosed. Exceptional termination is reified into $W$ as $\mathsf{Partial}$ obligations, all discharged in well-typed code. Non-termination arises only under a declared $\mathsf{Unbounded}^{-}$ capability — visible in the signature — or within a $\mathsf{Loop}$ branch — visible in that branch's disposition. In neither case is a bottom value produced; $\bot$ appears nowhere in the outcome space.*

*Proof sketch.* Part (i) combines Conservation (no witness and no exceptional outcome escapes a value) with Lemma 2 (the fragment terminates), leaving $V(\tau)$ as the only possible result. Part (ii): Preservation and Lemma 1 confine every reduction to the admissible fragment, so the sole steps beyond the terminating argument of (i) are those unlocked by a declared capability — whose phenomena are absorbed into $\mathsf{Total}$ — and $\mathsf{Loop}$ iteration, whose non-termination is carried by a $\mathsf{Break}$ obligation. Each such source is recorded in $\mathrm{caps}(e)$ or in a branch's disposition, both parts of the signature. And since $\bot \notin R$ holds unconditionally, no reduction ever yields a bottom value. $\qquad\blacksquare$

### A worked trace

To see the machinery discharge a single obligation end to end, take a partial head function on integer lists. Its empty branch has no value to return, so it raises an obligation with `tacet`:

$$
\mathsf{head}(xs) \;=\; \mathrm{select} \begin{cases} xs = [\,] & \mapsto\ \mathsf{tacet}(\mathsf{Empty}) \\ xs = h :: \_ & \mapsto\ h \end{cases}
$$

The non-empty branch is $\mathsf{Total}$: it returns $h : \mathsf{Int}$ with $\Delta = \cdot$. The empty branch is not. Evaluating $\mathsf{tacet}(\mathsf{Empty})$ introduces a $\mathsf{Reify}$ obligation of payload type $\mathsf{Int}$ into $\Delta$ — the symbol $\mathsf{Empty}$ is its value-level proxy — and forces a $\mathsf{Partial}$ witness into $\mathsf{head}$'s contract; the branch now carries $\Delta = \{\, l : \mathsf{Witness}(\mathsf{Int}) \,\}$, where $l$ is the obligation and $\mathsf{Witness}(\mathsf{Int})$ records the payload type inherited from that forced witness. By Global Branch Totality the branch cannot complete in this state, so the obligation must leave. It has three exits, and the honest signature of $\mathsf{head}$ is determined by which is taken.

If $\mathsf{head}$ discharges nothing itself, the obligation surfaces at the boundary as its forced witness, and $\mathsf{head}$ is honestly typed

$$
\mathsf{head} : \mathsf{List}\,\mathsf{Int} \to \mathsf{Witness}(\mathsf{Int}),
$$

announcing to every caller that the result must be reified before it can be used as an $\mathsf{Int}$. When a caller invokes $\mathsf{head}$, that witness exposes the obligation into the caller's own $\Delta$ (Section 2.3); a caller that wants a fallback then discharges it with a type-preserving reifier, and the linear context empties:

$$
\underbrace{\{\, l : \mathsf{Witness}(\mathsf{Int}) \,\}}_{\text{obligation live}} \;\xrightarrow{\ \mathsf{reify}_T(\,\cdot\,,\ x.\,0)\ }\; \underbrace{\cdot}_{\text{discharged}}, \qquad \text{result} \in V(\mathsf{Int}).
$$

Had the caller instead deferred first — $\mathsf{reify}_L(\,\cdot\,,\ x.\,\mathsf{tacet}(\dots))$ — the occurrence would have been replaced by a fresh $\mathsf{Partial}$ successor $l'$, threading the obligation one step downstream, each step drawing fuel, until some later $\mathsf{reify}_T$ or $\mathsf{reify}_\forall$ landed it in $V$. At no point is the empty case allowed to masquerade as an $\mathsf{Int}$, and at no point does a bottom appear. The signature of $\mathsf{head}$ is exactly as honest as its code: $\mathsf{Int}$ if the failure is answered internally, $\mathsf{Witness}(\mathsf{Int})$ if it is passed on.

$$
\underbrace{\{\, l : \mathsf{Witness}(\mathsf{Int}) \,\}}_{\text{obligation live}} \;\xrightarrow{\ \mathsf{reify}_T(\,\cdot\,,\ x.\,0)\ }\; \underbrace{\cdot}_{\text{discharged}}, \qquad \text{result} \in V(\mathsf{Int}).
$$

Had the caller instead deferred first — $\mathsf{reify}_L(\,\cdot\,,\ x.\,\mathsf{tacet}(\dots))$ — the occurrence would have been replaced by a fresh $\mathsf{Partial}$ successor $l'$, threading the obligation one step downstream, each step drawing fuel, until some later $\mathsf{reify}_T$ or $\mathsf{reify}_\forall$ landed it in $V$. At no point is the empty case allowed to masquerade as an $\mathsf{Int}$, and at no point does a bottom appear. The signature of $\mathsf{head}$ is exactly as honest as its code: $\mathsf{Int}$ if the failure is answered internally, $\mathsf{Witness}(\mathsf{Int})$ if it is passed on.

### What honesty does not claim

The theorem is deliberately modest in three respects, and stating the limits sharpens the claim.

It does not decide the halting problem. Honesty never asserts that an $\mathsf{Unbounded}^{-}$ function terminates; it asserts only that the *possibility* of non-termination is declared rather than hidden. The calculus trades a guarantee it cannot give for a disclosure it can.

It does not eliminate failure, divergence, or effects. A $\mathsf{Partial}$ function may still fail, a $\mathsf{Loop}$ may still run forever, an $\mathsf{Awaited}^{-}$ effect may still fire and be forgotten. What honesty removes is not these phenomena but their *invisibility*: each is forced to appear in a type, a capability, or a disposition.

And it does not make every well-typed program total. Totality in the strong sense holds only for the fragment of part (i). Elsewhere, non-termination remains possible — but only along the two disclosed routes, and never as a silent $\bot$. This is the exact sense in which Tacet is honest rather than merely safe: it does not promise that nothing goes wrong, only that nothing goes wrong *unannounced*.
