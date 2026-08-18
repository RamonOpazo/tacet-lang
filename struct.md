1. Title & Abstract: A concise summary (150–200 words) stating the problem (monadic complexity, bottom-type pollution) and your solution ($V \not\to \bot$, witness reification $W$, linear obligation tracking $L_f$).

2. Introduction & Motivation: Explain why traditional approaches fail (monad transformers create heavy cognitive friction; unchecked exceptions break totality) and present the high-level design goals of tacet.

3. Formal Semantics: The mathematical core you just developed:Result domain partitioning ($R = V \uplus W$) and pure value space ($V \not\to \bot$).Branch-indexed occurrence tracking ($L_f = \biguplus_{b \in B_f} \operatorname{obligations}(b)$).Reification and deferral morphisms ($\operatorname{reify}_T$, $\operatorname{reify}_{\forall}$, $\operatorname{defer}$).

4. Surface Syntax & Pragmatics: How the theory translates to user code (the single linear keyword, (op) := fn #Fixity operator bindings).

5. Compiler Pipeline & Verification: The 3-pass execution architecture, static operator harvesting, and dual-environment ($\Gamma, \Delta$) branch-wise verification.

6. Related Work: A brief comparison contrasting your model with Rust (linear typestates), Haskell (monadic effect stacks), and Clean/ATS (uniqueness types).

7. Conclusion & Future Work: Summary of achievements and next steps (formal mechanical proof in Coq/Agda, backend lowering).

Chapter 2: Dynamic Semantics and Reification Mechanics

- 2.1 Fuel, Capabilities, and Outcome Spaces
- 2.2 The Disposition Algebra & Flag Complex
- 2.3 Obligations as Total Spaces (Lf = ∫ obligations)
- 2.4 Type System & Linear Contexts (Δ)
- 2.5 Uniform Reification and Context Joining

Chapter 3: Metatheory and Soundness

- 3.1 Structural Properties & Context Admissibility
- 3.2 Strong Normalization of the Bounded Fragment
- 3.3 Type Safety (Preservation & Progress)
- 3.4 Global Branch Totality & Conservation
- 3.5 The Honesty Theorem

Chapter 4: Surface Syntax & Typestate Mechanics

- 4.1 Core Calculus vs Surface Syntac Mapping
  - Map the abstract syntax trees (AST) and core concepts from Chapter 2 ($W_L$, $\mathsf{reify}$, $\Delta$, capability declarations) to their human-friendly surface expressions.
  - Explain the syntactic sugar rules (e.g., how the postfix boundary operators ?, !, and ~ expand into core reification/discharge calls).
- 4.2-4.4 Surface Constructs & Mechanics
  - Detail affine typestates, linear context tracking in surface declarations, function signatures, and control-flow expressions.
- 4.5-end Complete Formal Surface Grammar
  - Provide the complete, unabridged grammar (using EBNF or standard notation).
  - Organize the grammar clearly into logical non-terminal categories:
    - Types & Capabilities: $\tau$, capabilities ($\mathsf{Unbounded!}$, etc.), dispositions.
    - Declarations & Signatures: Functions, typestate structures, module bindings.
    - Expressions & Statements: Value terms, linear bindings, branch constructs.
    - Boundary Operators & Reification: Postfix forms (?, !, ~), explicit reify blocks.
