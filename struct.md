1. Title & Abstract: A concise summary (150–200 words) stating the problem (monadic complexity, bottom-type pollution) and your solution ($V \not\to \bot$, witness reification $W$, linear obligation tracking $L_f$).

2. Introduction & Motivation: Explain why traditional approaches fail (monad transformers create heavy cognitive friction; unchecked exceptions break totality) and present the high-level design goals of tacet.

3. Formal Semantics: The mathematical core you just developed:Result domain partitioning ($R = V \uplus W$) and pure value space ($V \not\to \bot$).Branch-indexed occurrence tracking ($L_f = \biguplus_{b \in B_f} \operatorname{obligations}(b)$).Reification and deferral morphisms ($\operatorname{reify}_T$, $\operatorname{reify}_{\forall}$, $\operatorname{defer}$).

4. Surface Syntax & Pragmatics: How the theory translates to user code (the single linear keyword, (op) := fn #Fixity operator bindings).

5. Compiler Pipeline & Verification: The 3-pass execution architecture, static operator harvesting, and dual-environment ($\Gamma, \Delta$) branch-wise verification.

6. Related Work: A brief comparison contrasting your model with Rust (linear typestates), Haskell (monadic effect stacks), and Clean/ATS (uniqueness types).

7. Conclusion & Future Work: Summary of achievements and next steps (formal mechanical proof in Coq/Agda, backend lowering).
