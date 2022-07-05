# Expertise and information: an epistemic logic perspective

This repository contains the LaTeX source for the paper, the appendix
(containing missing proofs), and formalisation of some of the proofs in Lean.

- [Paper](latex/main.pdf)
- [Appendix](latex/appendix.pdf)

The proofs were checked with Lean version 3.35.1. To build, set up
[leanproject](https://leanprover-community.github.io/leanproject.html) and run
`leanproject get-mathlib-cache` followed by `leanproject build`, from the
`lean` directory.

The following results/definitions have been formalised (links go to the
relevant section of the source code):

* [Definition 1](lean/src/basic.lean#L36)
* [Proposition 2](lean/src/frame_properties.lean#L31)
* [Definition 2](lean/src/epistemic_logic.lean#L314)
* [Definition 3](lean/src/epistemic_logic.lean#L21)
* [Lemma 2](lean/src/epistemic_logic.lean#L55)
* Lemma 3: [1](lean/src/epistemic_logic.lean#L82), [2](lean/src/epistemic_logic.lean#L198), [3](lean/src/epistemic_logic.lean#L206)
* [Theorem 3](lean/src/epistemic_logic.lean#L437)
* [Lemma 4](lean/src/soundness.lean#L7)
* Lemma 5: [1](lean/src/axiom_system.lean#L214), [2](lean/src/axiom_system.lean#L237), [3](lean/src/axiom_system.lean#L247), [4](lean/src/axiom_system.lean#L286)
* [Lemma 6](lean/src/axiom_system.lean#L439)
* Lemma 7: [1](lean/src/completeness.lean#L23), [2](lean/src/completeness.lean#L63), [3](lean/src/completeness.lean#L71)
* Lemma 8: [1](lean/src/completeness.lean#L114), [2](lean/src/completeness.lean#L206), [3](lean/src/completeness.lean#L228)
* Corollary 1: [1](lean/src/completeness.lean#L173), [2](lean/src/completeness.lean#L194)
* [Lemma 9](lean/src/completeness.lean#L284)
* [Theorem 4](lean/src/completeness.lean#L667)
* [Proposition 4](lean/src/multi_source.lean#L373)
* [Lemma 10](lean/src/multi_source.lean#L177)
* [Proposition 6](lean/src/multi_source.lean#L487)
* [Theorem 8](lean/src/multi_source.lean#L571)

This list is automatically generated from the Lean/LaTeX source by the scripts
in the `python` directory.
