# Lean Final Project: Quotients and Homomorphisms in Universal Algebra

## Overview

This project formalizes a well known result from **universal algebra** in the Lean proof assistant:

> Let $A$ and $B$ be two algebras of the same signature and let $f : A \to B $
> be a **surjective homomorphism**, then the quotient algebra $A / \ker(f)$ is **isomorphic** to $B$.

The development is carried out in a general algebraic setting (with arbitrary signatures), then the result is 
demonstrated on two concrete groups.

---

## Main Result

Let:
- \( A \), \( B \) be algebras over the same signature,
- \( f : A \to B \) be a surjective homomorphism.

Then the project formalizes the proof that:
\[
A / \ker(f) \cong B
\]

---

## File Structure

- **`FinalProject/UniversalAlgebra.lean`**  
  Contains the main formalization part.

- **`FinalProject.lean`**  
  Example application on additive group \( (\mathbb{R}, +) \),
  and multiplicative group \( (\mathbb{R}^+, \cdot) \).
  
---

## Dependencies

- Lean 4
- Mathlib
