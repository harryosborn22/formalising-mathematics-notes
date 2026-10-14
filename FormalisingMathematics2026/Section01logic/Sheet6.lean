/-
Copyright (c) 2025 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Kevin Buzzard
-/
import Mathlib.Tactic -- imports all the Lean tactics


/-!

# Logic in Lean, example sheet 6 : "or" (`∨`)

We learn about how to manipulate `P ∨ Q` in Lean.

## Tactics

You'll need to know about the tactics from the previous sheets,
and also the following tactics

* `left` and `right`
* `cases` (new functionality)

-/


-- Throughout this sheet, `P`, `Q`, `R` and `S` will denote propositions.
variable (P Q R S : Prop)

example : P → P ∨ Q := by
  intro hP
  left
  exact hP

example : Q → P ∨ Q := by
  intro hQ
  right
  exact hQ

-- Here are a few ways to break down a disjunction
example : P ∨ Q → (P → R) → (Q → R) → R := by
  intro hPoQ
  cases hPoQ with
  | inl h => sorry
  | inr h => sorry

example : P ∨ Q → (P → R) → (Q → R) → R := by
  intro hPoQ hPR hQR
  obtain hP | hQ := hPoQ
  · specialize hPR hP
    exact hPR
  · specialize hQR hQ
    exact hQR

example : P ∨ Q → (P → R) → (Q → R) → R := by
  rintro (hP | hQ)
  · intro hPR hQR
    specialize hPR hP
    exact hPR
  · intro hPR hQR
    specialize hQR hQ
    exact hQR

-- symmetry of `or`
example : P ∨ Q → Q ∨ P := by
  rintro (hP | hQ)
  · right
    assumption
  · left
    assumption

-- associativity of `or`
example : (P ∨ Q) ∨ R ↔ P ∨ Q ∨ R := by
  constructor
  · rintro (PnQ | hR)
    · rcases PnQ with hP | hQ
      · left
        assumption
      · right
        left
        assumption
    · right
      right
      assumption
  ·

example : (P → R) → (Q → S) → P ∨ Q → R ∨ S := by
  sorry

example : (P → Q) → P ∨ R → Q ∨ R := by
  sorry

example : (P ↔ R) → (Q ↔ S) → (P ∨ Q ↔ R ∨ S) := by
  sorry

-- de Morgan's laws
example : ¬(P ∨ Q) ↔ ¬P ∧ ¬Q := by
  sorry

example : ¬(P ∧ Q) ↔ ¬P ∨ ¬Q := by
  sorry
