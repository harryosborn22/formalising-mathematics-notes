/-
Copyright (c) 2026 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/
module

public import Mathlib.Tactic -- imports all of the tactics in Lean's maths library

/-
You may only use the tactics from the first two lectures (`exact`, `intro`, `apply`, `specialize`,
`have`, `suffices`, `left`, `right`, `constructor`, `rcases`, `by_contra`, `by_cases`).
Do not use other tactics or term mode (if you know what that is).
-/

example (P Q : Prop) (hP : P) (hQ : P → P ∧ Q) : Q := by
  specialize hQ hP
  rcases hQ with ⟨h1, h2⟩
  exact h2

example (P Q : Prop) (hP : P) (hQ : P ∨ Q → Q) : Q := by
  apply hQ
  left
  exact hP

example (P : Prop) (hP : P) : P ∧ P := by
  constructor
  · exact hP
  · exact hP


example (P : Prop) (hP : P ∨ P) : P := by
  rcases hP with (h1 | h2)
  · exact h1
  · exact h2


example (P : Prop) (hP : ¬ ¬ P) : P := by
  by_contra hnP
  apply hP
  intro hP'
  apply hnP
  exact hP'
