/-
Copyright (c) 2026 Thomas Browning. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Thomas Browning
-/
module

public import Mathlib.Tactic -- imports all of the tactics in Lean's maths library

/-
Replace each sorry with a complete Lean proof, and reupload this file by 1pm Friday October 9.

You may only use the tactics from the first two lectures (`exact`, `intro`, `apply`, `specialize`,
`have`, `suffices`, `left`, `right`, `constructor`, `rcases`, `by_contra`, `by_cases`).
Do not use other tactics or term mode (if you know what that is).
-/

example (P Q : Prop) (hP : P) (hQ : P → Q) : P ∧ Q := by
  constructor
  · exact hP
  · apply hQ
    exact hP

example (P Q : Prop) (hP : P ∨ Q) (hQ : P → Q) : Q := by
  obtain h1 | h2 := hP
  · apply hQ
    exact h1
  · exact h2

example (P Q : Prop) (hP : P ∧ Q) : P ∨ Q := by
  obtain ⟨h, hQ⟩ := hP
  left
  exact h

example (h : ¬ True) : False := by
  apply h
  exact trivial

example (P : Prop) (hP : P) : ¬ ¬ P := by
  intro hnP
  apply hnP
  exact hP

example (P : Prop) (hP : ¬¬P) : P := by
  by_contra hnP
  apply hP
  exact hnP
