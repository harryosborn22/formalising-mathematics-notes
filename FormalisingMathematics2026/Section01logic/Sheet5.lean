/-
Copyright (c) 2025 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Kevin Buzzard
-/
import Mathlib.Tactic -- imports all the Lean tactics

/-!

# Logic in Lean, example sheet 5 : "iff" (`↔`)

We learn about how to manipulate `P ↔ Q` in Lean.

## Tactics

You'll need to know about the tactics from the previous sheets,
and also the following two new tactics:

* `rfl`
* `rw`

-/


variable (P Q R S : Prop)

example : P ↔ P := by
  rfl

example : (P ↔ Q) → (Q ↔ P) := by
  intro hPQ
  rw [hPQ]


example : (P ↔ Q) ↔ (Q ↔ P) := by
  constructor
  · intro hPQ
    rw [hPQ]
  · intro hQP
    rw [hQP]

example : (P ↔ Q) → (Q ↔ R) → (P ↔ R) := by
  intro hPQ hQR
  constructor
  · intro hP
    rw [← hQR]
    rwa [← hPQ]
  · intro hR
    rw [hPQ]
    rwa [hQR]

  -- The pattern `rw` then `assumption` is common enough that it can be abbreviated to `rwa`

example : P ∧ Q ↔ Q ∧ P := by
  constructor
  · intro nPQ
    obtain ⟨hP, hQ⟩ := nPQ
    constructor
    · exact hQ
    · exact hP
  · intro nQP
    obtain ⟨hQ, hP⟩ := nQP
    constructor
    · exact hP
    · exact hQ

example : (P ∧ Q) ∧ R ↔ P ∧ Q ∧ R := by
  constructor
  · intro hPQR
    obtain ⟨hPQ, hR⟩ := hPQR
    obtain ⟨hP, hQ⟩ := hPQ
    constructor
    · exact hP
    · constructor
      · exact hQ
      · exact hR
  · intro hPQR
    obtain ⟨hP, hQR⟩ := hPQR
    obtain ⟨hQ, hR⟩ := hQR
    constructor
    · constructor
      · exact hP
      · exact hQ
    · exact hR

example : (P ∧ Q) ∧ R ↔ P ∧ Q ∧ R := by
  constructor
  · intro hPQR
    constructor
    · exact hPQR.left.left
    · constructor
      · exact hPQR.left.right
      · exact hPQR.right
  · intro hPQR
    constructor
    · constructor
      · exact hPQR.left
      · exact hPQR.right.left
    · exact hPQR.right.right


example : P ↔ P ∧ True := by
  constructor
  · intro hP
    constructor
    · assumption
    · trivial
  · intro hPT
    exact hPT.left

example : False ↔ P ∧ False := by
  constructor
  · intro hF
    constructor
    · exfalso
      assumption
    · assumption
  · intro hPF
    exact hPF.right

example : (P ↔ Q) → (R ↔ S) → (P ∧ R ↔ Q ∧ S) := by
  intro PiffQ RiffS
  constructor
  · intro PnR
    constructor
    · rw [← PiffQ]
      exact PnR.left
    · rw [← RiffS]
      exact PnR.right
  · intro QnS
    constructor
    · rw [PiffQ]
      exact QnS.left
    · rw [RiffS]
      exact QnS.right


example : ¬(P ↔ ¬P) := by
  intro PiffnP
  obtain ⟨hPnP, hnPP⟩ := PiffnP
  by_cases hP : P
  · apply hPnP
    · assumption
    · assumption
  · apply hP
    apply hnPP
    exact hP
