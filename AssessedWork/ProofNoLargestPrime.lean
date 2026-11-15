module

public import Mathlib.Tactic -- imports all of the tactics in Lean's maths library

/-
Start by assuming there exists a natural number that is the largest prime

Show that there must exist a prime larger than that

So the assumption is false
-/

/- Let P be the proposition that there are infinitely many primes -/
variable (P : Prop)

example (P : Prop) : P := by
  sorry
