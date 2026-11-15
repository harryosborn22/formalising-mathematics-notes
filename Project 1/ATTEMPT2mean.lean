/-
HERE WE GO
-/
module

public import Mathlib.Tactic -- imports all of the tactics in Lean's maths library
import Mathlib.Order.Interval.Set.Defs
import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Algebra.Ring.Basic
import Mathlib.Analysis.SpecificLimits.Basic


-- variable {RealClosedDomain : Set.Ioo a b}
-- variable {RealClosedDomain : Set {x : ℝ | a < x ∧ x < b}}
-- variable {s : Set ℝ}
-- f supposed to be defined on [a,b] not ℝ
variable {a b : ℝ}
variable {f : ℝ → ℝ} {f' : ℝ → ℝ}

--axiom ab : a < b

--axiom opensubclosed : ∀ (a b : ℝ), (Set.Ioo a b) ⊆ (Set.Icc a b)

/-
BASIC RESULTS
-/

theorem ableq {a b : ℝ} : a ≤ b ↔ a - b ≤ 0 := by
  constructor
  · bound
  · bound

theorem divnegleq {a b : ℝ} {hb : b < 0} : a ≤ 0 → (a/b) ≥ 0 := by
  simp
  ring_nf
  sorry


def LocalExtremumAtc (f : ℝ → ℝ) (c : ℝ) :=
  ∃ δ > (0 : ℝ), ∀ x ∈ (Set.Ioo (c - δ) (c + δ)), (f x ≤ f c ∨ f c ≤ f x)

def TendsToLFromLeft (f : ℝ → ℝ) (c : ℝ) (L : ℝ) :=
  ∀ ε > (0 : ℝ), ∃ δ > (0 : ℝ), ∀ (x : ℝ), x - c < δ → |f x - L| < ε

def TendsToLFromRight (f : ℝ → ℝ) (c : ℝ) (L : ℝ) :=
  ∀ ε > (0 : ℝ), ∃ δ > (0 : ℝ), ∀ (x : ℝ), c - x < δ → |f x - L| < ε

def ContinuousAtc (f : ℝ → ℝ) (c : ℝ) :=
  (TendsToLFromLeft f c (f c)) ∧ (TendsToLFromRight f c (f c))

def DerivativeIsAtc (f : ℝ → ℝ) (c : ℝ) (L : ℝ) :=
  (TendsToLFromLeft (fun (x : ℝ) => (f x - f c)/(x - c)) c L) ∧ (TendsToLFromRight (fun (x : ℝ) => (f x - f c)/(x - c)) c L)

def DifferentiableAtc (f : ℝ → ℝ) (c : ℝ) :=
  ∃ (L : ℝ), DerivativeIsAtc f c L

/-
FERMATSTHEOREM
-/

-- theorem fermat_predicate : {α : Sort u_1} {β : α → Sort u_4} (x : α) (f : (x : α) → β x) :

--change ∀ᶠ (x : ℝ) in nhds c, f c ≤ f x at h_loc_min
--change {x : ℝ | f c ≤ f x} ∈ nhds c at h_loc_min

theorem fermatalt {c : ℝ} {f : ℝ → ℝ} {h_loc_ext : LocalExtremumAtc f c} {h_differentiable_at : DifferentiableAtc f c} : DerivativeIsAtc f c 0 := by
  choose L h_differentiable_at using h_differentiable_at
  rcases h_differentiable_at with ⟨h_tends_from_left, h_tends_from_right⟩
  choose δ hδ h_loc_ext using h_loc_ext
  have cballcontainsc : (Set.Ioo (c - δ) (c + δ)).Nonempty := by
    use (c)
    norm_num
    exact hδ
  choose x hx using cballcontainsc
  specialize h_loc_ext x hx
  -- for h < 0 (tending to from left)
  rcases h_loc_ext with (h_loc_min | h_loc_max)
  · rewrite [@ableq (f x) (f c)] at h_loc_min
    specialize h_tends_from_right δ hδ
    choose δ1 hδ1 h_tends_from_right using h_tends_from_right
    specialize h_tends_from_right x

    have hxc : x - c < 0 := by
      sorry
    apply @divnegleq (f x - f c) (x - c) h1 at h_loc_min
    sorry




  · sorry

theorem fermat {c : ℝ} {f : ℝ → ℝ} {h_loc_ext : LocalExtremumAtc f c} {h_differentiable_at : DifferentiableAtc f c} : DerivativeIsAtc f c 0 := by
  choose L h_differentiable_at using h_differentiable_at
  rcases h_differentiable_at with ⟨h_tends_from_left, h_tends_from_right⟩
  choose δ hδ h_loc_ext using h_loc_ext
  have cballcontainsc : (Set.Ioo (c - δ) (c + δ)).Nonempty := by
    use (c)
    norm_num
    exact hδ
  choose x hx using cballcontainsc
  specialize h_loc_ext x hx
  -- for h < 0 (tending to from left)
  constructor
  · intro ε hε
    rcases h_loc_ext with (h_loc_min | h_loc_max)
    · specialize h_tends_from_left ε hε
      choose δ1 hδ1 h_tends_from_left using h_tends_from_left
      use δ1
      constructor
      · exact hδ1
      · intro x1 hx1
        norm_num
        specialize h_tends_from_left x1 hx1
        simp at h_tends_from_left




      sorry
    · sorry
  · sorry




theorem boundedness {h_f_cont : ∀ x ∈ {x : ℝ | a ≤ x ∧ x ≤ b}, ∀ ε > (0 : ℝ), ∃ δ > (0 : ℝ)}


theorem mean_value_theorem {D : Set ℝ} {f : D → ℝ} {f' : interior D → ℝ} {f_cont : sorry} {f_diff : sorry} : ∃ (t : interior D), f' t = f  := by
  exact (@fermat a a b)
