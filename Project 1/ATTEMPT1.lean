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

universe u

variable {a b : ℝ}
-- variable {RealClosedDomain :  ∈ Set.Ioo a b}
-- variable {RealClosedDomain : Set {x : ℝ | a < x ∧ x < b}}
-- f supposed to be defined on [a,b] not ℝ
variable {D : Set ℝ}
variable {f : D → ℝ} {f' : ℝ → ℝ}

/-
BASIC RESULTS
-/

theorem ineqresult {a b : ℝ} : a ≤ b → a - b ≤ 0 := by
  intro hab
  linarith

theorem eq_imp_leq {x : ℝ} : x = 0 → 0 ≤ x := by bound

theorem le_imp_leq {x : ℝ} : x < 0 → x ≤ 0 := by bound

theorem ineqresult2 {a h : ℝ} {ha : a ≤ 0} {hh : h < 0} : 0 ≤ (a/h) := by
  sorry

def test (gg) :=
  ∀ m : gg, 1 < 0

def LocalExtremumAt {D : Set ℝ} (f : D → ℝ) (c : D) :=
  -- ∃ δ > (0 : ℝ), ∀ h ∈ {h : ℝ | 0 < |h| ∧ |h| < δ}, (f (c + h) ≤ f c ∨ f c ≤ f (c + h))
  ∃ δ > (0 : ℝ), ∀ h : (Set.Ioo (-δ) δ), f (c + h.val) ≤ f c ∨ f c ≤ f (c + h))

def TendsToLFromLeft (f : ℝ → ℝ) (c : ℝ) (L : ℝ) :=
  ∀ ε > (0 : ℝ), ∃ δ > (0 : ℝ), ∀ (x : Set.Ioo (c - δ) c), |f x - L| < ε

def TendsToLFromRight (f : ℝ → ℝ) (c : ℝ) (L : ℝ) :=
  ∀ ε > (0 : ℝ), ∃ δ > (0 : ℝ), ∀ (x : Set.Ioo c (c + δ)), |f x - L| < ε

def ContinuousAtc (f : ℝ → ℝ) (c : ℝ) :=
  (TendsToLFromLeft f c (f c)) ∧ (TendsToLFromRight f c (f c))

def DerivativeIsAtc {D : Set ℝ} (f : D → ℝ) (f' : ℝ → ℝ) (c : ℝ) :=
  (TendsToLFromRight (f - (f c)) c (f' c))

def DifferentiableAtc {D : Set ℝ} (f : D → ℝ) (c : ℝ) :=
  ∃ f' : ℝ → ℝ, DerivativeIsAtc f f' c


/-
FERMATSTHEOREM
-/

theorem fermat {D : Set ℝ} {c : D} {f : D → ℝ} {h_loc_ext_at : LocalExtremumAt f c} {h_diff_at : DifferentiableAtc f c} : f' c = 0 := by
  choose δ hδ h_loc_ext_at using h_loc_ext_at
  have hexists : (Set.Ioo (-δ) δ).Nonempty := by
    use (δ/2)
    norm_num
    constructor
    · linarith
    · exact hδ
  choose h hh using hexists
  specialize h_loc_ext_at h hh
  rcases h_loc_ext_at with (h_loc_max | h_loc_min)
  · apply (@ineqresult (f (c + h)) (f c)) at h_loc_max
    by_cases hNeg : (h < 0)
    · have divNeg : 0 ≤ (f (c + h) - f c)/h := by
        exact (@ineqresult2 (f (c + h) - f c) (h) (h_loc_max) (hNeg))
      sorry
    · sorry -- proving when h is greater than 0
  · sorry -- proving when h has a local minimum


-- theorem boundedness {h_f_cont : ∀ x ∈ {x : ℝ | a ≤ x ∧ x ≤ b}, ∀ ε > (0 : ℝ), ∃ δ > (0 : ℝ)}
