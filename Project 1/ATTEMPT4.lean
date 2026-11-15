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
-- import Mathlib.Topology.Defs.Basic


-- variable {RealClosedDomain : Set.Ioo a b}
-- variable {RealClosedDomain : Set {x : ℝ | a < x ∧ x < b}}
-- variable {s : Set ℝ}
-- f supposed to be defined on [a,b] not ℝ
variable {a b : ℝ}
variable {D E : (Set ℝ)}
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

def is_lim_fun (D : Set ℝ) (f : ℝ → ℝ) (c : ℝ) (L : ℝ) :=
  ∀ ε > 0, ∃ δ > 0, ∀ x ∈ D, |x - c| < δ → |f x - L| < ε

def IsOpenSet (E : Set ℝ) :=
  ∀ x : E, ∃ δ > (0 : ℝ), ∀ h < δ, 0 < h → x - h ∈ E ∧ x + h ∈ E

@[fun_prop]
def LocalExtremumAtc (f : ℝ → ℝ) (c : ℝ) :=
  ∃ δ > (0 : ℝ), ∀ x ∈ {x : ℝ | c - δ < x ∧ x < c + δ}, (f x - f c ≤ 0 ∨ f c - f x ≤ 0)

def TendsToLFromLeft (f : ℝ → ℝ) (c : ℝ) (L : ℝ) :=
  ∀ ε > (0 : ℝ), ∃ δ > (0 : ℝ), ∀ x < (c : ℝ), |x - c| < δ → |f x - L| < ε

def TendsToLFromRight (f : ℝ → ℝ) (c : ℝ) (L : ℝ) :=
  ∀ ε > (0 : ℝ), ∃ δ > (0 : ℝ), ∀ x > (c : ℝ), |x - c| < δ → |f x - L| < ε

@[fun_prop]
def ContinuousAtc (f : ℝ → ℝ) (c : ℝ) :=
  (TendsToLFromLeft f c (f c)) ∧ (TendsToLFromRight f c (f c))

def DerivativeIsAtc (f : ℝ → ℝ) (c : ℝ) (L : ℝ) :=
  (TendsToLFromLeft (fun (x : ℝ) => (f x - f c)/(x - c)) c L) ∧ (TendsToLFromRight (fun (x : ℝ) => (f x - f c)/(x - c)) c L)

@[fun_prop]
def DifferentiableAtc (f : ℝ → ℝ) (c : ℝ) :=
  ∃ (L : ℝ), DerivativeIsAtc f c L

lemma δNbhdIsNonempty (c : ℝ) (δ : ℝ) (hδ : δ > 0) : {x : ℝ | (c - δ < x ∧ x < c + δ) ∧ x ≠ c}.Nonempty := by
  use (c + δ/2)
  constructor
  · constructor
    · bound
    · bound
  · bound

lemma leqandneq (a : ℝ) (b : ℝ) (haleqb : a ≤ b) (haneqb : a ≠ b) : a < b := by
  by_contra hageqb
  bound

theorem fermataltalt (f : ℝ → ℝ) (c : ℝ) {h_loc_ext : LocalExtremumAtc f c} {h_differentiable_at : DifferentiableAtc f c} : DerivativeIsAtc f c 0 := by
  choose L hL using h_differentiable_at
  suffices deriv_is_0 : L = 0 by
    rewrite [deriv_is_0] at hL
    exact hL
  rcases hL with ⟨tends_from_left, tends_from_right⟩
  choose δ1 hδ1 h_loc_ext using h_loc_ext
  choose x hxδ hxneqc using δNbhdIsNonempty c δ1 hδ1
  specialize h_loc_ext x hxδ
  by_cases hxleqc : x ≤ c
  · let ?ε : ℝ := ?_
    · have hε : ε > 0 := by
      specialize tends_from_left ε hε
      choose δ2 hδ2 tends_from_left using tends_from_left
      specialize tends_from_left x
      specialize tends_from_left (@leqandneq x c hxleqc hxneqc)
      suffices final : |x - c| < δ2 by
        specialize tends_from_left final














  ·



theorem boundedness {h_f_cont : ∀ x ∈ {x : ℝ | a ≤ x ∧ x ≤ b}, ∀ ε > (0 : ℝ), ∃ δ > (0 : ℝ)}

theorem Cuahcy
