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
variable {f : D → ℝ} {f' : E → ℝ}

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

def LocalExtremumWithinAtc (D : Set ℝ) (f : D → ℝ) (c : D) :=
  ∃ δ > (0 : ℝ), ∀ x ∈ {x : D | c - δ < x ∧ x < c + δ}, (f x ≤ f c ∨ f c ≤ f x)

def TendsToLFromLeft (D : Set ℝ) (f : D → ℝ) (c : D) (L : ℝ) :=
  ∀ ε > (0 : ℝ), ∃ δ > (0 : ℝ), ∀ x < (c : D), |x.val - c.val| < δ → |f x - L| < ε

def TendsToLFromRight (D : Set ℝ) (f : D → ℝ) (c : D) (L : ℝ) :=
  ∀ ε > (0 : ℝ), ∃ δ > (0 : ℝ), ∀ x > (c : D), |x.val - c.val| < δ → |f x - L| < ε

def ContinuousAtc (D : Set ℝ) (f : D → ℝ) (c : D) :=
  (TendsToLFromLeft D f c (f c)) ∧ (TendsToLFromRight D f c (f c))

def DerivativeIsWithinAtc (E : Set ℝ) (f : E → ℝ) (c : E) (L : ℝ) :=
  (TendsToLFromLeft E (fun (x : E) => (f x - f c)/(x.val - c.val)) c L) ∧ (TendsToLFromRight E (fun (x : E) => (f x - f c)/(x.val - c.val)) c L)

def DifferentiableWithinAtc (E : Set ℝ) (f : E → ℝ) (c : E) :=
  ∃ (L : ℝ), DerivativeIsWithinAtc E f c L

lemma DeltaNeighbouhoodIsNonempty (E : Set ℝ) (E_Open : IsOpenSet E) (c : E) : ∃ δ > (0 : ℝ), {x : E | (c - δ < x ∧ x < c + δ) ∧ x ≠ c}.Nonempty := by
  specialize E_Open c
  choose δ hδ E_Open using E_Open
  use (δ)
  specialize E_Open (δ/2)
  simp at E_Open
  specialize E_Open hδ
  rcases E_Open with ⟨left,right⟩
  constructor
  · bound
  ·








/-
FERMATSTHEOREM
-/

-- theorem fermat_predicate : {α : Sort u_1} {β : α → Sort u_4} (x : α) (f : (x : α) → β x) :

--change ∀ᶠ (x : ℝ) in nhds c, f c ≤ f x at h_loc_min
--change {x : ℝ | f c ≤ f x} ∈ nhds c at h_loc_min
--change ∃ (f' : ℝ →L[ℝ] ℝ), HasFDerivWithinAt f f' D c at h_differentiable_at
--choose f' hf' using h_differentiable_at
/-
have nhdnonempty : ∃ x ∈ {x | f c ≤ f x}, True := by
      use c
      simp
    choose x hx using nhdnonempty
    simp at hx
    have nhdnonempty2 : ∃ X ∈ nhds c, True := by
      use {x} \ {c}
      simp -/


theorem fermataltalt (E : Set ℝ) (f : E → ℝ) (c : E) {h_E_open : IsOpenSet E} {h_loc_ext : LocalExtremumWithinAtc E f c} {h_differentiable_at : DifferentiableWithinAtc E f c} : DerivativeIsWithinAtc E f c 0 := by
  choose L hL using h_differentiable_at
  suffices deriv_is_0 : L = 0 by
    rewrite [deriv_is_0] at hL
    exact hL
  rcases hL with ⟨tends_from_left, tends_from_right⟩
  specialize h_E_open c
  choose δ1 hδ1 h_loc_ext using h_loc_ext
  choose δ2 hδ2 h_E_open using h_E_open
  have δballcnonempty : {x : E | (c - δ2 < x ∧ x < c + δ2) ∧ x ≠ c}.Nonempty := by
    simp
    use (c - (δ2/2))

  choose x hx using δballcnonempty
  change (c - δ < x ∧ x < c + δ) ∧ x ≠ c at hx
  specialize h_loc_ext x hx.left




theorem fermatalt (D E : Set ℝ) (f : D → ℝ) (c : D) {h_loc_ext : LocalExtremumWithinAtc D f c} {h_differentiable_at : DifferentiableWithinAtc D f c} : DerivativeIsWithinAtc D f c 0 := by
  choose L hL using h_differentiable_at
  suffices deriv_is_0 : L = 0 by
    rewrite [deriv_is_0] at hL
    exact hL
  rcases hL with ⟨tends_from_left, tends_from_right⟩
  choose δ hδ h_loc_ext using h_loc_ext
  have leftδballcnonempty : {x : D | c - δ < x ∧ x < c}.Nonempty := by
    sorry
  choose xleft hxleft using leftδballcnonempty
  have h2xleft : xleft < c := by
    simp at hxleft
    exact hxleft.2
  have h3xleft : xleft < c := by
    simp at hxleft
    exact hxleft.2
  have rightδballcnonempty : {x : D | c < x ∧ x < c + δ}.Nonempty := by
    sorry
  choose xright hxright using rightδballcnonempty
  have δballcnonempty : {x : D | c - δ < x ∧ x < c + δ}.Nonempty := by
    use c
    constructor
    · bound
    · bound
  choose x hx using δballcnonempty
  specialize h_loc_ext x hx
  let ε := (δ : ℝ)
  · have hε : ε > 0 := by exact hδ
    specialize tends_from_left ε hε
    specialize tends_from_right ε hε
    choose δ1 hδ1 tends_from_left using tends_from_left
    choose δ2 hδ2 tends_from_right using tends_from_right
    let δ3 := min δ1 δ2
    have hδ3 : δ3 > 0 := by bound
    have hexpand : L = 0 ↔ L ≤ 0 ∧ L ≥ 0 := by bound
    rw [hexpand]
    have hL1 : L ≤ 0 := by
      by_cases hxc : x = c
      · specialize tends_from_left x hx
        rewrite [hxc] at tends_from_left
        simp at tends_from_left
        specialize tends_from_left hδ1

      ·
    rcases h_loc_ext with (h_loc_min | h_loc_max)
    ·
      sorry
    · sorry

  · -- specify ε


theorem fermat {c : ℝ} {f : ℝ → ℝ} {h_loc_ext : IsLocalExtr f c} {h_differentiable_at : DifferentiableAt ℝ f c} : HasDerivAt f 0 c := by
  have h1 := DifferentiableAt.hasDerivAt h_differentiable_at
  suffices final : deriv f c = 0 by
    rewrite [final] at h1
    exact h1
  rcases h_loc_ext with (h_loc_min | h_loc_max)
  · change {x | f c ≤ f x} ∈ nhds c at h_loc_min
    have cballcontainsc : (nhds c).NeBot := by
      simp
    --rewrite [Filter.neBot_iff] at cballcontainsc
    have hf' : ∃ (f' : ℝ → ℝ), Filter.Tendsto f' (nhds c) (nhds (f' c)) := by
      use deriv f
      change (Filter.map (deriv f) (nhds c) ≤ (nhds (deriv f c)))







  · sorry









theorem boundedness {h_f_cont : ∀ x ∈ {x : ℝ | a ≤ x ∧ x ≤ b}, ∀ ε > (0 : ℝ), ∃ δ > (0 : ℝ)}
