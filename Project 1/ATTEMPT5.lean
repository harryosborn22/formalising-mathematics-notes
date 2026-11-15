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
import Mathlib.Topology.Defs.Basic
import Mathlib.Analysis.Calculus.Deriv.CompMul
import Mathlib.Order.Filter.Tendsto

variable {a b : ℝ}
variable {f : ℝ → ℝ} {f' : ℝ → ℝ}

@[fun_prop]
def MyLocalExtremumAt (f : ℝ → ℝ) (c : ℝ) :=
  ∃ δ > (0 : ℝ), ∀ x : Set.Ioo (c - δ) (c + δ), (f x - f c ≤ 0 ∨ f c - f x ≤ 0)

def TendsToLFromLeft (f : ℝ → ℝ) (c L ε δ : ℝ) :=
  ∀ x < (c : ℝ), c - x < δ → |f x - L| < ε

def TendsToLFromRight (f : ℝ → ℝ) (c L ε δ : ℝ) :=
  ∀ x > (c : ℝ), x - c < δ → |f x - L| < ε

@[fun_prop]
def TendsTo (f : ℝ → ℝ) (c : ℝ) (L : ℝ) :=
  ∀ ε > (0 : ℝ), ∃ δ > (0 : ℝ), TendsToLFromRight f c L ε δ ∧ TendsToLFromLeft f c L ε δ

@[fun_prop]
def MyContinuousAt (f : ℝ → ℝ) (c : ℝ) :=
  TendsTo f c (f c)

@[fun_prop]
def MyContinuousOn (f : ℝ → ℝ) (s : Set ℝ) :=
 ∀ x : s, MyContinuousAt f x

noncomputable def MySlope (a b : ℝ) (f : ℝ → ℝ) := (f b - f a) / (b - a)

@[fun_prop]
def MyDerivativeAt (f : ℝ → ℝ) (c : ℝ) (L : ℝ) :=
  TendsTo (fun (x : ℝ) => (MySlope x c f)) c L

@[fun_prop]
def MyDifferentiableAt (f : ℝ → ℝ) (c : ℝ) :=
  ∃ (L : ℝ), MyDerivativeAt f c L

@[fun_prop]
def MyDifferentiableOn (f : ℝ → ℝ) (S : Set ℝ) :=
  ∀ x : S, MyDifferentiableAt f x

@[fun_prop]
def MyIsDerivative (f f' : ℝ → ℝ) :=
  ∀ x : ℝ, MyDerivativeAt f x (f' x)

lemma δNbhdIsNonempty (c : ℝ) (δ : ℝ) (hδ : δ > 0) : {x : ℝ | (c - δ < x ∧ x < c + δ) ∧ x ≠ c}.Nonempty := by
  use (c + δ/2)
  constructor
  · constructor
    · bound
    · bound
  · bound

theorem DiffAlt (f : ℝ → ℝ) (c L : ℝ) {hL : L = 0} : Filter.Tendsto (fun (x) ↦ |x - c|⁻¹ * |f x - f c - (x - c) * L|) (nhds c) (nhds 0) ↔ Filter.Tendsto (fun x ↦ |x - c|⁻¹ * |f x - f c|) (nhds c) (nhds L) := by
  rw [hL]
  simp

def IsBoundedOn (a b : ℝ) (f : ℝ → ℝ) :=
  ∃ a' b' : ℝ, ∀ x ∈ (Set.Icc a b), a' ≤ f x ∧ f x ≤ b'

theorem DifferentiableOnSub (a b : ℝ) (f g : ℝ → ℝ) (hf : DifferentiableOn ℝ f (Set.Ioo a b)) (hf : DifferentiableOn ℝ g (Set.Ioo a b)) : DifferentiableOn ℝ (f - g) (Set.Ioo a b) := by
  fun_prop

lemma leimpneq (a b : ℝ) {hab : a < b} : b - a ≠ 0 := by bound

--theorem deriv_iff_tendsto_slope (f : ℝ → ℝ) (L : ℝ) (c : ℝ) (f_diff : DifferentiableAt ℝ f c) : deriv f c = L ↔ Filter.Tendsto (slope f c) (nhdsWithin c {c}ᶜ) (nhds L) := by
--  have has_deriv_at_iff_differentiable : HasDerivAt f (deriv f c) c ↔ DifferentiableAt ℝ f c := by apply hasDerivAt_deriv_iff


theorem fermat (f : ℝ → ℝ) (c : ℝ) (L : ℝ) {h_loc_ext : IsLocalExtr f c} {h_differentiable_at : HasDerivAt f L c} : L = 0 := by
  change HasDerivAtFilter f L (nhds c ×ˢ pure c) at h_differentiable_at
  rewrite [hasDerivAtFilter_iff_tendsto] at h_differentiable_at
  simp at h_differentiable_at
  change Filter.Tendsto (fun (x) ↦ |x - c|⁻¹ * |f x - f c - (x - c) * L|) (nhds c) (nhds 0) at h_differentiable_at
  suffices hL : Filter.Tendsto (fun x ↦ |x - c|⁻¹ * |f x - f c|) (nhds c) (nhds 0) by

  rewrite [tendsto_order] at h_differentiable_at
  rcases h_differentiable_at with ⟨from_left, from_right⟩
  change ∀ δ < 0, {x : ℝ | δ < |x - c|⁻¹ * |f x - f c - (x - c) * L|} ∈ nhds c at from_left
  rcases h_loc_ext with (loc_min | loc_max)
  · change {x : ℝ | f c ≤ f x} ∈ nhds c at loc_min
    have hnhds: {x : ℝ | f c ≤ f x}.Nonempty := by
      use c
      bound
    choose x hx using hnhds
    let h := x - c
    by_cases hh : h < 0
    · specialize from_left h hh
      have hnhds2 : {x | h < |x - c|⁻¹ * |f x - f c - (x - c) * L|}.Nonempty := by
        use c
        simp
        exact hh
      choose c' hc' using hnhds2
      rewrite [tendsto_order]
      constructor
      · change ∀ δ < 0, {x : ℝ | δ < |x - c|⁻¹ * |f x - f c|} ∈ nhds c
        intro δ1 hδ1
        suffices final : 0 ≤ |x - c|⁻¹ * |f x - f c| by

  · sorry

theorem boundedness (a b : ℝ) (f : ℝ → ℝ) {h_cont : ContinuousOn f (Set.Icc a b)} : IsBoundedOn a b f := by
  sorry

theorem extreme_value (a b : ℝ) (f : ℝ → ℝ) {h_cont : ContinuousOn f (Set.Icc a b)} : ∃ a' b' : (Set.Icc a b), ∀ x ∈ (Set.Icc a b), f a' ≤ f x ∧ f x ≤ f b' := by
  sorry

theorem rolle (a b : ℝ) (f f' : ℝ → ℝ) {hab : a < b} {h_cont : ContinuousOn f (Set.Icc a b)} {h_diff : DifferentiableOn ℝ f (Set.Ioo a b)} {hfab : f a = f b} : ∃ c ∈ (Set.Ioo a b), f' c = 0 := by
  sorry

theorem mean_value (a b : ℝ) (f f' : ℝ → ℝ) {hab : a < b} {h_cont : ContinuousOn f (Set.Icc a b)} {h_diff : DifferentiableOn ℝ f (Set.Ioo a b)} : ∃ c ∈ (Set.Ioo a b), f' c = slope f a b := by

  let g := (fun x : ℝ => (slope f a b) • x)
  let g' := (fun x : ℝ => slope f a b)

  have h_f_g_cont : ContinuousOn (f - g) (Set.Icc a b) := by
    fun_prop

  have h_g_diff : DifferentiableOn ℝ g (Set.Ioo a b) := by
    fun_prop

  have h_f_g_diff : DifferentiableOn ℝ (f - g) (Set.Ioo a b) := by
    fun_prop

  have h_f_g_a_b : (f - g) a = (f - g) b := by
    refine sub_eq_sub_iff_sub_eq_sub.mp ?_
    unfold g
    simp only [smul_eq_mul]
    rw [<- mul_sub (slope f a b) a b]
    unfold slope
    -- f a - f b = (f b - f a) / (b - a) * (a - b)

    rw [sub_eq_add_neg a b]
    rw [<- sub_eq_add_neg a b]
    rw [<- neg_sub b a]
    rw [mul_neg ((b - a)⁻¹ • (f b -ᵥ f a)) (b - a)]
    rw [<- neg_eq_iff_eq_neg]
    rw [neg_sub (f a) (f b)]
    rw [vsub_eq_sub]
    rw [smul_eq_mul]
    rw [mul_comm ((b - a)⁻¹ * (f b - f a)) (b - a)]
    rw [<- mul_assoc]
    rw [<- division_def]
    rw [mul_comm]
    rw [<- mul_div_assoc]
    rw [mul_div_cancel_right₀ (f b - f a) (@leimpneq a b hab)]

  have rolle := @rolle a b (f - g) (f' - g') hab h_f_g_cont h_f_g_diff h_f_g_a_b
  choose c hc rolle using rolle

  use c
  constructor
  · exact hc
  · rw [Pi.sub_apply] at rolle
    rw [sub_eq_zero] at rolle
    rw [rolle]
