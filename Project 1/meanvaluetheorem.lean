/-
Copyright (c) 2026 Harry Osborn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Harry Osborn
-/
module

public import Mathlib

/-!
# Mean Value Theorem

This file is a formalisation of the mean value theorem

## Main Results

- `mean_value`: the mean value theorem itself
- `MySlope` : the gradient between two points a and b
- `TendsTo`: an ε - δ definition of a function tending to a value
- `MyContinuousOn`: an ε - δ definition of a function being continuous on a set
- `MyDerivativeAt`: an ε - δ definition of the derivative of a differentiable function
-/

@[expose] public section

variable {a b : ℝ}
variable {f : ℝ → ℝ} {f' : ℝ → ℝ}

/-- The gradient of a function between a and b -/
noncomputable def MySlope (a b : ℝ) (f : ℝ → ℝ) := (f b - f a) / (b - a)

/-- Defines a δ-neighbourhood around a point c which is a local maximum
or minimum under a transform f (for future implementation of Fermat's theorem) -/
def MyLocalExtremumAt (f : ℝ → ℝ) (c : ℝ) :=
  ∃ δ > (0 : ℝ), ∀ x : Set.Ioo (c - δ) (c + δ), (f x - f c ≤ 0 ∨ f c - f x ≤ 0)

/-- Definition of a function tending to a limit from the left -/
def TendsToLFromLeft (f : ℝ → ℝ) (c L ε δ : ℝ) :=
  ∀ x < (c : ℝ), c - x < δ → |f x - L| < ε

/-- Definition of a function tending to a limit from the right -/
def TendsToLFromRight (f : ℝ → ℝ) (c L ε δ : ℝ) :=
  ∀ x > (c : ℝ), x - c < δ → |f x - L| < ε

/-- If a function tends to a point, then it tends to that point from the left and
the right -/
@[fun_prop]
def TendsTo (f : ℝ → ℝ) (c : ℝ) (L : ℝ) :=
  ∀ ε > (0 : ℝ), ∃ δ > (0 : ℝ), TendsToLFromLeft f c L ε δ ∧ TendsToLFromRight f c L ε δ

/-- A function is continuous at a point c if it tends to f c as x tends to c -/
@[fun_prop]
def MyContinuousAt (f : ℝ → ℝ) (c : ℝ) :=
  TendsTo f c (f c)

/-- A function is continuous on a domain if it is continuous at all points in
the domain -/
@[fun_prop]
def MyContinuousOn (f : ℝ → ℝ) (s : Set ℝ) :=
 ∀ c ∈ s, MyContinuousAt f c

/-- A function has derivative L at point c if the slope of f tends to L as x
tends to c -/
@[fun_prop]
def MyDerivativeAt (f : ℝ → ℝ) (c : ℝ) (L : ℝ) :=
  TendsTo (fun (x : ℝ) => (MySlope x c f)) c L

/-- A function is differentiable at a point c if ∃ L s.t the derivative of
f is L at c -/
@[fun_prop]
def MyDifferentiableAt (f : ℝ → ℝ) (c : ℝ) :=
  ∃ (L : ℝ), MyDerivativeAt f c L

/-- A function is differentiable on a domain if it has a derivative at all points
in the domain -/
@[fun_prop]
def MyDifferentiableOn (f : ℝ → ℝ) (S : Set ℝ) :=
  ∀ c ∈ S, ∃ L : ℝ,  MyDerivativeAt f c L

/-- A function f' is the derivative of another function f if the slope of f tends to
f' c as x tends to c -/
@[fun_prop]
def MyIsDerivative (f f' : ℝ → ℝ) :=
  ∀ c : ℝ, MyDerivativeAt f c (f' c)

/-- A function is bounded on a domain if ∃ a' and b' s.t. a' ≤ f x ≤ b' for all
x in the domain (for future implementation of the boundedness theorem) -/
@[fun_prop]
def MyIsBoundedOn (a b : ℝ) (f : ℝ → ℝ) :=
  ∃ a' b' : ℝ, ∀ x : Set.Icc a b, a' ≤ f x ∧ f x ≤ b'

/-- The slope of the difference between two functions is the difference of their slopes -/
theorem MySlopeSub (a b : ℝ) (f g : ℝ → ℝ) :
                   MySlope a b (f - g) = MySlope a b f - MySlope a b g := by
  unfold MySlope
  rw [div_sub_div_same (f b - f a) (g b - g a) (b - a)]
  rw [sub_sub_sub_comm]
  rfl

/-- Any constant function has derivative 0 -/
@[fun_prop]
theorem MyConstFunctionDerivativeAt (c k : ℝ) :
                                    MyDerivativeAt (fun (_ : ℝ) => k) c 0 := by
  intro ε hε
  use ε
  constructor
  · exact hε
  · constructor
    · intro x hx hxc
      unfold MySlope
      norm_num
      exact hε
    · intro x hx hxc
      unfold MySlope
      norm_num
      exact hε

/-- The identity function has derivative 1 -/
@[fun_prop]
theorem MyIdFunctionDerivativeAt (c : ℝ) :
                                 MyDerivativeAt (fun (x : ℝ) => x) c 1 := by
  intro ε hε
  use ε
  constructor
  · exact hε
  · constructor
    · intro x hx hxc
      have hx' : c - x ≠ 0 := by bound
      unfold MySlope
      norm_num
      rw [div_self hx']
      ring_nf
      exact hε
    · intro x hx hxc
      have hx' : c - x ≠ 0 := by bound
      unfold MySlope
      norm_num
      rw [div_self hx']
      ring_nf
      exact hε

/-- The derivative of the difference between two functions is the
difference of the derivatives -/
@[fun_prop]
theorem MyDerivativeSubAt (f g : ℝ → ℝ) (c fL gL : ℝ) {hf : MyDerivativeAt f c fL}
                              {hg : MyDerivativeAt g c gL} : MyDerivativeAt (f - g) c (fL - gL)
                              := by
  intro ε hε
  have hεover2 : (ε / 2) > 0 := by bound
  specialize hf (ε/2) hεover2
  specialize hg (ε/2) hεover2
  choose δ1 hδ1 hf using hf
  choose δ2 hδ2 hg using hg
  let δ := min δ1 δ2
  use δ
  have hδ : δ > 0 := by bound
  have hδδ1 : δ ≤ δ1 := by bound
  have hδδ2 : δ ≤ δ2 := by bound
  have hδ1' : ∀ a : ℝ, a < δ → a < δ1 := by
    intro a ha
    bound
  have hδ2' : ∀ a : ℝ, a < δ → a < δ2 := by
    intro a ha
    bound
  rcases hf with ⟨hfleft, hfright⟩
  rcases hg with ⟨hgleft, hgright⟩
  constructor
  · exact hδ
  · constructor
    · intro x hx hxc
      specialize hδ1' (c - x) hxc
      specialize hfleft x hx hδ1'
      specialize hδ2' (c - x) hxc
      specialize hgleft x hx hδ2'
      norm_num at hfleft
      norm_num at hgleft
      norm_num
      rw [MySlopeSub]
      rw [sub_sub_sub_comm]
      have htriangle :
           |MySlope x c f - fL - (MySlope x c g - gL)| ≤ |MySlope x c f - fL| + |MySlope x c g - gL|
           := by
        exact abs_sub (MySlope x c f - fL) (MySlope x c g - gL)
      suffices hresult : |MySlope x c f - fL| + |MySlope x c g - gL| < ε by
        exact Std.lt_of_le_of_lt htriangle hresult
      have h_abs_add : |MySlope x c f - fL| + |MySlope x c g - gL| < ε / 2 + ε / 2 := by
        exact add_lt_add hfleft hgleft
      norm_num at h_abs_add
      exact h_abs_add
    · intro x hx hxc
      specialize hδ1' (x - c) hxc
      specialize hfright x hx hδ1'
      specialize hδ2' (x - c) hxc
      specialize hgright x hx hδ2'
      norm_num at hfright
      norm_num at hgright
      norm_num
      rw [MySlopeSub]
      rw [sub_sub_sub_comm]
      have htriangle :
           |MySlope x c f - fL - (MySlope x c g - gL)| ≤ |MySlope x c f - fL| + |MySlope x c g - gL|
           := by
        exact abs_sub (MySlope x c f - fL) (MySlope x c g - gL)
      suffices hresult : |MySlope x c f - fL| + |MySlope x c g - gL| < ε by
        exact Std.lt_of_le_of_lt htriangle hresult
      have h_abs_add : |MySlope x c f - fL| + |MySlope x c g - gL| < ε / 2 + ε / 2 := by
        exact add_lt_add hfright hgright
      norm_num at h_abs_add
      exact h_abs_add

/-- The derivative of the product of a scalar and a function is the
product of the scalar and the function's derivative -/
@[fun_prop]
theorem MyDerivativeMulAt (f : ℝ → ℝ) (c k L : ℝ) {hf : MyDerivativeAt f c L} :
                              MyDerivativeAt (fun (x : ℝ) => k * f x) c (k * L) := by
  by_cases hk : k = 0
  · rw [hk]
    norm_num
    exact MyConstFunctionDerivativeAt c 0
  · intro ε hε
    change k ≠ 0 at hk
    have h_abs_k : |k| ≠ 0 := by exact abs_ne_zero.mpr hk
    have hkinv: |k|⁻¹ > 0 := by
      rw [<- abs_inv]
      norm_num
      exact hk
    have hkinvε: |k|⁻¹ * ε > 0 := by
      apply Right.mul_pos hkinv hε
    specialize hf (|k|⁻¹ * ε) hkinvε
    choose δ hδ hf using hf
    use δ
    rcases hf with ⟨hfleft, hfright⟩
    constructor
    · exact hδ
    · constructor
      · intro x hx hxc
        specialize hfleft x hx hxc
        unfold MySlope at hfleft
        unfold MySlope
        norm_num at hfleft
        norm_num
        rw [<- mul_sub_left_distrib]
        rw [mul_div_assoc]
        rw [<- mul_sub_left_distrib k ((f c - f x) / (c - x)) L]
        rw [abs_mul k ((f c - f x) / (c - x) - L)]
        rw [<- mul_lt_mul_iff_of_pos_left hkinv]
        rw [inv_mul_cancel_left₀ h_abs_k]
        exact hfleft
      · intro x hx hxc
        specialize hfright x hx hxc
        unfold MySlope at hfright
        unfold MySlope
        norm_num at hfright
        norm_num
        rw [<- mul_sub_left_distrib]
        rw [mul_div_assoc]
        rw [<- mul_sub_left_distrib k ((f c - f x) / (c - x)) L]
        rw [abs_mul k ((f c - f x) / (c - x) - L)]
        rw [<- mul_lt_mul_iff_of_pos_left hkinv]
        rw [inv_mul_cancel_left₀ h_abs_k]
        exact hfright

/-- Any constant function f has derivative f' 0 -/
@[fun_prop]
theorem MyConstFunctionIsDeriv (k : ℝ) :
                               MyIsDerivative (fun (_ : ℝ) => k) (fun (_ : ℝ) => 0) :=  by
  intro c
  exact (MyConstFunctionDerivativeAt c k)

/-- The identity function f has derivative f' = 1 -/
@[fun_prop]
theorem MyIdFunctionIsDeriv : MyIsDerivative (fun (x : ℝ) => x) (fun (_ : ℝ) => 1) := by
  intro c
  exact (MyIdFunctionDerivativeAt c)

/-- The derivative of the difference between two functions is
the difference of their derivatives -/
@[fun_prop]
theorem MyIsDerivSub (f g f' g' : ℝ → ℝ) {hf : MyIsDerivative f f'}
                              {hg : MyIsDerivative g g'} : MyIsDerivative (f - g) (f' - g') := by
  intro c
  specialize hf c
  specialize hg c
  fun_prop

/-- The derivative of the product of a function and a scalar is
the product of the derivative and the scalar -/
@[fun_prop]
theorem MyIsDerivMul (f f' : ℝ → ℝ) (k : ℝ) {hf : MyIsDerivative f f'} :
                     MyIsDerivative (fun (x : ℝ) => k * f x) (fun (x : ℝ) => k * f' x) := by
  intro c
  specialize hf c
  fun_prop

/-- Any constant function is differentiable -/
@[fun_prop]
theorem MyConstFuncDifferentiableOn (k : ℝ) (s : Set ℝ) :
                                    MyDifferentiableOn (fun (_ : ℝ) => k) s := by
  intro c hc
  use 0
  exact MyConstFunctionDerivativeAt c k

/-- The identity function is differentiable -/
@[fun_prop]
theorem MyIdFuncDifferentiableOn (s : Set ℝ) :
                                    MyDifferentiableOn (fun (x : ℝ) => x) s := by
  intro c hc
  use 1
  exact MyIdFunctionDerivativeAt c

/-- The difference between two differentiable functions is also differentiable -/
@[fun_prop]
theorem MyDifferentiableSubOn (f g : ℝ → ℝ) (s : Set ℝ) {hf : MyDifferentiableOn f s}
                              {hg : MyDifferentiableOn g s} : MyDifferentiableOn (f - g) s := by
  intro c hc
  specialize hf c hc
  specialize hg c hc
  choose fL hf using hf
  choose gL hg using hg
  use (fL - gL)
  fun_prop

/-- The product between a scalar and a differentiable function is also differentiable -/
@[fun_prop]
theorem MyDifferentiableMulOn (f : ℝ → ℝ) (k : ℝ) (s : Set ℝ) {hf : MyDifferentiableOn f s} :
                              MyDifferentiableOn (fun (x : ℝ) => k * f x) s := by
  intro c hc
  specialize hf c hc
  choose L hf using hf
  use (k * L)
  fun_prop

/-- Any constant function defined on a set is continuous on that set -/
@[fun_prop]
theorem MyConstFuncContOn (k : ℝ) (s : Set ℝ) :
                          MyContinuousOn (fun (_ : ℝ) => k) s := by
  intro c hc ε hε
  use ε
  constructor
  · exact hε
  · constructor
    · intro x hx hxc
      norm_num
      exact hε
    · intro x hc hxc
      norm_num
      exact hε

/-- The identity function defined on a set is continuous on that set -/
@[fun_prop]
theorem MyIdFuncContOn (s : Set ℝ) : MyContinuousOn (fun (x : ℝ) => x) s := by
  intro c hc ε hε
  use ε
  constructor
  · exact hε
  · constructor
    · intro x hx hxc
      norm_num
      rw [abs_lt]
      constructor
      · apply neg_lt_of_neg_lt
        bound
      · rw [<- sub_neg] at hx
        exact Std.lt_trans hx hε
    · intro x hx hxc
      norm_num
      rw [abs_lt]
      constructor
      · apply neg_lt_of_neg_lt
        bound
      · exact hxc

/-- The difference between two continuous functions is also continuous -/
@[fun_prop]
theorem MyContSubOn (f g : ℝ → ℝ) (s : Set ℝ) {hf : MyContinuousOn f s}
                    {hg : MyContinuousOn g s} : MyContinuousOn (f - g) s := by
  intro c hc ε hε
  have hε2 : ε / 2 > 0 := by bound
  specialize hf c hc (ε/2) hε2
  specialize hg c hc (ε/2) hε2
  choose δ1 hδ1 hf using hf
  choose δ2 hδ2 hg using hg
  rcases hf with ⟨hfleft, hfright⟩
  rcases hg with ⟨hgleft, hgright⟩
  let δ := min δ1 δ2
  use δ
  have hδ : δ > 0 := by bound
  have hδδ1 : δ ≤ δ1 := by bound
  have hδδ2 : δ ≤ δ2 := by bound
  have hδ1' : ∀ a : ℝ, a < δ → a < δ1 := by
    intro a ha
    bound
  have hδ2' : ∀ a : ℝ, a < δ → a < δ2 := by
    intro a ha
    bound
  constructor
  · exact hδ
  · constructor
    · intro x hx hxc
      specialize hδ1' (c - x) hxc
      specialize hfleft x hx hδ1'
      specialize hδ2' (c - x) hxc
      specialize hgleft x hx hδ2'
      simp only [Pi.sub_apply]
      rw [sub_sub_sub_comm]
      simp only [sub_eq_add_neg (f x - f c) (g x - g c)]
      have htriangle : |f x - f c + (g c - g x)| ≤ |f x - f c| + |g c - g x| := by
        exact abs_add_le (f x - f c) (g c - g x)
      norm_num
      suffices hresult : |f x - f c| + |g c - g x| < ε by
        exact Std.lt_of_le_of_lt htriangle hresult
      have h_abs_add : |f x - f c| + |g x - g c| < ε / 2 + ε / 2 := by
        exact add_lt_add hfleft hgleft
      norm_num at h_abs_add
      rw [abs_sub_comm (g c) (g x)]
      exact h_abs_add
    · intro x hx hxc
      specialize hδ1' (x - c) hxc
      specialize hfright x hx hδ1'
      specialize hδ2' (x - c) hxc
      specialize hgright x hx hδ2'
      simp only [Pi.sub_apply]
      rw [sub_sub_sub_comm]
      simp only [sub_eq_add_neg (f x - f c) (g x - g c)]
      have htriangle : |f x - f c + (g c - g x)| ≤ |f x - f c| + |g c - g x| := by
        exact abs_add_le (f x - f c) (g c - g x)
      norm_num
      suffices hresult : |f x - f c| + |g c - g x| < ε by
        exact Std.lt_of_le_of_lt htriangle hresult
      have h_abs_add : |f x - f c| + |g x - g c| < ε / 2 + ε / 2 := by
        exact add_lt_add hfright hgright
      norm_num at h_abs_add
      rw [abs_sub_comm (g c) (g x)]
      exact h_abs_add

lemma neq_gt_imp_gt (a b : ℝ) {ha : a ≠ 0} {hb : b > 0} : |a| * b > 0 := by
  suffices ha' : |a| > 0 by
    exact Right.mul_pos ha' hb
  simpa only [Right.mul_pos, abs_pos]

/-- The product between a scalar and a continuous function is also continuous -/
@[fun_prop]
theorem MyContConstMulOn (f : ℝ → ℝ) (k : ℝ) (s : Set ℝ) {hf : MyContinuousOn f s} :
                          MyContinuousOn (fun (x : ℝ) => k * f x) s := by
  by_cases hk : k = 0
  · rw [hk]
    norm_num
    fun_prop
  · intro c hc ε hε
    change k ≠ 0 at hk
    have hkinv : k⁻¹ ≠ 0 := by exact inv_ne_zero hk
    have hεk : |k⁻¹| * ε > 0 := by
      exact @neq_gt_imp_gt (k⁻¹) ε hkinv hε
    have h_abs_neq_zero : |k| ≠ 0 := by exact abs_ne_zero.mpr hk
    specialize hf c hc (|k⁻¹| * ε) hεk
    choose δ hδ hf using hf
    rcases hf with ⟨hfleft, hfright⟩
    use δ
    constructor
    · exact hδ
    · constructor
      · intro x hx hxc
        specialize hfleft x hx hxc
        norm_num
        rw [<- mul_sub_left_distrib]
        rw [abs_mul k (f x - f c)]
        have h_abs_k : |k| > 0 := by exact abs_pos.mpr hk
        have hkinvv : |k|⁻¹ > 0 := by exact inv_pos.mpr (h_abs_k)
        rw [<- mul_lt_mul_iff_of_pos_left hkinvv]
        rw [inv_mul_cancel_left₀ h_abs_neq_zero]
        rw [<- abs_inv k]
        exact hfleft
      · intro x hx hxc
        specialize hfright x hx hxc
        norm_num
        rw [<- mul_sub_left_distrib]
        rw [abs_mul k (f x - f c)]
        have h_abs_k : |k| > 0 := by exact abs_pos.mpr hk
        have hkinvv : |k|⁻¹ > 0 := by exact inv_pos.mpr (h_abs_k)
        rw [<- mul_lt_mul_iff_of_pos_left hkinvv]
        rw [inv_mul_cancel_left₀ h_abs_neq_zero]
        rw [<- abs_inv k]
        exact hfright

lemma leimpneq (a b : ℝ) {hab : a < b} : b - a ≠ 0 := by bound

/-- **Mean Value Theorem - a function f : ℝ → ℝ that is differentiable on the open.
interval (a, b) and continuous on the closed interval [a,b], then ∃ c ∈ (a, b) s.t.
f(b) - f(a) = f'(c)*(b - a)** -/
theorem mean_value (a b : ℝ) (f f' : ℝ → ℝ) {hab : a < b}
                   {hrolles : ∀ (f f' : ℝ → ℝ), MyContinuousOn f (Set.Icc a b) →
                   MyDifferentiableOn f (Set.Ioo a b) → MyIsDerivative f f' → f a = f b →
                   ∃ c ∈ (Set.Ioo a b), f' c = 0}
                   {hf' : MyIsDerivative f f'} {h_cont : MyContinuousOn f (Set.Icc a b)}
                   {h_diff : MyDifferentiableOn f (Set.Ioo a b)} :
                   ∃ c ∈ (Set.Ioo a b), f' c = MySlope a b f := by
  let g := (fun x : ℝ => (MySlope a b f) * x)
  let g' := (fun _ : ℝ => (MySlope a b f))
  have h_g_cont : MyContinuousOn g (Set.Icc a b) := by fun_prop
  have h_f_g_cont : MyContinuousOn (f - g) (Set.Icc a b) := by fun_prop
  have h_g_diff : MyDifferentiableOn g (Set.Ioo a b) := by fun_prop
  have h_f_g_diff : MyDifferentiableOn (f - g) (Set.Ioo a b) := by fun_prop
  have h_g' : MyIsDerivative g g' := by
    intro c ε hε
    use ε
    constructor
    · exact hε
    · constructor
      · intro x hx hxc
        unfold g' g MySlope
        norm_num
        rw [<- sub_pos] at hx
        have hx' : c - x ≠ 0 := by bound
        rw [<- mul_sub]
        rw [mul_div_assoc]
        rw [div_self hx']
        norm_num
        exact hε
      · intro x hx hxc
        unfold g' g MySlope
        norm_num
        have hx' : c - x ≠ 0 := by bound
        rw [<- mul_sub]
        rw [mul_div_assoc]
        rw [div_self hx']
        norm_num
        exact hε
  have h_f'_g' : MyIsDerivative (f - g) (f' - g') := by fun_prop
  have h_f_g_a_b : (f - g) a = (f - g) b := by
    rw [Pi.sub_apply]
    rw [Pi.sub_apply]
    rw [sub_eq_sub_iff_sub_eq_sub]
    unfold g
    unfold MySlope
    rw [<- mul_sub]
    rw [sub_eq_add_neg a b]
    rw [<- sub_eq_add_neg a b]
    rw [<- neg_sub b a]
    rw [mul_neg ((f b - f a) / (b - a)) (b - a)]
    rw [<- neg_eq_iff_eq_neg]
    rw [neg_sub (f a) (f b)]
    rw [mul_comm ((f b - f a) / (b - a)) (b - a)]
    rw [division_def]
    rw [<- mul_assoc]
    rw [<- division_def]
    rw [mul_comm]
    rw [mul_div_cancel_right₀ (f b - f a) (@leimpneq a b hab)]
  specialize hrolles (f - g) (f' - g') h_f_g_cont h_f_g_diff h_f'_g' h_f_g_a_b
  choose c hc hrolles using hrolles
  use c
  constructor
  · exact hc
  · rw [Pi.sub_apply] at hrolles
    rw [sub_eq_zero] at hrolles
    rw [hrolles]
