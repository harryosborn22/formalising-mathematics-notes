module

public import Mathlib

example {α β : Type*} (f : α → β) (s t : Set α) :
  f '' (s ∩ t) ⊆ f '' s ∩ f '' t := by
  intro a haf
  grind

example (x y : ℝ) (h : x < y) : -y < -x := by
  linarith

#check (2, 3)

#check fun n ↦ (-1) ^ n

#check False

#check Not

#check Type

universe u_1 u_2 u_3

example (α : Type u_1) (β : Type u_2) (γ : Type u_3) (f : α → β)
  (g : β → γ) (hgf : Function.Injective (g ∘ f)) (hf : Function.Surjective f) :
  ∀ a b : α, g (f a) = g (f b) → f a = f b := by
  intro a b h
  specialize hgf h
  rw [hgf]

example {α β γ : Type*} {f : α → β} (g : β → γ)
  (hgf : Function.Surjective (g ∘ f)) (hg : Function.Injective g) :
  Function.Surjective f := by
  intro b
  specialize hgf (g b)
  rcases hgf with ⟨a, ha⟩
  use a
  exact (hg ha)

example (a b c d : ℕ) :
  (a + b) * (c + d) = (b + a) * c + (a + b) * d := by
  rw [add_comm]
  rw [mul_add]


example {α : Type*} (s t : Set α) : s ∩ t ⊆ s ∪ t := by
  intro a ha
  rcases ha with ⟨hs, ht⟩
  left
  exact hs

example {α : Type*} (s t : Set α) : s ∩ t ⊆ s ∪ t :=
  fun a ha ↦ Or.inr ha.right

example {α β γ δ : Type*}
  {fαβ : α → β} {fβδ : β → δ} {fαγ : α → γ} {fγδ : γ → δ}
  (hαβ : Function.Surjective fαβ) (hαγ : Function.Surjective fαγ)
  (commutes : fβδ ∘ fαβ = fγδ ∘ fαγ) :
  Set.range fβδ = Set.range fγδ := by
  rw [<- hαβ.range_comp fβδ, commutes, hαγ.range_comp fγδ]
