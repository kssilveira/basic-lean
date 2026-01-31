namespace Basic

noncomputable section

inductive True : Prop where
  | intro : True

example : True := True.intro

inductive False : Prop

def False.elim {C : Sort u} (h : False) : C :=
  h.rec

def Not (a : Prop) : Prop := a → False

def absurd {a : Prop} {b : Sort v} (h₁ : a) (h₂ : Not a) : b :=
  (h₂ h₁).rec

example (hp : p) (hnp : Not p) : q := absurd hp hnp

example : Not False := sorry

inductive Eq : α → α → Prop where
  | refl (a : α) : Eq a a

example : Eq p p := Eq.refl p

def rfl {α : Sort u} {a : α} : Eq a a := Eq.refl a

example : Eq p p := rfl

def id {α : Sort u} (a : α) : α := a

theorem id_eq (a : α) : Eq (id a) a := Eq.refl a

theorem eq_id (a : α) : Eq a (id a) := Eq.refl a
