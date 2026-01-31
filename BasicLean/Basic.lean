namespace Basic

noncomputable section

inductive True : Prop where
  | intro : True

example : True := True.intro

inductive False : Prop

def False.elim {b : Sort u} (h_False : False) : b :=
  h_False.rec

def Not (a : Prop) : Prop := a → False

def absurd {a : Prop} {b : Sort v} (h_a : a) (h_Not_a : Not a) : b :=
  have h_False: False := h_Not_a h_a
  have res: b := False.elim h_False
  res

example (h_p : p) (h_Not_p : Not p) : q := absurd h_p h_Not_p

def id {α : Sort u} (a : α) : α := a

example : Not False := id

inductive Eq : α → α → Prop where
  | refl (a : α) : Eq a a

example : Eq p p := Eq.refl p

theorem id_eq (a : α) : Eq (id a) a := Eq.refl a

theorem eq_id (a : α) : Eq a (id a) := Eq.refl a

abbrev Eq.ndrec.{u1, u2} {α : Sort u2} {a : α} {motive : α → Sort u1} (m : motive a) {b : α} (h : Eq a b) : motive b :=
  h.rec m

theorem Eq.subst {α : Sort u} {motive : α → Prop} {a b : α} (h₁ : Eq a b) (h₂ : motive a) : motive b :=
  Eq.ndrec h₂ h₁

theorem Eq.symm {α : Sort u} {a b : α} (h_Eq_a_b : Eq a b) : Eq b a :=
  have h_Eq_a_a: Eq a a := Eq.refl a
  Eq.subst (motive := fun x => Eq x a) h_Eq_a_b h_Eq_a_a

theorem Eq.trans {α : Sort u} {a b c : α} (h_Eq_a_b : Eq a b) (h_Eq_b_c : Eq b c) : Eq a c :=
  have h_Eq_b_a : Eq b a := Eq.symm h_Eq_a_b
  Eq.subst (motive := fun x => Eq x c) h_Eq_b_a h_Eq_b_c

theorem congrArg {α : Sort u} {β : Sort v} {a₁ a₂ : α} (f : α → β) (h_Eq_a1_a2: Eq a₁ a₂) : Eq (f a₁) (f a₂) :=
  have h_Eq_a2_a1 : Eq a₂ a₁ := Eq.symm h_Eq_a1_a2
  have h_Eq_f_a2_f_a2: Eq (f a₂) (f a₂) := Eq.refl (f a₂)
  Eq.subst (motive := fun x => Eq (f x) (f a₂)) h_Eq_a2_a1 h_Eq_f_a2_f_a2

theorem congrFun {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x} (h_Eq_f_g : Eq f g) (a : α) : Eq (f a) (g a) :=
  have h_Eq_g_f : Eq g f := Eq.symm h_Eq_f_g
  have h_Eq_g_a_g_a : Eq (g a) (g a) := Eq.refl (g a)
  Eq.subst (motive := fun x => Eq (x a) (g a)) h_Eq_g_f h_Eq_g_a_g_a

theorem congr {α : Sort u} {β : Sort v} {f₁ f₂ : α → β} {a₁ a₂ : α} (h_Eq_f1_f2 : Eq f₁ f₂) (h_Eq_a1_a2 : Eq a₁ a₂) : Eq (f₁ a₁) (f₂ a₂) :=
  have h_Eq_f1_a1_f1_a2 : Eq (f₁ a₁) (f₁ a₂) := congrArg f₁ h_Eq_a1_a2
  Eq.subst (motive := fun x => Eq (f₁ a₁) (x a₂)) h_Eq_f1_f2 h_Eq_f1_a1_f1_a2
