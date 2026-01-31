namespace Basic

noncomputable section

inductive True : Prop where
  | intro : True

example : True := True.intro

inductive False : Prop

def False.elim {b : Sort u} (false : False) : b :=
  false.rec

example (false : False): b := False.elim false

def Not (a : Prop) : Prop := a → False

def absurd {a : Prop} {b : Sort v} (ha : a) (Not_a : Not a) : b :=
  have false: False := Not_a ha
  have res: b := False.elim false
  res

example (ha: a) (Not_a : Not a) : b := absurd ha Not_a

def id {α : Sort u} (a : α) : α := a

example : Not False := id

inductive Eq : α → α → Prop where
  | refl (a : α) : Eq a a

example : Eq a a := Eq.refl a

theorem id_eq (a : α) : Eq (id a) a := Eq.refl a

example : Eq (id a) a := id_eq a

theorem eq_id (a : α) : Eq a (id a) := Eq.refl a

example : Eq a (id a) := eq_id a

abbrev Eq.ndrec.{u, v} {α : Sort v} {a : α} {motive : α → Sort u} (m : motive a) {b : α} (h : Eq a b) : motive b :=
  h.rec m

theorem Eq.subst {α : Sort u} {motive : α → Prop} {a b : α} (Eq_ab : Eq a b) (motive_a : motive a) : motive b :=
  Eq.ndrec motive_a Eq_ab

theorem Eq.symm {α : Sort u} {a b : α} (Eq_ab : Eq a b) : Eq b a :=
  have Eq_aa: Eq a a := Eq.refl a
  Eq.subst (motive := fun x => Eq x a) Eq_ab Eq_aa

example (Eq_ab: Eq a b): Eq b a := Eq.symm Eq_ab

theorem Eq.trans {α : Sort u} {a b c : α} (Eq_ab : Eq a b) (Eq_bc : Eq b c) : Eq a c :=
  Eq.subst (motive := fun x => Eq a x) Eq_bc Eq_ab

example (Eq_ab : Eq a b) (Eq_bc : Eq b c) : Eq a c := Eq.trans Eq_ab Eq_bc

theorem congrArg {α : Sort u} {β : Sort v} {a b : α} (f : α → β) (Eq_ab: Eq a b) : Eq (f a) (f b) :=
  have Eq_fa_fa: Eq (f a) (f a) := Eq.refl (f a)
  Eq.subst (motive := fun x => Eq (f a) (f x)) Eq_ab Eq_fa_fa

theorem congrFun {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x} (Eq_fg : Eq f g) (a : α) : Eq (f a) (g a) :=
  have Eq_fa_fa : Eq (f a) (f a) := Eq.refl (f a)
  Eq.subst (motive := fun x => Eq (f a) (x a)) Eq_fg Eq_fa_fa

theorem congr {α : Sort u} {β : Sort v} {f g : α → β} {a b : α} (Eq_fg : Eq f g) (Eq_ab : Eq a b) : Eq (f a) (g b) :=
  have Eq_fa_fb : Eq (f a) (f b) := congrArg f Eq_ab
  Eq.subst (motive := fun x => Eq (f a) (x b)) Eq_fg Eq_fa_fb
