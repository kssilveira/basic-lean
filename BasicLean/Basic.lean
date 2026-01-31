namespace Basic

noncomputable section

inductive True : Prop where
  | intro : True

example : True := True.intro
example : a → True := fun _ => True.intro

inductive False : Prop

example : False → False := fun x => x

def False.elim {b : Sort u} (false : False) : b :=
  false.rec

example (false : False) : b := False.elim false
example (false : False) : b := false.elim

def Not (a : Prop) : Prop := a → False

example : Not False := fun x => x

def absurd {a : Prop} {b : Sort v} (ha : a) (Not_a : Not a) : b :=
  have false : False := Not_a ha
  have res : b := false.elim
  res

example (ha : a) (Not_a : Not a) : b := absurd ha Not_a

inductive Eq : α → α → Prop where
  | refl (a : α) : Eq a a

example : Eq a a := Eq.refl a

def id {α : Sort u} (a : α) : α := a

theorem id_eq (a : α) : Eq (id a) a := Eq.refl a

example : Eq (id a) a := id_eq a

theorem eq_id (a : α) : Eq a (id a) := Eq.refl a

example : Eq a (id a) := eq_id a

abbrev Eq.ndrec.{u, v} {α : Sort v} {a : α} {motive : α → Sort u} (m : motive a) {b : α} (h : Eq a b) : motive b :=
  h.rec m

theorem Eq.subst {α : Sort u} {motive : α → Prop} {a b : α} (Eq_ab : Eq a b) (motive_a : motive a) : motive b :=
  Eq.ndrec motive_a Eq_ab

theorem Eq.symm {α : Sort u} {a b : α} (Eq_ab : Eq a b) : Eq b a :=
  have Eq_aa : Eq a a := Eq.refl a
  Eq.subst (motive := fun x => Eq x a) Eq_ab Eq_aa

example (Eq_ab: Eq a b): Eq b a := Eq_ab.symm

theorem Eq.trans {α : Sort u} {a b c : α} (Eq_ab : Eq a b) (Eq_bc : Eq b c) : Eq a c :=
  Eq.subst (motive := fun x => Eq a x) Eq_bc Eq_ab

example (Eq_ab : Eq a b) (Eq_bc : Eq b c) : Eq a c := Eq.trans Eq_ab Eq_bc

theorem congrArg {α : Sort u} {β : Sort v} {a b : α} (f : α → β) (Eq_ab: Eq a b) : Eq (f a) (f b) :=
  have Eq_fa_fa : Eq (f a) (f a) := Eq.refl (f a)
  Eq.subst (motive := fun x => Eq (f a) (f x)) Eq_ab Eq_fa_fa

example (f : α → β) (Eq_ab: Eq a b) : Eq (f a) (f b) := congrArg f Eq_ab

theorem congrFun {α : Sort u} {β : α → Sort v} {f g : (x : α) → β x} (Eq_fg : Eq f g) (a : α) : Eq (f a) (g a) :=
  have Eq_fa_fa : Eq (f a) (f a) := Eq.refl (f a)
  Eq.subst (motive := fun x => Eq (f a) (x a)) Eq_fg Eq_fa_fa

example {f g : α → β} (Eq_fg : Eq f g) (a : α) : Eq (f a) (g a) := congrFun Eq_fg a

theorem congr {α : Sort u} {β : Sort v} {f g : α → β} {a b : α} (Eq_fg : Eq f g) (Eq_ab : Eq a b) : Eq (f a) (g b) :=
  have Eq_fa_fb : Eq (f a) (f b) := congrArg f Eq_ab
  Eq.subst (motive := fun x => Eq (f a) (x b)) Eq_fg Eq_fa_fb

example {f g : α → β} (Eq_fg : Eq f g) (Eq_ab : Eq a b) : Eq (f a) (g b) := congr Eq_fg Eq_ab

structure And (a b : Prop) : Prop where
  intro ::
  left : a
  right : b

example : And True True := And.intro True.intro True.intro
example (ha : a) : And a a := And.intro ha ha
example (ha : a) (hb : b) : And a b := And.intro ha hb
example (And_ab : And a b) : a := And_ab.left
example (And_ab : And a b) : b := And_ab.right

theorem And.symm (And_ab: And a b) : And b a :=
  have ha : a := And_ab.left
  have hb : b := And_ab.right
  And.intro hb ha

inductive Or (a b : Prop) : Prop where
  | inl (h : a) : Or a b
  | inr (h : b) : Or a b

theorem Or.intro_left (b : Prop) (h : a) : Or a b :=
  Or.inl h

theorem Or.intro_right (a : Prop) (h : b) : Or a b :=
  Or.inr h

example : Or True b := Or.intro_left b True.intro
example : Or b True := Or.intro_right b True.intro
example (ha : a) : Or a b := Or.intro_left b ha
example (ha : a) : Or b a := Or.intro_right b ha

theorem Or.elim {c : Prop} (Or_ab : Or a b) (left : a → c) (right : b → c) : c :=
  match Or_ab with
  | Or.inl h => left h
  | Or.inr h => right h

theorem Or.resolve_left  (Or_ab : Or a b) (Not_a : Not a) : b :=
  Or_ab.elim (fun ha => absurd ha Not_a) id

theorem Or.resolve_right (Or_ab: Or a b) (Not_b : Not b) : a :=
  Or_ab.elim id (fun hb => absurd hb Not_b)

theorem Or.neg_resolve_left (Or_Not_a_b : Or (Not a) b) (ha : a) : b :=
  Or_Not_a_b.elim (fun Not_a => absurd ha Not_a) id

theorem Or.neg_resolve_right (Or_a_Not_b : Or a (Not b)) (hb : b) : a :=
  Or_a_Not_b.elim id (fun Not_b => absurd hb Not_b)
