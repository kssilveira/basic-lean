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
example : False → b := fun false => false.elim

def Not (a : Prop) : Prop := a → False

example : Not False := fun x => x

def absurd {a : Prop} {b : Sort v} (ha : a) (Not_a : Not a) : b :=
  have false : False := Not_a ha
  have res : b := false.elim
  res

example (ha : a) (Not_a : Not a) : b := absurd ha Not_a
example (ha : a) : Not a → b := fun Not_a => absurd ha Not_a
example : a → Not a → b := fun ha => fun Not_a => absurd ha Not_a
example : a → Not a → b := fun ha Not_a => absurd ha Not_a

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
example : a → And a a := fun ha => And.intro ha ha
example (ha : a) (hb : b) : And a b := And.intro ha hb
example : a → b → And a b := fun ha hb => And.intro ha hb
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

inductive Bool : Type where
  | false : Bool
  | true : Bool

theorem eq_false_of_ne_true {b : Bool} (Not_Eq_b_true : Not (Eq b Bool.true)) : Eq b Bool.false :=
  match b with
  | Bool.true =>
    have Eq_true_true : Eq Bool.true Bool.true := Eq.refl Bool.true
    absurd Eq_true_true Not_Eq_b_true
  | Bool.false => Eq.refl Bool.false

theorem eq_true_of_ne_false {b : Bool} (Not_Eq_b_false : Not (Eq b Bool.false)) : Eq b Bool.true :=
  match b with
  | Bool.true => Eq.refl Bool.true
  | Bool.false =>
    have Eq_false_false : Eq Bool.false Bool.false := Eq.refl Bool.false
    absurd Eq_false_false Not_Eq_b_false

def Eq.Root {a b : Bool} (Eq_ab : Eq a b) : _root_.Eq a b :=
  match Eq_ab with
  | Eq.refl a => _root_.Eq.refl a

theorem ne_false_of_eq_true {b : Bool} (Eq_b_true : Eq b Bool.true) : Not (Eq b Bool.false) :=
  match b with
  | Bool.true  => fun Eq_true_false => Bool.noConfusion Eq_true_false.Root
  | Bool.false => Bool.noConfusion Eq_b_true.Root

theorem ne_true_of_eq_false {b : Bool} (Eq_b_false : Eq b Bool.false) : Not (Eq b Bool.true) :=
  match b with
  | Bool.true  => Bool.noConfusion Eq_b_false.Root
  | Bool.false => fun Eq_false_true => Bool.noConfusion Eq_false_true.Root

inductive Nat where
  | zero : Nat
  | succ : Nat → Nat

class LE (α : Type u) where
  le : α → α → Prop

class LT (α : Type u) where
  lt : α → α → Prop

def GE.ge {α : Type u} [LE α] (a b : α) : Prop := LE.le b a

def GT.gt {α : Type u} [LT α] (a b : α) : Prop := LT.lt b a

def Nat.add (a b : Nat) : Nat :=
  match b with
  | Nat.zero   => a
  | Nat.succ b_minus_1 => Nat.succ (Nat.add a b_minus_1)

def Nat.mul (a b : Nat) : Nat :=
  match b with
  | Nat.zero   => Nat.zero
  | Nat.succ b_minus_1 => Nat.add a (Nat.mul a b_minus_1)

def Nat.pow (a b : Nat) : Nat :=
  match b with
  | Nat.zero => Nat.succ Nat.zero
  | Nat.succ b_minus_1 => Nat.mul a (Nat.pow a b_minus_1)
