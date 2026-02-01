namespace Basic

noncomputable section

inductive True : Prop where
  | intro : True

example : True := True.intro
example : a → True := fun _ => True.intro

inductive False : Prop

example : False → False := fun x => x

def False.elim {b : Sort u} (false : False) : b := false.rec

example (false : False) : b := False.elim false
example (false : False) : b := false.elim
example : False → b := fun false => false.elim

def Not (a : Prop) : Prop := a → False

example : Not False := fun x => x

def absurd {a : Prop} {b : Sort v} (ha : a) (Not_a : Not a) : b :=
  have false : False := Not_a ha
  have hb : b := false.elim
  hb

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

abbrev Eq.ndrec.{u, v} {α : Sort v} {a : α} {motive : α → Sort u} (m : motive a) {b : α} (h : Eq a b) : motive b := h.rec m

theorem Eq.subst {α : Sort u} {motive : α → Prop} {a b : α} (Eq_ab : Eq a b) (motive_a : motive a) : motive b := ndrec motive_a Eq_ab

theorem Eq.symm {α : Sort u} {a b : α} (Eq_ab : Eq a b) : Eq b a :=
  have Eq_aa : Eq a a := Eq.refl a
  subst (motive := fun x => Eq x a) Eq_ab Eq_aa

example (Eq_ab: Eq a b): Eq b a := Eq_ab.symm

theorem Eq.trans {α : Sort u} {a b c : α} (Eq_ab : Eq a b) (Eq_bc : Eq b c) : Eq a c :=
  subst (motive := fun x => Eq a x) Eq_bc Eq_ab

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
  left  : a
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
  intro hb ha

inductive Or (a b : Prop) : Prop where
  | inl (h : a) : Or a b
  | inr (h : b) : Or a b

theorem Or.intro_left (b : Prop) (h : a) : Or a b := inl h

theorem Or.intro_right (a : Prop) (h : b) : Or a b := inr h

example : Or True b := Or.intro_left b True.intro
example : Or b True := Or.intro_right b True.intro
example (ha : a) : Or a b := Or.intro_left b ha
example (ha : a) : Or b a := Or.intro_right b ha

theorem Or.elim {c : Prop} (Or_ab : Or a b) (left : a → c) (right : b → c) : c :=
  match Or_ab with
  | inl h => left h
  | inr h => right h

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
  | true  : Bool

export Bool (false true)

theorem eq_false_of_ne_true {b : Bool} (Not_Eq_b_true : Not (Eq b true)) : Eq b false :=
  match b with
  | false => Eq.refl false
  | true  =>
    have Eq_true_true : Eq true true := Eq.refl true
    absurd Eq_true_true Not_Eq_b_true

theorem eq_true_of_ne_false {b : Bool} (Not_Eq_b_false : Not (Eq b false)) : Eq b true :=
  match b with
  | true  => Eq.refl true
  | false =>
    have Eq_false_false : Eq false false := Eq.refl false
    absurd Eq_false_false Not_Eq_b_false

def Eq.Root {α : Sort u} {a b : α } (Eq_ab : Eq a b) : _root_.Eq a b :=
  match Eq_ab with
  | refl a => _root_.Eq.refl a

def Eq.FromRoot {α : Sort u} {a b : α } (RootEq_ab : _root_.Eq a b) : Eq a b :=
  match RootEq_ab with
  | _root_.Eq.refl a => Eq.refl a

theorem ne_false_of_eq_true {b : Bool} (Eq_b_true : Eq b true) : Not (Eq b false) :=
  match b with
  | true  => fun Eq_true_false => Bool.noConfusion Eq_true_false.Root
  | false => Bool.noConfusion Eq_b_true.Root

theorem ne_true_of_eq_false {b : Bool} (Eq_b_false : Eq b false) : Not (Eq b true) :=
  match b with
  | true  => Bool.noConfusion Eq_b_false.Root
  | false => fun Eq_false_true => Bool.noConfusion Eq_false_true.Root

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
  | zero           => a
  | succ b_minus_1 => succ (add a b_minus_1)

def Nat.mul (a b : Nat) : Nat :=
  match b with
  | zero           => zero
  | succ b_minus_1 => add a (mul a b_minus_1)

def Nat.pow (a b : Nat) : Nat :=
  match b with
  | zero           => succ zero
  | succ b_minus_1 => mul a (pow a b_minus_1)

def Nat.beq : Nat → Nat → Bool
  | zero,   zero   => true
  | zero,   succ _ => false
  | succ _, zero   => false
  | succ n, succ m => beq n m

theorem Nat.eq_of_beq_eq_true {n m : Nat} (Eq_beq_nm_true : Eq (beq n m) true) : Eq n m :=
  match n, m with
  | zero,   zero   => Eq.refl Nat.zero
  | zero,   succ _ => Bool.noConfusion Eq_beq_nm_true.Root
  | succ _, zero   => Bool.noConfusion Eq_beq_nm_true.Root
  | succ n, succ m =>
    have Eq_nm : Eq n m := eq_of_beq_eq_true Eq_beq_nm_true
    congrArg succ Eq_nm

theorem Nat.ne_of_beq_eq_false {n m : Nat} (Eq_beq_nm_false : Eq (beq n m) false) : Not (Eq n m) :=
  match n, m with
  | zero,   zero   => Bool.noConfusion Eq_beq_nm_false.Root
  | zero,   succ _ => fun Eq_nm => Nat.noConfusion Eq_nm.Root
  | succ _, zero   => fun Eq_nm => Nat.noConfusion Eq_nm.Root
  | succ n, succ m => fun Eq_nm =>
    have Not_Eq_nm : Not (Eq n m) := ne_of_beq_eq_false Eq_beq_nm_false
    Nat.noConfusion Eq_nm.Root (fun RootEq_nm => absurd (Eq.FromRoot RootEq_nm) Not_Eq_nm)

/-
theorem Nat.beq_eq_true_of_eq {n m : Nat} (Eq_nm : Eq n m) : Eq (beq n m) true :=
  match n, m with
  | zero,   zero   => Eq.refl (beq zero zero)
  | zero,   succ _ => Nat.noConfusion Eq_nm.Root
  | succ _, zero   => Nat.noConfusion Eq_nm.Root
  | succ np, succ mp =>
  beq_eq_true_of_eq Eq_nm
  termination_by sizeOf n
  decreasing_by n

private theorem noConfusion_of_Nat.aux : (a : Nat) → (Nat.beq a a).rec False True
  | Nat.zero   => True.intro
  | Nat.succ n => noConfusion_of_Nat.aux n

theorem noConfusion_of_Nat {α : Sort u} (f : α → Nat) {a b : α} (Eq_ab : Eq a b) :
    (Nat.beq (f a) (f b)).rec False True :=
  have Eq_fa_fb : Eq (f a) (f b) := congrArg f Eq_ab
  Eq_fa_fb.Root ▸ noConfusion_of_Nat.aux (f a)
-/

protected inductive Nat.le (n : Nat) : Nat → Prop
  | refl     : Nat.le n n
  | step {m} : Nat.le n m → Nat.le n (succ m)

instance instLENat : LE Nat where
  le := Nat.le

theorem Nat.not_succ_le_zero (n : Nat) : LE.le (succ n) zero → False :=
  have Eq_m_zero_implies: ∀ m, Eq m zero → LE.le (succ n) m → False := fun _ Eq_m_zero Le_succ_n_m =>
    le.casesOn (motive := fun m _ => Eq m Nat.zero → False) Le_succ_n_m
      (fun Eq_succ_n_zero => Nat.noConfusion Eq_succ_n_zero.Root)
      (fun _ Eq_succ_m_zero => Nat.noConfusion Eq_succ_m_zero.Root)
      Eq_m_zero
  have Eq_zero_zero : Eq zero zero := Eq.refl zero
  Eq_m_zero_implies zero Eq_zero_zero
