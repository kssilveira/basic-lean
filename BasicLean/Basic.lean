namespace Basic

noncomputable section

/- True -/

inductive True : Prop where
  | intro : True

example : True := True.intro
example : a → True := fun _ => True.intro

/- False -/

inductive False : Prop

example : False → False := fun false => false

def False.elim {b : Sort u} (false : False) : b := false.rec

example (false : False) : b := False.elim false
example (false : False) : b := false.elim
example : False → b := fun false => false.elim

/- Not -/

def Not (a : Prop) : Prop := a → False

theorem not_false : Not False := fun false => false

theorem not_not_intro {p : Prop} (hp : p) : Not (Not p) :=
  fun Not_p => Not_p hp

example : Not (Not True) := fun Not_true => Not_true True.intro
example : Not (Not True) := not_not_intro True.intro

theorem mt {a b : Prop} (ab : a → b) (Not_b : Not b) : Not a :=
  fun ha => Not_b (ab ha)

theorem Not.imp {a b : Prop} (Not_b : Not b) (ab : a → b) : Not a := mt ab Not_b

def absurd {a : Prop} {b : Sort v} (ha : a) (Not_a : Not a) : b :=
  have false : False := Not_a ha
  false.elim

def Not.elim {α : Sort _} (Not_a : Not a) (ha : a) : α := absurd ha Not_a

example (ha : a) (Not_a : Not a) : b := absurd ha Not_a
example (ha : a) : Not a → b := fun Not_a => absurd ha Not_a
example : a → Not a → b := fun ha => fun Not_a => absurd ha Not_a
example : a → Not a → b := fun ha Not_a => absurd ha Not_a

theorem Not.intro {a : Prop} (af : a → False) : Not a := af

/- Implies -/

theorem imp_intro {α β : Prop} (h : α) : β → α := fun _ => h

theorem imp_imp_imp {a b c d : Prop} (ca : c → a) (bd : b → d) : (a → b) → (c → d) := fun ab => fun hc => bd (ab (ca hc))

/- And -/

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

abbrev And.elim (ab : a → b → α) (And_ab : And a b) : α := ab And_ab.left And_ab.right

/- Or -/

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

theorem Or.symm (Or_ab : Or a b) : Or b a :=
  Or_ab.elim (fun ha => Or.intro_right b ha) (fun hb => Or.intro_left a hb)

theorem Or.resolve_left  (Or_ab : Or a b) (Not_a : Not a) : b :=
  Or_ab.elim (fun ha => absurd ha Not_a) id

theorem Or.resolve_right (Or_ab: Or a b) (Not_b : Not b) : a :=
  Or_ab.elim id (fun hb => absurd hb Not_b)

theorem Or.neg_resolve_left (Or_Not_a_b : Or (Not a) b) (ha : a) : b :=
  Or_Not_a_b.elim (fun Not_a => absurd ha Not_a) id

theorem Or.neg_resolve_right (Or_a_Not_b : Or a (Not b)) (hb : b) : a :=
  Or_a_Not_b.elim id (fun Not_b => absurd hb Not_b)

/- Iff -/

structure Iff (a b : Prop) : Prop where
  intro ::
  mp    : a → b
  mpr   : b → a

example : Iff True True := Iff.intro (fun _ => True.intro) (fun _ => True.intro)
example : Iff False False := Iff.intro (fun false => false) (fun false => false)
example (ab : a → b) (ba : b → a) : Iff a b := Iff.intro ab ba
example (Iff_ab : Iff a b) : a → b := Iff_ab.mp
example (Iff_ab : Iff a b) : b → a := Iff_ab.mpr

theorem iff_iff_implies_and_implies {a b : Prop} : Iff (Iff a b) (And (a → b) (b → a)) :=
  Iff.intro (fun Iff_ab => And.intro Iff_ab.mp Iff_ab.mpr) (fun And_ab_ba => Iff.intro And_ab_ba.left And_ab_ba.right)

theorem Iff.refl (a : Prop) : Iff a a :=
  Iff.intro (fun ha => ha) (fun ha => ha)

theorem Iff.rfl {a : Prop} : Iff a a := Iff.refl a

theorem Iff.trans (Iff_ab : Iff a b) (Iff_bc : Iff b c) : Iff a c :=
  Iff.intro (fun ha => Iff_bc.mp (Iff_ab.mp ha)) (fun hc => Iff_ab.mpr (Iff_bc.mpr hc))

theorem Iff.symm (Iff_ab : Iff a b) : Iff b a := Iff.intro Iff_ab.mpr Iff_ab.mp

def Iff.elim (ab_ba : (a → b) → (b → a) → α) (Iff_ab : Iff a b) : α := ab_ba Iff_ab.mp Iff_ab.mpr

axiom propext {a b : Prop} : (Iff a b) → Eq a b

theorem Iff.subst {a b : Prop} {p : Prop → Prop} (Iff_ab : Iff a b) (pa : p a) : p b :=
  Eq.subst (propext Iff_ab) pa

theorem iff_of_true (ha : a) (hb : b) : Iff a b := Iff.intro (fun _ => hb) (fun _ => ha)
theorem iff_of_false (ha : Not a) (hb : Not b) : Iff a b := Iff.intro ha.elim hb.elim
theorem of_iff_true (Iff_at : Iff a True) : a := Iff_at.mpr True.intro
theorem iff_true_intro (ha : a) : Iff a True := iff_of_true ha True.intro
theorem not_of_iff_false : (Iff p False) → Not p := Iff.mp
theorem iff_false_intro (Not_a : Not a) : Iff a False := iff_of_false Not_a (fun false => false)

theorem Iff.comm : Iff (Iff a b) (Iff b a) := Iff.intro Iff.symm Iff.symm
theorem iff_comm : Iff (Iff a b) (Iff b a) := Iff.comm

theorem And.comm : Iff (And a b) (And b a) := Iff.intro And.symm And.symm
theorem and_comm : Iff (And a b) (And b a) := And.comm

theorem Or.comm : Iff (Or a b) (Or b a) := Iff.intro Or.symm Or.symm
theorem or_comm : Iff (Or a b) (Or b a) := Or.comm

theorem not_congr (Iff_ab : Iff a b) : Iff (Not a) (Not b) := Iff.intro (mt Iff_ab.mpr) (mt Iff_ab.mp)

theorem not_not_not : Iff (Not (Not (Not a))) (Not a) := Iff.intro (mt not_not_intro) not_not_intro

theorem iff_def  : Iff (Iff a b) (And (a → b) (b → a)) := iff_iff_implies_and_implies
theorem iff_def' : Iff (Iff a b) (And (b → a) (a → b)) := Iff.trans iff_def And.comm

/- Exists -/

inductive Exists {α : Sort u} (p : α → Prop) : Prop where
  | intro (w : α) (pw : p w) : Exists p

theorem Exists.elim {α : Sort u} {p : α → Prop} {b : Prop}
   (Exists_px : Exists (fun x => p x)) (All_px : ∀ (a : α), p a → b) : b :=
  match Exists_px with
  | intro a pa => All_px a pa

/- Set -/

class HasSubset (α : Type u) where
  Subset : α → α → Prop
export HasSubset (Subset)

class HasSSubset (α : Type u) where
  SSubset : α → α → Prop
export HasSSubset (SSubset)

abbrev Superset [HasSubset α] (a b : α) := Subset b a

abbrev SSuperset [HasSSubset α] (a b : α) := SSubset b a

class Union (α : Type u) where
  union : α → α → α

class Inter (α : Type u) where
  inter : α → α → α

/- Eq -/

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

/- Bool -/

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

/- Nat -/

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

protected inductive Nat.le (n : Nat) : Nat → Prop
  | refl     : Nat.le n n
  | step {m} : Nat.le n m → Nat.le n (succ m)

instance instLENat : LE Nat where
  le := Nat.le

theorem Nat.not_succ_le_zero (n : Nat) : LE.le (succ n) zero → False :=
  have Eq_m_zero_implies: ∀ m, Eq m zero → LE.le (succ n) m → False := fun _ Eq_m_zero Le_succ_n_m =>
    le.casesOn (motive := fun m _ => Eq m Nat.zero → False) Le_succ_n_m
      (fun Eq_succ_n_zero   => Nat.noConfusion Eq_succ_n_zero.Root)
      (fun _ Eq_succ_m_zero => Nat.noConfusion Eq_succ_m_zero.Root)
      Eq_m_zero
  have Eq_zero_zero : Eq zero zero := Eq.refl zero
  Eq_m_zero_implies zero Eq_zero_zero

theorem Nat.zero_le : (n : Nat) → LE.le zero n
  | zero   => Nat.le.refl
  | succ n => Nat.le.step (zero_le n)

theorem Nat.succ_le_succ : LE.le n m → LE.le (succ n) (succ m)
  | Nat.le.refl       => Nat.le.refl
  | Nat.le.step Le_nm => Nat.le.step (succ_le_succ Le_nm)

theorem Nat.le_succ_of_le (Le_nm : LE.le n m) : LE.le n (succ m) :=
  Nat.le.step Le_nm

theorem Nat.le_trans {n m k : Nat} (Le_nm : LE.le n m) : LE.le m k → LE.le n k
  | Nat.le.refl       => Le_nm
  | Nat.le.step Le_mk => Nat.le.step (Nat.le_trans Le_nm Le_mk)

theorem Nat.le_succ (n : Nat) : LE.le n (succ n) :=
  Nat.le.step Nat.le.refl

theorem Nat.le_refl (n : Nat) : LE.le n n :=
  Nat.le.refl

def Nat.pred : Nat → Nat
  | zero   => zero
  | succ n => n

theorem Nat.pred_le_pred : {n m : Nat} → LE.le n m → LE.le (pred n) (pred m)
  | _,           _, Nat.le.refl             => Nat.le.refl
  | zero,   succ _, Nat.le.step Le_zero_m   => Le_zero_m
  | succ _, succ _, Nat.le.step Le_succ_n_m => Nat.le_trans (le_succ _) Le_succ_n_m

theorem Nat.le_of_succ_le_succ {n m : Nat} : LE.le (succ n) (succ m) → LE.le n m :=
  pred_le_pred

theorem Nat.not_succ_le_self : (n : Nat) → Not (LE.le (succ n) n)
  | zero   => not_succ_le_zero _
  | succ n => fun Le_succ_n_n => absurd (le_of_succ_le_succ Le_succ_n_n) (not_succ_le_self n)

def Nat.ble : Nat → Nat → Bool
  | zero,   _      => true
  | succ _, zero   => false
  | succ n, succ m => ble n m

theorem Nat.le_of_ble_eq_true (Eq_ble_nm_true : Eq (Nat.ble n m) true) : LE.le n m :=
  match n, m with
  | zero,      _   => Nat.zero_le _
  | succ _, succ _ => Nat.succ_le_succ (le_of_ble_eq_true Eq_ble_nm_true)

theorem Nat.ble_self_eq_true : (n : Nat) → Eq (Nat.ble n n) true
  | zero   => Eq.refl (ble zero zero)
  | succ n => ble_self_eq_true n

def Nat.sub (n : Nat) : Nat → Nat
  | zero   => n
  | succ m => pred (Nat.sub n m)

theorem Nat.pred_le : ∀ (n : Nat), LE.le (Nat.pred n) n
  | zero   => Nat.le.refl
  | succ _ => le_succ _
