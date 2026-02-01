namespace Basic

noncomputable section

/- True -/

inductive True : Prop where
  | intro : True

-- true
-- ⊢ ⊤
example : True := True.intro

-- a implies true
-- ⊢ a → ⊤
example : a → True := fun _ => True.intro

/- False -/

inductive False : Prop

-- false implies false
-- ⊢ ⊥ → ⊥
example : False → False := fun false => false


-- false proves a
-- ⊥ ⊢ a
def False.elim (false : False) : a := false.rec
example (false : False) : a := False.elim false
example (false : False) : a := false.elim

-- false implies a
-- ⊢ ⊥ → a
example : False → a := fun false => false.elim

/- Not -/

def Not (a : Prop) : Prop := a → False

-- not false
-- ⊢ ¬⊥
theorem not_false : Not False := fun false => false

-- a proves not not a
-- a ⊢ ¬¬a
theorem not_not_intro (ha : a) : Not (Not a) :=
  fun na => na ha

-- not not true
-- ⊢ ¬¬⊤
example : Not (Not True) := not_not_intro True.intro

-- a implies b, not b prove not a
-- a → b, ¬b ⊢ ¬a
theorem Not.imp (nb : Not b) (ab : a → b) : Not a := fun ha => nb (ab ha)

-- not a, a proves b
-- ¬a, a ⊢ b
def Not.elim (na : Not a) (ha : a) : b :=
  have false : False := na ha
  false.elim

-- a ⊢ ¬a → b
example (ha : a) : Not a → b := fun na => na.elim ha

-- ⊢ a → ¬a → b
example : a → Not a → b := fun ha => fun na => na.elim ha
example : a → Not a → b := fun ha na => na.elim ha

-- a → ⊥ ⊢ ¬a
theorem Not.intro (af : a → False) : Not a := af

/- Implies -/

theorem imp_intro {α β : Prop} (h : α) : β → α := fun _ => h

-- a ⊢ b → a
example (ha : a) : b → a := fun _ => ha

theorem imp_imp_imp {a b c d : Prop} (ca : c → a) (bd : b → d) : (a → b) → (c → d) := fun ab => fun hc => bd (ab (ca hc))

-- c → a, b → d ⊢ (a → b) → (c → d)
example (ca : c → a) (bd : b → d) : (a → b) → (c → d) := imp_imp_imp ca bd

/- And -/

structure And (a b : Prop) : Prop where
  intro ::
  left  : a
  right : b

-- ⊢ ⊤ ∧ ⊤
example : And True True := And.intro True.intro True.intro

-- a ⊢ a ∧ a
example (ha : a) : And a a := And.intro ha ha

-- ⊢ a → a ∧ a
example : a → And a a := fun ha => And.intro ha ha

-- a, b ⊢ a ∧ b
example (ha : a) (hb : b) : And a b := And.intro ha hb

-- ⊢ a → b → a ∧ b
example : a → b → And a b := fun ha hb => And.intro ha hb

-- a ∧ b ⊢ a
example (And_ab : And a b) : a := And_ab.left

-- a ∧ b ⊢ b
example (And_ab : And a b) : b := And_ab.right

theorem And.symm (And_ab: And a b) : And b a :=
  have ha : a := And_ab.left
  have hb : b := And_ab.right
  intro hb ha

-- a ∧ b ⊢ b ∧ a
example (And_ab: And a b) : And b a := And_ab.symm

abbrev And.elim (ab : a → b → α) (And_ab : And a b) : α := ab And_ab.left And_ab.right

-- a → b → c, a ∧ b ⊢ c
example (ab : a → b → c) (And_ab : And a b) : c := And_ab.elim ab

/- Or -/

inductive Or (a b : Prop) : Prop where
  | inl (h : a) : Or a b
  | inr (h : b) : Or a b

theorem Or.intro_left (b : Prop) (h : a) : Or a b := inl h

theorem Or.intro_right (a : Prop) (h : b) : Or a b := inr h

-- ⊢ ⊤ ∨ b
example : Or True b := Or.intro_left b True.intro

-- ⊢ b ∨ ⊤
example : Or b True := Or.intro_right b True.intro

-- a ⊢ a ∨ b
example (ha : a) : Or a b := Or.intro_left b ha

-- b ⊢ a ∨ b
example (ha : a) : Or b a := Or.intro_right b ha

theorem Or.elim {c : Prop} (Or_ab : Or a b) (left : a → c) (right : b → c) : c :=
  match Or_ab with
  | inl h => left h
  | inr h => right h

-- a ∨ b, a → c, b → c ⊢ c
example (Or_ab : Or a b) (ac : a → c) (bc : b → c) : c := Or_ab.elim ac bc

theorem Or.symm (Or_ab : Or a b) : Or b a :=
  Or_ab.elim (fun ha => Or.intro_right b ha) (fun hb => Or.intro_left a hb)

-- a ∨ b ⊢ b ∨ a
example (Or_ab: Or a b) : Or b a := Or_ab.symm

theorem Or.resolve_left  (or_ab : Or a b) (na : Not a) : b :=
  or_ab.elim (fun ha => na.elim ha) id

-- a ∨ b, ¬a ⊢ b
example (Or_ab : Or a b) (Not_a : Not a) : b := Or_ab.resolve_left Not_a

theorem Or.resolve_right (or_ab: Or a b) (nb : Not b) : a :=
  or_ab.elim id (fun hb => nb.elim hb)

-- a ∨ b, ¬b ⊢ a
example (Or_ab: Or a b) (Not_b : Not b) : a := Or_ab.resolve_right Not_b

theorem Or.neg_resolve_left (or_nab : Or (Not a) b) (ha : a) : b :=
  or_nab.elim (fun na => na.elim ha) id

-- ¬a ∨ b, a ⊢ b
example (Or_Not_a_b : Or (Not a) b) (ha : a) : b := Or_Not_a_b.neg_resolve_left ha

theorem Or.neg_resolve_right (or_anb : Or a (Not b)) (hb : b) : a :=
  or_anb.elim id (fun nb => nb.elim hb)

-- a ∨ ¬b, b ⊢ ¬a
example (Or_a_Not_b : Or a (Not b)) (hb : b) : a := Or_a_Not_b.neg_resolve_right hb

/- Iff -/

structure Iff (a b : Prop) : Prop where
  intro ::
  mp    : a → b
  mpr   : b → a

-- ⊢ ⊤ ↔ ⊤
example : Iff True True := Iff.intro (fun _ => True.intro) (fun _ => True.intro)

-- ⊢ ⊥ ↔ ⊥
example : Iff False False := Iff.intro (fun false => false) (fun false => false)

-- a → b, b → a ⊢ a ↔ b
example (ab : a → b) (ba : b → a) : Iff a b := Iff.intro ab ba

-- a ↔ b ⊢ a → b
example (Iff_ab : Iff a b) : a → b := Iff_ab.mp

-- a ↔ b ⊢ b → a
example (Iff_ab : Iff a b) : b → a := Iff_ab.mpr

theorem iff_iff_implies_and_implies {a b : Prop} : Iff (Iff a b) (And (a → b) (b → a)) :=
  Iff.intro (fun Iff_ab => And.intro Iff_ab.mp Iff_ab.mpr) (fun And_ab_ba => Iff.intro And_ab_ba.left And_ab_ba.right)

-- ⊢ (a ↔ b) ↔ ((a → b) ∧ (b → a))
example : Iff (Iff a b) (And (a → b) (b → a)) := iff_iff_implies_and_implies

theorem Iff.refl (a : Prop) : Iff a a :=
  Iff.intro (fun ha => ha) (fun ha => ha)
theorem Iff.rfl {a : Prop} : Iff a a := Iff.refl a

-- ⊢ a ↔ a
example : Iff a a := Iff.refl a

theorem Iff.trans (Iff_ab : Iff a b) (Iff_bc : Iff b c) : Iff a c :=
  Iff.intro (fun ha => Iff_bc.mp (Iff_ab.mp ha)) (fun hc => Iff_ab.mpr (Iff_bc.mpr hc))

-- a ↔ b, b ↔ c ⊢ a ↔ c
example (Iff_ab : Iff a b) (Iff_bc : Iff b c) : Iff a c := Iff_ab.trans Iff_bc

theorem Iff.symm (Iff_ab : Iff a b) : Iff b a := Iff.intro Iff_ab.mpr Iff_ab.mp

-- a ↔ b ⊢ b ↔ a
example  (Iff_ab : Iff a b) : Iff b a := Iff_ab.symm

def Iff.elim (ab_ba : (a → b) → (b → a) → α) (Iff_ab : Iff a b) : α := ab_ba Iff_ab.mp Iff_ab.mpr

-- (a → b) → (b → a) → c, a ↔ b ⊢ c
example (ab_ba : (a → b) → (b → a) → c) (Iff_ab : Iff a b) : c := Iff_ab.elim ab_ba

theorem iff_of_true (ha : a) (hb : b) : Iff a b := Iff.intro (fun _ => hb) (fun _ => ha)

-- a, b ⊢ a ↔ b
example (ha : a) (hb : b) : Iff a b := iff_of_true ha hb

theorem iff_of_false (ha : Not a) (hb : Not b) : Iff a b := Iff.intro ha.elim hb.elim

-- ¬a, ¬b ⊢ a ↔ b
example (Not_a : Not a) (Not_b : Not b) : Iff a b := iff_of_false Not_a Not_b

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

theorem not_congr (Iff_ab : Iff a b) : Iff (Not a) (Not b) :=
  Iff.intro
    (fun na => na.imp Iff_ab.mpr)
    (fun nb => nb.imp Iff_ab.mp)

theorem not_not_not : Iff (Not (Not (Not a))) (Not a) :=
  Iff.intro
    (fun nnna => nnna.imp not_not_intro)
    (fun na => not_not_intro na)

theorem iff_def  : Iff (Iff a b) (And (a → b) (b → a)) := iff_iff_implies_and_implies
theorem iff_def' : Iff (Iff a b) (And (b → a) (a → b)) := Iff.trans iff_def And.comm

/- Theorem Proving in Lean 4 - 3.6. Examples of Propositional Validities
https://leanprover.github.io/theorem_proving_in_lean4/Propositions-and-Proofs/#examples-of-propositional-validities
-/

-- p ∧ q ↔ q ∧ p
example : Iff (And p q) (And q p) :=
  Iff.intro
    (fun And_pq => And.intro And_pq.right And_pq.left)
    (fun And_qp => And.intro And_qp.right And_qp.left)

-- p ∨ q ↔ q ∨ p
example : Iff (Or p q) (Or q p) :=
  Iff.intro
    (fun Or_pq => Or_pq.elim
      (fun hp => Or.intro_right q hp)
      (fun hq => Or.intro_left p hq))
    (fun Or_qp => Or_qp.elim
      (fun hq => Or.intro_right p hq)
      (fun hp => Or.intro_left q hp))

-- (p ∧ q) ∧ r ↔ p ∧ (q ∧ r)
example : Iff (And (And p q) r) (And p (And q r)) :=
  Iff.intro
    (fun And_pq_r => And.intro And_pq_r.left.left (And.intro And_pq_r.left.right And_pq_r.right))
    (fun And_p_qr => And.intro (And.intro And_p_qr.left And_p_qr.right.left) And_p_qr.right.right)

-- (p ∨ q) ∨ r ↔ p ∨ (q ∨ r)
example : Iff (Or (Or p q) r) (Or p (Or q r)) :=
  Iff.intro
    (fun Or_pq_r => Or_pq_r.elim
      (fun Or_pq => Or_pq.elim
        (fun hp => Or.intro_left (Or q r) hp)
        (fun hq => Or.intro_right p (Or.intro_left r hq)))
      (fun hr => Or.intro_right p (Or.intro_right q hr)))
    (fun Or_p_qr => Or_p_qr.elim
      (fun hp => Or.intro_left r (Or.intro_left q hp))
      (fun Or_qr => Or_qr.elim
        (fun hq => Or.intro_left r (Or.intro_right p hq))
        (fun hr => Or.intro_right (Or p q) hr)))

-- p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r)
example : Iff (And p (Or q r)) (Or (And p q) (And p r)) :=
  Iff.intro
    (fun p_qr => p_qr.right.elim
      (fun hq => Or.intro_left (And p r) (And.intro p_qr.left hq))
      (fun hr => Or.intro_right (And p q) (And.intro p_qr.left hr)))
    (fun pq_pr => pq_pr.elim
      (fun pq => And.intro pq.left (Or.intro_left r pq.right))
      (fun pr => And.intro pr.left (Or.intro_right q pr.right)))

-- p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r)
example : Iff (Or p (And q r)) (And (Or p q) (Or p r)) :=
  Iff.intro
    (fun p_qr => p_qr.elim
      (fun hp => And.intro (Or.intro_left q hp) (Or.intro_left r hp))
      (fun qr => And.intro (Or.intro_right p qr.left) (Or.intro_right p qr.right)))
    (fun pq_pr => pq_pr.left.elim
      (fun hp => Or.intro_left (And q r) hp)
      (fun hq => pq_pr.right.elim
        (fun hp => Or.intro_left (And q r) hp)
        (fun hr => Or.intro_right p (And.intro hq hr))))

-- (p → (q → r)) ↔ (p ∧ q → r)
example : Iff (p → (q → r)) (And p q → r) :=
  Iff.intro
    (fun pqr => fun pq => pqr pq.left pq.right)
    (fun pq_r => fun hp => fun hq => pq_r (And.intro hp hq))

-- ((p ∨ q) → r) ↔ (p → r) ∧ (q → r)
example : Iff (Or p q → r) (And (p → r) (q → r)) :=
  Iff.intro
    (fun pq_r => And.intro
      (fun hp => pq_r (Or.intro_left q hp))
      (fun hq => pq_r (Or.intro_right p hq)))
    (fun pr_qr => fun pq => pq.elim
      (fun hp => pr_qr.left hp)
      (fun hq => pr_qr.right hq))

-- ¬(p ∨ q) ↔ ¬p ∧ ¬q
example : Iff (Not (Or p q)) (And (Not p) (Not q)) :=
  Iff.intro
    (fun npq => And.intro
      (fun hp => npq (Or.intro_left q hp))
      (fun hq => npq (Or.intro_right p hq)))
    (fun np_nq => fun pq => pq.elim
      (fun hp => np_nq.left hp)
      (fun hq => np_nq.right hq))

-- ¬p ∨ ¬q → ¬(p ∧ q)
example : (Or (Not p) (Not q) → Not (And p q)) :=
  fun np_nq => np_nq.elim
    (fun np => fun pq => np pq.left)
    (fun nq => fun pq => nq pq.right)

-- ¬(p ∧ ¬p)
example : Not (And p (Not p)) :=
  fun p_np => p_np.right p_np.left

-- p ∧ ¬q → ¬(p → q)
example : And p (Not q) → Not (p → q) :=
  fun p_nq => fun pq => p_nq.right (pq p_nq.left)

-- ¬p → (p → q)
example : Not p → (p → q) :=
  fun np => fun p => (np p).elim

-- (¬p ∨ q) → (p → q)
example : Or (Not p) q → (p → q) :=
  fun np_q => fun hp => np_q.elim
    (fun np => (np hp).elim)
    (fun hq => hq)

-- p ∨ False ↔ p
example : Iff (Or p False) p :=
  Iff.intro
    (fun pf => pf.elim
      (fun hp => hp)
      (fun false => false.elim))
    (fun hp => Or.intro_left False hp)

-- p ∧ False ↔ False
example : Iff (And p False) False :=
  Iff.intro
    (fun pf => pf.right)
    (fun false => false.elim)

-- ¬(p ↔ ¬p)
example : Not (Iff p (Not p)) :=
  fun p_np =>
    have np := fun hp => (p_np.mp hp) hp
    np (p_np.mpr np)

-- (p → q) → (¬q → ¬p)
example : (p → q) → (Not q → Not p) :=
  fun pq => fun nq => fun hp => nq (pq hp)

/- Exists -/

inductive Exists {α : Sort u} (p : α → Prop) : Prop where
  | intro (w : α) (pw : p w) : Exists p

theorem Exists.elim {α : Sort u} {p : α → Prop} {b : Prop}
   (Exists_px : Exists (fun x => p x)) (All_px : (a : α) → p a → b) : b :=
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

axiom propext {a b : Prop} : (Iff a b) → Eq a b

theorem Iff.subst {a b : Prop} {p : Prop → Prop} (Iff_ab : Iff a b) (pa : p a) : p b :=
  Eq.subst (propext Iff_ab) pa

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

theorem eq_false_of_ne_true {b : Bool} (neq_bt : Not (Eq b true)) : Eq b false :=
  match b with
  | false => Eq.refl false
  | true  =>
    have eq_tt : Eq true true := Eq.refl true
    neq_bt.elim eq_tt

theorem eq_true_of_ne_false {b : Bool} (Not_Eq_b_false : Not (Eq b false)) : Eq b true :=
  match b with
  | true  => Eq.refl true
  | false =>
    have Eq_false_false : Eq false false := Eq.refl false
    Not_Eq_b_false.elim Eq_false_false

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

theorem Nat.add_zero (n : Nat) : Eq (add n zero) n := Eq.refl (add n zero)

theorem Nat.zero_add (n : Nat) : Eq (add zero n) n :=
  match n with
  | zero    => Eq.refl zero
  | succ n  => congrArg succ (Nat.zero_add n)

theorem Nat.succ_add (n m : Nat) : Eq (add (succ n) m) (succ (add n m)) :=
  match n, m with
  | n, zero   => Eq.refl (succ (add n zero))
  | n, succ m => congrArg succ (succ_add n m)

theorem Nat.add_succ (n m : Nat) : Eq (add n (succ m)) (succ (add n m)) := Eq.refl (succ (add n m))

theorem Nat.add_comm (n m : Nat) : Eq (add n m) (add m n) :=
  match n, m with
  | n, zero   => Eq.symm (Nat.zero_add n)
  | n, succ m =>
    (congrArg succ (add_comm n m)).trans (succ_add m n).symm

def Nat.mul (a b : Nat) : Nat :=
  match b with
  | zero           => zero
  | succ b_minus_1 => add a (mul a b_minus_1)

theorem Nat.mul_zero (n : Nat) : Eq (mul n zero) zero := Eq.refl (mul n zero)

theorem Nat.mul_succ (n m : Nat) : Eq (mul n (succ m)) (add n (mul n m)) := Eq.refl (add n (mul n m))

theorem Nat.zero_mul (n : Nat) : Eq (mul zero n) zero :=
  match n with
  | zero   => Eq.refl zero
  | succ n =>
    ((zero_mul n).symm.trans ((zero_add (mul zero n)).symm.trans (mul_succ zero n).symm)).symm

theorem Nat.mul_one (n : Nat) : Eq (mul n (succ zero)) n := Eq.refl (mul n (succ zero))

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
    Nat.noConfusion Eq_nm.Root (fun RootEq_nm => Not_Eq_nm.elim (Eq.FromRoot RootEq_nm))

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
  | succ n => fun Le_succ_n_n => (not_succ_le_self n).elim (le_of_succ_le_succ Le_succ_n_n)

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
