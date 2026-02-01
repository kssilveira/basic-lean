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

-- a implies b, not b
--   proves not a
-- a → b, ¬b ⊢ ¬a
theorem Not.imp (nb : Not b) (ab : a → b) : Not a :=
  fun ha => nb (ab ha)

-- not a, a
--   proves b
-- ¬a, a ⊢ b
def Not.elim (na : Not a) (ha : a) : b :=
  have false : False := na ha
  false.elim

-- a proves not a implies b
-- a ⊢ ¬a → b
example (ha : a) : Not a → b := fun na => na.elim ha

-- a implies not a implies b
-- ⊢ a → ¬a → b
example : a → Not a → b := fun ha => fun na => na.elim ha
example : a → Not a → b := fun ha na => na.elim ha

-- a implies false
--   proves not a
-- a → ⊥ ⊢ ¬a
theorem Not.intro (af : a → False) : Not a := af

/- Implies -/

-- a proves b implies a
-- a ⊢ b → a
theorem imp_intro {a : Prop} (ha : a) : b → a := fun _ => ha

-- c implies a, b implies d
--   proves (a implies b) implies (c implies d)
-- c → a, b → d ⊢ (a → b) → (c → d)
theorem imp_imp_imp {d : Prop}
    (ca : c → a) (bd : b → d) : (a → b) → (c → d) :=
  fun ab => fun hc => bd (ab (ca hc))

/- And -/

structure And (a b : Prop) : Prop where
  intro ::
  left  : a
  right : b

-- true and true
-- ⊢ ⊤ ∧ ⊤
example : And True True := And.intro True.intro True.intro

-- a proves a and a
-- a ⊢ a ∧ a
example (ha : a) : And a a := And.intro ha ha

-- a implies a and a
-- ⊢ a → a ∧ a
example : a → And a a := fun ha => And.intro ha ha

-- a, b
--   proves a and b
-- a, b ⊢ a ∧ b
example (ha : a) (hb : b) : And a b := And.intro ha hb

-- a implies b implies a and b
-- ⊢ a → b → a ∧ b
example : a → b → And a b := fun ha hb => And.intro ha hb

-- a and b
--   proves a
-- a ∧ b ⊢ a
example (and_ab : And a b) : a := and_ab.left

-- a and b
--   proves b
-- a ∧ b ⊢ b
example (and_ab : And a b) : b := and_ab.right

-- a and b
--   proves b and a
-- a ∧ b ⊢ b ∧ a
theorem And.symm (and_ab: And a b) : And b a :=
  have ha : a := and_ab.left
  have hb : b := and_ab.right
  intro hb ha

-- a implies b implies c, a and b
--   proves c
-- a → b → c, a ∧ b ⊢ c
abbrev And.elim (ab : a → b → c) (and_ab : And a b) : c :=
  ab and_ab.left and_ab.right

/- Or -/

inductive Or (a b : Prop) : Prop where
  | inl (h : a) : Or a b
  | inr (h : b) : Or a b

-- a proves a or b
-- a ⊢ a ∨ b
theorem Or.intro_left (b : Prop) (h : a) : Or a b := inl h

-- b proves a or b
-- b ⊢ a ∨ b
theorem Or.intro_right (a : Prop) (h : b) : Or a b := inr h

-- true or b
-- ⊢ ⊤ ∨ b
example : Or True b := Or.intro_left b True.intro

-- b or true
-- ⊢ b ∨ ⊤
example : Or b True := Or.intro_right b True.intro

-- a or b, a implies c, b implies c
--   proves c
-- a ∨ b, a → c, b → c ⊢ c
theorem Or.elim {c : Prop}
    (or_ab : Or a b) (ac : a → c) (bc : b → c) : c :=
  match or_ab with
  | inl ha => ac ha
  | inr hb => bc hb

-- a or b
--   proves b or a
-- a ∨ b ⊢ b ∨ a
theorem Or.symm (or_ab : Or a b) : Or b a :=
  or_ab.elim
    (fun ha => Or.intro_right b ha)
    (fun hb => Or.intro_left a hb)

-- a or b, not a
--   proves b
-- a ∨ b, ¬a ⊢ b
theorem Or.resolve_left  (or_ab : Or a b) (na : Not a) : b :=
  or_ab.elim (fun ha => na.elim ha) (fun hb => hb)

-- a or b, not b
--   proves a
-- a ∨ b, ¬b ⊢ a
theorem Or.resolve_right (or_ab: Or a b) (nb : Not b) : a :=
  or_ab.elim (fun ha => ha) (fun hb => nb.elim hb)

-- not a or b, a
--   proves b
-- ¬a ∨ b, a ⊢ b
theorem Or.neg_resolve_left (or_nab : Or (Not a) b) (ha : a) : b :=
  or_nab.elim (fun na => na.elim ha) (fun hb => hb)

-- a or not b, b
--   proves a
-- a ∨ ¬b, b ⊢ a
theorem Or.neg_resolve_right (or_anb : Or a (Not b)) (hb : b) : a :=
  or_anb.elim (fun ha => ha) (fun nb => nb.elim hb)

/- Iff -/

structure Iff (a b : Prop) : Prop where
  intro ::
  mp    : a → b
  mpr   : b → a

-- true iff true
-- ⊢ ⊤ ↔ ⊤
example : Iff True True :=
  Iff.intro (fun _ => True.intro) (fun _ => True.intro)

-- false iff false
-- ⊢ ⊥ ↔ ⊥
example : Iff False False :=
  Iff.intro (fun false => false) (fun false => false)

-- a implies b, b implies a
--   proves a iff b
-- a → b, b → a ⊢ a ↔ b
example (ab : a → b) (ba : b → a) : Iff a b := Iff.intro ab ba

-- a iff b
--   proves a implies b
-- a ↔ b ⊢ a → b
example (iff_ab : Iff a b) : a → b := iff_ab.mp

-- a iff b
--   proves b implies a
-- a ↔ b ⊢ b → a
example (iff_ab : Iff a b) : b → a := iff_ab.mpr

-- (a iff b) iff ((a implies b) and (b implies a))
-- ⊢ (a ↔ b) ↔ ((a → b) ∧ (b → a))
theorem iff_iff_implies_and_implies :
    Iff (Iff a b) (And (a → b) (b → a)) :=
  Iff.intro
    (fun iff_ab => And.intro iff_ab.mp iff_ab.mpr)
    (fun and_ab_ba => Iff.intro and_ab_ba.left and_ab_ba.right)

-- a iff a
-- ⊢ a ↔ a
theorem Iff.refl (a : Prop) : Iff a a :=
  Iff.intro (fun ha => ha) (fun ha => ha)

-- a iff b, b iff c
--   proves a iff c
-- a ↔ b, b ↔ c ⊢ a ↔ c
theorem Iff.trans
    (iff_ab : Iff a b) (iff_bc : Iff b c) : Iff a c :=
  Iff.intro
    (fun ha => iff_bc.mp (iff_ab.mp ha))
    (fun hc => iff_ab.mpr (iff_bc.mpr hc))

-- a iff b
--   proves b iff a
-- a ↔ b ⊢ b ↔ a
theorem Iff.symm (iff_ab : Iff a b) : Iff b a :=
  Iff.intro iff_ab.mpr iff_ab.mp

-- (a implies b) implies (b implies a) implies c, a iff b
--   proves c
-- (a → b) → (b → a) → c, a ↔ b ⊢ c
def Iff.elim
    (ab_ba : (a → b) → (b → a) → c) (iff_ab : Iff a b) : c :=
  ab_ba iff_ab.mp iff_ab.mpr

-- a, b
--   proves a iff b
-- a, b ⊢ a ↔ b
theorem iff_of_true (ha : a) (hb : b) : Iff a b :=
  Iff.intro (fun _ => hb) (fun _ => ha)

-- not a, not b
--   proves a iff b
-- ¬a, ¬b ⊢ a ↔ b
theorem iff_of_false (na : Not a) (nb : Not b) : Iff a b :=
  Iff.intro (fun ha => na.elim ha) (fun hb => nb.elim hb)

-- a iff true
--   proves a
-- a ↔ ⊤ ⊢ a
theorem of_iff_true (iff_at : Iff a True) : a :=
  iff_at.mpr True.intro

-- a proves a iff true
-- a ⊢ a ↔ ⊤
theorem iff_true_intro (ha : a) : Iff a True :=
  iff_of_true ha True.intro

-- a iff false
--   proves not a
-- a ↔ ⊥ ⊢ ¬a
theorem not_of_iff_false : (Iff a False) → Not a := Iff.mp

-- not a
--   proves a iff false
-- ¬a ⊢ a ↔ ⊥
theorem iff_false_intro (na : Not a) : Iff a False :=
  iff_of_false na (fun false => false)

-- (a iff b) iff (b iff a)
-- ⊢ (a ↔ b) ↔ (b ↔ a)
theorem Iff.comm : Iff (Iff a b) (Iff b a) :=
  Iff.intro Iff.symm Iff.symm

-- (a and b) iff (b and a)
-- ⊢ (a ∧ b) ↔ (b ∧ a)
theorem And.comm : Iff (And a b) (And b a) :=
  Iff.intro And.symm And.symm

-- (a or b) iff (b or a)
-- ⊢ (a ∨ b) ↔ (b ∨ a)
theorem Or.comm : Iff (Or a b) (Or b a) :=
  Iff.intro Or.symm Or.symm

-- a iff b
--   proves not a iff not b
-- a ↔ b ⊢ ¬a ↔ ¬b
theorem not_congr (iff_ab : Iff a b) : Iff (Not a) (Not b) :=
  Iff.intro
    (fun na => na.imp iff_ab.mpr)
    (fun nb => nb.imp iff_ab.mp)

-- not not not a iff not a
-- ⊢ ¬¬¬a ↔ ¬a
theorem not_not_not : Iff (Not (Not (Not a))) (Not a) :=
  Iff.intro
    (fun nnna => nnna.imp not_not_intro)
    (fun na => not_not_intro na)

-- (a iff b) iff (b implies a) and (a implies b)
-- ⊢ (a ↔ b) ↔ (b → a) ∧ (a → b)
theorem iff_def' : Iff (Iff a b) (And (b → a) (a → b)) :=
  Iff.trans iff_iff_implies_and_implies And.comm

/- Theorem Proving in Lean 4 - 3.6. Examples of Propositional Validities
https://leanprover.github.io/theorem_proving_in_lean4/Propositions-and-Proofs/#examples-of-propositional-validities
-/

-- p and q iff q and p
-- ⊢ p ∧ q ↔ q ∧ p
example : Iff (And p q) (And q p) :=
  Iff.intro
    (fun and_pq => And.intro and_pq.right and_pq.left)
    (fun and_qp => And.intro and_qp.right and_qp.left)

-- p or q iff q or p
-- ⊢ p ∨ q ↔ q ∨ p
example : Iff (Or p q) (Or q p) :=
  Iff.intro
    (fun or_pq => or_pq.elim
      (fun hp => Or.intro_right q hp)
      (fun hq => Or.intro_left p hq))
    (fun or_qp => or_qp.elim
      (fun hq => Or.intro_right p hq)
      (fun hp => Or.intro_left q hp))

-- (p and q) and r iff p and (q and r)
-- ⊢ (p ∧ q) ∧ r ↔ p ∧ (q ∧ r)
example : Iff (And (And p q) r) (And p (And q r)) :=
  Iff.intro
    (fun and_pq_r =>
      And.intro
        and_pq_r.left.left
        (And.intro and_pq_r.left.right and_pq_r.right))
    (fun and_p_qr =>
      And.intro
        (And.intro and_p_qr.left and_p_qr.right.left)
        and_p_qr.right.right)

-- (p or q) or r iff p or (q or r)
-- ⊢ (p ∨ q) ∨ r ↔ p ∨ (q ∨ r)
example : Iff (Or (Or p q) r) (Or p (Or q r)) :=
  Iff.intro
    (fun or_pq_r => or_pq_r.elim
      (fun or_pq => or_pq.elim
        (fun hp => Or.intro_left (Or q r) hp)
        (fun hq => Or.intro_right p (Or.intro_left r hq)))
      (fun hr => Or.intro_right p (Or.intro_right q hr)))
    (fun or_p_qr => or_p_qr.elim
      (fun hp => Or.intro_left r (Or.intro_left q hp))
      (fun or_qr => or_qr.elim
        (fun hq => Or.intro_left r (Or.intro_right p hq))
        (fun hr => Or.intro_right (Or p q) hr)))

-- p and (q or r) iff (p and q) or (p and r)
-- ⊢ p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r)
example : Iff (And p (Or q r)) (Or (And p q) (And p r)) :=
  Iff.intro
    (fun p_qr => p_qr.right.elim
      (fun hq => Or.intro_left (And p r) (And.intro p_qr.left hq))
      (fun hr => Or.intro_right (And p q) (And.intro p_qr.left hr)))
    (fun pq_pr => pq_pr.elim
      (fun pq => And.intro pq.left (Or.intro_left r pq.right))
      (fun pr => And.intro pr.left (Or.intro_right q pr.right)))

-- p or (q and r) iff (p or q) and (q or r)
-- ⊢ p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r)
example : Iff (Or p (And q r)) (And (Or p q) (Or p r)) :=
  Iff.intro
    (fun p_qr => p_qr.elim
      (fun hp => And.intro
        (Or.intro_left q hp)
        (Or.intro_left r hp))
      (fun qr => And.intro
        (Or.intro_right p qr.left)
        (Or.intro_right p qr.right)))
    (fun pq_pr => pq_pr.left.elim
      (fun hp => Or.intro_left (And q r) hp)
      (fun hq => pq_pr.right.elim
        (fun hp => Or.intro_left (And q r) hp)
        (fun hr => Or.intro_right p (And.intro hq hr))))

-- (p implies (q implies r)) iff (p and q implies r)
-- ⊢ (p → (q → r)) ↔ (p ∧ q → r)
example : Iff (p → (q → r)) (And p q → r) :=
  Iff.intro
    (fun pqr => fun pq => pqr pq.left pq.right)
    (fun pq_r => fun hp => fun hq => pq_r (And.intro hp hq))

-- ((p or q) implies r) iff (p implies r) and (q implies r)
-- ⊢ ((p ∨ q) → r) ↔ (p → r) ∧ (q → r)
example : Iff (Or p q → r) (And (p → r) (q → r)) :=
  Iff.intro
    (fun pq_r => And.intro
      (fun hp => pq_r (Or.intro_left q hp))
      (fun hq => pq_r (Or.intro_right p hq)))
    (fun pr_qr => fun pq => pq.elim
      (fun hp => pr_qr.left hp)
      (fun hq => pr_qr.right hq))

-- not (p or q) iff not p and not q
-- ⊢ ¬(p ∨ q) ↔ ¬p ∧ ¬q
example : Iff (Not (Or p q)) (And (Not p) (Not q)) :=
  Iff.intro
    (fun npq => And.intro
      (fun hp => npq (Or.intro_left q hp))
      (fun hq => npq (Or.intro_right p hq)))
    (fun np_nq => fun pq => pq.elim
      (fun hp => np_nq.left hp)
      (fun hq => np_nq.right hq))

-- not p or not q implies not (p and q)
-- ⊢ ¬p ∨ ¬q → ¬(p ∧ q)
example : (Or (Not p) (Not q) → Not (And p q)) :=
  fun np_nq => np_nq.elim
    (fun np => fun pq => np pq.left)
    (fun nq => fun pq => nq pq.right)

-- not (p and not p)
-- ⊢ ¬(p ∧ ¬p)
example : Not (And p (Not p)) :=
  fun p_np => p_np.right p_np.left

-- p and not q implies not (p implies q)
-- ⊢ p ∧ ¬q → ¬(p → q)
example : And p (Not q) → Not (p → q) :=
  fun p_nq => fun pq => p_nq.right (pq p_nq.left)

-- not p implies (p implies q)
-- ⊢ ¬p → (p → q)
example : Not p → (p → q) :=
  fun np => fun p => (np p).elim

-- (not p or q) implies (p implies q)
-- ⊢ (¬p ∨ q) → (p → q)
example : Or (Not p) q → (p → q) :=
  fun np_q => fun hp => np_q.elim
    (fun np => (np hp).elim)
    (fun hq => hq)

-- p or false implies p
-- ⊢ p ∨ False ↔ p
example : Iff (Or p False) p :=
  Iff.intro
    (fun pf => pf.elim
      (fun hp => hp)
      (fun false => false.elim))
    (fun hp => Or.intro_left False hp)

-- p and false iff false
-- ⊢ p ∧ False ↔ False
example : Iff (And p False) False :=
  Iff.intro
    (fun pf => pf.right)
    (fun false => false.elim)

-- not (p iff not p)
-- ⊢ ¬(p ↔ ¬p)
example : Not (Iff p (Not p)) :=
  fun p_np =>
    have np := fun hp => (p_np.mp hp) hp
    np (p_np.mpr np)

-- (p implies q) implies (not q implies not p)
-- ⊢ (p → q) → (¬q → ¬p)
example : (p → q) → (Not q → Not p) :=
  fun pq => fun nq => fun hp => nq (pq hp)

/- Eq -/

inductive Eq : α → α → Prop where
  | refl (a : α) : Eq a a

def id (a : α) : α := a

-- ⊢ (id a) = a
theorem id_eq (a : α) : Eq (id a) a := Eq.refl a

-- ⊢ a = (id a)
theorem eq_id (a : α) : Eq a (id a) := Eq.refl a

abbrev Eq.ndrec {motive : α → Sort u}
    (m : motive a) (h : Eq a b) : motive b :=
  h.rec m

-- a = b ⊢ f a = f b
theorem Eq.subst {motive : α → Prop}
    (eq_ab : Eq a b) (motive_a : motive a) : motive b :=
  ndrec motive_a eq_ab

-- ⊢ a ↔ b → a = b
axiom propext : (Iff a b) → Eq a b

-- a ↔ b, p a ⊢ p b
theorem Iff.subst {p : Prop → Prop}
    (iff_ab : Iff a b) (pa : p a) : p b :=
  Eq.subst (propext iff_ab) pa

-- a = b ⊢ b = a
theorem Eq.symm (eq_ab : Eq a b) : Eq b a :=
  have eq_aa : Eq a a := Eq.refl a
  subst (motive := fun x => Eq x a) eq_ab eq_aa

-- a = b, b = c ⊢ a = c
theorem Eq.trans (eq_ab : Eq a b) (eq_bc : Eq b c) : Eq a c :=
  subst (motive := fun x => Eq a x) eq_bc eq_ab

-- a = b ⊢ f a = f b
theorem congrArg (f : α → β) (eq_ab: Eq a b) : Eq (f a) (f b) :=
  have eq_fa_fa : Eq (f a) (f a) := Eq.refl (f a)
  Eq.subst (motive := fun x => Eq (f a) (f x)) eq_ab eq_fa_fa

-- f = g ⊢ f a = g a
theorem congrFun {β : α → Sort v} {f g : (x : α) → β x}
    (eq_fg : Eq f g) (a : α) : Eq (f a) (g a) :=
  have eq_fa_fa : Eq (f a) (f a) := Eq.refl (f a)
  Eq.subst (motive := fun x => Eq (f a) (x a)) eq_fg eq_fa_fa

-- f = g, a = b ⊢ f a = g b
theorem congr {f g : α → β} {a b : α}
    (eq_fg : Eq f g) (eq_ab : Eq a b) : Eq (f a) (g b) :=
  have eq_fa_fb : Eq (f a) (f b) := congrArg f eq_ab
  Eq.subst (motive := fun x => Eq (f a) (x b)) eq_fg eq_fa_fb

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

theorem eq_true_of_ne_false {b : Bool} (neq_bf : Not (Eq b false)) : Eq b true :=
  match b with
  | true  => Eq.refl true
  | false =>
    have eq_ff : Eq false false := Eq.refl false
    neq_bf.elim eq_ff

def Eq.Root {α : Sort u} {a b : α } (eq_ab : Eq a b) : _root_.Eq a b :=
  match eq_ab with
  | refl a => _root_.Eq.refl a

def Eq.FromRoot {α : Sort u} {a b : α } (Rooteq_ab : _root_.Eq a b) : Eq a b :=
  match Rooteq_ab with
  | _root_.Eq.refl a => Eq.refl a

theorem ne_false_of_eq_true {b : Bool} (eq_b_true : Eq b true) : Not (Eq b false) :=
  match b with
  | true  => fun eq_true_false => Bool.noConfusion eq_true_false.Root
  | false => Bool.noConfusion eq_b_true.Root

theorem ne_true_of_eq_false {b : Bool} (eq_b_false : Eq b false) : Not (Eq b true) :=
  match b with
  | true  => Bool.noConfusion eq_b_false.Root
  | false => fun eq_false_true => Bool.noConfusion eq_false_true.Root

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

theorem Nat.eq_of_beq_eq_true {n m : Nat} (eq_beq_nm_true : Eq (beq n m) true) : Eq n m :=
  match n, m with
  | zero,   zero   => Eq.refl Nat.zero
  | zero,   succ _ => Bool.noConfusion eq_beq_nm_true.Root
  | succ _, zero   => Bool.noConfusion eq_beq_nm_true.Root
  | succ n, succ m =>
    have eq_nm : Eq n m := eq_of_beq_eq_true eq_beq_nm_true
    congrArg succ eq_nm

theorem Nat.ne_of_beq_eq_false {n m : Nat} (eq_beq_nm_false : Eq (beq n m) false) : Not (Eq n m) :=
  match n, m with
  | zero,   zero   => Bool.noConfusion eq_beq_nm_false.Root
  | zero,   succ _ => fun eq_nm => Nat.noConfusion eq_nm.Root
  | succ _, zero   => fun eq_nm => Nat.noConfusion eq_nm.Root
  | succ n, succ m => fun eq_nm =>
    have neq_nm : Not (Eq n m) := ne_of_beq_eq_false eq_beq_nm_false
    Nat.noConfusion eq_nm.Root (fun Rooteq_nm => neq_nm.elim (Eq.FromRoot Rooteq_nm))

protected inductive Nat.le (n : Nat) : Nat → Prop
  | refl     : Nat.le n n
  | step {m} : Nat.le n m → Nat.le n (succ m)

instance instLENat : LE Nat where
  le := Nat.le

theorem Nat.not_succ_le_zero (n : Nat) : LE.le (succ n) zero → False :=
  have eq_m_zero_implies: ∀ m, Eq m zero → LE.le (succ n) m → False := fun _ eq_m_zero Le_succ_n_m =>
    le.casesOn (motive := fun m _ => Eq m Nat.zero → False) Le_succ_n_m
      (fun eq_succ_n_zero   => Nat.noConfusion eq_succ_n_zero.Root)
      (fun _ eq_succ_m_zero => Nat.noConfusion eq_succ_m_zero.Root)
      eq_m_zero
  have eq_zero_zero : Eq zero zero := Eq.refl zero
  eq_m_zero_implies zero eq_zero_zero

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

theorem Nat.le_of_ble_eq_true (eq_ble_nm_true : Eq (Nat.ble n m) true) : LE.le n m :=
  match n, m with
  | zero,      _   => Nat.zero_le _
  | succ _, succ _ => Nat.succ_le_succ (le_of_ble_eq_true eq_ble_nm_true)

theorem Nat.ble_self_eq_true : (n : Nat) → Eq (Nat.ble n n) true
  | zero   => Eq.refl (ble zero zero)
  | succ n => ble_self_eq_true n

def Nat.sub (n : Nat) : Nat → Nat
  | zero   => n
  | succ m => pred (Nat.sub n m)

theorem Nat.pred_le : ∀ (n : Nat), LE.le (Nat.pred n) n
  | zero   => Nat.le.refl
  | succ _ => le_succ _
