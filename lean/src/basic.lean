import data.set

-- syntax

-- we use natural numbers for atomic propositions
inductive Formula : Type
  | falsum : Formula
  | atom : ℕ -> Formula
  | and : Formula -> Formula -> Formula
  | neg : Formula -> Formula
  | implies : Formula -> Formula -> Formula
  | iff : Formula -> Formula -> Formula
  | exp : Formula -> Formula
  | sound : Formula -> Formula
  | univ : Formula -> Formula

-- infix notation
notation `⊥` := Formula.falsum
notation `P` n := Formula.atom n
notation φ `&` ψ := Formula.and φ ψ
notation `#` φ := Formula.neg φ
notation φ `⇒` ψ := Formula.implies φ ψ
notation φ `⇔` ψ := Formula.iff φ ψ
notation `E` φ := Formula.exp φ
notation `S` φ := Formula.sound φ
notation `A` φ := Formula.univ φ

-- semantics

-- expertise frame over a type α
structure Frame (α : Type) :=
  (has_expertise : set α -> Prop)

-- expertise model: extend a frame by adding a valuation function
--% latex_label: def_expertise_model
structure Model (α : Type) extends Frame α :=
  (val : ℕ → α → Prop)

def based_on_frame {α: Type} (m : Model α) (f : Frame α) :=
  ∀ a : set α, m.has_expertise a <-> f.has_expertise a

-- satisfaction relation
@[simp] def sat {α : Type} (m : Model α) : α -> Formula -> Prop
  | x ⊥  := false
  | x (P n)   := m.val n x
  | x (φ & ψ) := (sat x φ) ∧ (sat x ψ)
  | x (# φ)   := ¬(sat x φ)
  | x (φ ⇒ ψ) := (sat x φ) -> (sat x ψ)
  | x (φ ⇔ ψ) := (sat x φ) <-> (sat x ψ)
  | x (E φ)   := m.has_expertise {y | sat y φ}
  | x (S φ)   := ∀ a : set α, m.has_expertise a -> {y | sat y φ} ⊆ a -> x ∈ a
  | x (A φ)   := ∀ y : α, sat y φ

-- lift satisfaction relation to sets of formulas
@[simp] def set_sat {α : Type} (m : Model α) (x : α) (Γ : set Formula) :=
  ∀ φ ∈ Γ, sat m x φ

-- frame validity
@[simp] def valid_on_frame {α : Type} (f : Frame α) (φ : Formula) :=
  ∀ m : Model α, based_on_frame m f -> ∀ x : α, sat m x φ

-- general validity
@[simp] def valid (φ : Formula) := ∀ α : Type, ∀ m : Model α, ∀ x : α, sat m x φ

-- semantic consequence
@[simp] def consequence (Γ : set Formula) (φ : Formula) :=
  ∀ α : Type, ∀ m : Model α, ∀ x : α, set_sat m x Γ -> sat m x φ

-- closure properties for expertise predicates, frames and models
@[simp] def closed_under_intersections {α : Type} (exp : set α -> Prop) :=
  ∀ aa : set (set α), (∀ a ∈ aa, exp a) -> exp (⋂₀ aa)
@[simp] def closed_under_unions {α : Type} (exp : set α -> Prop) :=
  ∀ aa : set (set α), (∀ a ∈ aa, exp a) -> exp (⋃₀ aa)
@[simp] def closed_under_finite_intersections {α : Type} (exp : set α -> Prop) :=
  exp set.univ ∧ ∀ a b : set α, exp a -> exp b -> exp (a ∩ b)
@[simp] def closed_under_compl {α : Type} (exp : set α -> Prop) :=
  ∀ a : set α, exp a -> exp aᶜ

@[simp] def fclosed_under_intersections {α : Type} (f : Frame α) :=
  closed_under_intersections f.has_expertise
@[simp] def fclosed_under_unions {α : Type} (f : Frame α) :=
  closed_under_unions f.has_expertise

@[simp] def mclosed_under_intersections {α : Type} (m : Model α) :=
  closed_under_intersections m.has_expertise
@[simp] def mclosed_under_unions {α : Type} (m : Model α) :=
  closed_under_unions m.has_expertise
@[simp] def mclosed_under_compl {α : Type} (m : Model α) :=
  closed_under_compl m.has_expertise

-- closure under intersections implies closure under finite intersections
lemma int_implies_finite_int {α : Type} (exp : set α -> Prop) :
  closed_under_intersections exp -> closed_under_finite_intersections exp :=
begin
  intros h,
  apply and.intro,
    rw <-set.sInter_empty,
    apply h ∅,
    intros,
    apply absurd (set.not_mem_empty a),
    simp,
    assumption,

    intros a b h_a_exp h_b_exp,
    rw <-set.sInter_pair,
    apply h {a, b},
    intros c hmem,
    apply or.elim (set.eq_or_mem_of_mem_insert hmem),
      intro h_c_eq_a,
      rw h_c_eq_a,
      assumption,

      simp,
      intro h_c_eq_b,
      rw h_c_eq_b,
      assumption,
end

lemma finset_intersections {α : Type} (exp : set α -> Prop) :
  closed_under_finite_intersections exp ->
    ∀ aa : finset (set α), (∀ a ∈ aa, exp a) -> exp (⋂₀ aa) :=
begin
  intros h_cl_fin_int aa,
  apply finset.cons_induction_on aa,
    -- case a = ∅
    intros,
    simp,
    exact h_cl_fin_int.left,

    -- inductive step
    intros b aa h_b_not_mem_aa ih h,
    simp,
    apply h_cl_fin_int.right,
      apply h b,
      simp,

      apply ih,
      intros,
      apply h,
      simp,
      apply or.inr,
      assumption,
end

-- misc

def relation (α : Type) : Type := α -> α -> Prop

-- double negation elimintation (copied from "Theorem Proving in Lean", p32)
theorem dne {p : Prop} (h : ¬¬p) : p :=
  or.elim (em p)
  (assume hp : p, hp)
  (assume hnp : ¬p, absurd hnp h)

