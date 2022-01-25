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
--% latex label: def_expertise_model
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

-- misc

def relation (α : Type) : Type := α -> α -> Prop

-- double negation elimintation (copied from "Theorem Proving in Lean", p32)
theorem dne {p : Prop} (h : ¬¬p) : p :=
  or.elim (em p)
  (assume hp : p, hp)
  (assume hnp : ¬p, absurd hnp h)

