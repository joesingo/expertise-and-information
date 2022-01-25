import data.set.countable

import basic

-- provide functions to convert a formula to a list of ℕ and vice versa. the
-- fact that the conversion is successful (i.e. parsing and deparsing φ gives
-- back φ) is used to show that there are countably many formulas
namespace parser

@[simp] def parse_aux : list ℕ -> list Formula -> Formula
| []       [φ]           := φ
| (1 :: l) (ψ :: φ :: t) := parse_aux l ((φ & ψ) :: t)
| (2 :: l) (φ :: t)      := parse_aux l ((#φ) :: t)
| (3 :: l) (ψ :: φ :: t) := parse_aux l ((φ ⇒ ψ) :: t)
| (4 :: l) (ψ :: φ :: t) := parse_aux l ((φ ⇔ ψ) :: t)
| (5 :: l) (φ :: t)      := parse_aux l ((E φ) :: t)
| (6 :: l) (φ :: t)      := parse_aux l ((S φ) :: t)
| (7 :: l) (φ :: t)      := parse_aux l ((A φ) :: t)
| (8 :: l) t             := parse_aux l (⊥ :: t)
| (n :: l) t             := parse_aux l ((P (n - 9)) :: t)
| _        _             := ⊥

@[simp] def parse (input : list ℕ) : Formula := parse_aux input []

@[simp] def deparse : Formula -> list ℕ
| ⊥       := [8]
| (P n)   := [n + 9]
| (φ & ψ) := deparse φ ++ deparse ψ ++ [1]
| (#φ)    := deparse φ ++ [2]
| (φ ⇒ ψ) := deparse φ ++ deparse ψ ++ [3]
| (φ ⇔ ψ) := deparse φ ++ deparse ψ ++ [4]
| (E φ)   := deparse φ ++ [5]
| (S φ)   := deparse φ ++ [6]
| (A φ)   := deparse φ ++ [7]

lemma parse_aux_lemma (φ : Formula) :
  ∀ l : list ℕ, ∀ t : list Formula,
    parse_aux (deparse φ ++ l) t = parse_aux l (φ :: t) :=
begin
  induction φ,
  case falsum { intros l t, simp, },
  case atom { intros l t, simp },
  case and : φ ψ ih1 ih2
  {
    intros l t, simp,
    rw ih1 (deparse ψ ++ 1 :: l) t, rw ih2 (1 :: l) (φ :: t),
    simp,
  },
  case neg : φ ih
  {
    intros l t, simp,
    rw ih (2 :: l) t,
    simp,
  },
  case implies : φ ψ ih1 ih2
  {
    intros l t, simp,
    rw ih1 (deparse ψ ++ 3 :: l) t, rw ih2 (3 :: l) (φ :: t),
    simp,
  },
  case iff : φ ψ ih1 ih2
  {
    intros l t, simp,
    rw ih1 (deparse ψ ++ 4 :: l) t, rw ih2 (4 :: l) (φ :: t),
    simp,
  },
  case exp : φ ih
  {
    intros l t, simp,
    rw ih (5 :: l) t,
    simp,
  },
  case sound : φ ih
  {
    intros l t, simp,
    rw ih (6 :: l) t,
    simp,
  },
  case univ : φ ih
  {
    intros l t, simp,
    rw ih (7 :: l) t,
    simp,
  },
end

lemma parse_correct : ∀ φ, parse (deparse φ) = φ :=
begin
  intro φ,
  simp,
  have h, from parse_aux_lemma φ [] [],
  repeat { simp at h },
  exact h
end

lemma countably_many_formulas : set.countable (set.univ : set Formula) :=
begin
  suffices : set.range parse = set.univ,
    { rw <-this, exact set.countable_range parse, },
  apply set.eq_univ_iff_forall.mpr,
  intros φ,
  exact ⟨deparse φ, parse_correct φ⟩,
end

end parser
