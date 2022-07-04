import basic
import epistemic_logic

-- multi-source language
inductive MSFormula (J : Type) : Type
  -- propositional part and univ is the same as Formula
  | falsum : MSFormula
  | atom : ℕ -> MSFormula
  | and : MSFormula -> MSFormula -> MSFormula
  | neg : MSFormula -> MSFormula
  | implies : MSFormula -> MSFormula -> MSFormula
  | iff : MSFormula -> MSFormula -> MSFormula
  | univ : MSFormula -> MSFormula
  -- expertise and soundness formulas: individual, distributed and common
  | exp_indiv : J -> MSFormula -> MSFormula
  | sound_indiv : J -> MSFormula -> MSFormula
  | exp_dist : set J -> MSFormula -> MSFormula
  | sound_dist : set J -> MSFormula -> MSFormula
  | exp_com : set J -> MSFormula -> MSFormula
  | sound_com : set J -> MSFormula -> MSFormula

-- infix notation
notation `⊥` := MSFormula.falsum
notation `P` n := MSFormula.atom n
notation φ `&` ψ := MSFormula.and φ ψ
notation `#` φ := MSFormula.neg φ
notation φ `⇒` ψ := MSFormula.implies φ ψ
notation φ `⇔` ψ := MSFormula.iff φ ψ
notation `A` φ := MSFormula.univ φ
notation `E_indiv` j `;` φ := MSFormula.exp_indiv j φ
notation `S_indiv` j `;` φ := MSFormula.sound_indiv j φ
notation `E_dist` js `;` φ := MSFormula.exp_dist js φ
notation `S_dist` js `;` φ := MSFormula.sound_dist js φ
notation `E_com` js `;` φ := MSFormula.exp_com js φ
notation `S_com` js `;` φ := MSFormula.sound_com js φ

-- semantics

structure MSModel (α : Type) (J : Type) :=
  (has_expertise : J -> set α -> Prop)
  (val : ℕ -> α -> Prop)

-- distributed and common expertise predicates

-- first, define what it means for an expertise predicate to extend each
-- individual's expertise
def extends_indiv {α J : Type} (m : MSModel α J) (js : set J)
  (exp : set α -> Prop) :=
  ∀ j ∈ js, ∀ a : set α, m.has_expertise j a -> exp a

-- distributed expertise: close the union of individual expertise collections
-- under intersections and unions
def dist_expertise {α J : Type} (m : MSModel α J) (js : set J) : set α -> Prop :=
  let exps : set (set (set α)) :=
    {exp | extends_indiv m js exp ∧ closed_under_intersections exp ∧
           closed_under_unions exp}
  in ⋂₀exps

-- common expertise: intersection of the individual expertise collections
def com_expertise {α J : Type} (m : MSModel α J) (js : set J) : set α -> Prop :=
  λa, ∀ j ∈ js, m.has_expertise j a

-- state the semantic clause for soundness for an general expertise
-- predicate, to avoid repetition for each type of collective soundness
@[simp] def gen_soundness {α : Type} (exp : set α -> Prop) (b : set α)
  (x : α) := ∀ a : set α, exp a -> b ⊆ a -> x ∈ a

-- satisfaction relation
@[simp] def ms_sat {α : Type} {J : Type} (m : MSModel α J) :
  α -> MSFormula J -> Prop
  | x ⊥  := false
  | x (P n)   := m.val n x
  | x (φ & ψ) := (ms_sat x φ) ∧ (ms_sat x ψ)
  | x (# φ)   := ¬(ms_sat x φ)
  | x (φ ⇒ ψ) := (ms_sat x φ) -> (ms_sat x ψ)
  | x (φ ⇔ ψ) := (ms_sat x φ) <-> (ms_sat x ψ)
  | x (A φ)   := ∀ y : α, ms_sat y φ
  | x (E_indiv j ; φ) := m.has_expertise j {y | ms_sat y φ}
  | x (E_dist js ; φ) := dist_expertise m js {y | ms_sat y φ}
  | x (E_com js ; φ)  := com_expertise m js {y | ms_sat y φ}
  | x (S_indiv j ; φ) := gen_soundness (m.has_expertise j) {y | ms_sat y φ} x
  | x (S_dist js ; φ) := gen_soundness (dist_expertise m js) {y | ms_sat y φ} x
  | x (S_com js ; φ) := gen_soundness (com_expertise m js) {y | ms_sat y φ} x

-- closure properties for multi-source models
def ms_closed_under_unions {α J : Type} (m : MSModel α J) :=
  ∀ j : J, closed_under_unions (m.has_expertise j)
def ms_closed_under_intersections {α J : Type} (m : MSModel α J) :=
  ∀ j : J, closed_under_intersections (m.has_expertise j)

-- introduce multi-source epistemic logic with relational semantics
inductive MSKFormula (J : Type) : Type
  | falsum : MSKFormula
  | atom : ℕ -> MSKFormula
  | and : MSKFormula -> MSKFormula -> MSKFormula
  | neg : MSKFormula -> MSKFormula
  | implies : MSKFormula -> MSKFormula -> MSKFormula
  | iff : MSKFormula -> MSKFormula -> MSKFormula
  | univ : MSKFormula -> MSKFormula
  | know_indiv : J -> MSKFormula -> MSKFormula
  | know_shared : set J -> MSKFormula -> MSKFormula
  | know_dist : set J -> MSKFormula -> MSKFormula
  | know_com : set J -> MSKFormula -> MSKFormula

-- infix notation
notation `⊥` := MSKFormula.falsum
notation `P` n := MSKFormula.atom n
notation φ `&` ψ := MSKFormula.and φ ψ
notation `#` φ := MSKFormula.neg φ
notation φ `⇒` ψ := MSKFormula.implies φ ψ
notation φ `⇔` ψ := MSKFormula.iff φ ψ
notation `A` φ := MSKFormula.univ φ
notation `K_indiv` j `;` φ := MSKFormula.know_indiv j φ
notation `K_shared` js `;` φ := MSKFormula.know_shared js φ
notation `K_dist` js `;` φ := MSKFormula.know_dist js φ
notation `K_com` js `;` φ := MSKFormula.know_com js φ

-- relational model over α
structure MSRModel (α J : Type) :=
  (accessible : J -> relation α)
  (val : ℕ → α → Prop)

-- transitive closure of a relation. we use the definition xR+y iff ∃n, xR^ny
@[simp] def relation_product {α : Type} (r : relation α) : ℕ -> relation α
  | 0 := λx y, x = y
  | (n + 1) := λx y, ∃z, relation_product n x z ∧ r z y

def transitive_closure {α : Type} (r : relation α) : relation α :=
  λx y, ∃n, 0 < n ∧ relation_product r n x y

@[simp] def union_of_relations {α β : Type} (r : β -> relation α) : relation α :=
  λx y, ∃ b : β, r b x y

-- satisfaction relation. for simplicity we define common knowledge via the
-- transitive closure of the union of individual accessibility relations, and
-- show below that this is equivalent to the usual definition
@[simp] def ms_ksat {α J : Type} (m : MSRModel α J) : α -> MSKFormula J -> Prop
  | x ⊥       := false
  | x (P n)   := m.val n x
  | x (φ & ψ) := (ms_ksat x φ) ∧ (ms_ksat x ψ)
  | x (# φ)   := ¬(ms_ksat x φ)
  | x (φ ⇒ ψ) := (ms_ksat x φ) -> (ms_ksat x ψ)
  | x (φ ⇔ ψ) := (ms_ksat x φ) <-> (ms_ksat x ψ)
  | x (A φ)   := ∀ y : α, ms_ksat y φ
  | x (K_indiv j ; φ) := ∀ y : α, m.accessible j x y -> ms_ksat y φ
  | x (K_shared js ; φ) := ∀ j ∈ js, ∀ y : α, m.accessible j x y -> ms_ksat y φ
  | x (K_dist js ; φ) := ∀ y : α, (∀ j ∈ js, m.accessible j x y) -> ms_ksat y φ
  | x (K_com js ; φ)  := ∀ y : α,
    (transitive_closure (union_of_relations (λj : js, m.accessible j))) x y ->
      ms_ksat y φ

-- mapping from multi-source expertise to multi-source relational models
def ms_expmodel_to_rmodel {α J : Type} (m : MSModel α J) : MSRModel α J:=
  MSRModel.mk (λj, ep_relation (m.has_expertise j)) m.val

-- translation between languages
@[simp] def translation {J : Type} : MSFormula J -> MSKFormula J
  | ⊥       := ⊥
  | (P n)   := P n
  | (φ & ψ) := translation φ & translation ψ
  | (# φ)   := #(translation φ)
  | (φ ⇒ ψ) := translation φ ⇒ translation ψ
  | (φ ⇔ ψ) := translation φ ⇔ translation ψ
  | (A φ)   := A (translation φ)
  | (E_indiv j ; φ) := A ((# (translation φ)) ⇒ (K_indiv j ; (# (translation φ))))
  | (S_indiv j ; φ) := # (K_indiv j ; (# (translation φ)))
  | (E_dist js ; φ) := A ((# (translation φ)) ⇒ (K_dist js ; (# (translation φ))))
  | (S_dist js ; φ) := # (K_dist js ; (# (translation φ)))
  | (E_com js ; φ)  := A ((# (translation φ)) ⇒ (K_com js ; (# (translation φ))))
  | (S_com js ; φ)  := # (K_com js ; (# (translation φ)))

namespace multi_source

variables {α J : Type}

--% latex_label: lemma_common_knowledge_transitive_closure
--
-- we show that the definition of common knowledge above (i.e. usual relational
-- semantics corresponding to the transitive closure of the union of relations)
-- coincides with the usual one in terms of iterated shared knowledge

@[simp] def iterated_shared (js : set J) : MSKFormula J -> ℕ -> MSKFormula J
  | φ 0       := φ
  | φ (n + 1) := K_shared js ; (iterated_shared φ n)

lemma relation_product_property {r : relation α} {x y z : α} {n m : ℕ} :
  relation_product r n x y -> relation_product r m y z ->
  relation_product r (n + m) x z :=
begin
  revert n x y z,
  induction m,
    case zero
    {
      intros n x y z hr_xy heq,
      simp at *,
      rw <-heq,
      exact hr_xy
    },
    case succ : l ih
    {
      intros n x y z hr_xy hr_yz,
      apply exists.elim hr_yz,
      intros w h,
      show relation_product r ((n + l) + 1) x z, from
        ⟨w, ih hr_xy h.left, h.right⟩
    }
end

-- helper lemma to unwrap iterated shared knowledge of order k + 1
lemma iterated_shared_helper {m : MSRModel α J} {js : set J} {φ : MSKFormula J} (n : ℕ) :
  ∀ x : α, ms_ksat m x (iterated_shared js φ (n + 1)) ->
    ms_ksat m x (iterated_shared js (iterated_shared js φ 1) n) :=
begin
  induction n,
  case zero { intro x, simp },
  case succ : k ih
  {
    intros x h,
    simp,
    intros j1 hmem1 y hr,
    simp at h,
    apply ih,
    simp,
    intros j2 hmem2 z hrz,
    exact h j1 hmem1 y hr j2 hmem2 z hrz,
  }
end

lemma common_knowledge_def :
  ∀ m : MSRModel α J, ∀ js : set J, ∀ φ : MSKFormula J, ∀ x : α,
    ms_ksat m x (K_com js ; φ) <->
      ∀ n : ℕ, n > 0 -> ms_ksat m x (iterated_shared js φ n) :=
begin
  intros m js,
  let r := union_of_relations (λ j : js, m.accessible j),
  suffices : ∀ n : ℕ, ∀ x : α, ∀ φ : MSKFormula J,
    (∀y, relation_product r n x y -> ms_ksat m y φ) <->
      ms_ksat m x (iterated_shared js φ n),
  {
    intros φ x,
    apply iff.intro,
      intros hsat n hnpos,
      apply (this n x φ).mp,
      intros y hr,
      have hr_tr : transitive_closure r x y, from ⟨n, ⟨hnpos, hr⟩⟩,
      exact hsat y hr_tr,

      intros h_all_n y hr_tr,
      apply exists.elim hr_tr,
      intros n hprop,
      exact (this n x φ).mpr (h_all_n n hprop.left) y hprop.right,
  },
  intro n,
  induction n,
  case zero { intros x φ, simp, },
  case succ : k ih
  {
    intros x φ,
    apply iff.intro,
      intro h,
      simp,
      intros j hmem y hr,
      apply (ih y φ).mp,
      intros z hrz,
      apply h z,
      rw nat.succ_eq_one_add,
      refine relation_product_property _ hrz,
      simp,
      exact ⟨⟨j, hmem⟩, hr⟩,

      intros h y hr,
      let ψ := iterated_shared js φ 1,
      have h' : ms_ksat m x (iterated_shared js ψ k), from
        iterated_shared_helper k x h,
      apply exists.elim hr,
      intros z hprop,
      have hk := (ih x (iterated_shared js φ 1)).mpr h',
      have hzsat := hk z hprop.left,
      apply exists.elim hprop.right,
      intros j hrj,
      exact hzsat j (subtype.mem j) y hrj,
  }
end

-- distributed expertise is closed under intersections and unions
lemma dist_closed_intersections {m : MSModel α J} {js : set J} :
  closed_under_intersections (dist_expertise m js) :=
begin
  intros aa h_all_dexp,
  apply set.mem_sInter.mpr,
  intros exp h,
  have h_all_exp : ∀ a ∈ aa, exp a,
  {
    intros a ha_in_aa,
    have hdexp : dist_expertise m js a, from h_all_dexp a ha_in_aa,
    exact (set.mem_sInter.mp) hdexp exp h,
  },
  exact h.right.left aa h_all_exp
end

lemma dist_closed_unions {m : MSModel α J} {js : set J} :
  closed_under_unions (dist_expertise m js) :=
begin
  -- TODO: avoid duplication from above...
  intros aa h_all_dexp,
  apply set.mem_sInter.mpr,
  intros exp h,
  have h_all_exp : ∀ a ∈ aa, exp a,
  {
    intros a ha_in_aa,
    have hdexp : dist_expertise m js a, from h_all_dexp a ha_in_aa,
    exact (set.mem_sInter.mp) hdexp exp h,
  },
  exact h.right.right aa h_all_exp
end

-- distributed expertise extends individual expertise
lemma dist_extends_indiv {m : MSModel α J} {js : set J} :
  extends_indiv m js (dist_expertise m js) :=
begin
  intros j hmem a hexp,
  apply set.mem_sInter.mpr,
  intros exp' hmem',
  exact hmem'.left j hmem a hexp,
end

def finite_int_dist_expertise {α J : Type} (m : MSModel α J) (js : set J) : set α -> Prop :=
  let exps : set (set (set α)) :=
    {exp | extends_indiv m js exp ∧ closed_under_finite_intersections exp ∧
           closed_under_unions exp}
  in ⋂₀exps

lemma dist_equiv_finite_unions {α J : Type} [decidable_eq (set α)] (m : MSModel α J) (js : finset J) :
  ms_closed_under_intersections m -> ms_closed_under_unions m ->
    ∀ a : set α, dist_expertise m js a <-> finite_int_dist_expertise m js a :=
begin
  intros hmint hmunions a,
  let fexp := finite_int_dist_expertise m js,
  apply iff.intro,
    -- TODO: more duplication from above...
    have h_cl_unions : closed_under_unions fexp,
    {
      intros aa h_all_fexp,
      apply set.mem_sInter.mpr,
      intros exp h,
      have h_all_exp : ∀ a ∈ aa, exp a,
      {
        intros a ha_in_aa,
        exact (set.mem_sInter.mp) (h_all_fexp a ha_in_aa) exp h,
      },
      exact h.right.right aa h_all_exp
    },
    have h_extends_indiv : extends_indiv m js fexp,
    {
      intros j hmem a hexp,
      apply set.mem_sInter.mpr,
      intros exp' hmem',
      exact hmem'.left j hmem a hexp
    },
    suffices h_cl_int : closed_under_intersections fexp,
    {
      intros h_dist_exp,
      exact set.mem_sInter.mp h_dist_exp fexp
        ⟨h_extends_indiv, h_cl_int, h_cl_unions⟩,
    },
    suffices h_min_neighbourhoods :
      ∃ f : α -> set α, ∀ x, x ∈ f x ∧ fexp (f x)
        ∧ ∀ V : set α, x ∈ V -> fexp V -> f x ⊆ V,
    {
      intros aa h_all_fexp,
      apply exists.elim h_min_neighbourhoods,
      intros f hfprop,
      let b := ⋂₀ aa,
      have h : b = ⋃₀ λU, ∃ x, x ∈ b ∧ U = f x,
      {
        apply set.ext,
        intro x,
        apply iff.intro,
          intro h_x_mem_b,
          refine ⟨f x, _, (hfprop x).left⟩,
          refine ⟨x, h_x_mem_b, by refl⟩,

          intro h_x_mem_union,
          apply exists.elim h_x_mem_union,
          intros fy H,
          apply exists.elim H,
          intros H' h_x_mem_fy,
          apply exists.elim H',
          intros y h,
          suffices h_ss : fy ⊆ b, from
              set.mem_of_mem_of_subset h_x_mem_fy h_ss,
          apply set.subset_sInter,
          intros a h_a_mem_aa,
          have h_y_a : y ∈ a, from set.mem_sInter.mp h.left a h_a_mem_aa,
          rw h.right,
          exact (hfprop y).right.right a h_y_a (h_all_fexp a h_a_mem_aa),
      },
      have heq : ⋂₀ aa = b, by simp,
      rw [heq, h],
      apply h_cl_unions,
      intros a h_ex_x,
      apply exists.elim h_ex_x,
      intros x H,
      rw H.right,
      exact (hfprop x).right.left
    },
    let g : α -> J -> set α := λx, λj, ⋂₀ {a | m.has_expertise j a ∧ x ∈ a},
    let F : α -> finset (set α) := λx, finset.image (g x) js,
    let f : α -> set α := λx, ⋂₀ F x,
    apply exists.intro f,
    -- now need to prove the minimal property for f
    intro x,
    apply and.intro,
      -- x ∈ f x
      simp,

      apply and.intro,
      -- fexp (f x)
      have h_cl_finite_int : closed_under_finite_intersections fexp, from sorry,
      suffices h_exp_each_j : ∀ j, m.has_expertise j (g x j),
      {
        apply finset_intersections fexp h_cl_finite_int,
        intros a h_a_mem_F_x,
        apply exists.elim (finset.mem_image.mp h_a_mem_F_x),
        intros j H,
        apply exists.elim H,
        intros h_j_mem_js h_g_x_j_eq_a,
        rw <-h_g_x_j_eq_a,
        apply h_extends_indiv j h_j_mem_js,
        exact h_exp_each_j j,
      },
      intros j,
      apply hmint j,
      intros a h,
      exact h.left,

      -- minimality property
      intros v h_x_mem_v h_fexp_v,
      sorry,

    -- have fexp a, exp' extends individual and is closed under unions and
    -- arbitrary intersections. since exp' is closed under finite intersections
    -- too, we get exp' a
    intros h_fexp_a exp' h_extends,
    apply set.mem_sInter.mp h_fexp_a exp',
    refine ⟨h_extends.left, _, h_extends.right.right⟩,
    apply int_implies_finite_int,
    exact h_extends.right.left
end

@[simp] def unions_of_finite_int_of_extend {α J : Type} (m : MSModel α J) (js : set J)
 : set α -> Prop := λa, ∃ aa, a = ⋃₀ aa ∧ ∀ a' ∈ aa, ∃ bb : finset (set α),
            a' = ⋂₀ bb ∧ ∀ b ∈ bb, ∃ j ∈ js, m.has_expertise j b

lemma blah {α J : Type}  (m : MSModel α J) (js : finset J) :
  ms_closed_under_unions m -> ms_closed_under_intersections m ->
    dist_expertise m js = unions_of_finite_int_of_extend m js :=
begin
  intros hmunions hmint,
  apply set.ext,
  intro a,
  apply iff.intro,

    -- show that any set with dist expertise must be a union of finite
    -- intersections from the extension of the individual expertise prediactes
    let exp := unions_of_finite_int_of_extend m js,
    have h_extend : extends_indiv m js exp,
    {
      intros j h_j_mem_js a h_j_exp_a,
      let bb : finset (set α) := {a},
      let aa : set (set α) := {⋂₀ bb},
      apply exists.intro aa,
      apply and.intro,
        simp,

        intros a' h,
        apply exists.intro bb,
        simp,
        apply and.intro,
          rw set.eq_of_mem_singleton h,
          simp,
          apply exists.intro j,
          apply and.intro,
            assumption,
            assumption,
    },
    -- it suffices to show exp is closed under intersections and unions
    suffices h_closure : closed_under_intersections exp ∧ closed_under_unions exp,
    {
      intro h_dist_exp_a,
      apply set.mem_sInter.mp h_dist_exp_a exp,
      exact ⟨h_extend, h_closure⟩
    },
    apply and.intro,
      -- intersections
      sorry,

      -- unions
      intros aa h_all_exp,
      let aa' := ⋃ (H : a ∈ aa), set.univ,
      apply exists.intro aa',
        sorry,

    -- show that if a is a union of finite intersections from the union of the
    -- expertise predicates, then it belongs in dist_expertise
    intros h,
    apply exists.elim h,
    intros aa h',
    rw h'.left,
    apply dist_closed_unions,
    intros a h_a_mem_aa,
    apply exists.elim (h'.right a h_a_mem_aa),
    intros bb h'',
    rw h''.left,
    apply dist_closed_intersections,
    intros a' h_a'_mem_bb,
    apply exists.elim (h''.right a' h_a'_mem_bb),
    intros j H,
    apply exists.elim H,
    intros h_j_mem_js,
    apply dist_extends_indiv j h_j_mem_js
end

inductive joe_closure (p : set (set α)) : set α -> Prop
  | basic : ∀ a ∈ p, joe_closure a
  | fint  : ∀ a b, joe_closure a -> joe_closure b -> joe_closure (a ∩ b)
  | union : ∀ aa, (∀ a ∈ aa, joe_closure a) -> joe_closure (⋃₀ aa)

def union_exp {α J : Type} (m : MSModel α J) (js : set J) : set α -> Prop :=
  {a | ∃ j ∈ js, m.has_expertise j a}

structure min_neighbourhood {α : Type} (p : set α -> Prop) (x : α) : Type :=
  (neigh : set α)
  (mem : x ∈ neigh)
  (contained : p neigh)
  (min : ∀ U, x ∈ U -> p U -> neigh ⊆ U)

lemma closed_under_int_and_union_min_neigh {α : Type} (p : set α -> Prop) :
  closed_under_unions p ->
    ((closed_under_intersections p)
      <-> (∀ x, ∃ U, x ∈ U ∧ p U ∧ ∀ V, x ∈ V -> p V -> U ⊆ V)) :=
begin
  intros h_unions,
  apply iff.intro,
    intros h_int x,
    let U := ⋂₀ {V | x ∈ V ∧ p V},
    apply exists.intro U,
    refine ⟨_, _, _⟩,
      apply set.mem_sInter.mpr,
      intros V h,
      exact h.left,

      apply h_int,
      intros V h,
      exact h.right,

      intros V h_x_mem_v h_p_v,
      apply set.sInter_subset_of_mem,
      exact ⟨h_x_mem_v, h_p_v⟩,

    intros h aa h_all_p,
    sorry,
end

lemma bbb {α J : Type} (m : MSModel α J) (js : finset J) :
  ms_closed_under_intersections m -> ms_closed_under_unions m ->
    dist_expertise m js = joe_closure (union_exp m js) :=
begin
  intros hmint hmunions,
  apply set.ext,
  intros a0,
  apply iff.intro,
    let exp := joe_closure (union_exp m js),
    intro h,
    have h_unions : closed_under_unions exp, by
    {
        intros aa h_all_exp,
        apply joe_closure.union,
        exact h_all_exp
    },
    suffices h_int : closed_under_intersections exp,
    {
      apply set.mem_sInter.mpr h,
      apply and.intro,
        intros j hmem a hexp,
        exact joe_closure.basic a ⟨j, hmem, hexp⟩,
        exact ⟨h_int, h_unions⟩
      },
    sorry,

    intro h,
    induction h,
      case basic : a h
      {
        apply set.mem_sInter.mpr,
        intros exp' h',
        apply exists.elim h,
        intros j H,
        apply exists.elim H,
        intros,
        apply h'.left,
        repeat { assumption },
      },
      case fint : a b h_mem_a h_mem_b iha ihb
      {
        suffices hcl : closed_under_finite_intersections (dist_expertise m js),
          from hcl.right a b iha ihb,
        apply int_implies_finite_int,
        exact dist_closed_intersections,
      },
      case union : aa h_all_exp ih
      {
        apply dist_closed_unions,
        apply ih
      }
end

-- distributed expertise can equivalently be define by only closing under
-- *finite* unions, if each individual expertise predicate is closed under
-- unions and intersections. this corresponds to the join in the lattice of
-- topologies
/-\ def finite_union_dist_expertise {α J : Type} (m : MSModel α J) (js : set J) : set α -> Prop := \ -/
/-\   let exps : set (set (set α)) := \ -/
/-\     {exp | extends_indiv m js exp ∧ closed_under_intersections exp ∧ \ -/
/-\            closed_under_finite_unions exp} \ -/
/-\   in ⋂₀exps \ -/

/-\ lemma dist_equiv_finite_unions {α J : Type} (m : MSModel α J) (js : set J) : \ -/
/-\   ∀ a : set α, dist_expertise m js a <-> finite_union_dist_expertise m js a := \ -/
/-\ begin \ -/
/-\   intro a, \ -/
/-\   apply iff.intro, \ -/
/-\     let fexp := finite_union_dist_expertise m js, \ -/
/-\     have h_cl_inter : closed_under_intersections fexp, \ -/
/-\     { \ -/
/-\       intros aa h_all, \ -/
/-\       apply set.mem_sInter.mpr, \ -/
/-\       intros exp h, \ -/
/-\       have h_all_exp : ∀ a ∈ aa, exp a, \ -/
/-\       { \ -/
/-\         intros a ha_in_aa, \ -/
/-\         have hfexp : fexp a, from h_all a ha_in_aa, \ -/
/-\         exact (set.mem_sInter.mp) hfexp exp h, \ -/
/-\       }, \ -/
/-\       exact h.right.left aa h_all_exp \ -/
/-\     }, \ -/
/-\     -- sufficient to show that the closure under finite unions and \ -/
/-\     -- intersections is actually closed under arbitrary unions \ -/
/-\     suffices h : closed_under_unions fexp, \ -/
/-\     { \ -/
/-\       intros h_dist_exp, \ -/
/-\       -- TODO: more duplication from above... \ -/
/-\       have h1 : extends_indiv m js fexp, \ -/
/-\       { \ -/
/-\         intros j hmem a hexp, \ -/
/-\         apply set.mem_sInter.mpr, \ -/
/-\         intros exp' hmem', \ -/
/-\         exact hmem'.left j hmem a hexp \ -/
/-\       }, \ -/
/-\       exact set.mem_sInter.mp h_dist_exp fexp ⟨h1, h_cl_inter, h⟩ \ -/
/-\     }, \ -/
    /-\ suffices hmin_neigh : \ -/
    /-\   ∃ f : α -> set α, ∀ x : α, x ∈ f x ∧ fexp (f x)ᶜ \ -/
    /-\     ∧ ∀ V : set α, x ∈ V -> fexp Vᶜ -> f x ⊆ V, \ -/
    /-\ { \ -/
    /-\   apply exists.elim hmin_neigh, \ -/
    /-\   intros f hfprop aa h_all_exp, \ -/
    /-\   let b := ⋃₀aa, \ -/
    /-\   let c := bᶜ, \ -/
    /-\   have h1 : c = ⋃ x : c, f x, \ -/
    /-\   { \ -/
    /-\     apply set.ext, \ -/
    /-\     intros x, \ -/
    /-\     apply iff.intro, \ -/
    /-\       intro hmem, \ -/
    /-\       apply set.mem_Union.mpr, \ -/
    /-\       exact ⟨⟨x, hmem⟩, (hfprop x).left⟩, \ -/

    /-\       suffices h_ss_compl : ∀ y ∈ c, ∀ a ∈ aa, f y ⊆ aᶜ, \ -/
    /-\       { \ -/
    /-\         intros h_x_mem_union, \ -/
    /-\         apply exists.elim (set.mem_Union.mp h_x_mem_union), \ -/
    /-\         intros y h_x_mem_fy, \ -/
    /-\         simp, \ -/
    /-\         intros a h_a_mem_aa, \ -/
    /-\         apply (set.mem_compl_iff a x).mp, \ -/
    /-\         apply set.mem_of_mem_of_subset h_x_mem_fy, \ -/
    /-\         exact h_ss_compl y (subtype.mem y) a h_a_mem_aa \ -/
    /-\       }, \ -/
    /-\       intros y h_y_mem_c a h_a_mem_aa, \ -/
    /-\       simp at h_y_mem_c, \ -/
    /-\       apply (hfprop y).right.right aᶜ, \ -/
    /-\         apply (set.mem_compl_iff a y).mpr, \ -/
    /-\         exact h_y_mem_c a h_a_mem_aa, \ -/

    /-\         simp, \ -/
    /-\         exact h_all_exp a h_a_mem_aa, \ -/
    /-\   }, \ -/
    /-\   have h2 : ⋃₀aa = ⋂₀ (set.image (λx, (f x)ᶜ) c), \ -/
    /-\   { \ -/
    /-\     have heq : ⋃₀aa = cᶜ, by simp, \ -/
    /-\     rw [heq, h1], \ -/
    /-\     rw set.compl_Union, \ -/
    /-\     rw <-h1, \ -/
    /-\     simp at *, \ -/
    /-\     apply set.ext, \ -/
    /-\     intro x, \ -/
    /-\     simp at *, \ -/
    /-\   }, \ -/
    /-\   rw h2, \ -/
    /-\   apply h_cl_inter, \ -/
    /-\   intros a h_mem_image, \ -/
    /-\   apply exists.elim (set.mem_image_iff_bex.mp h_mem_image), \ -/
    /-\   intros x hxprop, \ -/
    /-\   apply exists.elim hxprop, \ -/
    /-\   intros hmem h_eq_fx_c, \ -/
    /-\   rw <-h_eq_fx_c, \ -/
    /-\   exact (hfprop x).right.left \ -/
    /-\ }, \ -/
    /-\ -- by choice, we just need to find a minimal neighbourhood \ -/
    /-\ suffices h_exists_min : \ -/
    /-\   ∀ x : α, ∃ U : set α, x ∈ U ∧ fexp Uᶜ \ -/
    /-\     ∧ ∀ V : set α, x ∈ V -> fexp Vᶜ -> U ⊆ V, \ -/
    /-\ { \ -/
    /-\   sorry \ -/
    /-\ }, \ -/
    /-\ sorry, \ -/

    /-\ intros h_fin_dist aa h, \ -/
    /-\ apply h_fin_dist aa, \ -/
    /-\ refine ⟨h.left, h.right.left, _⟩, \ -/
    /-\ apply unions_implies_funions, \ -/
    /-\ exact h.right.right \ -/
/-\ end \ -/

/-\ -- common expertise is closed under intersections and unions if the individual \ -/
/-\ -- expertise predicates are \ -/
/-\ -- NOTE: can weaken hypothesis to just j ∈ js... \ -/
/-\ lemma com_closed_intersections {m : MSModel α J} {js : set J} : \ -/
/-\   ms_closed_under_intersections m -> \ -/
/-\     closed_under_intersections (com_expertise m js) := \ -/
/-\ begin \ -/
/-\   intros h aa h_all_exp j hmem, \ -/
/-\   have h_all_jexp : ∀ a ∈ aa, m.has_expertise j a, \ -/
/-\   { \ -/
/-\     intros a ha_in_aa; \ -/
/-\     exact h_all_exp a ha_in_aa j hmem \ -/
/-\   }, \ -/
/-\   exact h j aa h_all_jexp \ -/
/-\ end \ -/

/-\ lemma com_closed_unions {m : MSModel α J} {js : set J} : \ -/
/-\   ms_closed_under_unions m -> \ -/
/-\     closed_under_unions (com_expertise m js) := \ -/
/-\ begin \ -/
/-\   intros h aa h_all_exp j hmem, \ -/
/-\   have h_all_jexp : ∀ a ∈ aa, m.has_expertise j a, \ -/
/-\   { \ -/
/-\     intros a ha_in_aa; \ -/
/-\     exact h_all_exp a ha_in_aa j hmem \ -/
/-\   }, \ -/
/-\   exact h j aa h_all_jexp \ -/
/-\ end \ -/

/-\ -- shortcuts for epistemic accessibility relations for individual and \ -/
/-\ -- collective expertise \ -/
/-\ @[simp] def indiv_ep_relation (m : MSModel α J) (j : J) : relation α := \ -/
/-\   ep_relation (m.has_expertise j) \ -/

/-\ @[simp] def dist_ep_relation (m : MSModel α J) (js : set J) : relation α := \ -/
/-\   ep_relation (dist_expertise m js) \ -/

/-\ @[simp] def com_ep_relation (m : MSModel α J) (js : set J) : relation α := \ -/
/-\   ep_relation (com_expertise m js) \ -/

/-\ @[simp] def union_ep_relation (m : MSModel α J) (js : set J) : relation α := \ -/
/-\   union_of_relations (λj : js, indiv_ep_relation m j) \ -/

/-\ -- epistemic accessibility relation corresponding to distributed expertise is \ -/
/-\ -- the intersection of the individual relations \ -/
/-\ --% latex_label: prop_rpdist \ -/
/-\ lemma dist_ep_relation_intersection : \ -/
/-\   ∀ m : MSModel α J, ∀ js : set J, ∀ x y : α, \ -/
/-\     (dist_ep_relation m js) x y <-> ∀ j ∈ js, (indiv_ep_relation m j) x y := \ -/
/-\ begin \ -/
/-\   intros m js x y, \ -/
/-\   apply iff.intro, \ -/
/-\     intros hdist_xy j hmem, \ -/
/-\     simp, \ -/
/-\     intros a hexp hya, \ -/
/-\     have h : dist_expertise m js a, from dist_extends_indiv j hmem a hexp, \ -/
/-\     exact hdist_xy a h hya, \ -/

/-\     intros h, \ -/
/-\     let exp : set α -> Prop := λa, dist_expertise m js a ∧ (y ∈ a -> x ∈ a), \ -/
/-\     suffices : extends_indiv m js exp ∧ closed_under_intersections exp ∧ closed_under_unions exp, \ -/
/-\     { \ -/
/-\       simp, \ -/
/-\       intros a hdexp hya, \ -/
/-\       have hexp := set.mem_sInter.mp hdexp exp this, \ -/
/-\       exact hexp.right hya \ -/
/-\     }, \ -/
/-\     apply and.intro, \ -/
/-\       -- show exp extends individual expertise \ -/
/-\       intros j hmem a hexp, \ -/
/-\       exact ⟨dist_extends_indiv j hmem a hexp, h j hmem a hexp⟩, \ -/
/-\       apply and.intro, \ -/
/-\       -- show exp closed under intersections \ -/
/-\       intros aa h_all_exp, \ -/
/-\       have h_all_distexp : ∀ a ∈ aa, dist_expertise m js a, by \ -/
/-\         intros a ha_in_aa; exact (h_all_exp a ha_in_aa).left, \ -/
/-\       apply and.intro, \ -/
/-\         -- show intersection is in dist_expertise \ -/
/-\         exact dist_closed_intersections aa h_all_distexp, \ -/
/-\         -- show y in intersection implies x is also \ -/
/-\         intro hy_int, \ -/
/-\         apply set.mem_sInter.mpr, \ -/
/-\         intros a ha_in_aa, \ -/
/-\         have hy_a : y ∈ a, from set.mem_sInter.mp hy_int a ha_in_aa, \ -/
/-\         exact (h_all_exp a ha_in_aa).right hy_a, \ -/

/-\       -- similarly, show exp closed under unions \ -/
/-\       intros aa h_all_exp, \ -/
/-\       have h_all_distexp : ∀ a ∈ aa, dist_expertise m js a, by \ -/
/-\         intros a ha_in_aa; exact (h_all_exp a ha_in_aa).left, \ -/
/-\       apply and.intro, \ -/
/-\         exact dist_closed_unions aa h_all_distexp, \ -/
/-\         intro hy_union, \ -/
/-\         apply set.mem_sUnion.mpr, \ -/
/-\         apply exists.elim hy_union, \ -/
/-\         intros a hexists, \ -/
/-\         apply exists.elim hexists, \ -/
/-\         intros ha_in_aa hy_a, \ -/
/-\         have hx_a : x ∈ a, from (h_all_exp a ha_in_aa).right hy_a, \ -/
/-\         exact ⟨a, ha_in_aa, hx_a⟩, \ -/
/-\ end \ -/

/-\ lemma transitive_closure_is_transitive {r : relation α} : \ -/
/-\   is_transitive (transitive_closure r) := \ -/
/-\ begin \ -/
/-\   intros x y z hxy hyz, \ -/
/-\   apply exists.elim hxy, \ -/
/-\   intros n hn_xy, \ -/
/-\   apply exists.elim hyz, \ -/
/-\   intros m hm_yz, \ -/
/-\   refine ⟨n + m, _, relation_product_property hn_xy.right hm_yz.right⟩, \ -/
/-\   apply nat.add_pos_left, \ -/
/-\   exact hn_xy.left \ -/
/-\ end \ -/

/-\ lemma dc_wrt_product {r : relation α} {a : set α} {n : ℕ} : \ -/
/-\   downwards_closed a r -> downwards_closed a (relation_product r n) := \ -/
/-\ begin \ -/
/-\   intro h, \ -/
/-\   induction n, \ -/
/-\     case zero \ -/
/-\     { \ -/
/-\       intros x y hr hya, \ -/
/-\       simp at *, \ -/
/-\       rw hr, \ -/
/-\       exact hya \ -/
/-\     }, \ -/
/-\     case succ : m ih \ -/
/-\     { \ -/
/-\       intros x z hrxz hza, \ -/
/-\       apply exists.elim hrxz, \ -/
/-\       intros y hr, \ -/
/-\       have hya : y ∈ a, from h y z hr.right hza, \ -/
/-\       exact ih x y hr.left hya \ -/
/-\     } \ -/
/-\ end \ -/

/-\ lemma dc_wrt_transitive_closure {r : relation α} {a : set α} : \ -/
/-\   downwards_closed a r <-> downwards_closed a (transitive_closure r) := \ -/
/-\ begin \ -/
/-\   apply iff.intro, \ -/
/-\     intros h x y hrtr hya, \ -/
/-\     apply exists.elim hrtr, \ -/
/-\     intros n hprop, \ -/
/-\     exact dc_wrt_product h x y hprop.right hya, \ -/

/-\     intros h x y hr hya, \ -/
/-\     have hrtr : transitive_closure r x y, \ -/
/-\     { \ -/
/-\       refine ⟨1, _, _⟩, \ -/
/-\         simp, \ -/
/-\         simp, \ -/
/-\         exact hr, \ -/
/-\     }, \ -/
/-\     exact h x y hrtr hya, \ -/
/-\ end \ -/

/-\ -- the relation corresponding to common expertise is the transitive closure of \ -/
/-\ -- the union of the individual relations \ -/
/-\ --% latex_label: prop_rcommon \ -/
/-\ lemma com_ep_relation_union : ∀ m : MSModel α J, ∀ js : set J, js.nonempty -> \ -/
/-\   ms_closed_under_unions m -> ms_closed_under_intersections m -> ∀ x y : α, \ -/
/-\     (com_ep_relation m js) x y <-> (transitive_closure (union_ep_relation m js)) x y := \ -/
/-\ begin \ -/
/-\   intros m js hjs_nonempty hmunions hmint, \ -/

/-\   -- introduce some names for relations and expertise predicates, for brevity \ -/
/-\   let r_com := com_ep_relation m js, \ -/
/-\   let r_union := union_ep_relation m js, \ -/
/-\   let r_tr := transitive_closure r_union, \ -/
/-\   let r_indiv := λj, indiv_ep_relation m j, \ -/
/-\   let exp_com := com_expertise m js, \ -/
/-\   let exp_indiv := λj, m.has_expertise j, \ -/

/-\   -- exp_com is reflexive and transitive \ -/
/-\   have h1 := ep_connection.ref_and_tr exp_com, \ -/

/-\   -- by an earlier result, it is sufficient to show that the two relations are \ -/
/-\   -- reflexive, transitive, and have the same downwards closed sets \ -/
/-\   apply ep_connection.same_dc_implies_equal, \ -/
/-\     exact h1.right, \ -/
/-\     exact h1.left, \ -/
/-\     exact transitive_closure_is_transitive, \ -/
/-\     -- need to use js ≠ ∅ to show the transitive closure of the union is reflexive \ -/
/-\     intro x, \ -/
/-\     refine ⟨1, _⟩, \ -/
/-\     simp, \ -/
/-\     exact ⟨set.nonempty.some hjs_nonempty, set.nonempty.some_mem hjs_nonempty⟩, \ -/
/-\     -- show same dc sets \ -/
/-\     intro a, \ -/
/-\     have hunions : closed_under_unions exp_com, from \ -/
/-\       com_closed_unions (λj, hmunions j), \ -/
/-\     have hint : closed_under_intersections exp_com, from \ -/
/-\       com_closed_intersections (λj, hmint j), \ -/
/-\     -- we have a series of equivalences: \ -/
/-\     calc \ -/
/-\       downwards_closed a r_com \ -/
/-\           <-> exp_com a : \ -/
/-\               iff.symm $ ep_connection.exp_iff_dc exp_com hunions hint a \ -/
/-\       ... <-> ∀ j ∈ js, m.has_expertise j a : by refl \ -/
/-\       ... <-> ∀ j ∈ js, downwards_closed a (r_indiv j) : by \ -/
/-\             { \ -/
/-\               apply forall_congr, \ -/
/-\               intros j, \ -/
/-\               apply imp_congr, \ -/
/-\                 refl, \ -/
/-\                 exact ep_connection.exp_iff_dc (exp_indiv j) (hmunions j) \ -/
/-\                   (hmint j) a \ -/
/-\             } \ -/
/-\       ... <-> downwards_closed a r_union : by \ -/
/-\             { \ -/
/-\               apply iff.intro, \ -/
/-\                 intro h, \ -/
/-\                 simp, \ -/
/-\                 introv hrunion_xy hya, \ -/
/-\                 apply exists.elim hrunion_xy, \ -/
/-\                 intros j hrj_xy, \ -/
/-\                 exact h j (subtype.mem j) x y hrj_xy hya, \ -/

/-\                 simp, \ -/
/-\                 intros h j hmem x y hrj_xy hya, \ -/
/-\                 exact h x y ⟨⟨j, hmem⟩, hrj_xy⟩ hya \ -/
/-\             } \ -/
/-\       ... <-> downwards_closed a r_tr : dc_wrt_transitive_closure \ -/
/-\ end \ -/

/-\ -- define when a multi-source formula does not feature the empty coalition js = ∅ \ -/
/-\ @[simp] def no_empty_coalition : MSFormula J -> Prop \ -/
/-\   | ⊥  := true \ -/
/-\   | (P n)   := true \ -/
/-\   | (φ & ψ) := no_empty_coalition φ ∧ no_empty_coalition ψ \ -/
/-\   | (# φ)   := no_empty_coalition φ \ -/
/-\   | (φ ⇒ ψ) := no_empty_coalition φ ∧ no_empty_coalition ψ \ -/
/-\   | (φ ⇔ ψ) := no_empty_coalition φ ∧ no_empty_coalition ψ \ -/
/-\   | (A φ)   := no_empty_coalition φ \ -/
/-\   | (E_indiv j ; φ) := no_empty_coalition φ \ -/
/-\   | (E_dist js ; φ) := no_empty_coalition φ ∧ js.nonempty \ -/
/-\   | (E_com js ; φ)  := no_empty_coalition φ ∧ js.nonempty \ -/
/-\   | (S_indiv j ; φ) := no_empty_coalition φ \ -/
/-\   | (S_dist js ; φ) := no_empty_coalition φ ∧ js.nonempty \ -/
/-\   | (S_com js ; φ)  := no_empty_coalition φ ∧ js.nonempty \ -/

/-\ -- multi-source generalisation of the ealier translation result \ -/
/-\ --% latex_label: thm_collective_s4s5_translation \ -/
/-\ theorem ms_semantic_translation : \ -/
/-\   ∀ m : MSModel α J, ms_closed_under_unions m -> ms_closed_under_intersections m -> \ -/
/-\     ∀ φ : MSFormula J, no_empty_coalition φ -> ∀ x : α, \ -/
/-\       ms_sat m x φ <-> ms_ksat (ms_expmodel_to_rmodel m) x (translation φ) := \ -/
/-\ begin \ -/
/-\   intros m hmunions hmint θ hne, \ -/
/-\   induction θ, \ -/
/-\   case falsum \ -/
/-\     { intro x, refl }, \ -/
/-\   case atom : n \ -/
/-\     { intro x; refl }, \ -/
/-\   case and : φ ψ ihφ ihψ \ -/
/-\     { intro x; simp at hne; exact and_congr (ihφ hne.left x) (ihψ hne.right x) }, \ -/
/-\   case neg : φ ih \ -/
/-\     { intro x; exact not_congr (ih hne x) }, \ -/
/-\   case implies : φ ψ ihφ ihψ \ -/
/-\     { intro x; simp at hne; exact imp_congr (ihφ hne.left x) (ihψ hne.right x) }, \ -/
/-\   case iff : φ ψ ihφ ihψ \ -/
/-\     { intro x; simp at hne; exact iff_congr (ihφ hne.left x) (ihψ hne.right x) }, \ -/
/-\   case univ : φ ih \ -/
/-\     { intro x; apply forall_congr; intro y; exact (ih hne y) }, \ -/
/-\   -- the cases of expertise and soundness all use the general results \ -/
/-\   -- exp_translation and sound_translation, plus results here on the relations \ -/
/-\   -- associated with collective expertise \ -/
/-\   case exp_indiv : j φ ih \ -/
/-\     { \ -/
/-\       intro x, \ -/
/-\       simp at hne, \ -/
/-\       apply ep_connection.exp_translation (ih hne), \ -/
/-\         exact hmunions j, \ -/
/-\         exact hmint j \ -/
/-\     }, \ -/
/-\   case sound_indiv : j φ ih \ -/
/-\     { \ -/
/-\       intro x, \ -/
/-\       simp at hne, \ -/
/-\       apply ep_connection.sound_translation (ih hne), \ -/
/-\         exact hmunions j, \ -/
/-\         exact hmint j, \ -/
/-\     }, \ -/
/-\   case exp_dist : js φ ih \ -/
/-\     { \ -/
/-\       intro x, \ -/
/-\       simp, \ -/
/-\       let a := {y | ms_sat m y φ}, \ -/
/-\       let b := {y | ms_ksat (ms_expmodel_to_rmodel m) y (translation φ)}, \ -/
/-\       simp at hne, \ -/
/-\       rw @ep_connection.exp_translation α (dist_expertise m js) a b \ -/
/-\         dist_closed_unions dist_closed_intersections (ih hne.left), \ -/
/-\       apply forall_congr, \ -/
/-\       intro y, \ -/
/-\       apply imp_congr, \ -/
/-\         refl, \ -/
/-\         apply forall_congr, \ -/
/-\         intro z, \ -/
/-\         apply imp_congr, \ -/
/-\           exact dist_ep_relation_intersection m js y z, \ -/
/-\           refl \ -/
/-\     }, \ -/
/-\   case sound_dist : js φ ih \ -/
/-\     { \ -/
/-\       intro x, \ -/
/-\       simp, \ -/
/-\       let a := {y | ms_sat m y φ}, \ -/
/-\       let b := {y | ms_ksat (ms_expmodel_to_rmodel m) y (translation φ)}, \ -/
/-\       simp at hne, \ -/
/-\       rw @ep_connection.sound_translation α (dist_expertise m js) a b \ -/
/-\         dist_closed_unions dist_closed_intersections x (ih hne.left), \ -/
/-\       simp, \ -/
/-\       apply exists_congr, \ -/
/-\       intro y, \ -/
/-\       apply and_congr, \ -/
/-\         exact dist_ep_relation_intersection m js x y, \ -/
/-\         refl, \ -/
/-\     }, \ -/
/-\     case exp_com : js φ ih \ -/
/-\     { \ -/
/-\       intro x, \ -/
/-\       simp, \ -/
/-\       let a := {y | ms_sat m y φ}, \ -/
/-\       let b := {y | ms_ksat (ms_expmodel_to_rmodel m) y (translation φ)}, \ -/
/-\       simp at hne, \ -/
/-\       have hjs : js.nonempty, from hne.right, \ -/
/-\       rw @ep_connection.exp_translation α (com_expertise m js) a b \ -/
/-\         (com_closed_unions hmunions) (com_closed_intersections hmint) \ -/
/-\         (ih hne.left), \ -/
/-\       apply forall_congr, \ -/
/-\       intro y, \ -/
/-\       apply imp_congr, \ -/
/-\         refl, \ -/
/-\         apply forall_congr, \ -/
/-\         intro z, \ -/
/-\         apply imp_congr, \ -/
/-\           let h := com_ep_relation_union m js hjs hmunions hmint y z, \ -/
/-\           simp at h, \ -/
/-\           exact h, \ -/
/-\           refl, \ -/
/-\     }, \ -/
/-\     case sound_com : js φ ih \ -/
/-\     { \ -/
/-\       intro x, \ -/
/-\       simp, \ -/
/-\       let a := {y | ms_sat m y φ}, \ -/
/-\       let b := {y | ms_ksat (ms_expmodel_to_rmodel m) y (translation φ)}, \ -/
/-\       simp at hne, \ -/
/-\       have hjs : js.nonempty, from hne.right, \ -/
/-\         rw @ep_connection.sound_translation α (com_expertise m js) a b \ -/
/-\           (com_closed_unions hmunions) (com_closed_intersections hmint) x \ -/
/-\           (ih hne.left), \ -/
/-\         simp, \ -/
/-\         apply exists_congr, \ -/
/-\         intro y, \ -/
/-\         apply and_congr, \ -/
/-\           let h := com_ep_relation_union m js hjs hmunions hmint x y, \ -/
/-\           simp at h, \ -/
/-\           exact h, \ -/
/-\           refl \ -/
/-\     } \ -/
/-\   end \ -/

end multi_source
