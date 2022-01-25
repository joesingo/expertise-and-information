import basic

-- connection between expertise logic and epistemic logic wrt relational
-- semantics

variable {α : Type}

-- properties of relations
@[simp] def is_reflexive {α : Type} (r : relation α) := ∀ x : α, r x x
@[simp] def is_transitive {α : Type} (r : relation α) :=
  ∀ x y z : α, r x y -> r y z -> r x z
@[simp] def is_symmetric {α : Type} (r : relation α) :=
  ∀ x y : α, r x y -> r y x
@[simp] def is_eqv {α : Type} (r : relation α) :=
  is_symmetric r ∧ is_reflexive r ∧ is_transitive r
@[simp] def downwards_closed {α : Type} (a : set α) (r : relation α) :=
  ∀ x y : α, r x y -> y ∈ a -> x ∈ a

-- epistemic accessibility relation associated with an expertise predicate
--% latex_label: def_rp
@[simp] def ep_relation (exp : set α -> Prop) : relation α :=
  λx, λy, ∀ a : set α, exp a -> y ∈ a -> x ∈ a

-- epistemic accessibility relation associated with a model
@[simp] def model_ep_relation (m : Model α) : relation α :=
  ep_relation m.has_expertise

namespace ep_connection

-- preliminary result: if every s-dc set is r-dc, for s transitive and r
-- reflexive, then r ⊆ s
lemma dc_helper : ∀ r s : relation α,
  is_transitive s -> is_reflexive s ->
  (∀ a : set α, downwards_closed a s -> downwards_closed a r) ->
  ∀ x y : α, r x y -> s x y :=
begin
  introv hs_tr hs_ref h hrxy,
  -- let a be the down-set of y wrt s
  let a := {z | s z y},
  -- a is dc wrt s by transitivity
  have ha_dc : downwards_closed a s, from
    λu v hsuv hva, hs_tr u v y hsuv hva,
  -- a is dc wrt r since r, s share dc sets
  have ha_dc_r : downwards_closed a r, from h a ha_dc,
  -- y is in a by reflexivity of s
  have hya : y ∈ a, from hs_ref y,
  -- since r x y and a is dc wrt r, x is in a
  have hxa : x ∈ a, from ha_dc_r x y hrxy hya,
  show s x y, from hxa
end

-- corollary: if two transitive and reflexive relations share the same dc-sets,
-- then they are equal
--% latex_label: lemma_same_dc_sets_implies_equality
lemma same_dc_implies_equal : ∀ r s : relation α,
  is_transitive r -> is_reflexive r -> is_transitive s -> is_reflexive s ->
  (∀ a : set α, (downwards_closed a r <-> downwards_closed a s)) ->
  ∀ x y : α, r x y <-> s x y :=
begin
  introv hr_tr hr_ref hs_tr hs_ref hsame_dc,
  exact ⟨λhrxy, dc_helper r s hs_tr hs_ref (λa, (hsame_dc a).mpr) x y hrxy,
         λhsxy, dc_helper s r hr_tr hr_ref (λa, (hsame_dc a).mp) x y hsxy⟩
end

-- the relation associated with any expertise predicate is reflexive and
-- transitive
lemma ref_and_tr : ∀ exp : set α -> Prop,
  is_reflexive (ep_relation exp) ∧ is_transitive (ep_relation exp) :=
begin
  intro exp,
  apply and.intro,
    -- reflexivity
    simp,
    -- transitivity
    simp,
    introv hrxy hryz hexp hza,
    have hya : y ∈ a, from hryz a hexp hza,
    show x ∈ a, from hrxy a hexp hya
end

--% latex_label: lemma_p_to_rp_mapping
lemma mref_and_tr : ∀ m : Model α,
  is_reflexive (model_ep_relation m) ∧ is_transitive (model_ep_relation m) :=
  λm, ref_and_tr m.has_expertise

-- the relation associated with a model closed under complements is an
-- equivalence relation
lemma equiv_reln :
  ∀ m : Model α, mclosed_under_compl m -> is_eqv (model_ep_relation m) :=
begin
  intros m hcompl,
  refine ⟨_, mref_and_tr m⟩,
  simp,
  introv hrxy hexp hxa,
  by_contradiction hcontr,
  apply absurd hxa,
  have h : y ∈ aᶜ, from hcontr,
  show x ∉ a, from hrxy aᶜ (hcompl a hexp) h
end

-- we have expertise on a set a iff a is downwards closed wrt the
-- associated relation
lemma exp_iff_dc : ∀ exp : set α -> Prop, closed_under_unions exp ->
  closed_under_intersections exp ->
  ∀ a : set α, exp a <-> downwards_closed a (ep_relation exp)
  :=
begin
  intro exp,
  let r := ep_relation exp,
  intros hmunions hmint a,
  apply iff.intro,
    -- if we have expertise on a, then a is downwards closed wrt r
    intro hexp,
      intros x y hrxy hya,
      exact hrxy a hexp hya,

    -- if a is downwards closed wrt r, then we have expertise on a
    intro hdc,
      -- we claim a is equal to the following union of intersections
      let bb := λy, {b | exp b ∧ y ∈ b},
      let b_map := λy, ⋂₀ bb y,
      let aa := set.image b_map a,
      let a' := ⋃₀aa,

      -- show equality
      have heq : a = a',
      {
        apply set.ext,
        intro x,
        apply iff.intro,
          -- a ⊆ a',
          intro hxa,
          -- sufficient to show x is in some set in aa
          apply set.mem_sUnion.mpr,
          apply exists.intro, apply exists.intro,
            show b_map x ∈ aa, from ⟨x, ⟨hxa, refl _⟩⟩,
            show x ∈ b_map x, from
            begin
              apply set.mem_sInter.mpr,
              intros b h_bb,
              exact h_bb.right
            end,

          -- a' ⊆ a,
          intro hxa',
          have h : ∃ c ∈ aa, x ∈ c, from set.mem_sUnion.mp hxa',
          apply exists.elim h,
            intros c h_ex_c_in_aa,
            apply exists.elim h_ex_c_in_aa,
            intros hc_in_aa hxc,
            -- since c ∈ aa, there is y ∈ a such that b_map y = c
            apply exists.elim hc_in_aa,
            intros y hh,
            have hya : y ∈ a, from hh.left,
            have hcby : b_map y = c, from hh.right,
            -- this means x ∈ b_map y, so r x y
            have hxby : x ∈ b_map y, by rw hcby; exact hxc,
            have hrxy : r x y,
            {
              intros b hbexp hyb,
              have hb_bby : b ∈ bb y, from ⟨hbexp, hyb⟩,
              exact set.mem_sInter.mp hxby b hb_bby,
            },
            show x ∈ a, from hdc x y hrxy hya
      },

      -- suffices to show expertise on a'
      rw heq,

      have hb_exp : ∀ y : α, exp (b_map y),
      {
        intro y,
        -- since exp is closed under intersections, it suffices to show
        -- expertise for each b ∈ bb y
        apply hmint (bb y),
        intros b hb_in_bby,
        exact hb_in_bby.left
      },

      show exp a',
      {
        -- since exp is closed under unions, it suffices to show expertise on
        -- each c ∈ aa
        apply hmunions aa,
        intros c hc_in_aa,
        -- since c ∈ aa, there is y ∈ a such that b_map y = c
        apply exists.elim hc_in_aa,
          intros y h,
          have hya : y ∈ a, from h.left,
          have hcby : b_map y = c, from h.right,
          show exp c, from hcby ▸ hb_exp y
      }
end

-- specialisation of the above to when the expertise predicate comes from a
-- model m
--% latex_label: lemma_p_to_rp_mapping
lemma model_exp_iff_dc : ∀ m : Model α, mclosed_under_unions m ->
  mclosed_under_intersections m ->
    ∀ a : set α, m.has_expertise a <-> downwards_closed a (model_ep_relation m)
  := λm hunions hint, exp_iff_dc m.has_expertise hunions hint

-- for every transitive and reflexive relation r there is a model m, closed
-- under unions and intersections, whose associated relation is equal to r
--% latex_label: lemma_p_to_rp_mapping
lemma surjectivity_s4 {α : Type} :
  ∀ r : relation α, is_reflexive r -> is_transitive r ->
    ∃ m : Model α, (mclosed_under_unions m ∧ mclosed_under_intersections m)
      ∧ ∀ x y, r x y <-> (model_ep_relation m) x y :=
begin
  intros r hr_ref hr_tr,
  -- construct a model where we have expertise on a iff a is dc wrt r
  -- (valuation is arbitrary)
  let exp : set α -> Prop := λa, downwards_closed a r,
  let val : ℕ -> α -> Prop := λn, λx, true,
  let f : Frame α := Frame.mk exp,
  let m : Model α := Model.mk f val,
  let rp := model_ep_relation m,
  let hrp_ref_tr := mref_and_tr m,
  apply exists.intro m,
  -- first show m is closed under unions and intersections
  have hmunions : mclosed_under_unions m,
  {
    -- unions: take any collection aa with expertise for each a ∈ aa
    intros aa hexp,
    -- need to show expertise on ∪aa, i.e. ∪aa is dc
    intros x y hrxy hyunion,
    -- by y ∈ ∪aa, there is a ∈ aa such that y ∈ a
    apply exists.elim (set.mem_sUnion.mp hyunion),
    intros a h_ex_a_in_aa,
    apply exists.elim h_ex_a_in_aa,
    intros ha_in_aa hya,
    -- a is downwards closed
    have hdc : downwards_closed a r, from hexp a ha_in_aa,
    -- hence x ∈ a too
    have hxa : x ∈ a, from (hdc x y) hrxy hya,
    -- thus x ∈ ∪aa
    apply set.mem_sUnion.mpr,
    exact ⟨a, ⟨ha_in_aa, hxa⟩⟩
  },
  have hmint : mclosed_under_intersections m,
  {
    -- similar to the case for unions
    intros aa hexp x y hrxy hyint,
    apply set.mem_sInter.mpr,
    intros a ha_in_aa,
    have hya : y ∈ a, from set.mem_sInter.mp hyint a ha_in_aa,
    show x ∈ a, from (hexp a ha_in_aa) x y hrxy hya
  },
  apply and.intro,
    exact (and.intro hmunions hmint),
    -- next show r = rp. since both relations are reflexive and transitive, by
    -- earlier result it is sufficient to show r and rp have the same dc sets
    apply same_dc_implies_equal
      r rp hr_tr hr_ref hrp_ref_tr.right hrp_ref_tr.left,
    intro a,
    -- this follows from definition of m and an earlier result showing
    -- that a is dc wrt rp iff we have expertise on a
    rw <-(model_exp_iff_dc m hmunions hmint a)
end

-- similarly, for every equivalence relation r there is a model m closed under
-- intersections and complements whose associated relation is r
lemma surjectivity_s5 {α : Type}  :
  ∀ r : relation α, is_reflexive r -> is_transitive r -> is_symmetric r ->
    ∃ m : Model α, (mclosed_under_intersections m ∧ mclosed_under_compl m)
      ∧ ∀ x y, r x y <-> (model_ep_relation m) x y :=
begin
  intros r hr_ref hr_tr hr_symm,
  -- take the model m from surjectivity_s4, and show it is closed under
  -- complements
  apply exists.elim (surjectivity_s4 r hr_ref hr_tr),
  intros m h,
  let hr_eq := h.right,
  let hmint := h.left.right,
  let hmunions := h.left.left,
  refine ⟨m, ⟨hmint, _⟩, hr_eq⟩,
  intros a hexp,
  -- suffices to show aᶜ is dc
  apply (model_exp_iff_dc m hmunions hmint aᶜ).mpr,
  intros x y h_epr_xy hyac,
  have hrxy : r x y, from (hr_eq x y).mpr h_epr_xy,
  have hryx : r y x, from hr_symm x y hrxy,
  have h_epr_yx : (model_ep_relation m) y x, from (hr_eq y x).mp hryx,
  by_contradiction hcontr,
  apply absurd hyac,
  simp at *,
  exact h_epr_yx a hexp hcontr
end

-- formal language for epistemic logic
inductive KFormula : Type
  | falsum : KFormula
  | atom : ℕ -> KFormula
  | and : KFormula -> KFormula -> KFormula
  | neg : KFormula -> KFormula
  | implies : KFormula -> KFormula -> KFormula
  | iff : KFormula -> KFormula -> KFormula
  | know : KFormula -> KFormula
  | univ : KFormula -> KFormula

-- infix notation
notation `⊥` := KFormula.falsum
notation `P` n := KFormula.atom n
notation φ `&` ψ := KFormula.and φ ψ
notation `#` φ := KFormula.neg φ
notation φ `⇒` ψ := KFormula.implies φ ψ
notation φ `⇔` ψ := KFormula.iff φ ψ
notation `K` φ := KFormula.know φ
notation `A` φ := KFormula.univ φ

-- relational model over α
--% latex_label: def_relational_models
structure RModel (α : Type) :=
  (accessible : relation α)
  (val : ℕ → α → Prop)

@[simp] def ksat (m : RModel α) : α -> KFormula -> Prop
  | x ⊥       := false
  | x (P n)   := m.val n x
  | x (φ & ψ) := (ksat x φ) ∧ (ksat x ψ)
  | x (# φ)   := ¬(ksat x φ)
  | x (φ ⇒ ψ) := (ksat x φ) -> (ksat x ψ)
  | x (φ ⇔ ψ) := (ksat x φ) <-> (ksat x ψ)
  | x (K φ)   := ∀ y : α, m.accessible x y -> ksat y φ
  | x (A φ)   := ∀ y : α, ksat y φ

-- mapping from expertise to relational models
def expmodel_to_rmodel (m : Model α) : RModel α :=
  RModel.mk (model_ep_relation m) m.val

-- translation from expertise to epistemic languanges
@[simp] def translation : Formula -> KFormula
  | ⊥       := ⊥
  | (P n)   := P n
  | (φ & ψ) := translation φ & translation ψ
  | (# φ)   := #(translation φ)
  | (φ ⇒ ψ) := translation φ ⇒ translation ψ
  | (φ ⇔ ψ) := translation φ ⇔ translation ψ
  | (E φ)   := A ((# (translation φ)) ⇒ (K (# (translation φ))))
  | (S φ)   := # (K (# (translation φ)))
  | (A φ)   := A (translation φ)

-- show the semantic translation result E and S formulas for any expertise
-- predicate (not necessarily associated with a model). this will allow the
-- proof to be re-used in the multi-source case
lemma exp_translation {exp : set α -> Prop} {a : α -> Prop} {b : α -> Prop}
  {hunions : closed_under_unions exp} {hint : closed_under_intersections exp}
  (h_iff : ∀ x : α, a x <-> b x) :
    exp a <-> (∀y, ¬(b y) -> (∀z, ep_relation exp y z -> ¬(b z))) :=
begin
  let r := ep_relation exp,
  apply iff.intro,
    intros hexp y hy_nb z hryz,
    by_contradiction hcontr,
    have hz_a : a z, from (h_iff z).mpr hcontr,
    apply absurd hy_nb,
    simp,
    have hdc : downwards_closed a r, from
      (exp_iff_dc exp hunions hint a).mp hexp,
    have hy_a : a y, from hdc y z hryz hz_a,
    show b y, from (h_iff y).mp hy_a,

    intro h,
    apply (exp_iff_dc exp hunions hint a).mpr,
    intros y z hryz hz_a,
    by_contradiction hcontr,
    apply absurd hz_a,
    have hy_nb : ¬b y, from mt (h_iff y).mpr hcontr,
    have hz_nb : ¬b z , from h y hy_nb z hryz,
    show ¬a z, from mt (h_iff z).mp hz_nb
end

lemma sound_translation {exp : set α -> Prop} {a : set α} {b : set α}
  {hunions : closed_under_unions exp} {hint : closed_under_intersections exp}
  {x : α} (h_iff : ∀ y : α, a y <-> b y) :
    (∀ c : set α, exp c -> a ⊆ c -> x ∈ c)
    <-> ¬(∀ y : α, ep_relation exp x y -> ¬b y) :=
begin
  let r := ep_relation exp,
  apply iff.intro,
    -- assume the soundness property (i.e. the set a is sound at x)
    intro h,
    -- suppose for contradiction that all successors of x are not in b
    by_contradiction hcontr,
    -- taking c to be the downwards closure of a, we have x ∈ c by soundness
    let c := {y | ∃z, a z ∧ r y z},
    have hdc : downwards_closed c r,
    {
      intros u v hruv hvc,
      apply exists.elim hvc,
      intros w hprop,
      have h_tr : is_transitive r, from (ref_and_tr exp).right,
      exact ⟨w, hprop.left, h_tr u v w hruv hprop.right⟩
    },
    have hexp : exp c, from (exp_iff_dc exp hunions hint c).mpr hdc,
    have hss : a ⊆ c,
    {
      intros u hmem,
      have h_ref : is_reflexive r, from (ref_and_tr exp).left,
      exact ⟨u, hmem, h_ref u⟩
    },
    have hxc : x ∈ c, from h c hexp hss,
    -- consequently there is some successor of x in a; by a = b this
    -- contradicts our earlier assumption
    apply exists.elim hxc,
    intros y hprop,
    have hy_nb : ¬b y, from hcontr y hprop.right,
    apply absurd hy_nb,
    simp,
    exact (h_iff y).mp hprop.left,

    -- if there is expertise on c, which contains a, but for contradiction x ∉
    -- c, then any successor of x cannot be in c and thus not in a = b
    intros h c hexp hss,
    by_contradiction hcontr,
    apply absurd h,
    simp,
    intros y hrxy,
    have hy_nc : y ∉ c,
    {
      by_contradiction hcontr2,
      have hdc : downwards_closed c r, from
        (exp_iff_dc exp hunions hint c).mp hexp,
      apply absurd hcontr,
      simp,
      exact hdc x y hrxy hcontr2
    },
    have hy_na : y ∉ a, from set.not_mem_subset hss hy_nc,
    show ¬b y, from mt (h_iff y).mpr hy_na
end

-- main result: the 1-to-1 mapping between expertise models (closed under
-- unions and intersections) and S4 relational models preserves the truth
-- values of formulas, using the translation defined above
--% latex_label: thm_s4s5_translation
theorem semantic_translation :
  ∀ m : Model α, mclosed_under_unions m -> mclosed_under_intersections m ->
    ∀ φ : Formula, ∀ x : α,
      sat m x φ <-> ksat (expmodel_to_rmodel m) x (translation φ) :=
begin
  intros m hmunions hmint θ,
  -- by induction on expertise formulas θ
  induction θ,
  case atom : n
    { intro x; refl },
  case and : φ ψ ihφ ihψ
    { intro x; exact and_congr (ihφ x) (ihψ x) },
  case neg : φ ih
    { intro x; exact not_congr (ih x) },
  case implies : φ ψ ihφ ihψ
    { intro x; exact imp_congr (ihφ x) (ihψ x) },
  case iff : φ ψ ihφ ihψ
    { intro x; exact iff_congr (ihφ x) (ihψ x) },
  case univ : φ ih
    { intro x; apply forall_congr; intro y; exact (ih y) },
  case falsum
    { intro x, refl },
  case exp : φ ih
  {
    intro x,
    apply exp_translation ih,
      exact hmunions,
      exact hmint,
  },
  case sound : φ ih
  {
    intro x,
    apply sound_translation ih,
      exact hmunions,
      exact hmint,
  }
end

end ep_connection
