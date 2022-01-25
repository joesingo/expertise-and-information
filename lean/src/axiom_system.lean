import order.zorn

import basic

-- towards proving completeness results, introduce the logic
inductive Proof : Formula -> Prop
  -- propositional logic. we include many redundant axioms to make working with
  -- Proofs simpler
  -- TODO: reduce redundancy
  | pl_refl {φ : Formula} : Proof (φ ⇒ φ)
  | pl2 {φ ψ : Formula} : Proof (φ ⇒ (ψ ⇒ φ))
  | pl3 {φ ψ θ : Formula} : Proof ((φ ⇒ (ψ ⇒ θ)) ⇒ ((φ ⇒ ψ) ⇒ (φ ⇒ θ)))
  | pl_mt {φ ψ : Formula} : Proof (((#φ) ⇒ (#ψ)) ⇒ (ψ ⇒ φ))
  | pl_neg {φ : Formula} : Proof ((φ ⇒ ⊥) ⇒ (#φ))
  | pl_negpair {φ : Formula} : Proof (φ ⇒ ((#φ) ⇒ ⊥))
  | pl_false_elim {φ : Formula} : Proof ⊥ -> Proof φ
  | pl_notbot : Proof #⊥
  | pl_dne {φ : Formula} : Proof ((##φ) ⇒ φ)
  | pl_and_intro {φ ψ : Formula} : Proof (ψ ⇒ φ ⇒ (φ & ψ))
  | pl_and_elim_l {φ ψ : Formula} : Proof ((φ & ψ) ⇒ φ)
  | pl_and_elim_r {φ ψ : Formula} : Proof ((φ & ψ) ⇒ ψ)
  | pl_neg_imp {φ ψ : Formula} : Proof ((#(φ ⇒ ψ)) ⇒ (φ & (#ψ)))
  | pl_iff_intro {φ ψ : Formula} : Proof ((φ ⇒ ψ) ⇒ ((ψ ⇒ φ) ⇒ (φ ⇔ ψ)))
  | pl_iff_elim {φ ψ : Formula} : Proof ((φ ⇔ ψ) ⇒ ((φ ⇒ ψ) & (ψ ⇒ φ)))

  -- E axioms
  | ea {φ : Formula} : Proof (E φ ⇔ A E φ)
  | re {φ ψ : Formula} : Proof ((A (φ ⇔ ψ)) ⇒ (E φ ⇔ E ψ))
  | we {φ ψ : Formula} : Proof ((A (φ ⇒ ψ)) ⇒ ((S φ & E ψ) ⇒ ψ))
  -- S axioms
  | t {φ : Formula} : Proof (φ ⇒ S φ)
  | s4 {φ : Formula} : Proof ((S S φ) ⇒ S φ)
  | ws {φ ψ : Formula} : Proof ((A (φ ⇒ ψ)) ⇒ ((S φ) ⇒ (S ψ)))
  -- A axioms
  | ka {φ ψ : Formula} : Proof ((A (φ ⇒ ψ)) ⇒ ((A φ) ⇒ (A ψ)))
  | ta {φ : Formula} : Proof ((A φ) ⇒ φ)
  | a5 {φ : Formula} : Proof ((#A φ) ⇒ A#A φ)
  -- inference rules
  | nec_a {φ : Formula} : Proof φ -> Proof (A φ)
  | modpon {φ ψ : Formula} : Proof φ -> Proof (φ ⇒ ψ) -> Proof ψ

prefix `⊢`:100 := Proof

-- define what it means for a set Γ to entail φ
--   base case 1: Γ entails any theorem
--   base case 2: Γ entails any of its members
--   modus ponens: if Γ entails both φ and φ ⇒ ψ, then Γ entails ψ
inductive entails (Γ : set Formula) : Formula -> Prop
  | thm {φ : Formula} : Proof φ -> entails φ
  | mem {φ : Formula} : φ ∈ Γ -> entails φ
  | mp {φ ψ : Formula} : entails φ -> entails (φ ⇒ ψ) -> entails ψ

-- consistency notions
def incons (Γ : set Formula) := entails Γ ⊥
@[simp] def cons (Γ : set Formula) := not (incons Γ)
def mcs (Γ : set Formula) := cons Γ ∧ ∀ Δ, Γ ⊆ Δ -> cons Δ -> Γ = Δ

namespace consistency

variables {φ ψ : Formula} {Γ : set Formula}

lemma entailment_monotone {Γ Δ : set Formula} : Γ ⊆ Δ ->
    entails Γ φ -> entails Δ φ :=
begin
  intro hsubset,
  intro hent,
  induction hent,
    case thm { apply entails.thm, assumption },
    case mem
    {
      apply entails.mem,
      apply set.mem_of_subset_of_mem hsubset,
      assumption
    },
    case mp
    {
      apply entails.mp,
      repeat {assumption},
    }
end

lemma entail_neg_pair_incons : entails Γ φ -> entails Γ (#φ) -> incons Γ :=
begin
  intros h1 h2,
  have h : entails Γ (φ ⇒ ((#φ) ⇒ ⊥)), from entails.thm Proof.pl_negpair,
  exact entails.mp h2 (entails.mp h1 h)
end

lemma mem_neg_pair : φ ∈ Γ -> (#φ) ∈ Γ -> incons Γ :=
begin
  intros hmem hmem_neg,
  apply entail_neg_pair_incons,
  repeat {apply entails.mem; assumption}
end

-- if Γ ∪ {ψ} entails ψ, then Γ entails φ ⇒ ψ
lemma splitting_lemma : entails (Γ ∪ {φ}) ψ -> entails Γ (φ ⇒ ψ) :=
begin
  intros hent,
  induction hent,
    case thm : ε hεthm
    {
      apply entails.thm,
      apply Proof.modpon hεthm,
      exact Proof.pl2
    },
    case mem : ε hmem
    {
      apply or.elim (em (ε ∈ Γ)),
        -- if ε ∈ Γ then clearly Γ entails φ ⇒ ε
        intro hmemΓ,
        have h : entails Γ ε, from entails.mem hmemΓ,
        apply entails.mp h,
        apply entails.thm,
        apply Proof.pl2,

        -- if ε ∉ Γ then ε = φ, so φ ⇒ ε is clear
        intro hnmemΓ,
        apply set.mem_union.elim hmem,
          intro hmemΓ,
          exact absurd hmemΓ hnmemΓ,

          intro heq,
          apply entails.thm,
          have h : ε = φ, from heq,
          rw h,
          apply Proof.pl_refl
    },
    case mp : ε δ hentε _ ih1 ih2
    {
      have himp : entails Γ (φ ⇒ ε), from
      begin
        apply or.elim (em (entails Γ ε)),
          intro hε,
          apply entails.mp hε,
          apply entails.thm,
          exact Proof.pl2,

          intro,
          exact ih1
      end,
      have hdouble_imp : entails Γ (φ ⇒ (ε ⇒ δ)), from
      begin
        apply or.elim (em (entails Γ (ε ⇒ δ))),
          intro himp,
          apply entails.mp himp,
          apply entails.thm,
          exact Proof.pl2,

          intro,
          exact ih2
      end,
      apply entails.mp himp,
      apply entails.mp hdouble_imp,
      apply entails.thm,
      exact Proof.pl3
    },
end

-- if Γ is consistent and Γ ∪ {φ} is insonsistent, then Γ entails ¬φ
lemma incons_implies_entails : incons (Γ ∪ {φ}) -> entails Γ #φ :=
begin
  intros h2,
  apply entails.mp (splitting_lemma h2),
  apply entails.thm,
  apply Proof.pl_neg,
end

-- we can add any formula entailed by a consistent set without losing
-- consistency
lemma entail_cons : cons Γ -> entails Γ φ -> cons (Γ ∪ {φ}) :=
begin
  intros hcons hent,
  by_contradiction hcontr,
  have h1 : entails Γ #φ, from incons_implies_entails (dne hcontr),
  have h2 : incons Γ, from entail_neg_pair_incons hent h1,
  exact absurd h2 hcons
end

-- if Γ does not entail φ then Γ ∪ {¬φ} is consistent
lemma not_entails_implies_cons : ¬entails Γ φ -> cons (Γ ∪ {#φ}) :=
begin
  intro hnent,
  by_contradiction hcontr,
  apply absurd hnent,
  simp,
  refine entails.mp _ (entails.thm Proof.pl_dne),
  exact incons_implies_entails (dne hcontr)
end

-- if Γ entails φ, then prefixing all formulas in Γ with A entails Aφ
lemma a_prefix_imp : entails Γ φ -> entails {(A ψ) | ψ ∈ Γ} (A φ) :=
begin
  intro h,
  induction h,
    -- if φ is a theorem then nec_a gives that Aφ is
    case thm
      { apply entails.thm, apply Proof.nec_a, repeat {assumption} },
    -- if φ is in the set then clearly Aφ is in Γ
    case mem : φ hmem
      { apply entails.mem, refine ⟨φ, hmem, _⟩, refl },
    -- for the inductive step we use K for A and modus ponens
    case mp : _ _ h1 h2 ih1 ih2
    {
      apply entails.mp ih1,
      apply entails.mp ih2,
      apply entails.thm,
      apply Proof.ka
    }
end

-- an mcs contains a formula if and only if it entails it
--% latex_label: lemma_mcs_facts
lemma membership : mcs Γ -> (φ ∈ Γ <-> entails Γ φ) :=
begin
  intro hmcs,
  apply iff.intro,
    intro h1,
    exact entails.mem h1,

    -- if Γ entails φ then Γ ∪ {φ} is consistent, so φ ∈ Γ by mcs
    intros,
    let Δ := Γ ∪ {φ},
    have heq : Γ = Δ, from
    begin
      apply (hmcs.right Δ),
        simp,
        apply entail_cons,
          exact hmcs.left,
          assumption
    end,
    rw heq,
    simp,
end

--% latex_label: lemma_mcs_facts
lemma mem_modpon : mcs Γ -> φ ∈ Γ -> (φ ⇒ ψ) ∈ Γ -> ψ ∈ Γ :=
begin
  intros hmcs hmem1 hmem2,
  apply (membership hmcs).mpr,
  have h1 : entails Γ φ, from (membership hmcs).mp hmem1,
  have h2 : entails Γ (φ ⇒ ψ), from (membership hmcs).mp hmem2,
  exact entails.mp h1 h2
end

--% latex_label: lemma_mcs_facts
lemma negations : mcs Γ -> ((#φ) ∈ Γ <-> φ ∉ Γ) :=
begin
  intro hmcs,
  apply iff.intro,
    -- if ¬φ ∈ Γ then φ ∈ Γ would give inconsistency by an earlier lemma
    intro hmem,
    by_contradiction hcontr,
    apply absurd hmcs.left,
    simp,
    apply entail_neg_pair_incons,
      exact (membership hmcs).mp hcontr,
      exact (membership hmcs).mp hmem,

    -- suppose φ ∉ Γ. then Γ ∪ {¬φ} is consistent, so ¬φ ∈ Γ by mcs
    intro hnmem,
    let Δ := Γ ∪ {#φ},
    have heq : Γ = Δ, from
    begin
      apply (hmcs.right Δ),
        simp,

        -- need to show Δ is consistent. suppose otherwise
        by_contradiction hcontr,
        have h : incons Δ, from dne hcontr,
        -- we show that φ ∈ Γ, giving a contradiction
        apply absurd hnmem,
        simp,
        -- by membership lemma and pl, we can show the Γ entails ¬¬φ
        apply (membership hmcs).mpr,
        have h2 : entails Γ (##φ), from incons_implies_entails h,
        apply entails.mp h2,
        apply entails.thm,
        apply Proof.pl_dne
    end,
    rw heq,
    simp
end

--% latex_label: lemma_mcs_facts
lemma conjunctions : mcs Γ -> ((φ & ψ) ∈ Γ <-> (φ ∈ Γ) ∧ (ψ ∈ Γ)) :=
begin
  intro hmcs,
  apply iff.intro,
    intro hmem_and,
    have h : entails Γ (φ & ψ), from (membership hmcs).mp hmem_and,
    apply and.intro,
      apply (membership hmcs).mpr,
      apply entails.mp h,
      apply entails.thm,
      apply Proof.pl_and_elim_l,

      apply (membership hmcs).mpr,
      apply entails.mp h,
      apply entails.thm,
      apply Proof.pl_and_elim_r,

    intro hmem_both,
    have h1 : entails Γ φ, from (membership hmcs).mp hmem_both.left,
    have h2 : entails Γ ψ, from (membership hmcs).mp hmem_both.right,
    apply (membership hmcs).mpr,
    apply entails.mp h1,
    apply entails.mp h2,
    apply entails.thm,
    apply Proof.pl_and_intro
end

lemma theorems (h1 : mcs Γ) (h2 : ⊢ φ) : φ ∈ Γ :=
  (membership h1).mpr (entails.thm h2)

lemma implications : mcs Γ -> ((φ ⇒ ψ) ∈ Γ <-> (φ ∈ Γ -> ψ ∈ Γ)) :=
begin
  intro hmcs,
  apply iff.intro,
    intros himp hφ,
    exact mem_modpon hmcs hφ himp,

    intro h,
    by_contradiction hcontr,
    apply absurd h,
    have hneg : (#(φ ⇒ ψ)) ∈ Γ, from (negations hmcs).mpr hcontr,
    have hand : (φ & (#ψ)) ∈ Γ, from
      (mem_modpon hmcs) hneg (theorems hmcs Proof.pl_neg_imp),
    simp,
    apply and.intro,
      exact ((conjunctions hmcs).mp hand).left,
      apply (negations hmcs).mp,
      exact ((conjunctions hmcs).mp hand).right,
end

lemma iffs : mcs Γ -> ((φ ⇔ ψ) ∈ Γ <-> (φ ∈ Γ <-> ψ ∈ Γ)) :=
begin
  intro hmcs,
  apply iff.intro,
    intro hiff,
    apply iff.intro,
      intro hφ,
      apply mem_modpon hmcs hφ,
      apply and.left,
      apply (conjunctions hmcs).mp,
      apply (implications hmcs).mp,
        apply theorems hmcs Proof.pl_iff_elim,
        exact hiff,

      intro hψ,
      apply mem_modpon hmcs hψ,
      apply and.right,
      apply (conjunctions hmcs).mp,
      apply (implications hmcs).mp,
        apply theorems hmcs Proof.pl_iff_elim,
        exact hiff,

    intro hφ_iff_ψ,
    have himp1 := (implications hmcs).mpr (hφ_iff_ψ).mp,
    have himp2 := (implications hmcs).mpr (hφ_iff_ψ).mpr,
    apply mem_modpon hmcs himp2,
    apply mem_modpon hmcs himp1,
    exact theorems hmcs Proof.pl_iff_intro
end


lemma falsum : mcs Γ -> (⊥ : Formula) ∉ Γ :=
begin
  intro hmcs,
  apply (negations hmcs).mp,
  apply theorems hmcs,
  exact Proof.pl_notbot
end

lemma exp : mcs Γ -> ((E φ) ∈ Γ <-> (A (E φ)) ∈ Γ) :=
begin
  intro hmcs,
  apply (iffs hmcs).mp,
  apply theorems hmcs,
  apply Proof.ea
end

-- lemma required below: if a non-empty collection of consistent sets is
-- totally ordered ⊆, anything entailed by the union is entailed by one of
-- its members
lemma union_chain_entailment (chain : set (set Formula)) :
  zorn.chain (⊆) chain -> chain.nonempty ->
  entails (⋃₀chain) φ -> ∃ Δ, Δ ∈ chain ∧ entails Δ φ :=

begin
  intros hc hne hent,
  induction hent,
  case thm : _ h { exact ⟨hne.some, hne.some_mem, entails.thm h⟩ },
  case mem : _ h
  {
    begin
      -- if φ is in the union, by definition there is some set in the chain
      -- containing φ, and hence entailing φ
      apply exists.elim (set.mem_sUnion.mp h),
      intros Δ hex,
      apply exists.elim hex,
      intros h_in_chain h_contains_φ,
      exact ⟨Δ, h_in_chain, entails.mem h_contains_φ⟩
    end
  },
  case mp : ε δ h1 h2 ih1 ih2
  {
    apply exists.elim ih1,
    intros Δ₁ h1,
    apply exists.elim ih2,
    intros Δ₂ h2,
    -- by the chain property, either Δ₁ = Δ₂ or one contains the other
    apply or.elim (em (Δ₁ = Δ₂)),
      intro heq,
      apply exists.intro Δ₁,
      apply and.intro h1.left,
      apply entails.mp h1.right,
      rw heq,
      exact h2.right,

      intro hne,
      apply or.elim (hc Δ₁ h1.left Δ₂ h2.left hne),
        intro h1_ss_2,
        apply exists.intro Δ₂,
        apply and.intro h2.left,
        apply entails.mp,
          exact entailment_monotone h1_ss_2 h1.right,
          exact h2.right,

        intro h2_ss_1,
        apply exists.intro Δ₁,
        apply and.intro h1.left,
        apply entails.mp h1.right,
        exact entailment_monotone h2_ss_1 h2.right
  }
end

--% latex_label: lemma_lindenbaum
lemma lindenbaum : cons Γ -> ∃Δ, (Γ ⊆ Δ ∧ mcs Δ) :=
  begin
    assume hcons,
    -- let x be the consistent extensions of Γ. it suffices to show that x
    -- has a maximal element wrt ⊆
    let x := {Δ | Γ ⊆ Δ ∧ cons Δ},
    suffices : ∃ M ∈ x, ∀ Λ ∈ x, M ⊆ Λ -> Λ = M,
    {
      apply exists.elim this,
      intros M hprop,
      apply exists.elim hprop,
      intros hmem_x hmax,
      apply exists.intro M,
      apply and.intro,
        exact hmem_x.left,

        apply and.intro hmem_x.right,
        intros Δ hsubset hcons,
        apply eq.symm,
        apply hmax Δ,
          apply and.intro,
            exact set.subset.trans hmem_x.left hsubset,
            exact hcons,
          exact hsubset
    },
    -- we show x has a maximum by Zorn's lemma. take any chain
    apply zorn.zorn_subset,
    intros chain hchain_in_x hc,
    apply or.elim chain.eq_empty_or_nonempty,
      -- if chain is empty, Γ is an upper bound
      intro hchain_empty,
      exact ⟨Γ,
             -- show Γ ∈ x
             begin apply and.intro, refl, exact hcons end,
             -- show Γ is an ub of ∅
             begin
              intros,
              by_contradiction,
              rw <-set.mem_empty_eq,
              rw <-hchain_empty,
              assumption
             end⟩,

      -- otherwise, let M be the union of the sets in the chain
      intro hchain_nonempty,
      let M := ⋃₀chain,
      -- need to show M is in x
      have hMx : M ∈ x,
      {
        apply and.intro,
          -- to show Γ ⊆ M, take some Δ ∈ chain and use chain ⊆ x to get Γ ⊆
          -- Δ ⊆ M
          let Δ := hchain_nonempty.some,
          let hmem := set.nonempty.some_mem hchain_nonempty,
          have h : Γ ⊆ Δ, from (hchain_in_x hmem).left,
          exact set.subset_sUnion_of_subset chain Δ h hmem,

          -- to show M is consistent, suppose not. by an earlier result there
          -- is some Δ ∈ chain which is inconsistent: contradiction
          by_contradiction hcontr,
          have hbot : entails M ⊥, from dne hcontr,
          apply exists.elim
            (union_chain_entailment chain hc hchain_nonempty hbot),
          intros Δ hΔ,
          apply absurd hΔ.right,
          have hΔ_in_x : Δ ∈ x, from
            set.mem_of_subset_of_mem hchain_in_x hΔ.left,
          exact hΔ_in_x.right
      },
      have hub : ∀ Δ, Δ ∈ chain -> Δ ⊆ M,
        { intros, apply set.subset_sUnion_of_mem, assumption },
      exact ⟨M, hMx, hub⟩

  end

end consistency

-- the inductive definition of entailment is equivalent to the usual one:
-- Γ entails φ if there is a finite set {ψ_1,...,ψ_n} ⊆ Γ such that
-- ⊢ (ψ_1 & ... & ψ_n) -> φ

namespace equivalent_entailment

variables {φ ψ : Formula} {Γ : set Formula}

-- iterated conjunction of a finite list of formulas
@[simp] def conjunction : list Formula -> Formula
  | []       := #⊥
  | (φ :: l) := φ & (conjunction l)

-- when is a list a "subset" of a set?
@[simp] def list_subset : list Formula -> set Formula -> Prop
  | []       _ := true
  | (φ :: l) Γ := list_subset l Γ ∧ φ ∈ Γ

-- lemmas to do with implications
lemma imp_transitivty {φ ψ θ : Formula} :
  ⊢ (φ ⇒ ψ) -> ⊢ (ψ ⇒ θ) -> ⊢ (φ ⇒ θ) :=
  λh1 h2, Proof.modpon h1 (Proof.modpon (Proof.modpon h2 Proof.pl2) Proof.pl3)

lemma imp_lemma {φ ψ θ : Formula} : ⊢ ((φ ⇒ ψ) ⇒ ((θ ⇒ φ) ⇒ (θ ⇒ ψ))) :=
    Proof.modpon Proof.pl2
      (Proof.modpon (Proof.modpon Proof.pl3 Proof.pl2) Proof.pl3)

-- lemma: we can move a conjunction on the lhs of an implication to an
-- implication on the rhs
lemma and_lemma {φ ψ θ : Formula} :
  ⊢ ((φ & ψ) ⇒ θ) <-> ⊢ (ψ ⇒ (φ ⇒ θ)) :=
  ⟨λh, Proof.modpon Proof.pl_and_intro
        (Proof.modpon (Proof.modpon h imp_lemma) imp_lemma),
   λh, Proof.modpon Proof.pl_and_elim_l
        (Proof.modpon (imp_transitivty Proof.pl_and_elim_r h) Proof.pl3)⟩

-- lemma: a kind of modus ponens for conjunctions of lists: if s implies φ and
-- t implies φ ⇒ ψ, then their concatenation s ++ t implies ψ
lemma conjunction_modpon {s t : list Formula} :
  ⊢ (conjunction s ⇒ φ) -> ⊢ (conjunction t ⇒ (φ ⇒ ψ)) ->
  ⊢ (conjunction (s ++ t) ⇒ ψ) :=
begin
  revert ψ,
  revert φ,
  induction s,
    case nil
    {
      intros φ ψ h1 h2,
      simp at *,
      have h3 : ⊢ ((φ ⇒ ψ) ⇒ ψ),
      {
        refine Proof.modpon _ (Proof.modpon Proof.pl_refl Proof.pl3),
        refine Proof.modpon _ Proof.pl2,
        exact Proof.modpon Proof.pl_notbot h1
      },
      exact imp_transitivty h2 h3
    },
    case cons : θ l ih
    {
      intros φ ψ h1 h2,
      apply and_lemma.mpr,
      apply ih (and_lemma.mp h1) (imp_transitivty h2 imp_lemma)
    }
  end

lemma list_subset_concat {s t : list Formula} :
  list_subset s Γ -> list_subset t Γ -> list_subset (s ++ t) Γ :=
begin
  intros hs ht,
  induction s,
    case nil { simp, exact ht },
    case cons : φ l ih { exact ⟨ih hs.left, hs.right⟩ }
end

-- main result: our inductive definition of entailment coincides with the usual
-- definition
lemma equivalent_entailment :
  entails Γ φ <-> ∃ s : list Formula,
    list_subset s Γ ∧ ⊢ (conjunction s ⇒ φ) :=
begin
  apply iff.intro,
    intro hent,
    induction hent,
      case thm : φ hthm
      {
        apply exists.intro [],
        simp,
        exact Proof.modpon hthm Proof.pl2
      },
      case mem : φ hmem
      {
        apply exists.intro [φ],
        simp,
        exact ⟨hmem, Proof.pl_and_elim_l⟩
      },
      case mp : φ ψ _ _ ih1 ih2
      {
        apply exists.elim ih1,
        intros s hsprop,
        apply exists.elim ih2,
        intros t htprop,
        exact ⟨s ++ t, list_subset_concat hsprop.left htprop.left,
                       conjunction_modpon hsprop.right htprop.right⟩
      },

    intro hex,
    apply exists.elim hex,
    intros s hsprop,
    revert φ,
    induction s,
      case nil
      {
        intros,
        apply entails.thm,
        simp at hsprop,
        exact Proof.modpon Proof.pl_notbot hsprop
      },
      case cons : ψ l ih
      {
        intros,
        simp at *,
        apply entails.mp,
          exact entails.mem hsprop.left.right,
          have h := and_lemma.mp hsprop.right,
          exact ih l hsprop.left.left h hsprop.left.left h
      }
end

end equivalent_entailment
