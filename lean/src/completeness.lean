import data.set.countable
import data.real.basic
import data.real.cardinality

import basic
import axiom_system
import parser

-- in this section we use x, y etc for maximally consistent sets
namespace completeness

def X := {x | mcs x}

-- relation on MCSes
@[simp] def r : relation X :=
  λx, λy, ∀φ, (A φ) ∈ (x : set Formula) -> φ ∈ (y : set Formula)

-- equivalence class of x under r
@[simp] def eqc (x : X) : set X := {y | r x y}

-- prove some properties of the relation r
--% latex_label: lemma_r_equiv_reln
lemma r_reflexive {x : X} : r x x :=
begin
  intro φ,
  intro hmem,
  have hmcs : mcs ↑x, from subtype.mem x,
  apply consistency.mem_modpon hmcs hmem,
  apply consistency.theorems hmcs,
  exact Proof.ta
end

lemma r_euclidean {x y z : X} : r x y -> r x z -> r y z :=
begin
  intros hrxy hrxz φ haφ_in_y,
  -- suppose for contradiction that Aφ ∈ y but φ ∉ z. we will show this
  -- contradicts consistency of y by showing ¬Aφ ∈ y
  by_contradiction hcontr,
  suffices : (#A φ) ∈ (y : set Formula),
  {
    apply absurd (subtype.mem y).left,
    simp,
    exact (consistency.mem_neg_pair haφ_in_y this)
  },
  -- for this we show A¬Aφ ∈ x and use r x y
  apply hrxy,
  have h : (A φ) ∉ (x : set Formula),
  {
    by_contradiction hcontr2,
    apply absurd hcontr,
    simp,
    exact hrxz φ hcontr2
  },
  -- since Aφ ∉ x, we have ¬Aφ ∈ x and hence A¬Aφ ∈ x by axiom 5 and mp
  have hxmcs : (x : set Formula) ∈ X, from subtype.mem x,
  apply consistency.mem_modpon hxmcs,
    exact (consistency.negations hxmcs).mpr h,
    apply consistency.theorems hxmcs,
    exact Proof.a5
end

--% latex_label: lemma_r_equiv_reln
lemma r_symmetric {x y : X} : r x y -> r y x :=
begin
  intro hrxy,
  apply r_euclidean hrxy,
  exact r_reflexive
end

--% latex_label: lemma_r_equiv_reln
lemma r_transitive {x y z : X} : r x y -> r y z -> r x z :=
begin
  intros hrxy hryz,
  have hryx : r y x, by apply r_symmetric; exact hrxy,
  exact r_euclidean hryx hryz
end

-- define the canonical model for x. states are pairs (y, t) where y ∈ eqc x
-- and t ∈ ℝ
def state_type (x : X) : Type := (eqc x) × ℝ

-- the "proof set" of φ are those (y, t) where φ ∈ y
@[simp] def proof_set (x : X) (φ : Formula) : set (state_type x) :=
  {p | φ ∈ (p.fst : set Formula)}

-- critical notion used in the canonical model construction
def s_closed (x : X) (a : set (state_type x)) :=
  ∀ φ : Formula, proof_set x φ ⊆ a -> proof_set x (S φ) ⊆ a

-- expertise function for the canonical model. we have expertise on a set a
-- iff either a is the proof set of some φ where Eφ ∈ x, or if a is s-closed
-- and not equal to any proof set
@[simp] def exp (x : X) (a : set (state_type x)) :=
  (∃ φ : Formula, (E φ) ∈ (x : set Formula) ∧ a = proof_set x φ)
  ∨ (s_closed x a ∧ ¬∃ φ : Formula, a = proof_set x φ)

-- finally, define the canonical frame and model
def frame (x : X) : Frame (state_type x) :=
  let h : x ∈ eqc x := r_reflexive in
  let some : ∃ y : (state_type x), true := ⟨(⟨x, h⟩, 0), trivial⟩ in
  Frame.mk (exp x)
def model (x : X) : Model (state_type x) :=
  let val : ℕ -> state_type x -> Prop := λn, λp, (P n) ∈ (p.fst : set Formula) in
  Model.mk (frame x) val

-- canonical truth set of φ
@[simp] def truth_set (x : X) (φ : Formula) : set (state_type x) :=
  {p | sat (model x) p φ}

-- preliminary results required to prove the truth lemma

-- we have Aφ ∈ x iff all y ∈ eqc contain φ
--% latex_label: lemma_xsigma_properties
lemma a_mem {φ : Formula} (x : X) :
  (A φ) ∈ (x : set Formula) <-> ∀ y : X, r x y -> φ ∈ (y : set Formula) :=
begin
  apply iff.intro,
    intros hmem y hr,
    exact hr φ hmem,

    intro hall,
    by_contradiction hcontr,
    let y := {ψ | (A ψ) ∈ (x : set Formula)},
    let z := y ∪ {#φ},
    have hzcons : cons z,
    {
      by_contradiction hcontr2,
      apply absurd hcontr,
      simp,
      have hxmcs : mcs x, from subtype.mem x,
      apply (consistency.membership hxmcs).mpr,
      let x' := {(A ψ) | ψ ∈ y},
      have hss : x' ⊆ x,
      {
        intros θ hmem,
        apply exists.elim hmem,
        intros ψ hex,
        apply exists.elim hex,
        intros hmem2 heq,
        rw <-heq,
        exact hmem2
      },
      apply consistency.entailment_monotone hss,
      apply consistency.a_prefix_imp,
      refine entails.mp _ (entails.thm Proof.pl_dne),
      exact consistency.incons_implies_entails (dne hcontr2)
    },
    apply exists.elim (consistency.lindenbaum hzcons),
    intros w₀ hextend,
    let w : X := ⟨w₀, hextend.right⟩,
    have hrxw : r x w,
    {
      intros ψ hmem,
      apply set.mem_of_subset_of_mem hextend.left,
      apply set.mem_union_left,
      exact hmem
    },
    have hwnφ : (#φ) ∈ ↑w,
    {
      apply set.mem_of_subset_of_mem hextend.left,
      apply set.mem_union_right,
      simp
    },
    apply absurd hextend.right.left,  -- contradict cons of w
    simp,
    apply consistency.mem_neg_pair,
      show φ ∈ w₀, from (hall w hrxw),
      show (#φ) ∈ w₀, from hwnφ
end

-- x and (y, t) contain the same A formulas
--% latex_label: cor_xsigma_agree_on_ae
lemma a_mem_same {φ : Formula} (x : X) (p : state_type x):
  (A φ) ∈ (x : set Formula) <-> (A φ) ∈ (p.fst : set Formula) :=
begin
  let y : X := p.fst,
  have hrxy : r x y, from subtype.mem p.fst,
  apply iff.intro,
    intro hmem_x,
    apply (a_mem y).mpr,
    intros z hryz,
    have hrxz : r x z, from r_transitive hrxy hryz,
    exact (a_mem x).mp hmem_x z hrxz,

    intro hmem_p,
    apply (a_mem x).mpr,
    intros z hrxz,
    have hryz : r y z, from r_euclidean hrxy hrxz,
    exact (a_mem y).mp hmem_p z hryz,
end

-- likewise for E formulas
--% latex_label: cor_xsigma_agree_on_ae
lemma e_mem_same {φ : Formula} (x : X) (p : state_type x):
  (E φ) ∈ (x : set Formula) <-> (E φ) ∈ (p.fst : set Formula) :=
begin
  have hxmcs : mcs x, from subtype.mem x,
  have hpmcs : (p.fst : set Formula) ∈ X, from subtype.mem ↑(p.fst),
  have h1 := consistency.exp hxmcs,
  have h2 := consistency.exp hpmcs,
  apply (iff_congr h1 h2).mpr,
  exact a_mem_same x p
end

--% latex_label: lemma_xsigma_properties
lemma a_implications {φ ψ : Formula} (x : X) :
  (A (φ ⇒ ψ)) ∈ (x : set Formula) <-> proof_set x φ ⊆ proof_set x ψ :=
begin
  apply iff.intro,
    intros haimp p hmem,
    have hr : r x p.fst, from subtype.mem p.fst,
    have himp_mem := (a_mem x).mp haimp (p.fst) hr,
    have hmcs : (p.fst : set Formula) ∈ X, from subtype.mem p.fst,
    exact (consistency.implications hmcs).mp himp_mem hmem,

    intros hss,
    apply (a_mem x).mpr,
    intros y hr,
    have hmcs : ↑y ∈ X, from subtype.mem y,
    apply (consistency.implications hmcs).mpr,
    intro hmem_φ,
    let p : state_type x := ⟨⟨y, hr⟩, 0⟩,
    have hpmem : p ∈ proof_set x φ, from hmem_φ,
    exact hss hpmem,
end

--% latex_label: lemma_xsigma_properties
lemma a_iffs {φ ψ : Formula} (x : X) :
  (A (φ ⇔ ψ)) ∈ (x : set Formula) <-> proof_set x φ = proof_set x ψ :=
begin
  have h1 : (A (φ ⇔ ψ)) ∈ (x : set Formula) <->
            (A (φ ⇒ ψ)) ∈ (x : set Formula) ∧ (A (ψ ⇒ φ)) ∈ (x : set Formula),
  {
    apply iff.intro,
      intro hiff,
      apply and.intro,
        apply (a_mem x).mpr,
        intros y hrxy,
        have hy_iff : (φ ⇔ ψ) ∈ (y : set Formula), from
          (a_mem x).mp hiff y hrxy,
        have hmcs : (y : set Formula) ∈ X, from subtype.mem y,
        apply consistency.mem_modpon hmcs,
          apply consistency.mem_modpon hmcs hy_iff,
          apply consistency.theorems hmcs,
          exact Proof.pl_iff_elim,
          apply consistency.theorems hmcs,
          exact Proof.pl_and_elim_l,

        -- TODO: avoid repetition. only change is right and elimination in the
        -- final step
        apply (a_mem x).mpr,
        intros y hrxy,
        have hy_iff : (φ ⇔ ψ) ∈ (y : set Formula), from
          (a_mem x).mp hiff y hrxy,
        have hmcs : (y : set Formula) ∈ X, from subtype.mem y,
        apply consistency.mem_modpon hmcs,
          apply consistency.mem_modpon hmcs hy_iff,
          apply consistency.theorems hmcs,
          exact Proof.pl_iff_elim,
          apply consistency.theorems hmcs,
          exact Proof.pl_and_elim_r,

      intros himps,
      apply (a_mem x).mpr,
      intros y hrxy,
      have h1 : (φ ⇒ ψ) ∈ (y : set Formula), from
        (a_mem x).mp himps.left y hrxy,
      have h2 : (ψ ⇒ φ) ∈ (y : set Formula), from
        (a_mem x).mp himps.right y hrxy,
      have hmcs : (y : set Formula) ∈ X, from subtype.mem y,
      apply consistency.mem_modpon hmcs h2,
      apply consistency.mem_modpon hmcs h1,
      apply consistency.theorems hmcs,
      exact Proof.pl_iff_intro
  },

  have hmcs : ↑x ∈ X, from subtype.mem x,
  have h2 := set.subset.antisymm_iff,
  apply (iff_congr h1 h2).mpr,
  exact and_congr (@a_implications φ ψ x) (@a_implications ψ φ x)
end

--% latex_label: lemma_truth_lemma
lemma truth_lemma (x : X) (φ : Formula) : truth_set x φ = proof_set x φ :=
begin
  induction φ,
    case atom : n
    {
      simp,
      apply set.ext,
      intros,
      simp,
      refl,
    },
    case and : φ ψ ihφ ihψ
    {
      have h1 : truth_set x (φ & ψ) = (truth_set x φ) ∩ (truth_set x ψ),
        by apply set.ext; simp,
      have h2 : proof_set x (φ & ψ) = (proof_set x φ) ∩ (proof_set x ψ),
      {
        apply set.ext,
        simp,
        intros p,
        have hmcs : (p.fst : set Formula) ∈ X, from subtype.mem (↑p.fst),
        exact consistency.conjunctions hmcs
      },
      rw [h1, h2, ihφ, ihψ],
    },
    case neg : φ ih
    {
      have h1 : truth_set x (# φ) = (truth_set x φ)ᶜ, by apply set.ext; simp,
      have h2 : proof_set x (# φ) = (proof_set x φ)ᶜ,
      {
        apply set.ext,
        simp,
        intro p,
        have hmcs : (p.fst : set Formula) ∈ X, from subtype.mem (↑p.fst),
        apply consistency.negations hmcs
      },
      rw [h1, h2, ih]
    },
    case implies : φ ψ ihφ ihψ
    {
      apply set.ext,
      intro p,
      have hmcs : (p.fst : set Formula) ∈ X, from subtype.mem (↑p.fst),
      have h1 : p ∈ truth_set x (φ ⇒ ψ) <-> (p ∈ (truth_set x φ) -> p ∈ (truth_set x ψ)), by
        simp,
      have h2 : p ∈ proof_set x (φ ⇒ ψ) <-> (p ∈ (proof_set x φ) -> p ∈ (proof_set x ψ)),
      {
        simp,
        exact consistency.implications hmcs
      },
      apply (iff_congr h1 h2).mpr,
      rw [ihφ, ihψ]
    },
    case iff : φ ψ ihφ ihψ
    {
      -- very similar to the case for implies
      apply set.ext,
      intro p,
      have hmcs : (p.fst : set Formula) ∈ X, from subtype.mem (↑p.fst),
      have h1 : p ∈ truth_set x (φ ⇔ ψ) <-> (p ∈ (truth_set x φ) <-> p ∈ (truth_set x ψ)), by
        simp,
      have h2 : p ∈ proof_set x (φ ⇔ ψ) <-> (p ∈ (proof_set x φ) <-> p ∈ (proof_set x ψ)),
      {
        simp,
        exact consistency.iffs hmcs
      },
      apply (iff_congr h1 h2).mpr,
      rw [ihφ, ihψ]
    },
    case exp : φ ih
    {
      apply set.ext,
      intro p,
      have hmcs : (p.fst : set Formula) ∈ X, from subtype.mem (↑p.fst),
      simp,
      apply iff.intro,
        -- suppose we have expertise on φ in the canonical model
        intro hexp,
        -- there are two cases
        apply or.elim hexp,
          -- in the first case there is ψ st Eψ ∈ x and φ, ψ have the same
          -- proof set
          intro h,
          apply exists.elim h,
          intros ψ H,
          have h1 : (E ψ) ∈ (p.fst : set Formula), from
            (e_mem_same x p).mp H.left,
          have h2 : proof_set x φ = proof_set x ψ, by
            rw <-ih; exact H.right,
          have h3 : (A (φ ⇔ ψ)) ∈ (x : set Formula), from (a_iffs x).mpr h2,
          have h4 : (A (φ ⇔ ψ)) ∈ (p.fst : set Formula), from
            (a_mem_same x p).mp h3,
          have h5 : (E φ ⇔ E ψ) ∈ (p.fst : set Formula), from
            consistency.mem_modpon hmcs h4
            (consistency.theorems hmcs Proof.re),
          show (E φ) ∈ (p.fst : set Formula), from
            ((consistency.iffs hmcs).mp h5).mpr h1,

          -- we get a contradiction in the second case from IH, so conclude
          -- by ex falso
          intro h,
          exfalso,
          apply absurd h.right,
          simp,
          exact ⟨φ, ih⟩,

        intro hmem,
        have h : (E φ) ∈ (x : set Formula), from (e_mem_same x p).mpr hmem,
        apply or.inl,
        existsi φ,
        apply and.intro,
          exact h,
          rw <-ih,
          refl,
    },
    case sound : φ ih
    {
      apply set.ext,
      intro p,
      apply iff.intro,
        -- for contradiction, suppose Sφ ∉ p.fst
        intro h,
        by_contradiction hcontr,
        apply absurd h,
        simp,
        let u := {a | (∃ ψ, a = proof_set x ψ) ∧ ¬(a ⊆ proof_set x (S φ))},
        -- since each a ∈ u have a ⊈ (ps Sφ), use axiom of choice to get a
        -- function f such that f a ∈ a \ (ps Sφ)
        have hch : ∀ (a : ↥u), ∃ (q : state_type x), q ∈ ↑a ∧ q ∉ proof_set x (S φ),
        {
          intros a,
          have ha_in_u : ↑a ∈ u, from subtype.mem a,
          apply exists.elim (set.not_subset.mp ha_in_u.right),
          intros q hex,
          apply exists.elim hex,
          intros h1 h2,
          apply exists.intro q,
          exact ⟨h1, h2⟩
        },
        apply exists.elim (classical.axiom_of_choice hch),
        intros f hfprop,
        -- collect all the f a into a set together with p
        let d₀ := set.range f,
        let d := set.insert p d₀,
        -- since each a ∈ u corresponds to some ψ, u and thus d are countable
        have hu_count : set.countable u,
        {
          suffices : u ⊆ (proof_set x) '' (set.univ),
          {
            apply set.countable.mono this,
            apply set.countable.image parser.countably_many_formulas
          },
          simp,
          intros a ha_in_u,
          simp,
          apply exists.elim ha_in_u.left,
          intros ψ heq,
          apply exists.intro ψ,
          symmetry,
          exact heq,
        },
        have hu_enc : encodable ↥u, from set.countable.to_encodable hu_count,
        have hd_count : set.countable d,
        {
          apply set.countable.insert p,
          -- need to reset class instance cache so lean knows u is encodable
          tactic.reset_instance_cache,
          apply set.countable_range f,
        },
        apply exists.elim (set.countable_iff_exists_inj_on.mp hd_count),
        intros fd hfd_inj,
        have hex : ∃ s : ℝ, (p.fst, s) ∉ d,
        {
          -- assuming the contrary, we get a contradiction by showing ℝ is
          -- countable
          by_contradiction hcontr,
          apply absurd cardinal.not_countable_real,
          simp,
          apply set.countable_iff_exists_inj_on.mpr,
          let g : ℝ → state_type x := λt, (p.fst, t),
          apply exists.intro (fd ∘ (λt, (p.fst, t))),
          apply set.inj_on.comp hfd_inj,
            -- show g is injective (on set.univ : ℝ)
            intros t1 _ t2 _ heq,
            exact (prod.mk.inj heq).right,
            -- show g maps into d
            intros t _,
            apply dne,
            have h := (forall_not_of_not_exists hcontr t),
            exact h
        },
        -- construct the set a which will be a counterexample for soundness in
        -- the canonical model
        apply exists.elim hex,
        intros s hsprop,
        let a := set.insert (p.fst, s) (proof_set x (S φ)),
        have hp_notin_a : p ∉ a,
        {
          by_contradiction hcontr2,
          apply or.elim (set.eq_or_mem_of_mem_insert hcontr2),
            -- if p = (p.fst, s) then by the property of s we have p ∉ d, but
            -- this contradicts the definition of d
            intro heq,
            have heq' : (p.fst, p.snd) = (p.fst, s), by simp; exact heq,
            apply absurd hsprop,
            simp,
            rw <-(prod.mk.inj heq').right,
            simp,
            exact set.mem_insert p _,

            -- p ∈ ps Sφ contradicts our original assumption
            intro,
            contradiction,
        },
        apply exists.intro a,
        apply and.intro,
          -- show expertise on a. we show the second property in the definition
          -- of expertise in the canonical model
          apply or.inr,
          apply and.intro,
            -- show a is s-closed. it suffices that whenever ps ψ ⊆ a we have ps
            -- Sψ ⊆ ps Sφ; by earlier lemmas this is equivalent to A(Sψ ⇒ Sφ) ∈ x
            intros ψ hψ_ss_a,
            suffices : proof_set x (S ψ) ⊆ proof_set x (S φ),
            {
              have hss : proof_set x (S φ) ⊆ a, from set.subset_insert _ _,
              exact set.subset.trans this hss
            },
            -- by construction of a we in fact have ps ψ ⊆ ps Sφ
            have hψ_ss_Sφ : proof_set x ψ ⊆ proof_set x (S φ),
            {
              -- suppose otherwise. then taking b = ps ψ we have b ∈ u. hence
              -- setting q = f b we have q ∈ ps ψ and q ∉ ps Sφ. from ps ψ ⊆ a we
              -- get q = (p.fst, s). but by definition of d₀ we also have q ∈ d₀
              -- ⊆ d, which contradicts the property of s
              by_contradiction hnss,
              apply absurd hsprop,
              simp,
              apply set.mem_insert_of_mem _,
              simp,
              let b := (proof_set x ψ),
              have hb_in_u : b ∈ u, from ⟨⟨ψ, refl b⟩, hnss⟩,
              let b' : ↥u := ⟨b, hb_in_u⟩,
              let q := f b',
              have hq_in_a : q ∈ a, from
                set.mem_of_subset_of_mem hψ_ss_a (hfprop b').left,
              apply exists.intro b,
              apply exists.intro,
                apply or.elim (set.eq_or_mem_of_mem_insert hq_in_a),
                  intro h,
                  rw <-h,

                  intros,
                  exfalso,
                  have h := (hfprop b').right,
                  contradiction,
                exact hb_in_u,
            },
            have hmem_x : (A(ψ ⇒ (S φ))) ∈ ↑x, from
              (a_implications x).mpr hψ_ss_Sφ,
            intros q hsψ_mem_q,
            have ha_mem_q : (A(ψ ⇒ (S φ))) ∈ (q.fst : set Formula), from
              (a_mem_same x q).mp hmem_x,
            simp,
            have hmcs : (q.fst : set Formula) ∈ X, from subtype.mem q.fst,
            have h1 := consistency.mem_modpon hmcs ha_mem_q
                        (consistency.theorems hmcs Proof.ws),
            have h2 := consistency.mem_modpon hmcs hsψ_mem_q h1,
            show (S φ) ∈ (q.fst : set Formula), from
              consistency.mem_modpon hmcs h2
                (consistency.theorems hmcs Proof.s4),

            -- show a is not equal to any proof set. indeed, if a = ps θ then
            -- since (p.fst, s) ∈ a, we have θ ∈ p.fst. hence p ∈ ps θ = a, which
            -- is a contradiction
            by_contradiction hex,
            apply exists.elim hex,
            intros θ hθ,
            apply absurd hp_notin_a,
            simp,
            rw hθ,
            simp,
            have h : (p.fst, s) ∈ proof_set x θ, by
              rw <-hθ; exact set.mem_insert _ _,
            exact h,

          -- show a contains ts φ
          -- suffices to show ps Φ ⊆ ps Sφ by IH
          apply and.intro,
          suffices : proof_set x φ ⊆ proof_set x (S φ),
          {
            have hts_def : {q | sat (model x) q φ} = truth_set x φ, by simp,
            rw [hts_def, ih],
            have hss : proof_set x (S φ) ⊆ a, from set.subset_insert _ _,
            exact set.subset.trans this hss
          },
          apply (a_implications x).mp,
          apply consistency.theorems (subtype.mem x),
          exact Proof.nec_a Proof.t,

          -- show p ∉ a
          exact hp_notin_a,

        intros hmem a hexp hss,
        apply or.elim hexp,
          intro h,
          apply exists.elim h,
          intros ψ hprop,
          rw hprop.right,
          simp,
          let y : X := p.fst,
          have hmcs : (y : set Formula) ∈ X, from subtype.mem p.fst,
          have hs_e : ((S φ) & (E ψ)) ∈ (y : set Formula),
          {
            apply (consistency.conjunctions hmcs).mpr,
            exact ⟨hmem, (e_mem_same x p).mp hprop.left⟩,
          },
          have ha_imp : (A (φ ⇒ ψ)) ∈ (y : set Formula),
          {
            apply (a_mem_same x p).mp,
            apply (a_implications x).mpr,
            rw <-hprop.right,
            rw <-ih,
            exact hss
          },
          apply consistency.mem_modpon hmcs hs_e,
          apply consistency.mem_modpon hmcs ha_imp,
          apply consistency.theorems hmcs,
          apply Proof.we,

          intro h,
          have hss : proof_set x (S φ) ⊆ a, by
            refine h.left φ _; rw <-ih; exact hss,
          apply set.mem_of_subset_of_mem hss,
          exact hmem
    },
    case univ : φ ih
    {
      apply set.ext,
      intro p,
      apply iff.intro,
        intro h,
        simp,
        apply (a_mem p.fst).mpr,
        intros y hrpy,
        have hrxp : r x p.fst, from subtype.mem p.fst,
        have hrxy : r x y, from r_transitive hrxp hrpy,
        let p' : state_type x := ⟨⟨y, hrxy⟩, 0⟩,
        have hts : p' ∈ truth_set x φ, by simp; exact h p',
        have hps : p' ∈ proof_set x φ, by rw <-ih; exact hts,
        show φ ∈ ↑y, from hps,

        intro h,
        simp,
        intro p',
        apply (set.ext_iff.mp ih p').mpr,
        have hrp : r x p.fst, from subtype.mem p.fst,
        have hrp' : r x p'.fst, from subtype.mem p'.fst,
        have hrpp' : r p.fst p'.fst, from r_euclidean hrp hrp',
        exact (a_mem p.fst).mp h p'.fst hrpp'
    },
    case falsum
    {
      apply set.ext,
      intro p,
      simp,
      have h : (p.fst : set Formula) ∈ X, from subtype.mem p.fst,
      exact consistency.falsum h
    }
end

-- alternative statement of the truth lemma
lemma truth_lemma2 (x : X) (φ : Formula) (p : state_type x) :
  sat (model x) p φ <-> φ ∈ (p.fst : set Formula) :=
begin
  have h1 : sat (model x) p φ <-> p ∈ truth_set x φ, by refl,
  have h2 : φ ∈ (p.fst : set Formula) <-> p ∈ proof_set x φ, by refl,
  apply (iff_congr h1 h2).mpr,
  exact set.ext_iff.mp (truth_lemma x φ) p
end

-- strong completeness
--% latex_label: thm_strong_completeness
theorem strong_completeness :
  ∀ Γ : set Formula, ∀ φ : Formula, (consequence Γ φ -> entails Γ φ) :=
begin
  introv hconseq,
  by_contradiction hnent,
  let Δ := Γ ∪ {#φ},
  have hss : Γ ⊆ Δ, from set.subset_union_left _ _,
  have hcons : cons Δ, from consistency.not_entails_implies_cons hnent,
  apply exists.elim (consistency.lindenbaum hcons),
  intros x₀ hextend,
  let x : X := ⟨x₀, hextend.right⟩,
  let p : state_type x := (⟨x, r_reflexive⟩, 0),
  let m := model x,
  have hsatΔ : ∀ ψ ∈ Δ, sat m p ψ,
  {
    intros ψ hmem,
    apply (truth_lemma2 x ψ p).mpr,
    apply set.mem_of_subset_of_mem hextend.left,
    exact hmem
  },
  have hsatΓ : ∀ ψ ∈ Γ, sat m p ψ, from
    λψ, λh, hsatΔ ψ (set.mem_of_subset_of_mem hss h),
  apply absurd (hconseq _ m p hsatΓ),
  apply hsatΔ (#φ),
  apply set.singleton_subset_iff.mp,
  exact set.subset_union_right _ _
end

end completeness
