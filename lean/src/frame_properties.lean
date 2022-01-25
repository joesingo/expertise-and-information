import basic

namespace frame_conditions

variables {α : Type} {f : Frame α} {φ : Formula}

-- lemma: ESφ is valid on frames closed under intersections
lemma e_s_intersections :
  fclosed_under_intersections f -> valid_on_frame f (E (S φ)) :=
begin
  intros hcl m h_based x,
  simp,
  let ts_φ := {y | sat m y φ},
  let aa := {a | m.has_expertise a ∧ ts_φ ⊆ a},
  -- show the truth set of Sφ is the intersection of aa
  have heq : {y | ∀a, m.has_expertise a → ts_φ ⊆ a → y ∈ a} = ⋂₀aa, by
    apply set.ext; intros; simp,
  rw heq,
  -- since m is based on f which is closed under intersections, it suffices to
  -- show expertise on each a ∈ aa, but this is clear from the definition of aa
  apply (h_based ⋂₀aa).mpr,
  apply hcl aa,
  intros a ha_in_aa,
  apply (h_based a).mp,
  exact ha_in_aa.left
end

-- any non-empty frame f is closed under intersections iff A(Sφ -> φ) -> Eφ is
-- valid for all φ
--% latex_label: prop_frame_conditions
lemma intersection_frame_condition {α : Type} [inhabited α] {f : Frame α} :
  fclosed_under_intersections f <-> ∀ φ : Formula, valid_on_frame f ((A((S φ) ⇒ φ)) ⇒ (E φ)) :=
begin
  apply iff.intro,
    -- show that the scheme is valid whenever f is closed under intersections
    intros hcl φ m h_based x,
    intro ha_imp,
    simp,
    let a := {y | sat m y φ},
    let b := {y | sat m y (S φ)},
    have heq : a = b,
    {
      apply set.ext,
      intro y,
      apply iff.intro,
        -- if y ∈ a then y ∈ b since φ -> Sφ is valid
        intro hya,
        intros c hc_exp ha_ss_c,
        exact ha_ss_c hya,

        -- if y ∈ b then by the assumption that A(Sφ ⇒ φ) holds, y ∈ a
        intro hyb,
        exact ha_imp y hyb,
    },
    apply (h_based a).mpr,
    rw heq,
    apply (h_based b).mp,
    show m.has_expertise b, from e_s_intersections hcl m h_based x,

    -- show by contraposition that f is closed under intersections whenever the
    -- scheme is valid
    intro h,
    by_contradiction hcontr,
    apply absurd h,
    simp,
    -- assume there is some collection aa with expertise on each a ∈ aa but not
    -- on b := ⋂₀aa
    have hex : ∃aa, (∀ a ∈ aa, f.has_expertise a) ∧ ¬f.has_expertise ⋂₀aa, by
      simp at hcontr; assumption,
    apply exists.elim hex,
    intros aa h,
    let b := ⋂₀aa,
    -- construct a model where all atoms evaluate to b
    let val := λn x, x ∈ b,
    let m := Model.mk f val,
    have h_based : based_on_frame m f, by
      intro a; refl,
    let p := P 0,
    -- we have A(Sp -> p) ∧ ¬Ep (at all points)
    apply exists.intro p,
    apply exists.intro m,
    refine ⟨h_based, _, h.right⟩,
    intros y hsp,
    apply set.mem_sInter.mpr,
    intros a ha_in_aa,
    have hss : b ⊆ a, from set.sInter_subset_of_mem ha_in_aa,
    exact hsp a (h.left a ha_in_aa) hss
end

end frame_conditions
