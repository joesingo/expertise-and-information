import basic
import axiom_system

namespace soundness

--% latex_label: lemma_soundness_m
lemma thm_soundness : ∀ φ : Formula, ((⊢ φ) -> valid φ) :=
begin
  intros φ hproof,
  simp,
  intros _ m,
  induction hproof,
    case pl_refl { simp },
    case pl2 { simp, intros, assumption },
    case pl3 { simp, intros _ h1 h2 h3, exact h1 h3 (h2 h3) },
    case pl_mt
    {
      intro x,
      simp,
      intros h1 h2,
      by_contradiction hc,
      exact absurd h2 (h1 hc)
    },
    case pl_neg { intro x; simp; intro, assumption },
    case pl_negpair { intro x, simp, intros h1 h2, exact h2 h1 },
    case pl_false_elim : _ _ ih { intro x; apply absurd (ih x); simp },
    case pl_notbot { intro x, simp },
    case pl_dne { intro x, simp },
    case pl_and_intro { intros x h1 h2, simp, exact ⟨h2, h1⟩ },
    case pl_and_elim_l { intros x h, apply and.elim_left, exact h },
    case pl_and_elim_r { intros x h, apply and.elim_right, exact h },
    case pl_neg_imp
      { intros x, simp, intros, apply and.intro, repeat { assumption }},
    case pl_iff_intro
      { intros, simp, intros, apply iff.intro, repeat {assumption }},
    case pl_iff_elim
      { intros, simp, intro h, exact ⟨h.mp, h.mpr⟩ },
    case ea { intro x, apply iff.intro, intros h y, exact h, intro h, exact h x },
    case re : φ ψ
    {
      intros x h,
      let a := {y | sat m y φ},
      let b := {y | sat m y ψ},
      have heq : a = b, from set.ext h,
      show m.has_expertise a <-> m.has_expertise b, by rw heq
    },
    case we : φ ψ
    {
      intros x himp hse,
      apply hse.left,
        exact hse.right,

        intros y h,
        exact himp y h
    },
    case t : φ { intros x hφ a _ hss; exact (hss hφ) },
    case s4 : φ
    {
      intros x hss a hexp hsup,
      have hsubset : {y | sat m y (S φ)} ⊆ a, from λy, λh, h a hexp hsup,
      exact hss a hexp hsubset
    },
    case ws : φ ψ
    {
      intros x himp hsφ a hexp hsup,
      apply hsφ ,
        exact hexp,
        intros y hyφ,
        exact hsup (himp y hyφ)
    },
    case ka : φ ψ { intros x h haφ y; exact h y (haφ y) },
    case ta : φ { intros x h; exact h x },
    case a5 : φ
      { intros x hna y; by_contradiction hcontr; exact absurd (dne hcontr) hna },
    case nec_a : φ hφ ih { intros x y, exact ih y },
    case modpon : φ ψ hφ himp ih ih2 { intro x, exact (ih2 x) (ih x) }
end

theorem soundness :
  ∀ Γ : set Formula, ∀ φ : Formula, (entails Γ φ -> consequence Γ φ) :=
begin
  intros Γ φ hent,
  simp,
  intros α m x hsatΓ,
  induction hent,
    case thm : θ hproof { exact thm_soundness θ hproof α m x },
    case mem : θ hmem { exact hsatΓ θ hmem },
    case mp : _ _ _ _ ih1 ih2 { exact ih2 ih1 }
end

end soundness
