import PPAC.Migration.ReverseSubstitution
import PPAC.Migration.SourceQuantifiers

/-! 原核全部27逻辑公理模式逐项回放到原19规则，不增加源推导构造。 -/
namespace PPAC.Migration.ReverseLogicalAxioms
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open ReverseSubstitution
attribute [local implicit_reducible] SetTheory.signature

theorem replay {free : Syntax.Ctx} {p : Syntax.Fm [] free} {n} {Γ : Source.Context n}
    (h : HilbertBaseAxiom ℒ p) (f : Reverse.Vars free n) :
    Source.Derives Γ (Reverse.formula empty f p) := by
  cases h with
  | implication_distribution p q r =>
      exact SourcePropositional.imp_distribution (Reverse.formula empty f p) (Reverse.formula empty f q) (Reverse.formula empty f r)
  | self_implication p =>
      exact SourcePropositional.self_implication (Reverse.formula empty f p)
  | weakening p q =>
      exact SourcePropositional.weakening (Reverse.formula empty f p) (Reverse.formula empty f q)
  | contradiction p q =>
      exact SourcePropositional.contradiction (Reverse.formula empty f p) (Reverse.formula empty f q)
  | classical p =>
      exact SourcePropositional.classical (Reverse.formula empty f p)
  | explosion p q =>
      exact SourcePropositional.explosion (Reverse.formula empty f p) (Reverse.formula empty f q)
  | case_analysis p q =>
      exact SourcePropositional.case_analysis (Reverse.formula empty f p) (Reverse.formula empty f q)
  | truth_intro  =>
      exact SourcePropositional.truth_intro
  | falsum_elimination p =>
      exact SourcePropositional.falsum_elimination (Reverse.formula empty f p)
  | negation_intro p =>
      exact SourcePropositional.negation_intro (Reverse.formula empty f p)
  | negation_elimination p =>
      exact SourcePropositional.negation_elimination (Reverse.formula empty f p)
  | conjunction_intro p q =>
      exact SourcePropositional.conjunction_intro (Reverse.formula empty f p) (Reverse.formula empty f q)
  | conjunction_elim_left p q =>
      exact SourcePropositional.conjunction_elim_left (Reverse.formula empty f p) (Reverse.formula empty f q)
  | conjunction_elim_right p q =>
      exact SourcePropositional.conjunction_elim_right (Reverse.formula empty f p) (Reverse.formula empty f q)
  | disjunction_intro_left p q =>
      exact SourcePropositional.disjunction_intro_left (Reverse.formula empty f p) (Reverse.formula empty f q)
  | disjunction_intro_right p q =>
      exact SourcePropositional.disjunction_intro_right (Reverse.formula empty f p) (Reverse.formula empty f q)
  | disjunction_elimination p q r =>
      exact SourcePropositional.disjunction_elimination (Reverse.formula empty f p) (Reverse.formula empty f q) (Reverse.formula empty f r)
  | biconditional_intro p q =>
      exact SourcePropositional.conjunction_intro _ _
  | biconditional_elim_left p q =>
      exact SourcePropositional.conjunction_elim_left _ _
  | biconditional_elim_right p q =>
      exact SourcePropositional.conjunction_elim_right _ _
  | forall_specialization sort body term =>
      cases sort
      simp only [Reverse.formula, instantiate_top]
      exact SourceQuantifiers.forall_specialization _ _
  | forall_distribution sort p q =>
      cases sort
      simp only [Reverse.formula, forall_top]
      exact SourceQuantifiers.forall_distribution _ _
  | vacuous_forall sort p =>
      cases sort
      simp only [Reverse.formula, forall_top, fresh_raise]
      exact SourceQuantifiers.vacuous_forall _
  | exists_introduction sort body term =>
      cases sort
      simp only [Reverse.formula, instantiate_top]
      exact SourceQuantifiers.exists_introduction _ _
  | exists_elimination sort p q =>
      cases sort
      simp only [Reverse.formula, forall_top, exists_top, fresh_raise]
      exact SourceQuantifiers.exists_elimination _ _
  | equality_substitution sort left right body =>
      cases sort
      simp only [Reverse.formula, instantiate_top]
      exact SourceQuantifiers.equality_substitution _ _ _
  | equality_reflexivity term =>
      exact .eqRefl _
end PPAC.Migration.ReverseLogicalAxioms
