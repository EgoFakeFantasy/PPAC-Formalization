import PPAC.Migration.OmegaStructureSyntax

/-! 用原Foundation和对象单元集证明任意内部集合不属于自身。 -/
namespace PPAC.Migration.ObjectIrreflexivity
open Source SourceAlgebra SourceLogic PairSyntax UnorderedPairLogic MinimalPredicates MinimalInstances

theorem singleton_irreflexive {m} {Γ : Context m} (x s : Fin m)
    (hf : Derives Γ (Source.SetLanguage.foundation.rename Fin.elim0))
    (hs : Derives Γ (pair s x x)) : Derives Γ (Formula.mem x x).neg := by
  have hi : Derives Γ (inhabited s) := by
    apply Derives.exI x
    simpa only [Formula.instantiate, Formula.rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
      using member_left s x x hs
  have hr := Derives.impE (foundation_instance s hf) hi
  let Z := setMinimal s.castSucc (Fin.last m)
  let Γz := Context.add Z (Context.image Formula.raise Γ)
  change Derives Γ (.ex Z) at hr
  apply Derives.exE (p := Z) hr
  have hsZ : Derives Γz (pair s.castSucc x.castSucc x.castSucc) := by
    simpa only [Formula.raise, pair_rename] using under hs Z
  have hZ : Derives Γz Z := .hyp (Or.inl rfl)
  have he := member_cases s.castSucc x.castSucc x.castSucc (Fin.last m) hsZ (.conjL hZ)
  have heq : Derives Γz (.equal (Fin.last m) x.castSucc) :=
    .disjE he (.hyp (Or.inl rfl)) (.hyp (Or.inl rfl))
  have hn := specialize_setMinimal s.castSucc (Fin.last m) x.castSucc hZ
  change Derives Γz (Formula.mem x.castSucc x.castSucc).neg
  apply Derives.impI
  have hxz := mem_container_subst x.castSucc (Fin.last m) x.castSucc
    (add (eq_symm heq) _) (.hyp (Or.inl rfl))
  exact .impE (.impE (add hn _) hxz) (member_left s.castSucc x.castSucc x.castSucc (add hsZ _))

theorem no_self_member {m} {Γ : Context m} (x : Fin m)
    (hf : Derives Γ (Source.SetLanguage.foundation.rename Fin.elim0))
    (hp : Derives Γ (Source.SetLanguage.pairing.rename Fin.elim0)) : Derives Γ (Formula.mem x x).neg := by
  have he := pairing_instance x x hp
  let S := pair (Fin.last m) x.castSucc x.castSucc
  let Γs := Context.add S (Context.image Formula.raise Γ)
  change Derives Γ (.ex S) at he
  apply Derives.exE (p := S) he
  have hfS : Derives Γs (Source.SetLanguage.foundation.rename Fin.elim0) := by
    simpa only [Formula.raise, closed_rename] using under hf S
  exact singleton_irreflexive x.castSucc (Fin.last m) hfS (.hyp (Or.inl rfl))

def sentence : Source.Sentence := ((Formula.mem (0 : Fin 1) 0).neg).close

def assumptions : Theory := fun q => q = Source.SetLanguage.foundation ∨ q = Source.SetLanguage.pairing

theorem source_proof : Derives (assumptions.at 0) sentence := by
  apply close_derives
  exact no_self_member 0 (.hyp ⟨_, Or.inl rfl, rfl⟩) (.hyp ⟨_, Or.inr rfl, rfl⟩)

theorem kernel_certificate : YesMetaZFC.Logic.FirstOrder.Derives (TheoryTransport.theory assumptions) []
    (Translation.sentence sentence) := TheoryTransport.sentence source_proof

theorem source_ZF : Derives (Source.SetLanguage.ZF.at 0) sentence := by
  refine Derives.weaken ?_ source_proof
  rintro q ⟨_, h, rfl⟩
  rcases h with rfl | rfl
  · exact ⟨_, Source.SetLanguage.IsZFAxiom.foundation, rfl⟩
  · exact ⟨_, Source.SetLanguage.IsZFAxiom.pairing, rfl⟩

theorem native_proof : YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence sentence) := by
  apply YesMetaZFC.Logic.FirstOrder.Derives.theory_cut (hFormula := kernel_certificate)
  rintro q ⟨_, h, rfl⟩
  rcases h with rfl | rfl
  · exact ZFEquivalence.source_foundation
  · exact ZFEquivalence.source_pairing
end PPAC.Migration.ObjectIrreflexivity
