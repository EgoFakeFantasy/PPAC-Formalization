/- Pinned GermSelectors.pattern_covariance uses left multiplication on the
whole germ quotient. Descend the existing permutation composition through
Same; construct its actual bijection graph without choosing representatives. -/
import PPAC.Migration.ConstructionGermRowCovariance

namespace PPAC.Migration.ConstructionGermLeftAction
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ForcingSupportSize (MapsTo Injection)
open ForcingConditionGraphs (Permutation CompositionGraph InverseGraph function_input function_unique)
open ConstructionGermCosets (Agree Same Class Classes Carrier)
open ConstructionComponentCofinal (Chain)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

theorem agree_left_iff {I A pi g h pg ph : M.Carrier .set}
    (hAI : (Project.FirstOrderSemantics.reduct M).MemberSubset A I)
    (hpi : Permutation I pi) (hg : MapsTo I I g) (hh : MapsTo I I h)
    (hpg : CompositionGraph I pi g pg) (hph : CompositionGraph I pi h ph) :
    Agree A pg ph ↔ Agree A g h := by
  constructor
  · intro he x y hx
    constructor
    · intro hxy
      obtain ⟨z,hyz,_⟩ := hpi.1.1.2 y (hg.2 x y hxy)
      obtain ⟨_,y',hxy',hy'z⟩ := (hph x z).mp ((he x z hx).mp ((hpg x z).mpr ⟨hAI x hx,y,hxy,hyz⟩))
      have e := hpi.2.1 y y' z hyz hy'z
      exact e.symm ▸ hxy'
    · intro hxy
      obtain ⟨z,hyz,_⟩ := hpi.1.1.2 y (hh.2 x y hxy)
      obtain ⟨_,y',hxy',hy'z⟩ := (hpg x z).mp ((he x z hx).mpr ((hph x z).mpr ⟨hAI x hx,y,hxy,hyz⟩))
      have e := hpi.2.1 y y' z hyz hy'z
      exact e.symm ▸ hxy'
  · intro he x z hx
    exact (hpg x z).trans ((and_congr Iff.rfl (exists_congr (fun y => and_congr (he x y hx) Iff.rfl))).trans (hph x z).symm)

theorem same_left_iff {w D I mul q zero root vertices chain pi g h pg ph : M.Carrier .set}
    (hChain : Chain w D I mul q zero root vertices chain)
    (hpi : Permutation I pi) (hg : MapsTo I I g) (hh : MapsTo I I h)
    (hpg : CompositionGraph I pi g pg) (hph : CompositionGraph I pi h ph) :
    Same w D chain pg ph ↔ Same w D chain g h := by
  constructor
  · rintro ⟨n,v,r,a,U,A,hn,hnv,hCode,hA,he⟩
    exact ⟨n,v,r,a,U,A,hn,hnv,hCode,hA,(agree_left_iff (ConstructionGermCosets.stage_range_subset hChain hnv hCode hA) hpi hg hh hpg hph).mp he⟩
  · rintro ⟨n,v,r,a,U,A,hn,hnv,hCode,hA,he⟩
    exact ⟨n,v,r,a,U,A,hn,hnv,hCode,hA,(agree_left_iff (ConstructionGermCosets.stage_range_subset hChain hnv hCode hA) hpi hg hh hpg hph).mpr he⟩

def At (w D I chain H pi C E : M.Carrier .set) : Prop := ∃ g product,
  (Project.FirstOrderSemantics.reduct M).mem g H ∧ (Project.FirstOrderSemantics.reduct M).mem product H ∧
    Class w D chain H g C ∧ Class w D chain H product E ∧ CompositionGraph I pi g product

def atFormula {m : Nat} (w D I chain H pi C E : Fin m) : Project.Formula 1 m :=
  .existsE (.existsE (.conj (.mem (.bound 1) (.bound H.succ.succ))
    (.conj (.mem (.bound 0) (.bound H.succ.succ))
      (.conj (ConstructionGermCosets.eqClass w.succ.succ D.succ.succ chain.succ.succ H.succ.succ 1 C.succ.succ)
        (.conj (ConstructionGermCosets.eqClass w.succ.succ D.succ.succ chain.succ.succ H.succ.succ 0 E.succ.succ)
          (ProjectSyntax.encode id (ForcingConditionGraphs.compositionGraph I.succ.succ pi.succ.succ 1 0)))))))

theorem atFormula_freeClosed {m : Nat} (w D I chain H pi C E : Fin m) :
    (atFormula w D I chain H pi C E).FreeClosed := by
  simp -implicitDefEqProofs [atFormula,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,ConstructionGermCosets.eqClass_freeClosed]

theorem atFormula_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w D I chain H pi C E : Fin m) :
    Project.Formula.satisfies env (atFormula w D I chain H pi C E) ↔
      At (env.bound w) (env.bound D) (env.bound I) (env.bound chain) (env.bound H) (env.bound pi) (env.bound C) (env.bound E) := by
  simp only [atFormula,At,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,ConstructionGermCosets.eqClass_semantics hM,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),ForcingConditionGraphs.compositionGraph_semantics (M := M)]
  rfl

theorem at_unique (hM : FirstOrder.Theory.Models M nativeZF)
    {w D I mul q zero root vertices chain H pi C E F : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w) (hChain : Chain w D I mul q zero root vertices chain)
    (hH : Carrier D I mul q root H) (hpi : Permutation I pi)
    (he : At w D I chain H pi C E) (hf : At w D I chain H pi C F) : E = F := by
  obtain ⟨g,pg,hg,_,hgC,hpgE,hpg⟩ := he
  obtain ⟨h,ph,hh,_,hhC,hphF,hph⟩ := hf
  have hSame := (ConstructionGermCosets.class_eq_iff hM hw (function_input hChain.1.1 hChain.2.1) hChain hh hgC hhC).mp rfl
  exact ConstructionGermCosets.class_eq_of_same hM hw hChain hpgE hphF
    ((same_left_iff hChain hpi ((hH g).mp hg).1.1 ((hH h).mp hh).1.1 hpg hph).mpr hSame)

theorem at_injective (hM : FirstOrder.Theory.Models M nativeZF)
    {w D I mul q zero root vertices chain H pi C E F : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w) (hChain : Chain w D I mul q zero root vertices chain)
    (hH : Carrier D I mul q root H) (hpi : Permutation I pi)
    (hc : At w D I chain H pi C F) (he : At w D I chain H pi E F) : C = E := by
  obtain ⟨g,pg,hg,_,hgC,hpgF,hpg⟩ := hc
  obtain ⟨h,ph,hh,hphH,hhE,hphF,hph⟩ := he
  have hSame := (ConstructionGermCosets.class_eq_iff hM hw (function_input hChain.1.1 hChain.2.1) hChain hphH hpgF hphF).mp rfl
  exact ConstructionGermCosets.class_eq_of_same hM hw hChain hgC hhE
    ((same_left_iff hChain hpi ((hH g).mp hg).1.1 ((hH h).mp hh).1.1 hpg hph).mp hSame)

theorem at_total (hM : FirstOrder.Theory.Models M nativeZF)
    {w D I mul unit q root chain H G pi C : M.Carrier .set}
    (hm : ForcingDiagramPoset.LeftCancelMonoid D mul unit)
    (hJ : ConstructionProbeSharedIntersections.ConditionalJoins D mul) (hq : Injection D I q)
    (hH : Carrier D I mul q root H) (hG : Classes w D chain H G)
    (hpi : (Project.FirstOrderSemantics.reduct M).mem pi H)
    (hC : (Project.FirstOrderSemantics.reduct M).mem C G) : ∃ E, At w D I chain H pi C E := by
  obtain ⟨g,hg,hgC⟩ := (hG C).mp hC
  have hp := (hH pi).mp hpi
  have hg' := (hH g).mp hg
  obtain ⟨pg,hpg,hComp⟩ := ForcingConditionGraphs.exists_composition hM hp.1 hg'.1
  have hpgH := (hH pg).mpr (ConstructionGermSeparation.stabilizes_composition hM hm hJ hq hp hg' hpg hComp)
  obtain ⟨E,hE⟩ := ConstructionGermCosets.exists_class hM w D chain H pg
  exact ⟨E,g,pg,hg,hpgH,hgC,hE,hComp⟩

theorem at_surjective (hM : FirstOrder.Theory.Models M nativeZF)
    {w D I mul unit q root chain H G pi E : M.Carrier .set}
    (hm : ForcingDiagramPoset.LeftCancelMonoid D mul unit)
    (hJ : ConstructionProbeSharedIntersections.ConditionalJoins D mul) (hq : Injection D I q)
    (hH : Carrier D I mul q root H) (hG : Classes w D chain H G)
    (hpi : (Project.FirstOrderSemantics.reduct M).mem pi H)
    (hE : (Project.FirstOrderSemantics.reduct M).mem E G) : ∃ C, At w D I chain H pi C E := by
  obtain ⟨g,hg,hgE⟩ := (hG E).mp hE
  have hp := (hH pi).mp hpi
  have hg' := (hH g).mp hg
  obtain ⟨inv,hi,hInv⟩ := ForcingConditionGraphs.exists_inverse hM hp.1
  have hiH := ConstructionGermSeparation.stabilizes_inverse hM hq hp hi hInv
  obtain ⟨diff,hd,hDiff⟩ := ForcingConditionGraphs.exists_composition hM hi hg'.1
  have hdH := (hH diff).mpr (ConstructionGermSeparation.stabilizes_composition hM hm hJ hq hiH hg' hd hDiff)
  obtain ⟨C,hC⟩ := ConstructionGermCosets.exists_class hM w D chain H diff
  refine ⟨C,diff,g,hdH,hg,hC,hgE,?_⟩
  intro x z
  constructor
  · intro hxz
    obtain ⟨y,hy,hyz⟩ := hp.1.2.2 z (hg'.1.1.2 x z hxz)
    exact ⟨function_input hg'.1.1.1 hxz,y,(hDiff x y).mpr ⟨function_input hg'.1.1.1 hxz,z,hxz,(hInv y z).mp hyz⟩,hyz⟩
  · rintro ⟨_,y,hxy,hyz⟩
    obtain ⟨_,z',hxz',hz'y⟩ := (hDiff x y).mp hxy
    have e := function_unique hp.1.1.1 ((hInv y z').mpr hz'y) hyz
    exact e ▸ hxz'

def Action (w D I chain H G pi f : M.Carrier .set) : Prop := Permutation G f ∧ ∀ C E,
  PureKuratowski.PairMember M C E f ↔ (Project.FirstOrderSemantics.reduct M).mem C G ∧ At w D I chain H pi C E

def action {m : Nat} (w D I chain H G pi f : Fin m) : Project.Formula 1 m :=
  .conj (ProjectSyntax.encode id (ForcingConditionGraphs.permutation G f))
    (.forallE (.forallE (.iff (ProjectSyntax.encode id (Source.SetLanguage.edge f.succ.succ 1 0))
      (.conj (.mem (.bound 1) (.bound G.succ.succ))
        (atFormula w.succ.succ D.succ.succ I.succ.succ chain.succ.succ H.succ.succ pi.succ.succ 1 0)))))

theorem action_freeClosed {m : Nat} (w D I chain H G pi f : Fin m) : (action w D I chain H G pi f).FreeClosed := by
  simp -implicitDefEqProofs [action,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,atFormula_freeClosed]

theorem action_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w D I chain H G pi f : Fin m) :
    Project.Formula.satisfies env (action w D I chain H G pi f) ↔
      Action (env.bound w) (env.bound D) (env.bound I) (env.bound chain) (env.bound H) (env.bound G) (env.bound pi) (env.bound f) := by
  simp only [action,Action,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_iff_iff,
    Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,atFormula_semantics hM,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),ForcingConditionGraphs.permutation_semantics (M := M),KuratowskiZF.source_edge]
  rfl

theorem construction (hM : FirstOrder.Theory.Models M nativeZF)
    {w D I mul unit q zero root vertices chain H G pi : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hm : ForcingDiagramPoset.LeftCancelMonoid D mul unit)
    (hJ : ConstructionProbeSharedIntersections.ConditionalJoins D mul) (hq : Injection D I q)
    (hChain : Chain w D I mul q zero root vertices chain)
    (hH : Carrier D I mul q root H) (hG : Classes w D chain H G)
    (hpi : (Project.FirstOrderSemantics.reduct M).mem pi H) : ∃ f, Action w D I chain H G pi f := by
  let schema : Project.BinarySchema 6 := { body := atFormula 2 3 4 5 6 7 1 0, freeClosed := atFormula_freeClosed .. }
  let env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) 6 := {
    bound := Fin.cases w (Fin.cases D (Fin.cases I (Fin.cases chain (Fin.cases H (fun _ => pi))))), free := fun _ => w }
  have he C E : schema.denote env C E ↔ At w D I chain H pi C E :=
    atFormula_semantics hM ((env.push C).push E) 2 3 4 5 6 7 1 0
  obtain ⟨f,hf,hEdge⟩ := ZF.exists_setFunctionFromTo_of_denote (ModelTransfer.project_models_iff.mp hM)
    (KuratowskiZF.interpretation hM) schema env (source := G) (target := G) (by
      intro C hC
      obtain ⟨E,hE⟩ := at_total hM hm hJ hq hH hG hpi hC
      exact ⟨E,(he C E).mpr hE⟩)
    (fun C _ E F hE hF => at_unique hM hw hChain hH ((hH pi).mp hpi).1 ((he C E).mp hE) ((he C F).mp hF)) (by
      intro C E _ hE
      obtain ⟨_,pg,_,hpg,_,hClass,_⟩ := (he C E).mp hE
      exact (hG E).mpr ⟨pg,hpg,hClass⟩)
  have hEdge' C E : PureKuratowski.PairMember M C E f ↔ (Project.FirstOrderSemantics.reduct M).mem C G ∧ At w D I chain H pi C E :=
    (hEdge C E).trans (and_congr Iff.rfl (he C E))
  refine ⟨f,⟨(ForcingSupportSize.native_mapsTo hM G G f).mpr hf,?_,?_⟩,hEdge'⟩
  · intro C E F hCF hEF
    exact at_injective hM hw hChain hH ((hH pi).mp hpi).1 ((hEdge' C F).mp hCF).2 ((hEdge' E F).mp hEF).2
  · intro E hE
    obtain ⟨C,hAt⟩ := at_surjective hM hm hJ hq hH hG hpi hE
    have hAtCopy := hAt
    obtain ⟨g,_,hg,_,hClass,_,_⟩ := hAtCopy
    have hC := (hG C).mpr ⟨g,hg,hClass⟩
    exact ⟨C,hC,(hEdge' C E).mpr ⟨hC,hAt⟩⟩

def constructionSentence {m : Nat} (w D I mul unit q zero root vertices chain H G pi : Fin m) : Project.Sentence where
  formula := Project.Formula.forallClosure m (.imp (Project.Formula.isOmega (.bound w)) (.imp (ProjectSyntax.encode id (ForcingDiagramPoset.leftCancelMonoid D mul unit)) (.imp (ConstructionProbeSharedIntersections.conditionalJoins D mul) (.imp (ProjectSyntax.encode id (Source.SetLanguage.injection q D I)) (.imp (ConstructionComponentCofinal.chain w D I mul q zero root vertices chain) (.imp (ConstructionGermCosets.carrier D I mul q root H) (.imp (ConstructionGermCosets.classes w D chain H G) (.imp (.mem (.bound pi) (.bound H)) (.existsE (action w.succ D.succ I.succ chain.succ H.succ G.succ pi.succ 0))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,Project.Formula.isOmega,ProjectSyntax.freeClosed,
      ConstructionProbeSharedIntersections.conditionalJoins_freeClosed,ConstructionComponentCofinal.chain_freeClosed,
      ConstructionGermCosets.carrier_freeClosed,ConstructionGermCosets.classes_freeClosed,action_freeClosed]

theorem construction_models {m : Nat} (w D I mul unit q zero root vertices chain H G pi : Fin m) (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence (constructionSentence w D I mul unit q zero root vertices chain H G pi)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) (constructionSentence w D I mul unit q zero root vertices chain H G pi)]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_isOmega_iff,GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingDiagramPoset.leftCancelMonoid_semantics (M := M),ConstructionProbeSharedIntersections.conditionalJoins_semantics hM,
    ForcingSupportSize.injection_semantics (M := M),ConstructionComponentCofinal.chain_semantics hM,
    ConstructionGermCosets.carrier_semantics hM,ConstructionGermCosets.classes_semantics hM,
    Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,action_semantics hM]
  exact construction hM

theorem construction_kernel_certificate {m : Nat} (w D I mul unit q zero root vertices chain H G pi : Fin m) :
    FirstOrder.Derives nativeZF [] (Project.fo_sentence (constructionSentence w D I mul unit q zero root vertices chain H G pi)) :=
  ModelTransfer.derives (fun _ hM => construction_models w D I mul unit q zero root vertices chain H G pi hM)

end PPAC.Migration.ConstructionGermLeftAction
