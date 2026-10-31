/- Pinned GermSelectors.pattern/pattern_mk:430-437.
The actual germ quotient maps to the actual space of rawPattern graphs.
Congruence makes the value unique, so no new representative choice is needed.
The endpoint constructs all value spaces and proves evaluation at EVERY
representative, exactly the source pattern_mk equation. -/
import PPAC.Migration.ConstructionGermPatternCongruence

namespace PPAC.Migration.ConstructionGermPattern
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ForcingSupportSize (MapsTo)
open ForcingCohenCoordinates (Cartesian)
open ConstructionGermRawPattern (RawPattern)
open ConstructionGermEventual (Space)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

def At (w D chain H N alpha B A E det R pr C P : M.Carrier .set) : Prop := ∃ g,
  (Project.FirstOrderSemantics.reduct M).mem g H ∧ ConstructionGermCosets.Class w D chain H g C ∧
    RawPattern w N alpha B A E det g R pr P

def atFormula {m : Nat} (w D chain H N alpha B A E det R pr C P : Fin m) : Project.Formula 1 m := .existsE
  (.conj (.mem (.bound 0) (.bound H.succ))
    (.conj (ConstructionGermCosets.eqClass w.succ D.succ chain.succ H.succ 0 C.succ)
      (ConstructionGermRawPattern.rawPattern w.succ N.succ alpha.succ B.succ A.succ E.succ det.succ 0 R.succ pr.succ P.succ)))

theorem atFormula_freeClosed {m : Nat} (w D chain H N alpha B A E det R pr C P : Fin m) :
    (atFormula w D chain H N alpha B A E det R pr C P).FreeClosed := by
  simp -implicitDefEqProofs [atFormula,Definitional.Formula.FreeClosed,ConstructionGermCosets.eqClass_freeClosed,
    ConstructionGermRawPattern.rawPattern_freeClosed]

theorem atFormula_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w D chain H N alpha B A E det R pr C P : Fin m) :
    Project.Formula.satisfies env (atFormula w D chain H N alpha B A E det R pr C P) ↔
      At (env.bound w) (env.bound D) (env.bound chain) (env.bound H) (env.bound N) (env.bound alpha)
        (env.bound B) (env.bound A) (env.bound E) (env.bound det) (env.bound R) (env.bound pr) (env.bound C) (env.bound P) := by
  simp only [atFormula,At,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    ConstructionGermCosets.eqClass_semantics hM,ConstructionGermRawPattern.rawPattern_semantics hM]
  rfl

theorem at_unique (hM : FirstOrder.Theory.Models M nativeZF)
    {w D I mul q zero root vertices chain H N X reps alpha B A E det R pr C P T : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hChain : ConstructionComponentCofinal.Chain w D I mul q zero root vertices chain)
    (hDet : ConstructionGermDetectors.Detectors D I chain X reps det)
    (hExact : ConstructionGermEventual.Exact w pr)
    (hP : At w D chain H N alpha B A E det R pr C P) (hT : At w D chain H N alpha B A E det R pr C T) : P = T := by
  obtain ⟨g,_,hCg,hPg⟩ := hP
  obtain ⟨h,hh,hCh,hTh⟩ := hT
  have hzero := ForcingConditionGraphs.function_input hChain.1.1 hChain.2.1
  have hSame := (ConstructionGermCosets.class_eq_iff hM hw hzero hChain hh hCg hCh).mp rfl
  exact ConstructionGermPatternCongruence.rawPattern_congr hM hChain hDet hSame hExact hPg hTh

def Pattern (w D chain H G N alpha B A E T det R pr F : M.Carrier .set) : Prop := MapsTo G T F ∧ ∀ C P,
  PureKuratowski.PairMember M C P F ↔ (Project.FirstOrderSemantics.reduct M).mem C G ∧ At w D chain H N alpha B A E det R pr C P

def pattern {m : Nat} (w D chain H G N alpha B A E T det R pr F : Fin m) : Project.Formula 1 m := .conj
  (ProjectSyntax.encode id (Source.SetLanguage.mapsTo F G T))
  (.forallE (.forallE (.iff (ProjectSyntax.encode id (Source.SetLanguage.edge F.succ.succ 1 0))
    (.conj (.mem (.bound 1) (.bound G.succ.succ))
      (atFormula w.succ.succ D.succ.succ chain.succ.succ H.succ.succ N.succ.succ alpha.succ.succ B.succ.succ
        A.succ.succ E.succ.succ det.succ.succ R.succ.succ pr.succ.succ 1 0)))))

theorem pattern_freeClosed {m : Nat} (w D chain H G N alpha B A E T det R pr F : Fin m) :
    (pattern w D chain H G N alpha B A E T det R pr F).FreeClosed := by
  simp -implicitDefEqProofs [pattern,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,atFormula_freeClosed]

theorem pattern_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w D chain H G N alpha B A E T det R pr F : Fin m) :
    Project.Formula.satisfies env (pattern w D chain H G N alpha B A E T det R pr F) ↔
      Pattern (env.bound w) (env.bound D) (env.bound chain) (env.bound H) (env.bound G) (env.bound N) (env.bound alpha)
        (env.bound B) (env.bound A) (env.bound E) (env.bound T) (env.bound det) (env.bound R) (env.bound pr) (env.bound F) := by
  simp only [pattern,Pattern,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_forall_iff,
    Project.Formula.satisfies_iff_iff,Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,atFormula_semantics hM,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,ForcingSupportSize.mapsTo_semantics (M := M)]
  rfl

theorem exists_pattern (hM : FirstOrder.Theory.Models M nativeZF)
    {w D I mul q zero root vertices chain H G N X reps K C B alpha A S E T det R pr : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hChain : ConstructionComponentCofinal.Chain w D I mul q zero root vertices chain)
    (hDet : ConstructionGermDetectors.Detectors D I chain X reps det)
    (hH : ConstructionGermCosets.Carrier D I mul q root H) (hG : ConstructionGermCosets.Classes w D chain H G)
    (hX : Cartesian N w X) (hC : Cartesian I K C) (hR : MapsTo C B R)
    (hAlpha : (Project.FirstOrderSemantics.reduct M).MemberSubset alpha K)
    (hA : Space alpha B A) (hS : Space w A S) (hT : Space N E T)
    (hpr : MapsTo S E pr) (hExact : ConstructionGermEventual.Exact w pr) :
    ∃ F, Pattern w D chain H G N alpha B A E T det R pr F := by
  let schema : Project.BinarySchema 12 := {
    body := atFormula 2 3 4 5 6 7 8 9 10 11 12 13 1 0, freeClosed := atFormula_freeClosed .. }
  let env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) 12 := {
    bound := Fin.cases w (Fin.cases D (Fin.cases chain (Fin.cases H (Fin.cases N (Fin.cases alpha
      (Fin.cases B (Fin.cases A (Fin.cases E (Fin.cases det (Fin.cases R (fun _ => pr))))))))))), free := fun _ => R }
  have he C P : schema.denote env C P ↔ At w D chain H N alpha B A E det R pr C P :=
    atFormula_semantics hM ((env.push C).push P) 2 3 4 5 6 7 8 9 10 11 12 13 1 0
  obtain ⟨F,hF,hEdge⟩ := ZF.exists_setFunctionFromTo_of_denote (ModelTransfer.project_models_iff.mp hM)
    (KuratowskiZF.interpretation hM) schema env (source := G) (target := T) (by
      intro C hCG
      obtain ⟨g,hg,hClass⟩ := (hG C).mp hCG
      have hgMap : MapsTo I I g := ((hH g).mp hg).1.1
      obtain ⟨P,hP⟩ := ConstructionGermRawPattern.exists_rawPattern hM hX hC hDet.1 hgMap hR hAlpha hA hS hpr
      exact ⟨P,(he C P).mpr ⟨g,hg,hClass,hP⟩⟩)
    (fun C _ P T hP hT => at_unique hM hw hChain hDet hExact ((he C P).mp hP) ((he C T).mp hT)) (by
      intro C P _ hP
      obtain ⟨_,_,_,hRaw⟩ := (he C P).mp hP
      exact (hT P).mpr hRaw.1)
  exact ⟨F,(ForcingSupportSize.native_mapsTo hM G T F).mpr hF,
    fun C P => (hEdge C P).trans (and_congr Iff.rfl (he C P))⟩

/-- Evaluation at every representative; source pattern_mk, not only chosen representatives. -/
def Realizes (w D chain H N alpha B A E det R pr F : M.Carrier .set) : Prop := ∀ g C P,
  (Project.FirstOrderSemantics.reduct M).mem g H → ConstructionGermCosets.Class w D chain H g C →
    RawPattern w N alpha B A E det g R pr P → PureKuratowski.PairMember M C P F

theorem pattern_mk {w D chain H G N alpha B A E T det R pr F : M.Carrier .set}
    (hG : ConstructionGermCosets.Classes w D chain H G)
    (hF : Pattern w D chain H G N alpha B A E T det R pr F) : Realizes w D chain H N alpha B A E det R pr F := by
  intro g C P hg hClass hRaw
  exact (hF.2 C P).mpr ⟨(hG C).mpr ⟨g,hg,hClass⟩,g,hg,hClass,hRaw⟩

def realizes {m : Nat} (w D chain H N alpha B A E det R pr F : Fin m) : Project.Formula 1 m :=
  .forallE (.forallE (.forallE (.imp (.mem (.bound 2) (.bound H.succ.succ.succ))
    (.imp (ConstructionGermCosets.eqClass w.succ.succ.succ D.succ.succ.succ chain.succ.succ.succ H.succ.succ.succ 2 1)
      (.imp (ConstructionGermRawPattern.rawPattern w.succ.succ.succ N.succ.succ.succ alpha.succ.succ.succ B.succ.succ.succ
        A.succ.succ.succ E.succ.succ.succ det.succ.succ.succ 2 R.succ.succ.succ pr.succ.succ.succ 0)
        (ProjectSyntax.encode id (Source.SetLanguage.edge F.succ.succ.succ 1 0)))))))

theorem realizes_freeClosed {m : Nat} (w D chain H N alpha B A E det R pr F : Fin m) :
    (realizes w D chain H N alpha B A E det R pr F).FreeClosed := by
  simp -implicitDefEqProofs [realizes,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
    ConstructionGermCosets.eqClass_freeClosed,ConstructionGermRawPattern.rawPattern_freeClosed]

theorem realizes_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w D chain H N alpha B A E det R pr F : Fin m) :
    Project.Formula.satisfies env (realizes w D chain H N alpha B A E det R pr F) ↔
      Realizes (env.bound w) (env.bound D) (env.bound chain) (env.bound H) (env.bound N) (env.bound alpha)
        (env.bound B) (env.bound A) (env.bound E) (env.bound det) (env.bound R) (env.bound pr) (env.bound F) := by
  simp only [realizes,Realizes,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_imp_iff,
    Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,ConstructionGermCosets.eqClass_semantics hM,
    ConstructionGermRawPattern.rawPattern_semantics hM,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge]
  rfl

theorem construction (hM : FirstOrder.Theory.Models M nativeZF)
    {w D I mul q zero root vertices chain H G N X reps K C B alpha det R : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hChain : ConstructionComponentCofinal.Chain w D I mul q zero root vertices chain)
    (hDet : ConstructionGermDetectors.Detectors D I chain X reps det)
    (hH : ConstructionGermCosets.Carrier D I mul q root H) (hG : ConstructionGermCosets.Classes w D chain H G)
    (hX : Cartesian N w X) (hC : Cartesian I K C) (hR : MapsTo C B R)
    (hAlpha : (Project.FirstOrderSemantics.reduct M).MemberSubset alpha K) :
    ∃ A S E pr T F, Space alpha B A ∧ Space w A S ∧ MapsTo S E pr ∧ ConstructionGermEventual.Classes w S E ∧
      ConstructionGermEventual.Projection w S pr ∧ ConstructionGermEventual.Exact w pr ∧ Space N E T ∧
        Pattern w D chain H G N alpha B A E T det R pr F ∧ Realizes w D chain H N alpha B A E det R pr F := by
  obtain ⟨A,hA⟩ := ZF.exists_functionSpace (ModelTransfer.project_models_iff.mp hM) (KuratowskiZF.interpretation hM) alpha B
  have hA' : Space alpha B A := fun f => (hA f).trans (ForcingSupportSize.native_mapsTo hM alpha B f).symm
  obtain ⟨S,E,pr,hS,hpr,hE,hProj,hExact⟩ := ConstructionGermEventual.construction hM A hw
  obtain ⟨T,hT⟩ := ZF.exists_functionSpace (ModelTransfer.project_models_iff.mp hM) (KuratowskiZF.interpretation hM) N E
  have hT' : Space N E T := fun f => (hT f).trans (ForcingSupportSize.native_mapsTo hM N E f).symm
  obtain ⟨F,hF⟩ := exists_pattern hM hw hChain hDet hH hG hX hC hR hAlpha hA' hS hT' hpr hExact
  exact ⟨A,S,E,pr,T,F,hA',hS,hpr,hE,hProj,hExact,hT',hF,pattern_mk hG hF⟩

def constructionSentence {m : Nat} (w D I mul q zero root vertices chain H G N X reps K C B alpha det R : Fin m) : Project.Sentence where
  formula := Project.Formula.forallClosure m (.imp (Project.Formula.isOmega (.bound w)) (.imp (ConstructionComponentCofinal.chain w D I mul q zero root vertices chain) (.imp (ConstructionGermDetectors.detectors D I chain X reps det) (.imp (ConstructionGermCosets.carrier D I mul q root H) (.imp (ConstructionGermCosets.classes w D chain H G) (.imp (ProjectSyntax.encode id (ForcingCohenCoordinates.cartesian N w X)) (.imp (ProjectSyntax.encode id (ForcingCohenCoordinates.cartesian I K C)) (.imp (ProjectSyntax.encode id (Source.SetLanguage.mapsTo R C B)) (.imp (Project.Formula.subset (.bound alpha) (.bound K)) (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.conj (ConstructionGermEventual.space alpha.succ.succ.succ.succ.succ.succ B.succ.succ.succ.succ.succ.succ 5) (.conj (ConstructionGermEventual.space w.succ.succ.succ.succ.succ.succ 5 4) (.conj (ProjectSyntax.encode id (Source.SetLanguage.mapsTo 2 4 3)) (.conj (ConstructionGermEventual.classes w.succ.succ.succ.succ.succ.succ 4 3) (.conj (ConstructionGermEventual.projection w.succ.succ.succ.succ.succ.succ 4 2) (.conj (ConstructionGermEventual.exactProjection w.succ.succ.succ.succ.succ.succ 2) (.conj (ConstructionGermEventual.space N.succ.succ.succ.succ.succ.succ 3 1) (.conj (pattern w.succ.succ.succ.succ.succ.succ D.succ.succ.succ.succ.succ.succ chain.succ.succ.succ.succ.succ.succ H.succ.succ.succ.succ.succ.succ G.succ.succ.succ.succ.succ.succ N.succ.succ.succ.succ.succ.succ alpha.succ.succ.succ.succ.succ.succ B.succ.succ.succ.succ.succ.succ 5 3 1 det.succ.succ.succ.succ.succ.succ R.succ.succ.succ.succ.succ.succ 2 0) (realizes w.succ.succ.succ.succ.succ.succ D.succ.succ.succ.succ.succ.succ chain.succ.succ.succ.succ.succ.succ H.succ.succ.succ.succ.succ.succ N.succ.succ.succ.succ.succ.succ alpha.succ.succ.succ.succ.succ.succ B.succ.succ.succ.succ.succ.succ 5 3 det.succ.succ.succ.succ.succ.succ R.succ.succ.succ.succ.succ.succ 2 0))))))))))))))))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,Project.Formula.isOmega,Project.Formula.subset,ProjectSyntax.freeClosed,
      ConstructionComponentCofinal.chain_freeClosed,ConstructionGermDetectors.detectors_freeClosed,
      ConstructionGermCosets.carrier_freeClosed,ConstructionGermCosets.classes_freeClosed,
      ConstructionGermEventual.space_freeClosed,ConstructionGermEventual.classes_freeClosed,
      ConstructionGermEventual.projection_freeClosed,ConstructionGermEventual.exactProjection_freeClosed,pattern_freeClosed,realizes_freeClosed]

theorem construction_models {m : Nat} (w D I mul q zero root vertices chain H G N X reps K C B alpha det R : Fin m) (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence (constructionSentence w D I mul q zero root vertices chain H G N X reps K C B alpha det R)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) (constructionSentence w D I mul q zero root vertices chain H G N X reps K C B alpha det R)]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_isOmega_iff,Project.Formula.satisfies_subset_iff,Project.Term.eval_bound,
    ConstructionComponentCofinal.chain_semantics hM,ConstructionGermDetectors.detectors_semantics hM,
    ConstructionGermCosets.carrier_semantics hM,ConstructionGermCosets.classes_semantics hM,
    ConstructionGermEventual.space_semantics hM,ConstructionGermEventual.classes_semantics hM,
    ConstructionGermEventual.projection_semantics hM,ConstructionGermEventual.exactProjection_semantics hM,pattern_semantics hM,realizes_semantics hM,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),ForcingSupportSize.mapsTo_semantics (M := M),
    ForcingCohenCoordinates.cartesian_semantics (M := M)]
  exact construction hM

theorem construction_kernel_certificate {m : Nat} (w D I mul q zero root vertices chain H G N X reps K C B alpha det R : Fin m) :
    FirstOrder.Derives nativeZF [] (Project.fo_sentence (constructionSentence w D I mul q zero root vertices chain H G N X reps K C B alpha det R)) :=
  ModelTransfer.derives (fun _ hM => construction_models w D I mul q zero root vertices chain H G N X reps K C B alpha det R hM)

end PPAC.Migration.ConstructionGermPattern
