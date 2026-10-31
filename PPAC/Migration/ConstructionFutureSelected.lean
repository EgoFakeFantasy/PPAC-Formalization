/- Pinned CellReorder.future_cut selected successor, consuming the actual
CellCuts.restrict_selected producer. Preserve its already constructed typed
multiplication graphs and original identity inclusions. No new cell,
closure, presentation or multiplication producer is introduced. -/
import PPAC.Migration.ConstructionFutureLimit

namespace PPAC.Migration.ConstructionFutureSelected
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ConstructionSelectedCellRestriction (Base)
open ConstructionUnionPushout (Square)
open ConstructionConservativeHull (Closure ProductGraph)
open ConstructionCellRestriction (Stages Attachment Restricted)
open ConstructionStepCell (TypedProduct)
open ConstructionFutureFamily (CutAt)
open ConstructionFirstAppearance (Timeline Cover NewAt Index)
open ConstructionIntermediate (Sup)
open ForcingConditionGraphs (FunctionOn IdentityGraph function_unique)
open ForcingSupportSize (MapsTo)
open ConstructionProbeLetters (Representatives)
open ForcingDiagramPoset (LeftCancelMonoid Conical)
open ConstructionProbeSharedIntersections (ConditionalJoins)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

/-- Existing conservative-subobject facts at the SUPPLIED typed product and
identity graph. All input witnesses are retained outputs of the producer. -/
theorem base_fixed {V GV e D pairs mul inc : M.Carrier .set}
    (hv : LeftCancelMonoid V GV e) (hc : Conical V GV e) (hJ : ConditionalJoins V GV)
    (hD : Closure V GV e D) (hPairs : Representatives D D pairs) (hMul : MapsTo pairs D mul)
    (hProduct : ProductGraph D GV mul) (hFn : FunctionOn D inc) (hId : IdentityGraph D inc) :
    Base V GV e D pairs mul inc := by
  obtain ⟨hHom,hCons⟩ := ConstructionCellRestriction.identity_inclusion hv hc hJ hD hProduct hFn hId
  exact ⟨hD,hPairs,hMul,hProduct,ConstructionConservativeHull.monoid hv hD hProduct,
    ConstructionConservativeHull.conical hc hD.1 hProduct,hId,hHom,hCons,
    ConstructionConservativeHull.conditional_joins hJ hD hProduct⟩

/-- Four actual ambient Base records and the exact original selected square. -/
theorem from_restricted (hM : FirstOrder.Theory.Models M nativeZF)
    {w zero V GV e D T retained cut next mul pairs cutMul inc GT GNext old inclusion : M.Carrier .set}
    (hv : LeftCancelMonoid V GV e) (hc : Conical V GV e) (hJ : ConditionalJoins V GV)
    (hD : Closure V GV e D) (hT : Closure V GV e T)
    (h : Restricted hM w zero V GV e D T retained cut next mul pairs cutMul inc GT GNext old inclusion) :
    ∃ PD PT PN iT, Base V GV e D PD mul old ∧ Base V GV e T PT GT iT ∧
      Base V GV e cut pairs cutMul inc ∧ Base V GV e next PN GNext inclusion ∧
      Square cut next D T cutMul GNext mul GT e inc inclusion old ∧
      Attachment hM w zero cut cutMul e next GNext := by
  obtain ⟨hBase,hProdD,_,hCutV,hNextV,hProdT,hProdNext,_,_,_,_,_,_,hIdOld,hOld,hOldCons,
    hCutNext,hCutNextCons,hIncl,hInclCons,hIdIncl,hPush,hAttach,hTypedD,hTypedT,hTypedNext⟩ := h
  obtain ⟨PD,hPD,hMulD⟩ := hTypedD
  obtain ⟨PT,hPT,hMulT⟩ := hTypedT
  obtain ⟨PN,hPN,hMulNext⟩ := hTypedNext
  obtain ⟨hCutD,hPairs,hMulCut,hProdCut,_,_,hIdCut,hCutOld,hCutOldCons,_⟩ := hBase
  obtain ⟨iT,hIT,hIdT⟩ := ForcingConditionGraphs.exists_identity hM T
  have hBaseD := base_fixed hv hc hJ hD hPD hMulD hProdD hOld.1.1 hIdOld
  have hBaseT := base_fixed hv hc hJ hT hPT hMulT hProdT hIT.1.1 hIdT
  have hBaseCut := base_fixed hv hc hJ hCutV hPairs hMulCut
    (ConstructionCellRestriction.product_comp hProdCut hProdD hCutD.1) hCutOld.1.1 hIdCut
  have hBaseNext := base_fixed hv hc hJ hNextV hPN hMulNext hProdNext hIncl.1.1 hIdIncl
  refine ⟨PD,PT,PN,iT,hBaseD,hBaseT,hBaseCut,hBaseNext,?_,hAttach⟩
  exact ⟨(fun x hx => hCutNext.1.2 x x ((hIdCut x x).mpr ⟨hx,rfl⟩)),hCutD.1,
    (fun x hx => hIncl.1.2 x x ((hIdIncl x x).mpr ⟨hx,rfl⟩)),
    (fun x hx => hOld.1.2 x x ((hIdOld x x).mpr ⟨hx,rfl⟩)),
    hCutNext,hCutNextCons,hCutOld,hCutOldCons,hIncl,hInclCons,hOld,hOldCons,hPush⟩

/-- Original adjacent-stage and retained-cut data, all in the same V. -/
def Step (hM : FirstOrder.Theory.Models M nativeZF)
    (w zero V GV e S retained i j : M.Carrier .set) : Prop :=
  ∃ D T cut next PD PT PC PN mul GT GCut GNext idD idT iCut iNext,
    PureKuratowski.PairMember M i D S ∧ PureKuratowski.PairMember M j T S ∧
    CutAt retained S i cut ∧ CutAt retained S j next ∧
    Base V GV e D PD mul idD ∧ Base V GV e T PT GT idT ∧
    Base V GV e cut PC GCut iCut ∧ Base V GV e next PN GNext iNext ∧
    Square cut next D T GCut GNext mul GT e iCut iNext idD ∧
    Attachment hM w zero cut GCut e next GNext

theorem cover_unique (hM : FirstOrder.Theory.Models M nativeZF)
    {V I R bottom S i j k : M.Carrier .set} (hT : Timeline hM V I R bottom S)
    (hij : Cover I R i j) (hik : Cover I R i k) : j = k := by
  rcases ConstructionFirstAppearance.cover_le hM hT.1 hij hik.2.1 hik.2.2.1 with he | hjk
  · exact he
  · exact (hik.2.2.2 j hij.2.1 hij.2.2.1 hjk).elim

/-- Consume the actual dependency-closed selected cell. No caller supplies
an Attachment, selected Square, inverse, or typed multiplication oracle. -/
theorem selected (hM : FirstOrder.Theory.Models M nativeZF)
    {w zero one V GV e I R bottom S index cells deps retained i j x : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ z, ¬ (Project.FirstOrderSemantics.reduct M).mem z zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hv : LeftCancelMonoid V GV e) (hc : Conical V GV e) (hJ : ConditionalJoins V GV)
    (hStages : Stages V GV e S) (hRet : Closure V GV e retained)
    (hT : Timeline hM V I R bottom S) (hIndex : Index V I R bottom S index)
    (hCells : ConstructionStepCellSelection.Graph hM w zero one V GV e I R S cells)
    (hNew : ConstructionStepCellSelection.AtNew hM w zero one V GV e I R S cells)
    (hGlobal : ConstructionGlobalDependencies.Graph zero V I R bottom S index cells deps)
    (hClosed : ConstructionCountableConservativeHull.DependenciesClosed deps retained)
    (hCover : Cover I R i j) (hx : (Project.FirstOrderSemantics.reduct M).mem x retained)
    (hxi : NewAt I R S i x) : Step hM w zero V GV e S retained i j := by
  obtain ⟨cell,j',D,T,cut,next,mul,pairs,cutMul,inc,GT,GNext,old,inclusion,
    _,hCover',hiD,hjT,_,hRetained,hNext,hRestricted⟩ :=
    ConstructionCellRestriction.selected hM hw hz hzw hv hc hJ hStages hRet hT hIndex hCells hNew hGlobal hClosed hx hxi
  have he := cover_unique hM hT hCover' hCover
  subst j'
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,hCut,_⟩ := hRetained
  obtain ⟨PD,PT,PN,iT,hBaseD,hBaseT,hBaseCut,hBaseNext,hSquare,hAttach⟩ :=
    from_restricted hM hv hc hJ (hStages i D hiD) (hStages j T hjT) hRestricted
  exact ⟨D,T,cut,next,PD,PT,pairs,PN,mul,GT,cutMul,GNext,old,iT,inc,inclusion,
    hiD,hjT,⟨D,hiD,hCut⟩,⟨T,hjT,hNext⟩,hBaseD,hBaseT,hBaseCut,hBaseNext,hSquare,hAttach⟩

/-- Same carrier, ambient multiplication and typed identity graph determine
both actual graphs. This only aligns existing Base witnesses. -/
theorem base_graphs_unique (hM : FirstOrder.Theory.Models M nativeZF)
    {V GV e D P Q G H i j : M.Carrier .set}
    (h : Base V GV e D P G i) (h' : Base V GV e D Q H j) : G = H ∧ i = j := by
  obtain ⟨_,hP,hG,hProduct,_,_,hId,_,hCons,_⟩ := h
  obtain ⟨_,hQ,hH,hProduct',_,_,hId',_,hCons',_⟩ := h'
  exact ⟨ConstructionFutureFamily.multiplication_unique hM ⟨P,hP,hG,hProduct⟩ ⟨Q,hQ,hH,hProduct'⟩,
    ForcingDiagramPoset.injection_ext hM hCons.1 hCons'.1 (fun x y => (hId x y).trans (hId' x y).symm)⟩

/-- Source future_cut's selected successor, with its actual cell/attachment
and typed square produced from the original timeline/dependency data. The
ordinary supremum at j gains its Base and full Square; no such target
closure or target pushout is an input. -/
theorem advance (hM : FirstOrder.Theory.Models M nativeZF)
    {w zero one V GV e I R bottom S index cells deps retained a i j x
      A B C P E F PA PB PC PP GA GB GC GP ia ib ic ip : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ z, ¬ (Project.FirstOrderSemantics.reduct M).mem z zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hv : LeftCancelMonoid V GV e) (hc : Conical V GV e) (hJ : ConditionalJoins V GV)
    (hStages : Stages V GV e S) (hRet : Closure V GV e retained)
    (hTimeline : Timeline hM V I R bottom S) (hIndex : Index V I R bottom S index)
    (hCells : ConstructionStepCellSelection.Graph hM w zero one V GV e I R S cells)
    (hNew : ConstructionStepCellSelection.AtNew hM w zero one V GV e I R S cells)
    (hGlobal : ConstructionGlobalDependencies.Graph zero V I R bottom S index cells deps)
    (hClosed : ConstructionCountableConservativeHull.DependenciesClosed deps retained)
    (hCover : Cover I R i j) (hx : (Project.FirstOrderSemantics.reduct M).mem x retained) (hxi : NewAt I R S i x)
    (hA : Base V GV e A PA GA ia) (hB : Base V GV e B PB GB ib)
    (hC : Base V GV e C PC GC ic) (hP : Base V GV e P PP GP ip)
    (hPrev : Sup V GV e C B P) (hSquare : Square A B C P GA GB GC GP e ia ib ic)
    (haC : PureKuratowski.PairMember M a C S) (hai : a = i ∨ PureKuratowski.PairMember M a i R)
    (hiB : CutAt retained S i B) (hjE : CutAt retained S j E) (hF : Sup V GV e C E F) :
    ∃ PE GE ie PF GF iF, Base V GV e E PE GE ie ∧ Base V GV e F PF GF iF ∧
      Sup V GV e C E F ∧ Square A E C F GA GE GC GF e ia ie ic := by
  obtain ⟨D,T,B',E',PD,PT,PB',PE,GD,GT,GB',GE,idD,idT,ib',ie,
    hiD,_,hCutB,hCutE,hBaseD,hBaseT,hBaseB,hBaseE,hStep,hAttach⟩ :=
    selected hM hw hz hzw hv hc hJ hStages hRet hTimeline hIndex hCells hNew hGlobal hClosed hCover hx hxi
  have hEqB := ConstructionFutureFamily.cut_unique hM hTimeline.2.1 hCutB hiB
  have hEqE := ConstructionFutureFamily.cut_unique hM hTimeline.2.1 hCutE hjE
  subst B' E'
  obtain ⟨hGB,hIB⟩ := base_graphs_unique hM hBaseB hB
  subst GB' ib'
  have hCD : ConstructionRealCuts.Subset C D := by
    intro z hzC
    obtain ⟨D',hD',hzD'⟩ := hTimeline.2.2.2.2.2.1 a i z hai ⟨C,haC,hzC⟩
    exact (function_unique hTimeline.2.1 hD' hiD) ▸ hzD'
  obtain ⟨F',PF,GF,iF,hBaseF,hSupF,_,_,hOut⟩ := ConstructionFutureCut.selected hM hw hz hzw
    hv hc hJ hA hB hC hBaseD hBaseE hBaseT hP hPrev hSquare hStep hAttach hCD
  have hEqF := ConstructionFutureFamily.sup_unique hM hSupF hF
  subst F'
  exact ⟨PE,GE,ie,PF,GF,iF,hBaseE,hBaseF,hF,hOut⟩


def stepFormula {m : Nat} (w zero V GV e S retained i j : Fin m) : Project.Formula 1 m :=
  (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.conj (ProjectSyntax.encode id (Source.SetLanguage.edge S.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ i.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ 15)) (.conj (ProjectSyntax.encode id (Source.SetLanguage.edge S.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ j.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ 14)) (.conj (ConstructionFutureFamily.cutAt retained.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ S.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ i.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ 13) (.conj (ConstructionFutureFamily.cutAt retained.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ S.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ j.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ 12) (.conj (ConstructionSelectedCellRestriction.baseFormula V.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ GV.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ e.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ 15 11 7 3) (.conj (ConstructionSelectedCellRestriction.baseFormula V.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ GV.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ e.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ 14 10 6 2) (.conj (ConstructionSelectedCellRestriction.baseFormula V.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ GV.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ e.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ 13 9 5 1) (.conj (ConstructionSelectedCellRestriction.baseFormula V.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ GV.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ e.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ 12 8 4 0) (.conj (ConstructionUnionPushout.square 13 12 15 14 5 4 7 6 e.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ 1 0 3) (ConstructionCellRestriction.attachmentFormula w.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ zero.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ 13 5 e.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ 12 4))))))))))))))))))))))))))

theorem stepFormula_freeClosed {m : Nat} (w zero V GV e S retained i j : Fin m) :
    (stepFormula w zero V GV e S retained i j).FreeClosed := by
  simp -implicitDefEqProofs [stepFormula,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,ConstructionFutureFamily.cutAt_freeClosed,ConstructionSelectedCellRestriction.baseFormula_freeClosed,ConstructionUnionPushout.square_freeClosed,ConstructionCellRestriction.attachmentFormula_freeClosed]

theorem stepFormula_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w zero V GV e S retained i j : Fin m) :
    Project.Formula.satisfies env (stepFormula w zero V GV e S retained i j) ↔ Step hM (env.bound w) (env.bound zero) (env.bound V) (env.bound GV) (env.bound e) (env.bound S) (env.bound retained) (env.bound i) (env.bound j) := by
  simp only [stepFormula,Step,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,ConstructionFutureFamily.cutAt_semantics hM,ConstructionSelectedCellRestriction.baseFormula_semantics hM,ConstructionUnionPushout.square_semantics hM,ConstructionCellRestriction.attachmentFormula_semantics hM]
  rfl

/-- Pure-membership instance, returned through the existing nativeZF kernel. -/
def selectedSentence {m : Nat} (w zero one V GV e I R bottom S index cells deps retained i j x : Fin m) : Project.Sentence where
  formula := Project.Formula.forallClosure m (.imp (Project.Formula.isOmega (.bound w)) (.imp (Project.Formula.isEmpty (.bound zero)) (.imp (.mem (.bound zero) (.bound w)) (.imp (ProjectSyntax.encode id (ForcingDiagramPoset.leftCancelMonoid V GV e)) (.imp (ProjectSyntax.encode id (ForcingDiagramPoset.conical V GV e)) (.imp (ConstructionProbeSharedIntersections.conditionalJoins V GV) (.imp (ConstructionCellRestriction.stages V GV e S) (.imp (ConstructionConservativeHull.closure V GV e retained) (.imp (ConstructionFirstAppearance.timeline V I R bottom S) (.imp (ConstructionFirstAppearance.indexGraph V I R bottom S index) (.imp (ConstructionStepCellSelection.graph w zero one V GV e I R S cells) (.imp (ConstructionStepCellSelection.atNew w zero one V GV e I R S cells) (.imp (ConstructionGlobalDependencies.graph zero V I R bottom S index cells deps) (.imp (ConstructionCountableConservativeHull.dependenciesClosed deps retained) (.imp (ConstructionFirstAppearance.cover I R i j) (.imp (.mem (.bound x) (.bound retained)) (.imp (ConstructionFirstAppearance.newAt I R S i x) (stepFormula w zero V GV e S retained i j))))))))))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,Project.Formula.isOmega,Project.Formula.isEmpty,ProjectSyntax.freeClosed,ConstructionProbeSharedIntersections.conditionalJoins_freeClosed,ConstructionCellRestriction.stages_freeClosed,ConstructionConservativeHull.closure_freeClosed,ConstructionFirstAppearance.timeline_freeClosed,ConstructionFirstAppearance.indexGraph_freeClosed,ConstructionStepCellSelection.graph_freeClosed,ConstructionStepCellSelection.atNew_freeClosed,ConstructionGlobalDependencies.graph_freeClosed,ConstructionCountableConservativeHull.dependenciesClosed_freeClosed,ConstructionFirstAppearance.cover_freeClosed,ConstructionFirstAppearance.newAt_freeClosed,stepFormula_freeClosed]

theorem selected_models {m : Nat} (w zero one V GV e I R bottom S index cells deps retained i j x : Fin m) (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence (selectedSentence w zero one V GV e I R bottom S index cells deps retained i j x)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) (selectedSentence w zero one V GV e I R bottom S index cells deps retained i j x)]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,Project.Term.eval_bound,GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),Project.Formula.satisfies_isOmega_iff,Project.Formula.satisfies_isEmpty_iff,Project.Formula.satisfies_mem_iff,ForcingDiagramPoset.leftCancelMonoid_semantics (M := M),ForcingDiagramPoset.conical_semantics (M := M),ConstructionProbeSharedIntersections.conditionalJoins_semantics hM,ConstructionCellRestriction.stages_semantics hM,ConstructionConservativeHull.closure_semantics hM,ConstructionFirstAppearance.timeline_semantics hM,ConstructionFirstAppearance.indexGraph_semantics hM,ConstructionStepCellSelection.graph_semantics hM,ConstructionStepCellSelection.atNew_semantics hM,ConstructionGlobalDependencies.graph_semantics hM,ConstructionCountableConservativeHull.dependenciesClosed_semantics hM,ConstructionFirstAppearance.cover_semantics hM,ConstructionFirstAppearance.newAt_semantics hM,stepFormula_semantics hM]
  exact selected hM

theorem selected_kernel_certificate {m : Nat} (w zero one V GV e I R bottom S index cells deps retained i j x : Fin m) :
    FirstOrder.Derives nativeZF [] (Project.fo_sentence (selectedSentence w zero one V GV e I R bottom S index cells deps retained i j x)) :=
  ModelTransfer.derives (fun _ hM => selected_models w zero one V GV e I R bottom S index cells deps retained i j x hM)

/-- Pure-membership instance, returned through the existing nativeZF kernel. -/
def advanceSentence {m : Nat} (w zero one V GV e I R bottom S index cells deps retained a i j x A B C P E F PA PB PC PP GA GB GC GP ia ib ic ip : Fin m) : Project.Sentence where
  formula := Project.Formula.forallClosure m (.imp (Project.Formula.isOmega (.bound w)) (.imp (Project.Formula.isEmpty (.bound zero)) (.imp (.mem (.bound zero) (.bound w)) (.imp (ProjectSyntax.encode id (ForcingDiagramPoset.leftCancelMonoid V GV e)) (.imp (ProjectSyntax.encode id (ForcingDiagramPoset.conical V GV e)) (.imp (ConstructionProbeSharedIntersections.conditionalJoins V GV) (.imp (ConstructionCellRestriction.stages V GV e S) (.imp (ConstructionConservativeHull.closure V GV e retained) (.imp (ConstructionFirstAppearance.timeline V I R bottom S) (.imp (ConstructionFirstAppearance.indexGraph V I R bottom S index) (.imp (ConstructionStepCellSelection.graph w zero one V GV e I R S cells) (.imp (ConstructionStepCellSelection.atNew w zero one V GV e I R S cells) (.imp (ConstructionGlobalDependencies.graph zero V I R bottom S index cells deps) (.imp (ConstructionCountableConservativeHull.dependenciesClosed deps retained) (.imp (ConstructionFirstAppearance.cover I R i j) (.imp (.mem (.bound x) (.bound retained)) (.imp (ConstructionFirstAppearance.newAt I R S i x) (.imp (ConstructionSelectedCellRestriction.baseFormula V GV e A PA GA ia) (.imp (ConstructionSelectedCellRestriction.baseFormula V GV e B PB GB ib) (.imp (ConstructionSelectedCellRestriction.baseFormula V GV e C PC GC ic) (.imp (ConstructionSelectedCellRestriction.baseFormula V GV e P PP GP ip) (.imp (ConstructionIntermediate.sup V GV e C B P) (.imp (ConstructionUnionPushout.square A B C P GA GB GC GP e ia ib ic) (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge S a C)) (.imp (ConstructionFutureLimit.closedLe R a i) (.imp (ConstructionFutureFamily.cutAt retained S i B) (.imp (ConstructionFutureFamily.cutAt retained S j E) (.imp (ConstructionIntermediate.sup V GV e C E F) (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.conj (ConstructionSelectedCellRestriction.baseFormula V.succ.succ.succ.succ.succ.succ GV.succ.succ.succ.succ.succ.succ e.succ.succ.succ.succ.succ.succ E.succ.succ.succ.succ.succ.succ 5 4 3) (.conj (ConstructionSelectedCellRestriction.baseFormula V.succ.succ.succ.succ.succ.succ GV.succ.succ.succ.succ.succ.succ e.succ.succ.succ.succ.succ.succ F.succ.succ.succ.succ.succ.succ 2 1 0) (.conj (ConstructionIntermediate.sup V.succ.succ.succ.succ.succ.succ GV.succ.succ.succ.succ.succ.succ e.succ.succ.succ.succ.succ.succ C.succ.succ.succ.succ.succ.succ E.succ.succ.succ.succ.succ.succ F.succ.succ.succ.succ.succ.succ) (ConstructionUnionPushout.square A.succ.succ.succ.succ.succ.succ E.succ.succ.succ.succ.succ.succ C.succ.succ.succ.succ.succ.succ F.succ.succ.succ.succ.succ.succ GA.succ.succ.succ.succ.succ.succ 4 GC.succ.succ.succ.succ.succ.succ 1 e.succ.succ.succ.succ.succ.succ ia.succ.succ.succ.succ.succ.succ 3 ic.succ.succ.succ.succ.succ.succ))))))))))))))))))))))))))))))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,Project.Formula.isOmega,Project.Formula.isEmpty,ProjectSyntax.freeClosed,ConstructionProbeSharedIntersections.conditionalJoins_freeClosed,ConstructionCellRestriction.stages_freeClosed,ConstructionConservativeHull.closure_freeClosed,ConstructionFirstAppearance.timeline_freeClosed,ConstructionFirstAppearance.indexGraph_freeClosed,ConstructionStepCellSelection.graph_freeClosed,ConstructionStepCellSelection.atNew_freeClosed,ConstructionGlobalDependencies.graph_freeClosed,ConstructionCountableConservativeHull.dependenciesClosed_freeClosed,ConstructionFirstAppearance.cover_freeClosed,ConstructionFirstAppearance.newAt_freeClosed,ConstructionSelectedCellRestriction.baseFormula_freeClosed,ConstructionIntermediate.sup_freeClosed,ConstructionUnionPushout.square_freeClosed,ConstructionFutureLimit.closedLe_freeClosed,ConstructionFutureFamily.cutAt_freeClosed]

theorem advance_models {m : Nat} (w zero one V GV e I R bottom S index cells deps retained a i j x A B C P E F PA PB PC PP GA GB GC GP ia ib ic ip : Fin m) (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence (advanceSentence w zero one V GV e I R bottom S index cells deps retained a i j x A B C P E F PA PB PC PP GA GB GC GP ia ib ic ip)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) (advanceSentence w zero one V GV e I R bottom S index cells deps retained a i j x A B C P E F PA PB PC PP GA GB GC GP ia ib ic ip)]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,Project.Term.eval_bound,GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),Project.Formula.satisfies_isOmega_iff,Project.Formula.satisfies_isEmpty_iff,Project.Formula.satisfies_mem_iff,ForcingDiagramPoset.leftCancelMonoid_semantics (M := M),ForcingDiagramPoset.conical_semantics (M := M),ConstructionProbeSharedIntersections.conditionalJoins_semantics hM,ConstructionCellRestriction.stages_semantics hM,ConstructionConservativeHull.closure_semantics hM,ConstructionFirstAppearance.timeline_semantics hM,ConstructionFirstAppearance.indexGraph_semantics hM,ConstructionStepCellSelection.graph_semantics hM,ConstructionStepCellSelection.atNew_semantics hM,ConstructionGlobalDependencies.graph_semantics hM,ConstructionCountableConservativeHull.dependenciesClosed_semantics hM,ConstructionFirstAppearance.cover_semantics hM,ConstructionFirstAppearance.newAt_semantics hM,ConstructionSelectedCellRestriction.baseFormula_semantics hM,ConstructionIntermediate.sup_semantics hM,ConstructionUnionPushout.square_semantics hM,KuratowskiZF.source_edge,ConstructionFutureLimit.closedLe_semantics hM,ConstructionFutureFamily.cutAt_semantics hM,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff]
  exact advance hM

theorem advance_kernel_certificate {m : Nat} (w zero one V GV e I R bottom S index cells deps retained a i j x A B C P E F PA PB PC PP GA GB GC GP ia ib ic ip : Fin m) :
    FirstOrder.Derives nativeZF [] (Project.fo_sentence (advanceSentence w zero one V GV e I R bottom S index cells deps retained a i j x A B C P E F PA PB PC PP GA GB GC GP ia ib ic ip)) :=
  ModelTransfer.derives (fun _ hM => advance_models w zero one V GV e I R bottom S index cells deps retained a i j x A B C P E F PA PB PC PP GA GB GC GP ia ib ic ip hM)

end PPAC.Migration.ConstructionFutureSelected
