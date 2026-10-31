/- Pinned CellReorder.future_cut: base, selected/omitted successors, and
directed-union assembly for the limit branch.
Use the same ordinary generated supremum and the full monoid pushout.
Consumer: the definable internal-index induction for future_cut. This file
does not assert that induction, or replace it by external well-foundedness. -/
import PPAC.Migration.ConstructionFutureFamily

namespace PPAC.Migration.ConstructionFutureCut
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ConstructionSelectedCellRestriction (Base)
open ConstructionUnionPushout (Square base_inclusion)
open ConstructionIntermediate (Sup)
open ConstructionRealCuts (Subset)
open ConstructionCellRestriction (Attachment Stages)
open ConstructionFutureFamily (CutAt Products Multiplication)
open ConstructionFirstAppearance (Timeline Cover NewAt)
open ConstructionSubobjectUnion (Union)
open ConstructionDirectedSystem (IndexLaws)
open ConstructionBlockStages (MonotoneImages)
open ConstructionProbePushout (Hom)
open ConstructionProbeMappedPath (NodeMap)
open ForcingConditionGraphs (IdentityGraph FunctionOn function_unique function_input)
open ForcingDiagramPoset (LeftCancelMonoid Conical)
open ConstructionProbeSharedIntersections (ConditionalJoins)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

/-- Identity inclusions compose on the literal smaller carrier. -/
theorem inclusion_comp {A B ia ib : M.Carrier .set}
    (hAB : Subset A B) (hIA : IdentityGraph A ia) (hIB : IdentityGraph B ib) :
    NodeMap ia ib ia := by
  intro x y
  constructor
  · intro hxy
    obtain ⟨hx,rfl⟩ := (hIA x y).mp hxy
    exact ⟨x,(hIA x x).mpr ⟨hx,rfl⟩,(hIB x x).mpr ⟨hAB x hx,rfl⟩⟩
  · rintro ⟨z,hxz,hzy⟩
    obtain ⟨hx,rfl⟩ := (hIA x z).mp hxz
    obtain ⟨_,rfl⟩ := (hIB x y).mp hzy
    exact (hIA x x).mpr ⟨hx,rfl⟩

/-- Source Square.identity, with the original typed conservative inclusions. -/
theorem initial (hM : FirstOrder.Theory.Models M nativeZF)
    {V GV e A C PA PC GA GC ia ic : M.Carrier .set}
    (hv : LeftCancelMonoid V GV e) (hc : Conical V GV e) (hJ : ConditionalJoins V GV)
    (hA : Base V GV e A PA GA ia) (hC : Base V GV e C PC GC ic) (hAC : Subset A C) :
    Sup V GV e C A C ∧ Square A A C C GA GA GC GC e ia ia ic := by
  obtain ⟨haa,caa⟩ := base_inclusion hv hc hJ hA hA (fun _ h => h)
  obtain ⟨hac,cac⟩ := base_inclusion hv hc hJ hA hC hAC
  obtain ⟨hcc,ccc⟩ := base_inclusion hv hc hJ hC hC (fun _ h => h)
  refine ⟨⟨⟨hC.1.1,hC.1.2.1,hC.1.2.2.1⟩,fun _ h => h,hAC,fun _ _ h _ => h⟩,
    fun _ h => h,hAC,hAC,fun _ h => h,haa,caa,hac,cac,hac,cac,hcc,ccc,?_⟩
  exact ConstructionPushoutPasting.of_id hM hac hA.2.2.2.2.2.2.1 hC.2.2.2.2.2.2.1

/-- Source Square.paste on the SAME inclusion graphs. No restriction on
the target of the universal property is introduced. -/
theorem paste (hM : FirstOrder.Theory.Models M nativeZF)
    {A B C D E F GA GB GC GD GE GF e ia ib ic idD ie : M.Carrier .set}
    (hmB : LeftCancelMonoid B GB e) (hmD : LeftCancelMonoid D GD e)
    (hmE : LeftCancelMonoid E GE e) (hmF : LeftCancelMonoid F GF e)
    (hIA : IdentityGraph A ia) (hIB : IdentityGraph B ib)
    (hIC : IdentityGraph C ic) (hID : IdentityGraph D idD)
    (h : Square A B C D GA GB GC GD e ia ib ic)
    (h' : Square B E D F GB GE GD GF e ib ie idD) :
    Square A E C F GA GE GC GF e ia ie ic := by
  obtain ⟨hAB,hAC,hBD,hCD,homAB,consAB,homAC,consAC,homBD,consBD,homCD,consCD,hPush⟩ := h
  obtain ⟨hBE,_,hEF,hDF,homBE,consBE,_,_,homEF,consEF,homDF,consDF,hPush'⟩ := h'
  have hAE := inclusion_comp hAB hIA hIB
  have hCF := inclusion_comp hCD hIC hID
  have homAE : Hom A E GA GE e e ia :=
    ⟨⟨homAB.1.1,fun x y hxy => hBE y (homAB.1.2 x y hxy)⟩,
      homAB.2.1,ConstructionProbePushout.composition_preserves hAE homAB.2.2 homBE.2.2⟩
  have homCF : Hom C F GC GF e e ic :=
    ⟨⟨homCD.1.1,fun x y hxy => hDF y (homCD.1.2 x y hxy)⟩,
      homCD.2.1,ConstructionProbePushout.composition_preserves hCF homCD.2.2 homDF.2.2⟩
  have consAE := ConstructionIntermediate.conservative_comp hmB hmE consAB consBE homBE.2.2 homAE.1 hAE
  have consCF := ConstructionIntermediate.conservative_comp hmD hmF consCD consDF homDF.2.2 homCF.1 hCF
  exact ⟨(fun x hx => hBE x (hAB x hx)),hAC,hEF,(fun x hx => hDF x (hCD x hx)),
    homAE,consAE,homAC,consAC,homEF,consEF,homCF,consCF,
    ConstructionPushoutPasting.paste hM homAB.1 homBD homCD homBE homDF hAE hCF hPush hPush'⟩

/-- Source future_cut's selected successor: the earlier future apex R is
placed inside the old original stage D, then the actual intermediate cell
is pasted. Exact generation is recovered from the resulting full pushout. -/
theorem selected (hM : FirstOrder.Theory.Models M nativeZF)
    {w zero V GV e A B C D E T R PA PB PC PD PE PT PR GA GB GC GD GE GT GR
      ia ib ic idD ie it ir : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ z, ¬ (Project.FirstOrderSemantics.reduct M).mem z zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hv : LeftCancelMonoid V GV e) (hc : Conical V GV e) (hJ : ConditionalJoins V GV)
    (hA : Base V GV e A PA GA ia) (hB : Base V GV e B PB GB ib)
    (hC : Base V GV e C PC GC ic) (hD : Base V GV e D PD GD idD)
    (hE : Base V GV e E PE GE ie) (hT : Base V GV e T PT GT it)
    (hR : Base V GV e R PR GR ir)
    (hSup : Sup V GV e C B R) (hSquare : Square A B C R GA GB GC GR e ia ib ic)
    (hStep : Square B E D T GB GE GD GT e ib ie idD)
    (hAttach : Attachment hM w zero B GB e E GE) (hCD : Subset C D) :
    ∃ F PF GF iF, Base V GV e F PF GF iF ∧ Sup V GV e C E F ∧ Subset F T ∧
      Attachment hM w zero R GR e F GF ∧ Square A E C F GA GE GC GF e ia ie ic := by
  have hRD : Subset R D := hSup.2.2.2 D ⟨hD.1.1,hD.1.2.1,hD.1.2.2.1⟩ hCD hStep.2.1
  obtain ⟨F,PF,GF,iF,hF,_,hFT,hRF,hMid⟩ := ConstructionIntermediate.intermediate hM hw hz hzw
    hv hc hJ hB hE hD hT hR hStep hAttach hSup.2.2.1 hRD
  have hOut := paste hM hB.2.2.2.2.1 hR.2.2.2.2.1 hE.2.2.2.2.1 hF.2.2.2.2.1 hA.2.2.2.2.2.2.1 hB.2.2.2.2.2.2.1 hC.2.2.2.2.2.2.1
    hR.2.2.2.2.2.2.1 hSquare hMid
  have hGenerated := ConstructionIntermediate.apex_sup hM hE hC hF hOut
  exact ⟨F,PF,GF,iF,hF,⟨hGenerated.1,hGenerated.2.2.1,hGenerated.2.1,
    fun S hS hCS hES => hGenerated.2.2.2 S hS hES hCS⟩,hFT,hRF,hOut⟩

/-- Source restrict_omitted follows from the actual cover and absence of a
retained new element. No decidable/external successor structure is used. -/
theorem omitted_cut (hM : FirstOrder.Theory.Models M nativeZF)
    {V I R bottom S retained i j A B : M.Carrier .set}
    (hTimeline : Timeline hM V I R bottom S) (hCover : Cover I R i j)
    (hA : CutAt retained S i A) (hB : CutAt retained S j B)
    (hOmit : ∀ x, (Project.FirstOrderSemantics.reduct M).mem x retained → ¬ NewAt I R S i x) :
    A = B := by
  classical
  obtain ⟨D,hD,hA⟩ := hA
  obtain ⟨T,hT,hB⟩ := hB
  apply (ModelTransfer.extensionality hM).eq_of_same_members A B
  intro x
  constructor
  · intro hx
    obtain ⟨hRet,hxD⟩ := (hA x).mp hx
    obtain ⟨E,hE,hxE⟩ := hTimeline.2.2.2.2.2.1 i j x (Or.inr hCover.2.2.1) ⟨D,hD,hxD⟩
    have he := function_unique hTimeline.2.1 hE hT
    exact (hB x).mpr ⟨hRet,he ▸ hxE⟩
  · intro hx
    obtain ⟨hRet,hxT⟩ := (hB x).mp hx
    apply Classical.byContradiction
    intro hNot
    apply hOmit x hRet
    refine ⟨hCover.1,j,hCover,⟨T,hT,hxT⟩,?_⟩
    rintro ⟨E,hE,hxE⟩
    have he := function_unique hTimeline.2.1 hE hD
    exact hNot ((hA x).mpr ⟨hRet,he ▸ hxE⟩)

/-- Local induction witnesses remain propositions about actual internal
sets. Collect no chosen family of proof witnesses or representatives. -/
def LocalSquares (V GV e K Bs Ds A C GA GC ia ic : M.Carrier .set) : Prop :=
  ∀ i B D, (Project.FirstOrderSemantics.reduct M).mem i K →
    PureKuratowski.PairMember M i B Bs → PureKuratowski.PairMember M i D Ds →
    ∃ PB PD GB GD ib idD, Base V GV e B PB GB ib ∧ Base V GV e D PD GD idD ∧
      Square A B C D GA GB GC GD e ia ib ic

/-- Identify supplied multiplication-family values with the actual local
Base witnesses. The typed graph premise rules out junk graph rows. -/
theorem products_at
    {K GV Domains Muls i D G : M.Carrier .set}
    (hD : FunctionOn K Domains) (hP : Products K GV Domains Muls)
    (hiD : PureKuratowski.PairMember M i D Domains) (hiG : PureKuratowski.PairMember M i G Muls) :
    Multiplication D GV G := by
  obtain ⟨D',hD',hG⟩ := ((hP.2 i G).mp hiG).2
  have he := function_unique hD hD' hiD
  exact he ▸ hG

/-- The actual families from ConstructionFutureFamily supply Square.union's
input, without selecting one Base witness simultaneously at each index. -/
theorem local_family (hM : FirstOrder.Theory.Models M nativeZF)
    {V GV e K Bs Ds BMs DMs A C GA GC ia ic : M.Carrier .set}
    (hBs : FunctionOn K Bs) (hDs : FunctionOn K Ds)
    (hBM : Products K GV Bs BMs) (hDM : Products K GV Ds DMs)
    (hAC : Subset A C) (hLocal : LocalSquares V GV e K Bs Ds A C GA GC ia ic) :
    ConstructionUnionPushout.Family K Bs Ds BMs DMs A C GC GV e ia ic := by
  refine ⟨hBs,hDs,hBM.1,hDM.1,hAC,?_⟩
  intro i B D GB GD hi hiB hiD hiGB hiGD
  obtain ⟨PB,PD,GB',GD',ib,idD,hB,hD,hSquare⟩ := hLocal i B D hi hiB hiD
  have heB := ConstructionFutureFamily.multiplication_unique hM
    (products_at hBs hBM hiB hiGB) ⟨PB,hB.2.1,hB.2.2.1,hB.2.2.2.1⟩
  have heD := ConstructionFutureFamily.multiplication_unique hM
    (products_at hDs hDM hiD hiGD) ⟨PD,hD.2.1,hD.2.2.1,hD.2.2.2.1⟩
  subst GB' GD'
  obtain ⟨hAB,_,hBD,hCD,_,_,_,_,hBDHom,_,_,_,hPush⟩ := hSquare
  exact ⟨hAB,hBD,hCD,hB.2.2.2.1,hD.2.2.2.1,ib,hBDHom.1.1,hB.2.2.2.2.2.2.1,hPush⟩

/-- Source future_cut's directed-union assembly: produce the actual union
apex and identify its exact ordinary supremum using the full pushout.
The interval and cut-continuity hypotheses must still come from Timeline. -/
theorem limit (hM : FirstOrder.Theory.Models M nativeZF)
    {V GV e K E Bs Ds BMs DMs A B C PA PB PC GA GB GC ia ib ic : M.Carrier .set}
    (hv : LeftCancelMonoid V GV e) (hc : Conical V GV e) (hJ : ConditionalJoins V GV)
    (hIndex : IndexLaws K E) (hne : ∃ i, (Project.FirstOrderSemantics.reduct M).mem i K)
    (hBs : FunctionOn K Bs) (hDs : FunctionOn K Ds)
    (hBM : Products K GV Bs BMs) (hDM : Products K GV Ds DMs)
    (hBMono : MonotoneImages K E Bs) (hDMono : MonotoneImages K E Ds)
    (hLocal : LocalSquares V GV e K Bs Ds A C GA GC ia ic)
    (hUnion : Union K Bs B)
    (hA : Base V GV e A PA GA ia) (hB : Base V GV e B PB GB ib) (hC : Base V GV e C PC GC ic) :
    ∃ D PD GD idD, Base V GV e D PD GD idD ∧ Union K Ds D ∧ Sup V GV e C B D ∧
      Square A B C D GA GB GC GD e ia ib ic := by
  have hStagesB : Stages V GV e Bs := by
    intro i Bi hiB
    have hi := function_input hBs hiB
    obtain ⟨Di,hiD,_⟩ := hDs.2 i hi
    obtain ⟨_,_,_,_,_,_,hBaseB,_,_⟩ := hLocal i Bi Di hi hiB hiD
    exact hBaseB.1
  have hStagesD : Stages V GV e Ds := by
    intro i Di hiD
    have hi := function_input hDs hiD
    obtain ⟨Bi,hiB,_⟩ := hBs.2 i hi
    obtain ⟨_,_,_,_,_,_,_,hBaseD,_⟩ := hLocal i Bi Di hi hiB hiD
    exact hBaseD.1
  obtain ⟨i,hi⟩ := hne
  obtain ⟨Bi,hiB,_⟩ := hBs.2 i hi
  obtain ⟨Di,hiD,_⟩ := hDs.2 i hi
  obtain ⟨_,_,_,_,_,_,_,_,hSquare⟩ := hLocal i Bi Di hi hiB hiD
  have hFamily := local_family hM hBs hDs hBM hDM hSquare.2.1 hLocal
  obtain ⟨D,PD,GD,idD,hUD,hBaseD⟩ := ConstructionSubobjectUnion.directedSup hM hv hc hJ
    hIndex ⟨i,hi⟩ hDs hDMono hStagesD
  have hOut := ConstructionUnionPushout.union_square hM hv hc hJ hIndex ⟨i,hi⟩ hFamily
    hStagesB hStagesD hBMono hDMono hUnion hUD hA hB hC hBaseD
  have hSup := ConstructionIntermediate.apex_sup hM hB hC hBaseD hOut
  exact ⟨D,PD,GD,idD,hBaseD,hUD,⟨hSup.1,hSup.2.2.1,hSup.2.1,
    fun S hS hCS hBS => hSup.2.2.2 S hS hBS hCS⟩,hOut⟩

def localSquaresFormula {m : Nat} (V GV e K Bs Ds A C GA GC ia ic : Fin m) : Project.Formula 1 m :=
  (.forallE (.forallE (.forallE (.imp (.mem (.bound 2) (.bound K.succ.succ.succ)) (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge Bs.succ.succ.succ 2 1)) (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge Ds.succ.succ.succ 2 0)) (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.conj (ConstructionSelectedCellRestriction.baseFormula V.succ.succ.succ.succ.succ.succ.succ.succ.succ GV.succ.succ.succ.succ.succ.succ.succ.succ.succ e.succ.succ.succ.succ.succ.succ.succ.succ.succ 7 5 3 1) (.conj (ConstructionSelectedCellRestriction.baseFormula V.succ.succ.succ.succ.succ.succ.succ.succ.succ GV.succ.succ.succ.succ.succ.succ.succ.succ.succ e.succ.succ.succ.succ.succ.succ.succ.succ.succ 6 4 2 0) (ConstructionUnionPushout.square A.succ.succ.succ.succ.succ.succ.succ.succ.succ 7 C.succ.succ.succ.succ.succ.succ.succ.succ.succ 6 GA.succ.succ.succ.succ.succ.succ.succ.succ.succ 3 GC.succ.succ.succ.succ.succ.succ.succ.succ.succ 2 e.succ.succ.succ.succ.succ.succ.succ.succ.succ ia.succ.succ.succ.succ.succ.succ.succ.succ.succ 1 ic.succ.succ.succ.succ.succ.succ.succ.succ.succ)))))))))))))))

theorem localSquaresFormula_freeClosed {m : Nat} (V GV e K Bs Ds A C GA GC ia ic : Fin m) :
    (localSquaresFormula V GV e K Bs Ds A C GA GC ia ic).FreeClosed := by
  simp -implicitDefEqProofs [localSquaresFormula,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,ConstructionSelectedCellRestriction.baseFormula_freeClosed,ConstructionUnionPushout.square_freeClosed]

theorem localSquaresFormula_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (V GV e K Bs Ds A C GA GC ia ic : Fin m) :
    Project.Formula.satisfies env (localSquaresFormula V GV e K Bs Ds A C GA GC ia ic) ↔ LocalSquares (env.bound V) (env.bound GV) (env.bound e) (env.bound K) (env.bound Bs) (env.bound Ds) (env.bound A) (env.bound C) (env.bound GA) (env.bound GC) (env.bound ia) (env.bound ic) := by
  simp only [localSquaresFormula,LocalSquares,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,ConstructionSelectedCellRestriction.baseFormula_semantics hM,ConstructionUnionPushout.square_semantics hM]
  rfl

def initialSentence {m : Nat} (V GV e A C PA PC GA GC ia ic : Fin m) : Project.Sentence where
  formula := Project.Formula.forallClosure m
    (.imp (ProjectSyntax.encode id (ForcingDiagramPoset.leftCancelMonoid V GV e)) (.imp (ProjectSyntax.encode id (ForcingDiagramPoset.conical V GV e)) (.imp (ConstructionProbeSharedIntersections.conditionalJoins V GV) (.imp (ConstructionSelectedCellRestriction.baseFormula V GV e A PA GA ia) (.imp (ConstructionSelectedCellRestriction.baseFormula V GV e C PC GC ic) (.imp (Project.Formula.subset (.bound A) (.bound C)) (.conj (ConstructionIntermediate.sup V GV e C A C) (ConstructionUnionPushout.square A A C C GA GA GC GC e ia ia ic))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,Project.Formula.subset,ConstructionProbeSharedIntersections.conditionalJoins_freeClosed,ConstructionSelectedCellRestriction.baseFormula_freeClosed,ConstructionUnionPushout.square_freeClosed,ConstructionIntermediate.sup_freeClosed]

theorem initial_models {m : Nat} (V GV e A C PA PC GA GC ia ic : Fin m) (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence (initialSentence V GV e A C PA PC GA GC ia ic)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) (initialSentence V GV e A C PA PC GA GC ia ic)]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_subset_iff,Project.Term.eval_bound,GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),ForcingDiagramPoset.leftCancelMonoid_semantics (M := M),ForcingDiagramPoset.conical_semantics (M := M),ConstructionProbeSharedIntersections.conditionalJoins_semantics hM,ConstructionSelectedCellRestriction.baseFormula_semantics hM,ConstructionUnionPushout.square_semantics hM,ConstructionIntermediate.sup_semantics hM]
  exact initial hM

theorem initial_kernel_certificate {m : Nat} (V GV e A C PA PC GA GC ia ic : Fin m) :
    FirstOrder.Derives nativeZF [] (Project.fo_sentence (initialSentence V GV e A C PA PC GA GC ia ic)) :=
  ModelTransfer.derives (fun _ hM => initial_models V GV e A C PA PC GA GC ia ic hM)

def selectedSentence {m : Nat} (w zero V GV e A B C D E T R PA PB PC PD PE PT PR GA GB GC GD GE GT GR ia ib ic idD ie it ir : Fin m) : Project.Sentence where
  formula := Project.Formula.forallClosure m
    (.imp (Project.Formula.isOmega (.bound w)) (.imp (Project.Formula.isEmpty (.bound zero)) (.imp (.mem (.bound zero) (.bound w)) (.imp (ProjectSyntax.encode id (ForcingDiagramPoset.leftCancelMonoid V GV e)) (.imp (ProjectSyntax.encode id (ForcingDiagramPoset.conical V GV e)) (.imp (ConstructionProbeSharedIntersections.conditionalJoins V GV) (.imp (ConstructionSelectedCellRestriction.baseFormula V GV e A PA GA ia) (.imp (ConstructionSelectedCellRestriction.baseFormula V GV e B PB GB ib) (.imp (ConstructionSelectedCellRestriction.baseFormula V GV e C PC GC ic) (.imp (ConstructionSelectedCellRestriction.baseFormula V GV e D PD GD idD) (.imp (ConstructionSelectedCellRestriction.baseFormula V GV e E PE GE ie) (.imp (ConstructionSelectedCellRestriction.baseFormula V GV e T PT GT it) (.imp (ConstructionSelectedCellRestriction.baseFormula V GV e R PR GR ir) (.imp (ConstructionIntermediate.sup V GV e C B R) (.imp (ConstructionUnionPushout.square A B C R GA GB GC GR e ia ib ic) (.imp (ConstructionUnionPushout.square B E D T GB GE GD GT e ib ie idD) (.imp (ConstructionCellRestriction.attachmentFormula w zero B GB e E GE) (.imp (Project.Formula.subset (.bound C) (.bound D)) (.existsE (.existsE (.existsE (.existsE (.conj (ConstructionSelectedCellRestriction.baseFormula V.succ.succ.succ.succ GV.succ.succ.succ.succ e.succ.succ.succ.succ 3 2 1 0) (.conj (ConstructionIntermediate.sup V.succ.succ.succ.succ GV.succ.succ.succ.succ e.succ.succ.succ.succ C.succ.succ.succ.succ E.succ.succ.succ.succ 3) (.conj (Project.Formula.subset (.bound 3) (.bound T.succ.succ.succ.succ)) (.conj (ConstructionCellRestriction.attachmentFormula w.succ.succ.succ.succ zero.succ.succ.succ.succ R.succ.succ.succ.succ GR.succ.succ.succ.succ e.succ.succ.succ.succ 3 1) (ConstructionUnionPushout.square A.succ.succ.succ.succ E.succ.succ.succ.succ C.succ.succ.succ.succ 3 GA.succ.succ.succ.succ GE.succ.succ.succ.succ GC.succ.succ.succ.succ 1 e.succ.succ.succ.succ ia.succ.succ.succ.succ ie.succ.succ.succ.succ ic.succ.succ.succ.succ)))))))))))))))))))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,Project.Formula.isOmega,Project.Formula.isEmpty,Project.Formula.subset,ConstructionProbeSharedIntersections.conditionalJoins_freeClosed,ConstructionSelectedCellRestriction.baseFormula_freeClosed,ConstructionUnionPushout.square_freeClosed,ConstructionIntermediate.sup_freeClosed,ConstructionCellRestriction.attachmentFormula_freeClosed]

theorem selected_models {m : Nat} (w zero V GV e A B C D E T R PA PB PC PD PE PT PR GA GB GC GD GE GT GR ia ib ic idD ie it ir : Fin m) (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence (selectedSentence w zero V GV e A B C D E T R PA PB PC PD PE PT PR GA GB GC GD GE GT GR ia ib ic idD ie it ir)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) (selectedSentence w zero V GV e A B C D E T R PA PB PC PD PE PT PR GA GB GC GD GE GT GR ia ib ic idD ie it ir)]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_mem_iff,Project.Formula.satisfies_subset_iff,Project.Term.eval_bound,GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),Project.Formula.satisfies_isOmega_iff,Project.Formula.satisfies_isEmpty_iff,ForcingDiagramPoset.leftCancelMonoid_semantics (M := M),ForcingDiagramPoset.conical_semantics (M := M),ConstructionProbeSharedIntersections.conditionalJoins_semantics hM,ConstructionSelectedCellRestriction.baseFormula_semantics hM,ConstructionUnionPushout.square_semantics hM,ConstructionIntermediate.sup_semantics hM,ConstructionCellRestriction.attachmentFormula_semantics hM]
  exact selected hM

theorem selected_kernel_certificate {m : Nat} (w zero V GV e A B C D E T R PA PB PC PD PE PT PR GA GB GC GD GE GT GR ia ib ic idD ie it ir : Fin m) :
    FirstOrder.Derives nativeZF [] (Project.fo_sentence (selectedSentence w zero V GV e A B C D E T R PA PB PC PD PE PT PR GA GB GC GD GE GT GR ia ib ic idD ie it ir)) :=
  ModelTransfer.derives (fun _ hM => selected_models w zero V GV e A B C D E T R PA PB PC PD PE PT PR GA GB GC GD GE GT GR ia ib ic idD ie it ir hM)

def omittedSentence {m : Nat} (V I R bottom S retained i j A B : Fin m) : Project.Sentence where
  formula := Project.Formula.forallClosure m
    (.imp (ConstructionFirstAppearance.timeline V I R bottom S) (.imp (ConstructionFirstAppearance.cover I R i j) (.imp (ConstructionFutureFamily.cutAt retained S i A) (.imp (ConstructionFutureFamily.cutAt retained S j B) (.imp (.forallE (.imp (.mem (.bound 0) (.bound retained.succ)) (.neg (ConstructionFirstAppearance.newAt I.succ R.succ S.succ i.succ 0)))) (Project.Formula.extensionalEq (.bound A) (.bound B)))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,Project.Formula.extensionalEq,ConstructionFirstAppearance.timeline_freeClosed,ConstructionFirstAppearance.cover_freeClosed,ConstructionFirstAppearance.newAt_freeClosed,ConstructionFutureFamily.cutAt_freeClosed]

theorem omitted_models {m : Nat} (V I R bottom S retained i j A B : Fin m) (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence (omittedSentence V I R bottom S retained i j A B)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) (omittedSentence V I R bottom S retained i j A B)]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_neg_iff,Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,Project.Formula.satisfies_extensionalEq_iff_eq (ModelTransfer.extensionality hM),ConstructionFirstAppearance.timeline_semantics hM,ConstructionFirstAppearance.cover_semantics hM,ConstructionFirstAppearance.newAt_semantics hM,ConstructionFutureFamily.cutAt_semantics hM]
  exact omitted_cut hM

theorem omitted_kernel_certificate {m : Nat} (V I R bottom S retained i j A B : Fin m) :
    FirstOrder.Derives nativeZF [] (Project.fo_sentence (omittedSentence V I R bottom S retained i j A B)) :=
  ModelTransfer.derives (fun _ hM => omitted_models V I R bottom S retained i j A B hM)

def limitSentence {m : Nat} (V GV e K E Bs Ds BMs DMs A B C PA PB PC GA GB GC ia ib ic : Fin m) : Project.Sentence where
  formula := Project.Formula.forallClosure m
    (.imp (ProjectSyntax.encode id (ForcingDiagramPoset.leftCancelMonoid V GV e)) (.imp (ProjectSyntax.encode id (ForcingDiagramPoset.conical V GV e)) (.imp (ConstructionProbeSharedIntersections.conditionalJoins V GV) (.imp (ConstructionDirectedSystem.indexLaws K E) (.imp (.existsE (.mem (.bound 0) (.bound K.succ))) (.imp (ProjectSyntax.encode id (Source.SetLanguage.functionOn Bs K)) (.imp (ProjectSyntax.encode id (Source.SetLanguage.functionOn Ds K)) (.imp (ConstructionFutureFamily.productsFormula K GV Bs BMs) (.imp (ConstructionFutureFamily.productsFormula K GV Ds DMs) (.imp (ConstructionBlockStages.monotoneImages K E Bs) (.imp (ConstructionBlockStages.monotoneImages K E Ds) (.imp (localSquaresFormula V GV e K Bs Ds A C GA GC ia ic) (.imp (ConstructionSubobjectUnion.unionFormula K Bs B) (.imp (ConstructionSelectedCellRestriction.baseFormula V GV e A PA GA ia) (.imp (ConstructionSelectedCellRestriction.baseFormula V GV e B PB GB ib) (.imp (ConstructionSelectedCellRestriction.baseFormula V GV e C PC GC ic) (.existsE (.existsE (.existsE (.existsE (.conj (ConstructionSelectedCellRestriction.baseFormula V.succ.succ.succ.succ GV.succ.succ.succ.succ e.succ.succ.succ.succ 3 2 1 0) (.conj (ConstructionSubobjectUnion.unionFormula K.succ.succ.succ.succ Ds.succ.succ.succ.succ 3) (.conj (ConstructionIntermediate.sup V.succ.succ.succ.succ GV.succ.succ.succ.succ e.succ.succ.succ.succ C.succ.succ.succ.succ B.succ.succ.succ.succ 3) (ConstructionUnionPushout.square A.succ.succ.succ.succ B.succ.succ.succ.succ C.succ.succ.succ.succ 3 GA.succ.succ.succ.succ GB.succ.succ.succ.succ GC.succ.succ.succ.succ 1 e.succ.succ.succ.succ ia.succ.succ.succ.succ ib.succ.succ.succ.succ ic.succ.succ.succ.succ))))))))))))))))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,ConstructionProbeSharedIntersections.conditionalJoins_freeClosed,ConstructionSelectedCellRestriction.baseFormula_freeClosed,ConstructionUnionPushout.square_freeClosed,ConstructionIntermediate.sup_freeClosed,ConstructionFutureFamily.productsFormula_freeClosed,ConstructionDirectedSystem.indexLaws_freeClosed,ConstructionBlockStages.monotoneImages_freeClosed,ConstructionSubobjectUnion.unionFormula_freeClosed,localSquaresFormula_freeClosed]

theorem limit_models {m : Nat} (V GV e K E Bs Ds BMs DMs A B C PA PB PC GA GB GC ia ib ic : Fin m) (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence (limitSentence V GV e K E Bs Ds BMs DMs A B C PA PB PC GA GB GC ia ib ic)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) (limitSentence V GV e K E Bs Ds BMs DMs A B C PA PB PC GA GB GC ia ib ic)]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),ForcingDiagramPoset.leftCancelMonoid_semantics (M := M),ForcingDiagramPoset.conical_semantics (M := M),ConstructionProbeSharedIntersections.conditionalJoins_semantics hM,ConstructionSelectedCellRestriction.baseFormula_semantics hM,ConstructionUnionPushout.square_semantics hM,ConstructionIntermediate.sup_semantics hM,ConstructionFutureFamily.productsFormula_semantics hM,ConstructionDirectedSystem.indexLaws_semantics hM,ConstructionBlockStages.monotoneImages_semantics hM,ConstructionSubobjectUnion.unionFormula_semantics hM,ForcingConditionGraphs.functionOn_semantics (M := M),localSquaresFormula_semantics hM]
  exact limit hM

theorem limit_kernel_certificate {m : Nat} (V GV e K E Bs Ds BMs DMs A B C PA PB PC GA GB GC ia ib ic : Fin m) :
    FirstOrder.Derives nativeZF [] (Project.fo_sentence (limitSentence V GV e K E Bs Ds BMs DMs A B C PA PB PC GA GB GC ia ib ic)) :=
  ModelTransfer.derives (fun _ hM => limit_models V GV e K E Bs Ds BMs DMs A B C PA PB PC GA GB GC ia ib ic hM)

end PPAC.Migration.ConstructionFutureCut
