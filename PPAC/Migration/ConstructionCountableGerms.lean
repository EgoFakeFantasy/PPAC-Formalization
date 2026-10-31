/- Pinned ConcreteQuotients.cells_bottom_countable:154 and countable_germs:210.
Consume the existing saturation zero row, literal flattened bottom and entire
cell-tower quotient. The initial carrier is the existing Base's internal omega;
no bottom-countability oracle or replacement base is introduced. -/
import PPAC.Migration.ConstructionCountableQuotient

namespace PPAC.Migration.ConstructionCountableGerms
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ConstructionTowerHistory (Row)
open ForcingSupportSize (Small MapsTo Injection)
open ForcingConditionGraphs (function_input function_unique)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

theorem initial_row (hM : FirstOrder.Theory.Models M nativeZF)
    (hOrder : Project.Gw_order_d (InnerModel.Js_lt_d (M := Project.FirstOrderSemantics.reduct M)))
    (hChoice : ConstructionDirectedCardinality.Choice (M := M))
    {w Q values top D mul unit mark H C zero one u K mu B history : M.Carrier .set}
    (hctx : ConstructionSaturationIterationCases.Context hM w Q values top D mul unit mark H C zero one u K mu B)
    (hrec : ConstructionSaturationIteration.Recursive hM w Q values top D mul unit mark H C zero one K mu B B history)
    (hzB : (Project.FirstOrderSemantics.reduct M).mem zero B) :
    ∃ incoming identity, Row history zero D mul unit mark H C incoming identity zero := by
  have hctxCopy := hctx
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,hB,_⟩ := hctxCopy
  have hv := (ConstructionSaturationIterationValidity.recursive_valid_small hM hOrder hChoice hctx hrec (fun _ h => h)).1
  obtain ⟨code,hCode,_⟩ := hv.1.1.2 zero hzB
  obtain ⟨prior,hRestrict,hOp⟩ := hrec.2 zero hzB code hCode
  have hPriorRec := Structure.IsRecursiveSequence.restriction hrec hzB hRestrict
  have hPrior := ConstructionSaturationIterationValidity.recursive_valid_small hM hOrder hChoice hctx hPriorRec (hB.transitive zero hzB)
  have hGood : ConstructionSaturationIteration.Good hM w Q values top D mul unit mark H C mu B prior zero :=
    ⟨hB.mem hzB,hzB,hPrior.1,hPrior.2⟩
  have hCase := (ConstructionSaturationIteration.valid_step hM hOrder hChoice hctx hGood hOp).1
  rcases hCase with ⟨_,hInitial⟩ | ⟨hne,_⟩ | ⟨hne,_⟩
  · obtain ⟨_,identity,incoming,_,_,_,_,_,_,_,_,hPack⟩ := hInitial
    exact ⟨incoming,identity,code,hCode,hPack⟩
  · exact (hne rfl).elim
  · exact (hne rfl).elim

/-- The SAME least flattened stage is the image of the actual omega base. -/
theorem bottom_countable (hM : FirstOrder.Theory.Models M nativeZF)
    (hOrder : Project.Gw_order_d (InnerModel.Js_lt_d (M := Project.FirstOrderSemantics.reduct M)))
    (hChoice : ConstructionDirectedCardinality.Choice (M := M))
    {w Q values top mul unit mark H C zero one u K mu B history outerF kappa V
      terminalLegs traces Indices A r I R S ODomains OE OImages bottom : M.Carrier .set}
    (hctx : ConstructionSaturationIterationCases.Context hM w Q values top w mul unit mark H C zero one u K mu B)
    (hrec : ConstructionSaturationIteration.Recursive hM w Q values top w mul unit mark H C zero one K mu B B history)
    (hindex : ConstructionSaturationIndex.Data hM w mu kappa B)
    (ht : ConstructionBlockTraces.Family hM w Q values top zero one K mu history outerF kappa traces)
    (hd : ConstructionBlockIndex.Data hM kappa traces Indices A r I R)
    (ho : ConstructionBlockContinuity.OuterData B history outerF terminalLegs V ODomains OE OImages)
    (hb : ConstructionFlatOuter.Bottoms kappa zero S OImages)
    (hT : ConstructionFirstAppearance.Timeline hM V I R bottom S) :
    ∃ base, PureKuratowski.PairMember M bottom base S ∧ Small base w := by
  have hctxCopy := hctx
  obtain ⟨hw,_,_,_,_,_,_,hz,_,_⟩ := hctxCopy
  have hZF := ModelTransfer.project_models_iff.mp hM
  let P := KuratowskiZF.interpretation hM
  have hk := hindex.1.1
  have hzK := Structure.IsOrdinal.empty_mem_of_nonempty (ZF.modelsKP hZF) hk ⟨w,hindex.2.2.1⟩ hz
  have hzB := (hindex.2.2.2.1 zero).mpr (Or.inl hzK)
  obtain ⟨incoming,identity,hrow⟩ := initial_row hM hOrder hChoice hctx hrec hzB
  have hzD := ConstructionTowerHistory.chart_of_row 0 ho.1 hzB hrow
  obtain ⟨literal,hBottom,_,_⟩ := ConstructionCutLimits.construction hM hk ht hd ⟨w,hindex.2.2.1⟩
  have he : bottom = literal := by
    rcases hT.2.2.2.1 literal hBottom.2.1 with he | hl
    · exact he
    rcases hBottom.2.2 bottom hT.2.2.1 with he | hr
    · exact he.symm
    exact False.elim (hT.1.linear.2.1.1 bottom hT.2.2.1
      (hT.1.linear.2.1.2 bottom hT.2.2.1 literal hBottom.2.1 bottom hT.2.2.1 hl hr))
  subst literal
  obtain ⟨base,hbase,_⟩ := hT.2.1.2 bottom hT.2.2.1
  obtain ⟨image,himage,_⟩ := ho.2.2.2.2.1.1.2 zero hzB
  have hRange := ((ho.2.2.2.2.1.2 zero image).mp himage).2
  obtain ⟨N,f,hN,hf,hRange⟩ := hRange
  have en : N = w := function_unique ho.1.1 hN hzD
  subst N
  have hMaps := ho.2.2.1.2 zero w f hzB hzD hf
  have hMapImage : MapsTo w image f := ⟨hMaps.1,fun x y hxy => (hRange y).mpr ⟨x,function_input hMaps.1 hxy,hxy⟩⟩
  have eqImage : base = image := (ModelTransfer.extensionality hM).eq_of_same_members base image (by
    intro x
    have hLeft : (Project.FirstOrderSemantics.reduct M).mem x base ↔ ConstructionFirstAppearance.At S bottom x := by
      constructor
      · exact fun hx => ⟨base,hbase,hx⟩
      · rintro ⟨other,ho',hx⟩
        exact function_unique hT.2.1 ho' hbase ▸ hx
    have hRight : ConstructionFirstAppearance.At OImages zero x ↔ (Project.FirstOrderSemantics.reduct M).mem x image := by
      constructor
      · rintro ⟨other,ho',hx⟩
        exact function_unique ho.2.2.2.2.1.1 ho' himage ▸ hx
      · exact fun hx => ⟨image,himage,hx⟩
    exact hLeft.trans ((hb zero bottom hzK hBottom.1 x).trans hRight))
  obtain ⟨id,hId⟩ := ZF.exists_identityBijection hZF P w
  have hSmall := ExistingOrdinalImage.ordinal_image_bound_l P hZF
    (ExistingCardinalBounds.omega_cardinal_l P hZF hw).1 ⟨id,hId.1⟩
    ((ForcingSupportSize.native_mapsTo hM w image f).mp hMapImage)
    (fun y hy => (hRange y).mp hy)
  exact ⟨base,hbase,eqImage ▸ (ForcingSupportSize.native_small hM image w).mpr hSmall⟩

/-- Source countable_germs for the actual saturated terminal row. All cells,
closures, indices, gates and the countable bottom are produced here. -/
theorem construction (hM : FirstOrder.Theory.Models M nativeZF)
    (hOrder : Project.Gw_order_d (InnerModel.Js_lt_d (M := Project.FirstOrderSemantics.reduct M)))
    (hChoice : ConstructionDirectedCardinality.Choice (M := M))
    {w Q values top mul unit mark H C zero one u K mu B history P outerF kappa V GV e markV HV CV terminalLegs baseV labels q root vertices chain : M.Carrier .set}
    (hctx : ConstructionSaturationIterationCases.Context hM w Q values top w mul unit mark H C zero one u K mu B)
    (hrec : ConstructionSaturationIteration.Recursive hM w Q values top w mul unit mark H C zero one K mu B B history)
    (hindex : ConstructionSaturationIndex.Data hM w mu kappa B)
    (hf : ConstructionTowerTransitions.Matrix B history zero P outerF)
    (hr : Row history kappa V GV e markV HV CV terminalLegs baseV kappa)
    (hX : ConstructionComponentCarrier.Carrier V labels GV q vertices)
    (hC : ConstructionComponentCofinal.Chain w V labels GV q zero root vertices chain)
    (hq : Injection V labels q) :
    ∃ group quotient projection, ConstructionGermCosets.Result w V labels GV q root chain group quotient projection := by
  obtain ⟨traces,Indices,A,r,I,R,S,ODomains,OE,OImages,bottom,cells,ht,hd,hS,ho,hb,_,hT,_,hCells,hNew⟩ :=
    ConstructionStepCellSelection.construction hM hOrder hChoice hctx hrec hindex hf hr
  obtain ⟨index,hIndex⟩ := ConstructionFirstAppearance.exists_index hM hT
  obtain ⟨base,hbase,hSmall⟩ := bottom_countable hM hOrder hChoice hctx hrec hindex ht hd ho hb hT
  have hv := (ConstructionSaturationIterationValidity.recursive_valid_small hM hOrder hChoice hctx hrec (fun _ h => h)).1
  have hV := (hv.2.1 kappa hindex.2.2.2.1.predecessor_mem V GV e markV HV CV terminalLegs baseV hr).1
  have hStages := ConstructionCellRestriction.actual_stages hM hv hindex.2.2.2.1 hf hr ht hS.1
  have hctxCopy := hctx
  obtain ⟨hw,_,_,_,_,_,_,hz,hzw,_⟩ := hctxCopy
  exact ConstructionCountableQuotient.construction hM hChoice hw hz hzw hV.1 hV.2.1 hV.2.2.1
    hStages hT hIndex hCells hNew hd hS.1 hbase hSmall hX hC hq

def constructionSentence {m : Nat} (w Q values top mul unit mark H C zero one u K mu B history P outerF kappa V GV e markV HV CV terminalLegs baseV labels q root vertices chain : Fin m) : Project.Sentence where
  formula := Project.Formula.forallClosure m (.imp (ConstructionSaturationIterationCases.context w Q values top w mul unit mark H C zero one u K mu B) (.imp (ConstructionSaturationIteration.recursive w Q values top w mul unit mark H C zero one K mu B B history) (.imp (ConstructionSaturationIndex.data w mu kappa B) (.imp (ConstructionTowerTransitions.matrix B history zero P outerF) (.imp (ConstructionTowerHistory.row history kappa V GV e markV HV CV terminalLegs baseV kappa) (.imp (ConstructionComponentCarrier.carrier V labels GV q vertices) (.imp (ConstructionComponentCofinal.chain w V labels GV q zero root vertices chain) (.imp (ProjectSyntax.encode id (Source.SetLanguage.injection q V labels)) (.existsE (.existsE (.existsE (ConstructionGermCosets.resultFormula w.succ.succ.succ V.succ.succ.succ labels.succ.succ.succ GV.succ.succ.succ q.succ.succ.succ root.succ.succ.succ chain.succ.succ.succ 2 1 0))))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,ConstructionGermCosets.resultFormula_freeClosed,
      ConstructionSaturationIterationCases.context_freeClosed,
      ConstructionSaturationIteration.recursive_freeClosed,
      ConstructionSaturationIndex.data_freeClosed,
      ConstructionTowerTransitions.matrix_freeClosed,
      ConstructionTowerHistory.row_freeClosed,
      ConstructionComponentCarrier.carrier_freeClosed,
      ConstructionComponentCofinal.chain_freeClosed]

theorem construction_models {m : Nat} (w Q values top mul unit mark H C zero one u K mu B history P outerF kappa V GV e markV HV CV terminalLegs baseV labels q root vertices chain : Fin m)
    (hM : FirstOrder.Theory.Models M nativeZF)
    (hOrder : Project.Gw_order_d (InnerModel.Js_lt_d (M := Project.FirstOrderSemantics.reduct M)))
    (hChoice : ConstructionDirectedCardinality.Choice (M := M)) :
    (Project.fo_sentence (constructionSentence w Q values top mul unit mark H C zero one u K mu B history P outerF kappa V GV e markV HV CV terminalLegs baseV labels q root vertices chain)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM)
    (constructionSentence w Q values top mul unit mark H C zero one u K mu B history P outerF kappa V GV e markV HV CV terminalLegs baseV labels q root vertices chain)]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_exists_iff,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingSupportSize.injection_semantics (M := M),ConstructionGermCosets.resultFormula_semantics hM,
    ConstructionSaturationIterationCases.context_semantics hM,
    ConstructionSaturationIteration.recursive_semantics hM,
    ConstructionSaturationIndex.data_semantics hM,
    ConstructionTowerTransitions.matrix_semantics hM,
    ConstructionTowerHistory.row_semantics hM,
    ConstructionComponentCarrier.carrier_semantics hM,
    ConstructionComponentCofinal.chain_semantics hM]
  exact construction hM hOrder hChoice

theorem construction_kernel_certificate {m : Nat} (w Q values top mul unit mark H C zero one u K mu B history P outerF kappa V GV e markV HV CV terminalLegs baseV labels q root vertices chain : Fin m) : FirstOrder.Derives nativeZF []
    (Project.fo_sentence (ConstructibleGround.relative (constructionSentence w Q values top mul unit mark H C zero one u K mu B history P outerF kappa V GV e markV HV CV terminalLegs baseV labels q root vertices chain))) := by
  apply ModelTransfer.derives
  intro M hM
  have hL := ConstructibleSource.model_zf hM
  have hRawChoice := (Project.FirstOrderSemantics.sentence_correct
    (ModelTransfer.extensionality hL) Axioms.choice).mp (ConstructibleSource.model_choice hM)
  let z := Classical.choice ((ConstructibleSource.model hM).nonempty .set)
  let env : SetTheory.Env (Project.FirstOrderSemantics.reduct (ConstructibleSource.model hM)) 0 :=
    { bound := Fin.elim0, free := fun _ => z }
  have hSat : Project.Formula.satisfies env (ConstructionDirectedCardinality.choice (m := 0)) := by
    change Project.Formula.satisfies env (Axioms.choice.formula.rename Fin.elim0)
    rw [Project.Formula.satisfies_rename]
    exact hRawChoice env.free
  have hChoice := (ConstructionDirectedCardinality.choice_semantics hL env).mp hSat
  apply ConstructibleGround.relative_models hM (constructionSentence w Q values top mul unit mark H C zero one u K mu B history P outerF kappa V GV e markV HV CV terminalLegs baseV labels q root vertices chain)
  exact (Project.FirstOrderSemantics.sentence_correct
    (ModelTransfer.extensionality hL) (constructionSentence w Q values top mul unit mark H C zero one u K mu B history P outerF kappa V GV e markV HV CV terminalLegs baseV labels q root vertices chain)).mp (construction_models w Q values top mul unit mark H C zero one u K mu B history P outerF kappa V GV e markV HV CV terminalLegs baseV labels q root vertices chain hL (ConstructionRoundSelection.l_order hM) hChoice)

end PPAC.Migration.ConstructionCountableGerms
