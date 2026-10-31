/- Pinned ConservativeCells.Cell.map/simulation/pushout, consumed by
CellCuts.Square.realization/intermediate and future_cut's selected successor.
Keep the supplied source Cell. Reuse the actual Probe/Merger producers and
full simulation pushouts; targets remain arbitrary internal base changes. -/
import PPAC.Migration.ConstructionUnionPushout

namespace PPAC.Migration.ConstructionCellBaseChange
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ConstructionCellRestriction (Cell Attachment)
open ConstructionProbePushout (Hom IsPushout)
open ConstructionProbeConservative (Conservative)
open ConstructionProbeSharedIntersections (ConditionalJoins)
open ConstructionProbeMappedPath (NodeMap)
open ForcingDiagramPoset (LeftCancelMonoid Conical)
open ForcingSupportSize (MapsTo Injection)
open ForcingConditionGraphs (IdentityGraph InverseGraph function_input function_unique)
open ConstructionAttachmentCoefficients (OldFixed)
open ForcingSupportedNames (Range)
open ConstructionSelectedCellRestriction (Base)
open ConstructionUnionPushout (Square)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

/-- The actual mapped cell, all extension Object fields, and the conservative
simulation with its complete arbitrary-target pushout. -/
def Mapped (hM : FirstOrder.Theory.Models M nativeZF)
    (w zero D mul e W G unit O N mulN eN f WN GN unitN ON H : M.Carrier .set) : Prop :=
  Hom D W mul G e unit O ∧ Conservative D W mul G O ∧ Hom D N mul mulN e eN f ∧ Conservative D N mul mulN f ∧
  Cell hM w zero N mulN eN WN GN unitN ON ∧
  LeftCancelMonoid WN GN unitN ∧ Conical WN GN unitN ∧ ConditionalJoins WN GN ∧
  Hom N WN mulN GN eN unitN ON ∧ Conservative N WN mulN GN ON ∧
  Hom W WN G GN unit unitN H ∧ Conservative W WN G GN H ∧
  IsPushout N W WN mulN G GN eN unit unitN O f H ON ∧
  ∃ pairs, ConstructionProbeLetters.Representatives WN WN pairs ∧ MapsTo pairs WN GN

/-- Keep the conditional joins already supplied by the full Merger producer. -/
theorem merger_presentation (hM : FirstOrder.Theory.Models M nativeZF)
    {w n zero N mulN eN PN : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ z, ¬ (Project.FirstOrderSemantics.reduct M).mem z zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hmN : LeftCancelMonoid N mulN eN) (hcN : Conical N mulN eN) (hJN : ConditionalJoins N mulN)
    (hPN : ConstructionMergerRelations.Prescription n N PN)
    (hValidN : ConstructionMergerRelations.Valid n N mulN PN) :
    ∃ CN LN projectionN AN WN TN BN GN unitN ON rootsN,
      ConstructionMergerPushout.Presentation w n zero N mulN eN PN CN LN projectionN AN WN TN BN GN unitN ON rootsN ∧
      LeftCancelMonoid WN GN unitN ∧ Conical WN GN unitN ∧ ConditionalJoins WN GN ∧ Conservative N WN mulN GN ON := by
  obtain ⟨CN,LN,projectionN,KN,AN,WN,IN,TN,BN,GN,unitN,hParent,hUnit,hmWN,hcWN,_,hJWN⟩ :=
    ConstructionMergerWordCones.exists_system hM hw hz hzw hmN hcN hJN hPN hValidN
  obtain ⟨hC,hp,hL,hProjection,hEq,_,_,hAction,_,hCopy,hW,_,_,hWordAction,_,hB,hG,hProduct⟩ := hParent
  obtain ⟨ON,hInj,hOG⟩ := ConstructionMergerOldEmbedding.exists_old_graph hM hz hzw hW
  have hOH : Hom N WN mulN GN eN unitN ON := ⟨hInj.1,(hOG eN unitN).mpr hUnit,
    ConstructionMergerOldEmbedding.preserves_products hOG hWordAction hProduct⟩
  obtain ⟨rootsN,hRootsMap,hRoots⟩ := ConstructionMergerRoots.exists_root_graph hM hw hz hzw hmN hW hC hp hUnit
  exact ⟨CN,LN,projectionN,AN,WN,TN,BN,GN,unitN,ON,rootsN,
    ⟨hmN,hPN,hC,hL,hp,hProjection,hEq,hAction,hCopy,hW,hWordAction,hProduct,hUnit,
      hmWN.1,hmWN.2.2,hB,hG,hOG,hOH,hRootsMap,hRoots⟩,hmWN,hcWN,hJWN,
    ConstructionMergerOldEmbedding.old_conservative hM hw hz hzw hW hB hG hWordAction hProduct hInj hOG⟩

/-- Construct both source alternatives over the supplied conservative base map.
No surjectivity premise: this is Cell.map, not only rangeAttachment. -/
theorem exists_mapped (hM : FirstOrder.Theory.Models M nativeZF)
    {w zero D mul e W G unit O N mulN eN f : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ z, ¬ (Project.FirstOrderSemantics.reduct M).mem z zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hCell : Cell hM w zero D mul e W G unit O)
    (hOld : Conservative D W mul G O) (hJ : ConditionalJoins D mul)
    (hmN : LeftCancelMonoid N mulN eN) (hcN : Conical N mulN eN) (hJN : ConditionalJoins N mulN)
    (hf : Hom D N mul mulN e eN f) (hCons : Conservative D N mul mulN f) :
    ∃ WN GN unitN ON H, Mapped hM w zero D mul e W G unit O N mulN eN f WN GN unitN ON H := by
  rcases hCell with ⟨a,b,d,node,factor,terminal,target,S,C,projection,I,act,E,K,P,hbne,hdne,hA,hTerminal⟩ |
    ⟨n,P,C,L,projection,A,T,B,roots,hn,_,hValid,hA⟩
  · obtain ⟨fa,fb,mapped,hfa,hfb,hfbN,hfbne,_,hMapped,hPathN,_⟩ :=
      ConstructionRequestMaps.probe_map hM hCons hf.2.2 hf.2.1 hA.b_mem hbne hA.path
    obtain ⟨fd,hfd,_⟩ := hf.1.1.2 d hA.d_mem
    have hfdne : fd ≠ eN := fun heq => hdne (hCons.1.2 d e eN (heq ▸ hfd) hf.2.1)
    obtain ⟨factorN,terminalN,targetN,SN,CN,projectionN,IN,actN,EN,WN,unitN,GN,KN,PN,ON,hB,hTerminalN,hConON,hProductN⟩ :=
      ConstructionMappedProbe.exists_presentation hM hw hz hzw hmN hcN hJN hfbN hfbne (hf.1.2 d fd hfd) hfdne hPathN
    have hFactorMap := ConstructionProbeMappedPath.factor_map hA.path hf.1 hMapped hf.2.2 hA.factors hB.factors
    have hTerminalMap := ConstructionProbeMappedPath.terminal_map hA.path hf.1 hMapped hf.2.2 hfa hTerminal hTerminalN
    have hTable := ConstructionProbePath.table_laws hM hw hz hA.monoid hA.path hA.factors hTerminal
    have hMeets := ConstructionProbeTransitions.meets_laws hM hw hA.monoid hA.path hA.factors hTable
    have hTableN := ConstructionProbePath.table_laws hM hw hz hmN hB.path hB.factors hTerminalN
    have hMeetsN := ConstructionProbeTransitions.meets_laws hM hw hmN hB.path hB.factors hTableN
    obtain ⟨letters,hLetters,_,hAlphabet⟩ := ConstructionProbeAlphabetMap.exists_alphabet_simulation hM
      hA.monoid hmN hA.path hB.path hA.factors hB.factors hCons.1 hf.2.2 hCons.2.1 hFactorMap
      hA.representatives hA.letters hA.projection_map hA.projection_law hA.equality
      hB.representatives hB.projection_map hB.equality hMeets hMeetsN hA.action hB.action
      hA.terminals_map hTerminalMap hA.target_law hB.target_law hA.exit_law hB.exit_law hfd
    obtain ⟨H,_,hH,hConH,_,hPush⟩ := ConstructionProbePushout.exists_pushout hA hB hw hz hzw
      hCons hf.2.2 hAlphabet hfb hf.2.1 hfd hFactorMap hTerminalMap hJ hOld hConON hLetters
    have hmWN := ConstructionProbeWordMonoid.monoid_laws hM hw hz hzw hmN hB.alphabet hB.word hB.b_mem hB.old_unit hB.multiplication
    have hcWN := ConstructionProbeOldEmbedding.word_conical hM hw hz hzw hcN hB.alphabet hB.word hB.old_unit hB.multiplication
    have hJWN := ConstructionProbeConditionalJoins.conditional_joins hM hw hz hzw hmN hcN hB.alphabet
      hB.word hB.b_mem hfbne hB.multiplication hB.old_unit hB.old_graph hJN hConON
    have hOldLaws := ConstructionProbeOldEmbeddingSyntax.embedding_laws hM hw hz hzw hmN hB.alphabet
      hB.word hB.b_mem hB.old_unit hB.multiplication hB.old_graph
    have hOH : Hom N WN mulN GN eN unitN ON := ⟨hB.old_map,hOldLaws.1,
      fun x y z fx fy fz hp hx hy hzv => hOldLaws.2.1 x y z fx fy fz hx hy hzv hp⟩
    have hSourceOld := ConstructionProbeOldEmbeddingSyntax.embedding_laws hM hw hz hzw hA.monoid hA.alphabet
      hA.word hA.b_mem hA.old_unit hA.multiplication hA.old_graph
    have hOldHom : Hom D W mul G e unit O := ⟨hA.old_map,hSourceOld.1,
      fun x y z fx fy fz hp hx hy hzv => hSourceOld.2.1 x y z fx fy fz hx hy hzv hp⟩
    exact ⟨WN,GN,unitN,ON,H,hOldHom,hOld,hf,hCons,Or.inl ⟨fa,fb,fd,mapped,factorN,terminalN,targetN,SN,CN,projectionN,IN,actN,EN,KN,PN,hfbne,hfdne,hB,hTerminalN⟩,
      hmWN,hcWN,hJWN,hOH,hConON,hH,hConH,hPush,hProductN⟩
  · obtain ⟨PN,hGraph,hMap,hPN,hValidIff,_,_⟩ := ConstructionMergerPrescriptionMap.exists_system
      hM hA.monoid hmN hA.prescription hCons hf.2.2 hJ
    have hValidN := hValidIff.mpr hValid
    obtain ⟨CN,LN,projectionN,AN,WN,TN,BN,GN,unitN,ON,rootsN,hB,hmWN,hcWN,hJWN,hConON⟩ :=
      merger_presentation hM hw hz hzw hmN hcN hJN hPN hValidN
    obtain ⟨H,hH,hRoots,_,hPush⟩ := ConstructionMergerPushout.exists_pushout hM hA hB hw hz hzw hf hMap
    have hConH := ConstructionMergerWordTransport.simulation_conservative hA hB hM hw hz hzw
      hCons hf.2.2 hf.2.1 hMap hJ hH hPush.1 hRoots
    exact ⟨WN,GN,unitN,ON,H,hA.old_hom,hOld,hf,hCons,Or.inr ⟨n,PN,CN,LN,projectionN,AN,TN,BN,rootsN,hn,
      ConstructionRequestCarrier.wellFormed_of_graph hGraph hPN,hValidN,hB⟩,
      hmWN,hcWN,hJWN,hB.old_hom,hConON,hH,hConH,hPush,BN,hB.product_representatives,hB.product_map⟩

/-- Source presentationPushout's old equation at the actual inverse graph. -/
theorem inverse_old {A B W O F inv ia : M.Carrier .set}
    (hO : MapsTo A W O) (hInv : MapsTo B W inv)
    (hInverse : InverseGraph F inv) (hFixed : OldFixed O F) (hIa : IdentityGraph A ia) :
    NodeMap ia inv O := by
  intro a u
  constructor
  · intro hau
    exact ⟨a,(hIa a a).mpr ⟨function_input hO.1 hau,rfl⟩,(hInverse u a).mp (hFixed a u hau)⟩
  · rintro ⟨b,hab,hbu⟩
    obtain ⟨ha,rfl⟩ := (hIa a b).mp hab
    obtain ⟨v,hav,_⟩ := hO.1.2 a ha
    have eu := function_unique hInv.1 hbu ((hInverse v a).mp (hFixed a v hav))
    exact eu.symm ▸ hav

/-- The actual comparison, including both forward and inverse base equations. -/
def Realized (hM : FirstOrder.Theory.Models M nativeZF)
    (w zero A GA e W G unit O F C GC D GD ia ic WN GN unitN ON H realization inverse : M.Carrier .set) : Prop :=
  Mapped hM w zero A GA e W G unit O C GC e ia WN GN unitN ON H ∧
  ConstructionPushoutIdentification.Comparison WN D GN GD unitN e H ON F ic realization inverse ∧
  OldFixed ON realization ∧ Range WN realization D

/-- Construct the actual mapped cell and realize it in the supplied apex.
Both new/old equations are retained, not merely the existence of an isomorphism. -/
theorem realization (hM : FirstOrder.Theory.Models M nativeZF)
    {w zero V GV e A B C D PA PB PC PD GA GB GC GD ia ib ic idD W G unit O F inv : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ z, ¬ (Project.FirstOrderSemantics.reduct M).mem z zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hBaseA : Base V GV e A PA GA ia) (hBaseB : Base V GV e B PB GB ib)
    (hBaseC : Base V GV e C PC GC ic) (hBaseD : Base V GV e D PD GD idD)
    (hSquare : Square A B C D GA GB GC GD e ia ib ic)
    (hCell : Cell hM w zero A GA e W G unit O) (hOld : Conservative A W GA G O)
    (hF : Hom W B G GB unit e F) (hInv : Hom B W GB G e unit inv)
    (hInverse : InverseGraph F inv) (hFixed : OldFixed O F) :
    ∃ WN GN unitN ON H realization inverse,
      Realized hM w zero A GA e W G unit O F C GC D GD ia ic WN GN unitN ON H realization inverse ∧
      Attachment hM w zero C GC e D GD := by
  obtain ⟨_,_,_,_,_,_,hIa,_,_,hJA⟩ := hBaseA
  obtain ⟨_,_,_,_,_,_,hIb,_,_,_⟩ := hBaseB
  obtain ⟨_,_,_,_,hmC,hcC,hIc,_,_,hJC⟩ := hBaseC
  obtain ⟨_,hPairsD,hMulD,_,hmD,_,_,_,_,_⟩ := hBaseD
  obtain ⟨_,_,hBD,_,hAB,_,hAC,hACCons,hBDHom,_,hCDHom,_,hPush⟩ := hSquare
  obtain ⟨WN,GN,unitN,ON,H,hMapped⟩ := exists_mapped hM hw hz hzw hCell hOld hJA hmC hcC hJC hAC hACCons
  have hKeep := hMapped
  obtain ⟨hOH,_,_,_,hCellN,hmWN,_,_,hON,hONCons,hH,_,hPushN,pairsN,hPairsN,hMulN⟩ := hMapped
  have hFComp := ConstructionPushoutIdentification.right_identity hF.1 hIb
  have hFD : Hom W D G GD unit e F :=
    ⟨⟨hF.1.1,fun x y hxy => hBD y (hF.1.2 x y hxy)⟩,hF.2.1,
      ConstructionProbePushout.composition_preserves hFComp hF.2.2 hBDHom.2.2⟩
  have hPresentation := ConstructionPushoutIdentification.change_left hM hAB.1 hBDHom hInv hF
    (fun x y => (hInverse y x).symm) (inverse_old hOH.1 hInv.1 hInverse hFixed hIa) hFComp hPush
  obtain ⟨realization,inverse,hComparison⟩ := ConstructionPushoutIdentification.exists_comparison hM
    hPairsN hMulN hmWN.1 hmWN.2.2 hPairsD hMulD hmD.1 hmD.2.2 hH hON hFD hCDHom hPushN hPresentation
  have hComparisonKeep := hComparison
  obtain ⟨hR,hRI,hRInv,_,hOldEquation,_,_⟩ := hComparison
  have hFixedN : OldFixed ON realization := by
    intro a u hau
    exact (ConstructionProbePushout.composition_value hON.1 hOldEquation hau).mp
      ((hIc a a).mpr ⟨function_input hON.1.1 hau,rfl⟩)
  have hRange : Range WN realization D := by
    intro y
    constructor
    · intro hy
      obtain ⟨x,hyx,_⟩ := hRI.1.1.2 y hy
      exact ⟨x,hRI.1.2 y x hyx,(hRInv x y).mpr hyx⟩
    · rintro ⟨x,_,hxy⟩
      exact hR.1.2 x y hxy
  exact ⟨WN,GN,unitN,ON,H,realization,inverse,⟨hKeep,hComparisonKeep,hFixedN,hRange⟩,
    WN,GN,unitN,ON,realization,inverse,hCellN,hmWN,hON,hONCons,hR,hRI,hRInv,hFixedN,hRange⟩

/-- Source Square.attachment, consuming the ORIGINAL supplied attachment. -/
theorem attachment (hM : FirstOrder.Theory.Models M nativeZF)
    {w zero V GV e A B C D PA PB PC PD GA GB GC GD ia ib ic idD : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ z, ¬ (Project.FirstOrderSemantics.reduct M).mem z zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hBaseA : Base V GV e A PA GA ia) (hBaseB : Base V GV e B PB GB ib)
    (hBaseC : Base V GV e C PC GC ic) (hBaseD : Base V GV e D PD GD idD)
    (hSquare : Square A B C D GA GB GC GD e ia ib ic)
    (hAttach : Attachment hM w zero A GA e B GB) : Attachment hM w zero C GC e D GD := by
  obtain ⟨W,G,unit,O,F,inv,hCell,_,_,hOld,hF,hInv,hInverse,hFixed,_⟩ := hAttach
  obtain ⟨_,_,_,_,_,_,_,_,hTarget⟩ := realization hM hw hz hzw hBaseA hBaseB hBaseC hBaseD
    hSquare hCell hOld hF hInv hInverse hFixed
  exact hTarget

def mapped {m : Nat} (w zero D mul e W G unit O N mulN eN f WN GN unitN ON H : Fin m) : Project.Formula 1 m :=
  (.conj (ConstructionProbePushoutSyntax.hom D W mul G e unit O) (.conj
  (ConstructionProbeConservativeSyntax.conservative D W mul G O) (.conj (ConstructionProbePushoutSyntax.hom D N mul
  mulN e eN f) (.conj (ConstructionProbeConservativeSyntax.conservative D N mul mulN f) (.conj
  (ConstructionCellRestriction.cellFormula w zero N mulN eN WN GN unitN ON) (.conj (ProjectSyntax.encode id
  (ForcingDiagramPoset.leftCancelMonoid WN GN unitN)) (.conj (ProjectSyntax.encode id (ForcingDiagramPoset.conical WN
  GN unitN)) (.conj (ConstructionProbeSharedIntersections.conditionalJoins WN GN) (.conj
  (ConstructionProbePushoutSyntax.hom N WN mulN GN eN unitN ON) (.conj
  (ConstructionProbeConservativeSyntax.conservative N WN mulN GN ON) (.conj (ConstructionProbePushoutSyntax.hom W WN G
  GN unit unitN H) (.conj (ConstructionProbeConservativeSyntax.conservative W WN G GN H) (.conj
  (ConstructionProbePushoutSyntax.isPushout N W WN mulN G GN eN unit unitN O f H ON) (.existsE (.conj
  (ConstructionProbeLetters.representatives WN.succ WN.succ 0) (ProjectSyntax.encode id (Source.SetLanguage.mapsTo
  GN.succ 0 WN.succ)))))))))))))))))

theorem mapped_freeClosed {m : Nat} (w zero D mul e W G unit O N mulN eN f WN GN unitN ON H : Fin m) :
    (mapped w zero D mul e W G unit O N mulN eN f WN GN unitN ON H).FreeClosed := by
  simp -implicitDefEqProofs [mapped,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,ConstructionProbePushoutSyntax.hom_freeClosed,ConstructionProbeConservativeSyntax.conservative_freeClosed,ConstructionCellRestriction.cellFormula_freeClosed,ConstructionProbeSharedIntersections.conditionalJoins_freeClosed,ConstructionProbePushoutSyntax.isPushout_freeClosed,ConstructionProbeLetters.representatives_freeClosed]

theorem mapped_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w zero D mul e W G unit O N mulN eN f WN GN unitN ON H : Fin m) :
    Project.Formula.satisfies env (mapped w zero D mul e W G unit O N mulN eN f WN GN unitN ON H) ↔ Mapped hM (env.bound w) (env.bound zero) (env.bound D) (env.bound mul) (env.bound e) (env.bound W) (env.bound G) (env.bound unit) (env.bound O) (env.bound N) (env.bound mulN) (env.bound eN) (env.bound f) (env.bound WN) (env.bound GN) (env.bound unitN) (env.bound ON) (env.bound H) := by
  simp only [mapped,Mapped,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_exists_iff,GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),ConstructionProbePushoutSyntax.hom_semantics hM,ConstructionProbeConservativeSyntax.conservative_semantics hM,ConstructionCellRestriction.cellFormula_semantics hM,ForcingDiagramPoset.leftCancelMonoid_semantics (M := M),ForcingDiagramPoset.conical_semantics (M := M),ConstructionProbeSharedIntersections.conditionalJoins_semantics hM,ConstructionProbePushoutSyntax.isPushout_semantics hM,ConstructionProbeLetters.representatives_semantics hM,ForcingSupportSize.mapsTo_semantics (M := M)]
  rfl

def realized {m : Nat} (w zero A GA e W G unit O F C GC D GD ia ic WN GN unitN ON H realization inverse : Fin m) : Project.Formula 1 m :=
  (.conj (mapped w zero A GA e W G unit O C GC e ia WN GN unitN ON H) (.conj
  (ConstructionPushoutIdentification.comparison WN D GN GD unitN e H ON F ic realization inverse) (.conj
  (ConstructionAttachmentCoefficients.oldFixed ON realization) (ProjectSyntax.encode id (ForcingSupportedNames.range
  WN realization D)))))

theorem realized_freeClosed {m : Nat} (w zero A GA e W G unit O F C GC D GD ia ic WN GN unitN ON H realization inverse : Fin m) :
    (realized w zero A GA e W G unit O F C GC D GD ia ic WN GN unitN ON H realization inverse).FreeClosed := by
  simp -implicitDefEqProofs [realized,Definitional.Formula.FreeClosed,mapped_freeClosed,ConstructionPushoutIdentification.comparison_freeClosed,ConstructionAttachmentCoefficients.oldFixed_freeClosed,ProjectSyntax.freeClosed]

theorem realized_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w zero A GA e W G unit O F C GC D GD ia ic WN GN unitN ON H realization inverse : Fin m) :
    Project.Formula.satisfies env (realized w zero A GA e W G unit O F C GC D GD ia ic WN GN unitN ON H realization inverse) ↔ Realized hM (env.bound w) (env.bound zero) (env.bound A) (env.bound GA) (env.bound e) (env.bound W) (env.bound G) (env.bound unit) (env.bound O) (env.bound F) (env.bound C) (env.bound GC) (env.bound D) (env.bound GD) (env.bound ia) (env.bound ic) (env.bound WN) (env.bound GN) (env.bound unitN) (env.bound ON) (env.bound H) (env.bound realization) (env.bound inverse) := by
  simp only [realized,Realized,Project.Formula.satisfies_conj_iff,mapped_semantics hM,ConstructionPushoutIdentification.comparison_semantics hM,ConstructionAttachmentCoefficients.oldFixed_semantics hM,GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),ForcingSupportedNames.range_semantics (M := M)]
  rfl

def mappedSentence {m : Nat} (w zero D mul e W G unit O N mulN eN f : Fin m) : Project.Sentence where
  formula := Project.Formula.forallClosure m
    (.imp (Project.Formula.isOmega (.bound w)) (.imp (Project.Formula.isEmpty (.bound zero)) (.imp (.mem (.bound zero)
    (.bound w)) (.imp (ConstructionCellRestriction.cellFormula w zero D mul e W G unit O) (.imp
    (ConstructionProbeConservativeSyntax.conservative D W mul G O) (.imp
    (ConstructionProbeSharedIntersections.conditionalJoins D mul) (.imp (ProjectSyntax.encode id
    (ForcingDiagramPoset.leftCancelMonoid N mulN eN)) (.imp (ProjectSyntax.encode id (ForcingDiagramPoset.conical N
    mulN eN)) (.imp (ConstructionProbeSharedIntersections.conditionalJoins N mulN) (.imp
    (ConstructionProbePushoutSyntax.hom D N mul mulN e eN f) (.imp (ConstructionProbeConservativeSyntax.conservative D
    N mul mulN f) (.existsE (.existsE (.existsE (.existsE (.existsE (mapped w.succ.succ.succ.succ.succ
    zero.succ.succ.succ.succ.succ D.succ.succ.succ.succ.succ mul.succ.succ.succ.succ.succ e.succ.succ.succ.succ.succ
    W.succ.succ.succ.succ.succ G.succ.succ.succ.succ.succ unit.succ.succ.succ.succ.succ O.succ.succ.succ.succ.succ
    N.succ.succ.succ.succ.succ mulN.succ.succ.succ.succ.succ eN.succ.succ.succ.succ.succ f.succ.succ.succ.succ.succ 4
    3 2 1 0)))))))))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,Project.Formula.isOmega,Project.Formula.isEmpty,ConstructionCellRestriction.cellFormula_freeClosed,ConstructionProbeConservativeSyntax.conservative_freeClosed,ConstructionProbeSharedIntersections.conditionalJoins_freeClosed,ConstructionProbePushoutSyntax.hom_freeClosed,mapped_freeClosed]

theorem mapped_models {m : Nat} (w zero D mul e W G unit O N mulN eN f : Fin m) (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence (mappedSentence w zero D mul e W G unit O N mulN eN f)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) (mappedSentence w zero D mul e W G unit O N mulN eN f)]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),Project.Formula.satisfies_isOmega_iff,Project.Formula.satisfies_isEmpty_iff,ConstructionCellRestriction.cellFormula_semantics hM,ConstructionProbeConservativeSyntax.conservative_semantics hM,ConstructionProbeSharedIntersections.conditionalJoins_semantics hM,ForcingDiagramPoset.leftCancelMonoid_semantics (M := M),ForcingDiagramPoset.conical_semantics (M := M),ConstructionProbePushoutSyntax.hom_semantics hM,mapped_semantics hM]
  exact exists_mapped hM

theorem mapped_kernel_certificate {m : Nat} (w zero D mul e W G unit O N mulN eN f : Fin m) :
    FirstOrder.Derives nativeZF [] (Project.fo_sentence (mappedSentence w zero D mul e W G unit O N mulN eN f)) :=
  ModelTransfer.derives (fun _ hM => mapped_models w zero D mul e W G unit O N mulN eN f hM)

def realizationSentence {m : Nat} (w zero V GV e A B C D PA PB PC PD GA GB GC GD ia ib ic idD W G unit O F inv : Fin m) : Project.Sentence where
  formula := Project.Formula.forallClosure m
    (.imp (Project.Formula.isOmega (.bound w)) (.imp (Project.Formula.isEmpty (.bound zero)) (.imp (.mem (.bound zero)
    (.bound w)) (.imp (ConstructionSelectedCellRestriction.baseFormula V GV e A PA GA ia) (.imp
    (ConstructionSelectedCellRestriction.baseFormula V GV e B PB GB ib) (.imp
    (ConstructionSelectedCellRestriction.baseFormula V GV e C PC GC ic) (.imp
    (ConstructionSelectedCellRestriction.baseFormula V GV e D PD GD idD) (.imp (ConstructionUnionPushout.square A B C
    D GA GB GC GD e ia ib ic) (.imp (ConstructionCellRestriction.cellFormula w zero A GA e W G unit O) (.imp
    (ConstructionProbeConservativeSyntax.conservative A W GA G O) (.imp (ConstructionProbePushoutSyntax.hom W B G GB
    unit e F) (.imp (ConstructionProbePushoutSyntax.hom B W GB G e unit inv) (.imp (ProjectSyntax.encode id
    (ForcingConditionGraphs.inverseGraph F inv)) (.imp (ConstructionAttachmentCoefficients.oldFixed O F) (.existsE
    (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.conj (realized w.succ.succ.succ.succ.succ.succ.succ
    zero.succ.succ.succ.succ.succ.succ.succ A.succ.succ.succ.succ.succ.succ.succ GA.succ.succ.succ.succ.succ.succ.succ
    e.succ.succ.succ.succ.succ.succ.succ W.succ.succ.succ.succ.succ.succ.succ G.succ.succ.succ.succ.succ.succ.succ
    unit.succ.succ.succ.succ.succ.succ.succ O.succ.succ.succ.succ.succ.succ.succ F.succ.succ.succ.succ.succ.succ.succ
    C.succ.succ.succ.succ.succ.succ.succ GC.succ.succ.succ.succ.succ.succ.succ D.succ.succ.succ.succ.succ.succ.succ
    GD.succ.succ.succ.succ.succ.succ.succ ia.succ.succ.succ.succ.succ.succ.succ ic.succ.succ.succ.succ.succ.succ.succ
    6 5 4 3 2 1 0) (ConstructionCellRestriction.attachmentFormula w.succ.succ.succ.succ.succ.succ.succ
    zero.succ.succ.succ.succ.succ.succ.succ C.succ.succ.succ.succ.succ.succ.succ GC.succ.succ.succ.succ.succ.succ.succ
    e.succ.succ.succ.succ.succ.succ.succ D.succ.succ.succ.succ.succ.succ.succ
    GD.succ.succ.succ.succ.succ.succ.succ)))))))))))))))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,Project.Formula.isOmega,Project.Formula.isEmpty,ConstructionSelectedCellRestriction.baseFormula_freeClosed,ConstructionUnionPushout.square_freeClosed,ConstructionCellRestriction.cellFormula_freeClosed,ConstructionProbeConservativeSyntax.conservative_freeClosed,ConstructionProbePushoutSyntax.hom_freeClosed,ConstructionAttachmentCoefficients.oldFixed_freeClosed,realized_freeClosed,ConstructionCellRestriction.attachmentFormula_freeClosed]

theorem realization_models {m : Nat} (w zero V GV e A B C D PA PB PC PD GA GB GC GD ia ib ic idD W G unit O F inv : Fin m) (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence (realizationSentence w zero V GV e A B C D PA PB PC PD GA GB GC GD ia ib ic idD W G unit O F inv)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) (realizationSentence w zero V GV e A B C D PA PB PC PD GA GB GC GD ia ib ic idD W G unit O F inv)]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),Project.Formula.satisfies_isOmega_iff,Project.Formula.satisfies_isEmpty_iff,ConstructionSelectedCellRestriction.baseFormula_semantics hM,ConstructionUnionPushout.square_semantics hM,ConstructionCellRestriction.cellFormula_semantics hM,ConstructionProbeConservativeSyntax.conservative_semantics hM,ConstructionProbePushoutSyntax.hom_semantics hM,ForcingConditionGraphs.inverseGraph_semantics (M := M),ConstructionAttachmentCoefficients.oldFixed_semantics hM,realized_semantics hM,ConstructionCellRestriction.attachmentFormula_semantics hM]
  exact realization hM

theorem realization_kernel_certificate {m : Nat} (w zero V GV e A B C D PA PB PC PD GA GB GC GD ia ib ic idD W G unit O F inv : Fin m) :
    FirstOrder.Derives nativeZF [] (Project.fo_sentence (realizationSentence w zero V GV e A B C D PA PB PC PD GA GB GC GD ia ib ic idD W G unit O F inv)) :=
  ModelTransfer.derives (fun _ hM => realization_models w zero V GV e A B C D PA PB PC PD GA GB GC GD ia ib ic idD W G unit O F inv hM)

def attachmentSentence {m : Nat} (w zero V GV e A B C D PA PB PC PD GA GB GC GD ia ib ic idD : Fin m) : Project.Sentence where
  formula := Project.Formula.forallClosure m
    (.imp (Project.Formula.isOmega (.bound w)) (.imp (Project.Formula.isEmpty (.bound zero)) (.imp (.mem (.bound zero)
    (.bound w)) (.imp (ConstructionSelectedCellRestriction.baseFormula V GV e A PA GA ia) (.imp
    (ConstructionSelectedCellRestriction.baseFormula V GV e B PB GB ib) (.imp
    (ConstructionSelectedCellRestriction.baseFormula V GV e C PC GC ic) (.imp
    (ConstructionSelectedCellRestriction.baseFormula V GV e D PD GD idD) (.imp (ConstructionUnionPushout.square A B C
    D GA GB GC GD e ia ib ic) (.imp (ConstructionCellRestriction.attachmentFormula w zero A GA e B GB)
    (ConstructionCellRestriction.attachmentFormula w zero C GC e D GD))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,Project.Formula.isOmega,Project.Formula.isEmpty,ConstructionSelectedCellRestriction.baseFormula_freeClosed,ConstructionUnionPushout.square_freeClosed,ConstructionCellRestriction.attachmentFormula_freeClosed]

theorem attachment_models {m : Nat} (w zero V GV e A B C D PA PB PC PD GA GB GC GD ia ib ic idD : Fin m) (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence (attachmentSentence w zero V GV e A B C D PA PB PC PD GA GB GC GD ia ib ic idD)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) (attachmentSentence w zero V GV e A B C D PA PB PC PD GA GB GC GD ia ib ic idD)]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,Project.Formula.satisfies_isOmega_iff,Project.Formula.satisfies_isEmpty_iff,ConstructionSelectedCellRestriction.baseFormula_semantics hM,ConstructionUnionPushout.square_semantics hM,ConstructionCellRestriction.attachmentFormula_semantics hM]
  exact attachment hM

theorem attachment_kernel_certificate {m : Nat} (w zero V GV e A B C D PA PB PC PD GA GB GC GD ia ib ic idD : Fin m) :
    FirstOrder.Derives nativeZF [] (Project.fo_sentence (attachmentSentence w zero V GV e A B C D PA PB PC PD GA GB GC GD ia ib ic idD)) :=
  ModelTransfer.derives (fun _ hM => attachment_models w zero V GV e A B C D PA PB PC PD GA GB GC GD ia ib ic idD hM)

end PPAC.Migration.ConstructionCellBaseChange
