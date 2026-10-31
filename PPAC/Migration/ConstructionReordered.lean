/- Pinned CellReorder.future_selected/future_omitted_square/reordered.
Consume the actual source cell records and existing full pushout geometry.
The new tower uses exactly stage(i) sup retained in the SAME terminal monoid. -/
import PPAC.Migration.ConstructionFutureTower

namespace PPAC.Migration.ConstructionReordered
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ConstructionSelectedCellRestriction (Base)
open ConstructionUnionPushout (Square base_inclusion)
open ConstructionConservativeHull (Closure ProductGraph)
open ConstructionCellRestriction (Stages Cell Attachment)
open ConstructionFutureFamily (CutAt Suprema Products)
open ConstructionFirstAppearance (Timeline Cover NewAt Index)
open ConstructionIntermediate (Sup)
open ConstructionRealCuts (Subset)
open ConstructionProbePushout (Hom)
open ConstructionProbeConservative (Conservative)
open ForcingConditionGraphs (function_unique function_input)
open ForcingSupportSize (Injection)
open ForcingDiagramPoset (LeftCancelMonoid Conical)
open ConstructionProbeSharedIntersections (ConditionalJoins)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

/-- Read the actual image isomorphism using the existing inverse_hom. -/
theorem attachment_image (hM : FirstOrder.Theory.Models M nativeZF)
    {w zero V GV e D GD T PT GT it W G unit O F : M.Carrier .set}
    (hT : Base V GV e T PT GT it) (hCell : Cell hM w zero D GD e W G unit O)
    (hmW : LeftCancelMonoid W G unit) (hOld : Hom D W GD G e unit O)
    (hCons : Conservative D W GD G O) (hF : Hom W V G GV unit e F)
    (hInj : Injection W V F) (hFixed : ConstructionAttachmentCoefficients.OldFixed O F)
    (hRange : ForcingSupportedNames.Range W F T) : Attachment hM w zero D GD e T GT := by
  have hMap : ForcingSupportSize.MapsTo W T F :=
    ⟨hF.1.1,fun x y hxy => (hRange y).mpr ⟨x,function_input hF.1.1 hxy,hxy⟩⟩
  have hHom : Hom W T G GT unit e F := by
    refine ⟨hMap,hF.2.1,?_⟩
    intro x y z fx fy fz hprod hx hy hz
    exact (hT.2.2.2.1 fx fy fz).mpr ⟨hMap.2 x fx hx,hMap.2 y fy hy,hF.2.2 x y z fx fy fz hprod hx hy hz⟩
  obtain ⟨inv,hInv,hInverse⟩ := ConstructionCellSimulationEquiv.inverse_hom hM hmW hT.2.2.2.2.1 hHom ⟨hMap,hInj.2⟩ hRange
  exact ⟨W,G,unit,O,F,inv,hCell,hmW,hOld,hCons,hHom,hInv,hInverse,hFixed,hRange⟩

/-- The chosen source record already contains the full original attachment.
Recover its inverse at the actual stage and align the typed product graph. -/
theorem attachment_of_data (hM : FirstOrder.Theory.Models M nativeZF)
    {w zero one V GV e D T cell PD PT GD GT idD it : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ z, ¬ (Project.FirstOrderSemantics.reduct M).mem z zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hD : Base V GV e D PD GD idD) (hT : Base V GV e T PT GT it)
    (hData : ConstructionStepCell.Data hM w zero one V GV e D T cell) :
    Attachment hM w zero D GD e T GT := by
  rcases hData with h | h
  · obtain ⟨mul,a,b,d,node,factor,terminal,target,L,C,projection,I,act,E,W,unit,G,K,P,O,F,
      p0,p1,presentation,parameters,old,generators,supports,deps,
      _,_,_,hmD,_,_,hA,hF,hInj,hFixed,hRange,_,_,_,hbne,hdne,hTerminal,hOldCons,_,hProduct,hTyped⟩ := h
    obtain ⟨pairs,hPairs,hMap⟩ := hTyped
    have he := ConstructionFutureFamily.multiplication_unique hM ⟨pairs,hPairs,hMap,hProduct⟩
      ⟨PD,hD.2.1,hD.2.2.1,hD.2.2.2.1⟩
    subst mul
    have hmW := ConstructionProbeWordMonoid.monoid_laws hM hw hz hzw hmD hA.alphabet hA.word hA.b_mem hA.old_unit hA.multiplication
    have hOld := ConstructionProbeOldEmbeddingSyntax.embedding_laws hM hw hz hzw hmD hA.alphabet hA.word hA.b_mem hA.old_unit hA.multiplication hA.old_graph
    have hO : Hom D W GD G e unit O := ⟨hA.old_map,hOld.1,
      fun x y z fx fy fz hp hx hy hzv => hOld.2.1 x y z fx fy fz hx hy hzv hp⟩
    exact attachment_image hM hT (Or.inl ⟨a,b,d,node,factor,terminal,target,L,C,projection,I,act,E,K,P,hbne,hdne,hA,hTerminal⟩)
      hmW hO hOldCons hF hInj hFixed hRange
  · obtain ⟨mul,n,P,C,L,projection,A,W,TW,B,G,unit,O,roots,F,p0,presentation,parameters,old,generators,supports,deps,
      _,_,hn,_,_,_,hValid,hA,hF,hInj,hFixed,hRange,_,_,_,hmW,_,_,hProduct,hWell,hTyped⟩ := h
    obtain ⟨pairs,hPairs,hMap⟩ := hTyped
    have he := ConstructionFutureFamily.multiplication_unique hM ⟨pairs,hPairs,hMap,hProduct⟩
      ⟨PD,hD.2.1,hD.2.2.1,hD.2.2.2.1⟩
    subst mul
    have hOldInj : Injection D W O := ⟨hA.old_hom.1,fun x y q hx hy =>
      ConstructionProbeRaw.old_injective ((hA.old_graph x q).mp hx) ((hA.old_graph y q).mp hy)⟩
    have hOldCons := ConstructionMergerOldEmbedding.old_conservative hM hw hz hzw hA.word
      hA.product_representatives hA.product_map hA.word_action hA.product hOldInj hA.old_graph
    exact attachment_image hM hT (Or.inr ⟨n,P,C,L,projection,A,TW,B,roots,hn,hWell,hValid,hA⟩)
      hmW hA.old_hom hOldCons hF hInj hFixed hRange

/-- Every nonidentity original adjacent stage consumes its actual AtNew cell.
No original Attachment oracle is added to the reordered-tower input. -/
theorem original_step (hM : FirstOrder.Theory.Models M nativeZF)
    {w zero one V GV e I R bottom S cells i j D T PD PT GD GT idD it : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ z, ¬ (Project.FirstOrderSemantics.reduct M).mem z zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hTimeline : Timeline hM V I R bottom S)
    (hNew : ConstructionStepCellSelection.AtNew hM w zero one V GV e I R S cells)
    (hCover : Cover I R i j) (hiD : PureKuratowski.PairMember M i D S)
    (hjT : PureKuratowski.PairMember M j T S)
    (hD : Base V GV e D PD GD idD) (hT : Base V GV e T PT GT it) :
    D = T ∨ Attachment hM w zero D GD e T GT := by
  classical
  by_cases he : D = T
  · exact Or.inl he
  have hDT : Subset D T := by
    intro x hx
    obtain ⟨E,hjE,hxE⟩ := hTimeline.2.2.2.2.2.1 i j x (Or.inr hCover.2.2.1) ⟨D,hiD,hx⟩
    exact (function_unique hTimeline.2.1 hjE hjT) ▸ hxE
  have hx : ∃ x, (Project.FirstOrderSemantics.reduct M).mem x T ∧ ¬ (Project.FirstOrderSemantics.reduct M).mem x D := by
    apply Classical.byContradiction
    intro hn
    apply he
    apply (ModelTransfer.extensionality hM).eq_of_same_members D T
    intro x
    exact ⟨hDT x,fun hx => Classical.byContradiction (fun hnx => hn ⟨x,hx,hnx⟩)⟩
  obtain ⟨x,hxT,hxD⟩ := hx
  have hxi : NewAt I R S i x := ⟨hCover.1,j,hCover,⟨T,hjT,hxT⟩,by
    rintro ⟨D',hiD',hxD'⟩
    exact hxD ((function_unique hTimeline.2.1 hiD' hiD) ▸ hxD')⟩
  obtain ⟨cell,j',D',T',deps,_,hCover',hiD',hjT',_,hData,_⟩ := hNew i x hxi
  have hej := ConstructionFutureSelected.cover_unique hM hTimeline hCover' hCover
  subst j'
  have heD := function_unique hTimeline.2.1 hiD' hiD
  have heT := function_unique hTimeline.2.1 hjT' hjT
  subst D' T'
  exact Or.inr (attachment_of_data hM hw hz hzw hD hT hData)

/-- Full Square reflection, reusing the original arbitrary-target pushout. -/
theorem flip {A B C D GA GB GC GD e ia ib ic : M.Carrier .set}
    (h : Square A B C D GA GB GC GD e ia ib ic) : Square A C B D GA GC GB GD e ia ic ib := by
  obtain ⟨hAB,hAC,hBD,hCD,hHomAB,hConsAB,hHomAC,hConsAC,hHomBD,hConsBD,hHomCD,hConsCD,hPush⟩ := h
  exact ⟨hAC,hAB,hCD,hBD,hHomAC,hConsAC,hHomAB,hConsAB,hHomCD,hConsCD,hHomBD,hConsBD,
    ConstructionPushoutPasting.flip hPush⟩

/-- Source Square.cancel_left, only assembling existing typed inclusions and
calling the already proved full arbitrary-target IsPushout.cancel_left. -/
theorem cancel_left (hM : FirstOrder.Theory.Models M nativeZF)
    {V GV e A B C D E F PA PB PC PD PE PF GA GB GC GD GE GF ia ib ic idD ie iF : M.Carrier .set}
    (hv : LeftCancelMonoid V GV e) (hc : Conical V GV e) (hJ : ConditionalJoins V GV)
    (hA : Base V GV e A PA GA ia) (hB : Base V GV e B PB GB ib)
    (hC : Base V GV e C PC GC ic) (hD : Base V GV e D PD GD idD)
    (hE : Base V GV e E PE GE ie) (hF : Base V GV e F PF GF iF)
    (hLeft : Square A B C D GA GB GC GD e ia ib ic)
    (hOuter : Square A E C F GA GE GC GF e ia ie ic)
    (hBE : Subset B E) (hDF : Subset D F) : Square B E D F GB GE GD GF e ib ie idD := by
  obtain ⟨hAB,_,hBD,hCD,hABHom,_,_,_,hBDHom,hBDCons,hCDHom,_,hPush⟩ := hLeft
  obtain ⟨_,_,hEF,_,_,_,_,_,hEFHom,hEFCons,_,_,hOuterPush⟩ := hOuter
  obtain ⟨hBEHom,hBECons⟩ := base_inclusion hv hc hJ hB hE hBE
  obtain ⟨hDFHom,hDFCons⟩ := base_inclusion hv hc hJ hD hF hDF
  have hAE := ConstructionFutureCut.inclusion_comp hAB hA.2.2.2.2.2.2.1 hB.2.2.2.2.2.2.1
  have hCF := ConstructionFutureCut.inclusion_comp hCD hC.2.2.2.2.2.2.1 hD.2.2.2.2.2.2.1
  have hComm : ConstructionProbePushout.SquareComm ib ib ie idD := by
    intro x y z q hxy hxz
    obtain ⟨hx,rfl⟩ := (hB.2.2.2.2.2.2.1 x y).mp hxy
    obtain ⟨_,rfl⟩ := (hB.2.2.2.2.2.2.1 x z).mp hxz
    exact ⟨fun h => (hD.2.2.2.2.2.2.1 x q).mpr ⟨hBD x hx,((hE.2.2.2.2.2.2.1 x q).mp h).2⟩,
      fun h => (hE.2.2.2.2.2.2.1 x q).mpr ⟨hBE x hx,((hD.2.2.2.2.2.2.1 x q).mp h).2⟩⟩
  exact ⟨hBE,hBD,hEF,hDF,hBEHom,hBECons,hBDHom,hBDCons,hEFHom,hEFCons,hDFHom,hDFCons,
    ConstructionPushoutPasting.cancel_left hM hABHom.1 hBDHom hCDHom hBEHom hDFHom hAE hCF hPush hComm hOuterPush⟩

/-- Align the produced future square with supplied actual Base witnesses. -/
theorem square_at (hM : FirstOrder.Theory.Models M nativeZF)
    {w zero one V GV e I R bottom top S index cells deps retained futures i A D F PA PD PF PR GA GD GF GR ia idD iF ir : M.Carrier .set}
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
    (htop : (Project.FirstOrderSemantics.reduct M).mem top I)
    (hTop : ∀ i, (Project.FirstOrderSemantics.reduct M).mem i I → i = top ∨ PureKuratowski.PairMember M i top R)
    (hTerminal : PureKuratowski.PairMember M top V S)
    (hF : Suprema I V GV e retained S futures)
    (hi : (Project.FirstOrderSemantics.reduct M).mem i I)
    (hiD : PureKuratowski.PairMember M i D S) (hiF : PureKuratowski.PairMember M i F futures)
    (hiA : CutAt retained S i A) (hA : Base V GV e A PA GA ia)
    (hD : Base V GV e D PD GD idD) (hBaseF : Base V GV e F PF GF iF)
    (hRetBase : Base V GV e retained PR GR ir) : Square A retained D F GA GR GD GF e ia ir idD := by
  obtain ⟨PF',GF',iF',hBaseF',hSquare⟩ := ConstructionFutureTower.future_square hM hw hz hzw hv hc hJ
    hStages hRet hT hIndex hCells hNew hGlobal hClosed htop hTop hTerminal hi hiD hiA hA hD hRetBase
    (ConstructionFutureTower.sup_at hT.2.1 hF hiD hiF)
  obtain ⟨heG,hei⟩ := ConstructionFutureSelected.base_graphs_unique hM hBaseF' hBaseF
  subst GF' iF'
  exact hSquare

/-- The actual source reordered.step: selected cells become identity;
omitted nonidentity cells are transported by the existing Square.attachment. -/
theorem step (hM : FirstOrder.Theory.Models M nativeZF)
    {w zero one V GV e I R bottom top S index cells deps retained futures i j F G PF PG GF GG iF iG : M.Carrier .set}
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
    (htop : (Project.FirstOrderSemantics.reduct M).mem top I)
    (hTop : ∀ i, (Project.FirstOrderSemantics.reduct M).mem i I → i = top ∨ PureKuratowski.PairMember M i top R)
    (hTerminal : PureKuratowski.PairMember M top V S)
    (hFutures : Suprema I V GV e retained S futures)
    (hCover : Cover I R i j) (hiF : PureKuratowski.PairMember M i F futures)
    (hjG : PureKuratowski.PairMember M j G futures)
    (hBaseF : Base V GV e F PF GF iF) (hBaseG : Base V GV e G PG GG iG) :
    F = G ∨ Attachment hM w zero F GF e G GG := by
  classical
  obtain ⟨D,hiD,_⟩ := hT.2.1.2 i hCover.1
  obtain ⟨T,hjT,_⟩ := hT.2.1.2 j hCover.2.1
  have hSupF := ConstructionFutureTower.sup_at hT.2.1 hFutures hiD hiF
  have hSupG := ConstructionFutureTower.sup_at hT.2.1 hFutures hjT hjG
  have hDT := ConstructionFutureLimit.timeline_mono hM hT i j D T hCover.1 hCover.2.1 hCover.2.2.1 hiD hjT
  have hFG := ConstructionFutureFamily.suprema_mono hFutures (ConstructionFutureLimit.timeline_mono hM hT)
    i j F G hCover.1 hCover.2.1 hCover.2.2.1 hiF hjG
  by_cases hs : ∃ x, (Project.FirstOrderSemantics.reduct M).mem x retained ∧ NewAt I R S i x
  · obtain ⟨x,hx,hxi⟩ := hs
    obtain ⟨D',T',A,B,PD,PT,PA,PB,GD,GT,GA,GB,idD,it,ia,ib,
      hiD',hjT',_,hjB,hBaseD,hBaseT,_,hBaseB,hSquare,_⟩ := ConstructionFutureSelected.selected hM
      hw hz hzw hv hc hJ hStages hRet hT hIndex hCells hNew hGlobal hClosed hCover hx hxi
    have heD := function_unique hT.2.1 hiD' hiD
    have heT := function_unique hT.2.1 hjT' hjT
    subst D' T'
    have hSupT := ConstructionIntermediate.apex_sup hM hBaseB hBaseD hBaseT hSquare
    have hBRet : Subset B retained := by
      obtain ⟨_,_,hCut⟩ := hjB
      exact fun z hz => ((hCut z).mp hz).1
    have hTF := hSupT.2.2.2 F hSupF.1 (fun z hz => hSupF.2.1 z (hBRet z hz)) hSupF.2.2.1
    have hGF := hSupG.2.2.2 F hSupF.1 hSupF.2.1 hTF
    exact Or.inl ((ModelTransfer.extensionality hM).eq_of_same_members F G (fun z => ⟨hFG z,hGF z⟩))
  · obtain ⟨PD,GD,idD,hBaseD⟩ := ConstructionFutureFamily.base_of_closed hM hv hc hJ (hStages i D hiD)
    obtain ⟨PT,GT,it,hBaseT⟩ := ConstructionFutureFamily.base_of_closed hM hv hc hJ (hStages j T hjT)
    rcases original_step hM hw hz hzw hT hNew hCover hiD hjT hBaseD hBaseT with heDT | hAttach
    · subst T
      exact Or.inl (ConstructionFutureFamily.sup_unique hM hSupF hSupG)
    · obtain ⟨A,hiA⟩ := ConstructionFutureFamily.cut_exists hM hT.2.1 hCover.1
      obtain ⟨B,hjB⟩ := ConstructionFutureFamily.cut_exists hM hT.2.1 hCover.2.1
      have heAB := ConstructionFutureCut.omitted_cut hM hT hCover hiA hjB
        (fun x hx hn => hs ⟨x,hx,hn⟩)
      subst B
      obtain ⟨PA,GA,ia,hBaseA⟩ := ConstructionFutureFamily.base_of_closed hM hv hc hJ
        (ConstructionFutureFamily.cut_closed hStages hRet hiA)
      obtain ⟨PR,GR,ir,hRetBase⟩ := ConstructionFutureFamily.base_of_closed hM hv hc hJ hRet
      have hSqF := square_at hM hw hz hzw hv hc hJ hStages hRet hT hIndex hCells hNew hGlobal
        hClosed htop hTop hTerminal hFutures hCover.1 hiD hiF hiA hBaseA hBaseD hBaseF hRetBase
      have hSqG := square_at hM hw hz hzw hv hc hJ hStages hRet hT hIndex hCells hNew hGlobal
        hClosed htop hTop hTerminal hFutures hCover.2.1 hjT hjG hjB hBaseA hBaseT hBaseG hRetBase
      have hSq := cancel_left hM hv hc hJ hBaseA hBaseD hRetBase hBaseF hBaseT hBaseG
        (flip hSqF) (flip hSqG) hDT hFG
      exact Or.inr (ConstructionCellBaseChange.attachment hM hw hz hzw hBaseD hBaseT hBaseF hBaseG hSq hAttach)

/-- Source step property for all original internal adjacent indices and
all typed presentations of the same actual future carriers. -/
def Steps (hM : FirstOrder.Theory.Models M nativeZF)
    (w zero V GV e I R futures : M.Carrier .set) : Prop :=
  ∀ i j F G PF PG GF GG iF iG, (i = j ∨ Cover I R i j) →
    PureKuratowski.PairMember M i F futures → PureKuratowski.PairMember M j G futures →
    Base V GV e F PF GF iF → Base V GV e G PG GG iG →
    F = G ∨ Attachment hM w zero F GF e G GG

/-- Full original reordered tower fields, with exact bottom when the
retained carrier contains the original bottom stage. -/
def Result (hM : FirstOrder.Theory.Models M nativeZF)
    (w zero V GV e I R bottom top S retained futures muls : M.Carrier .set) : Prop :=
  Suprema I V GV e retained S futures ∧ Products I GV futures muls ∧
    Stages V GV e futures ∧ Timeline hM V I R bottom futures ∧
    PureKuratowski.PairMember M top V futures ∧ Steps hM w zero V GV e I R futures ∧
    ∀ D, PureKuratowski.PairMember M bottom D S → Subset D retained →
      PureKuratowski.PairMember M bottom retained futures

/-- Complete source reordered: actual family, monotonicity, terminal,
continuity, original-cell steps and exact initial carrier. -/
theorem construction (hM : FirstOrder.Theory.Models M nativeZF)
    {w zero one V GV e I R bottom top S index cells deps retained : M.Carrier .set}
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
    (htop : (Project.FirstOrderSemantics.reduct M).mem top I)
    (hTop : ∀ i, (Project.FirstOrderSemantics.reduct M).mem i I → i = top ∨ PureKuratowski.PairMember M i top R)
    (hTerminal : PureKuratowski.PairMember M top V S)
    : ∃ futures muls, Result hM w zero V GV e I R bottom top S retained futures muls := by
  obtain ⟨futures,muls,hF,hmuls,hStagesF,hTF,hTopF⟩ := ConstructionFutureTower.construction hM
    hw hz hzw hv hc hJ hStages hRet hT hIndex hCells hNew hGlobal hClosed htop hTop hTerminal
  refine ⟨futures,muls,hF,hmuls,hStagesF,hTF,hTopF,?_,?_⟩
  · intro i j F G PF PG GF GG iF iG hij hiF hjG hBaseF hBaseG
    rcases hij with rfl | hij
    · exact Or.inl (function_unique hF.1 hiF hjG)
    exact step hM hw hz hzw hv hc hJ hStages hRet hT hIndex hCells hNew hGlobal hClosed
      htop hTop hTerminal hF hij hiF hjG hBaseF hBaseG
  · intro D hbotD hD
    exact ConstructionFutureTower.bottom hM hT.2.1 hF hT.2.2.1 hRet hbotD hD

def stepsFormula {m : Nat} (w zero V GV e I R futures : Fin m) : Project.Formula 1 m :=
  (.forallE (.forallE (.forallE (.forallE (.forallE (.forallE (.forallE (.forallE (.forallE (.forallE (.imp (.disj (Project.Formula.extensionalEq (.bound 9) (.bound 8)) (ConstructionFirstAppearance.cover I.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ R.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ 9 8)) (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge futures.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ 9 7)) (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge futures.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ 8 6)) (.imp (ConstructionSelectedCellRestriction.baseFormula V.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ GV.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ e.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ 7 5 3 1) (.imp (ConstructionSelectedCellRestriction.baseFormula V.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ GV.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ e.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ 6 4 2 0) (.disj (Project.Formula.extensionalEq (.bound 7) (.bound 6)) (ConstructionCellRestriction.attachmentFormula w.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ zero.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ 7 3 e.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ 6 2)))))))))))))))))

theorem stepsFormula_freeClosed {m : Nat} (w zero V GV e I R futures : Fin m) :
    (stepsFormula w zero V GV e I R futures).FreeClosed := by
  simp -implicitDefEqProofs [stepsFormula,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
    Project.Formula.extensionalEq,ConstructionFirstAppearance.cover_freeClosed,
    ConstructionSelectedCellRestriction.baseFormula_freeClosed,ConstructionCellRestriction.attachmentFormula_freeClosed]

theorem stepsFormula_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w zero V GV e I R futures : Fin m) :
    Project.Formula.satisfies env (stepsFormula w zero V GV e I R futures) ↔ Steps hM (env.bound w) (env.bound zero) (env.bound V) (env.bound GV) (env.bound e) (env.bound I) (env.bound R) (env.bound futures) := by
  simp only [stepsFormula,Steps,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_imp_iff,
    Project.Formula.satisfies_disj_iff,Project.Formula.satisfies_extensionalEq_iff_eq (ModelTransfer.extensionality hM),
    Project.Term.eval_bound,GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,
    ConstructionFirstAppearance.cover_semantics hM,ConstructionSelectedCellRestriction.baseFormula_semantics hM,ConstructionCellRestriction.attachmentFormula_semantics hM]
  rfl

def resultFormula {m : Nat} (w zero V GV e I R bottom top S retained futures muls : Fin m) : Project.Formula 1 m :=
  (.conj (ConstructionFutureFamily.supremaFormula I V GV e retained S futures) (.conj (ConstructionFutureFamily.productsFormula I GV futures muls) (.conj (ConstructionCellRestriction.stages V GV e futures) (.conj (ConstructionFirstAppearance.timeline V I R bottom futures) (.conj (ProjectSyntax.encode id (Source.SetLanguage.edge futures top V)) (.conj (stepsFormula w zero V GV e I R futures) (.forallE (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge S.succ bottom.succ 0)) (.imp (Project.Formula.subset (.bound 0) (.bound retained.succ)) (ProjectSyntax.encode id (Source.SetLanguage.edge futures.succ bottom.succ retained.succ)))))))))))

theorem resultFormula_freeClosed {m : Nat} (w zero V GV e I R bottom top S retained futures muls : Fin m) :
    (resultFormula w zero V GV e I R bottom top S retained futures muls).FreeClosed := by
  simp -implicitDefEqProofs [resultFormula,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
    Project.Formula.subset,stepsFormula_freeClosed,ConstructionFutureFamily.supremaFormula_freeClosed,ConstructionFutureFamily.productsFormula_freeClosed,ConstructionCellRestriction.stages_freeClosed,ConstructionFirstAppearance.timeline_freeClosed]

theorem resultFormula_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w zero V GV e I R bottom top S retained futures muls : Fin m) :
    Project.Formula.satisfies env (resultFormula w zero V GV e I R bottom top S retained futures muls) ↔ Result hM (env.bound w) (env.bound zero) (env.bound V) (env.bound GV) (env.bound e) (env.bound I) (env.bound R) (env.bound bottom) (env.bound top) (env.bound S) (env.bound retained) (env.bound futures) (env.bound muls) := by
  simp only [resultFormula,Result,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_forall_iff,
    Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_subset_iff,Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,
    stepsFormula_semantics hM,ConstructionFutureFamily.supremaFormula_semantics hM,ConstructionFutureFamily.productsFormula_semantics hM,ConstructionCellRestriction.stages_semantics hM,ConstructionFirstAppearance.timeline_semantics hM]
  rfl

/-- Complete source reordered as a pure-membership nativeZF theorem. -/
def constructionSentence {m : Nat} (w zero one V GV e I R bottom top S index cells deps retained : Fin m) : Project.Sentence where
  formula := Project.Formula.forallClosure m (.imp (Project.Formula.isOmega (.bound w)) (.imp (Project.Formula.isEmpty (.bound zero)) (.imp (.mem (.bound zero) (.bound w)) (.imp (ProjectSyntax.encode id (ForcingDiagramPoset.leftCancelMonoid V GV e)) (.imp (ProjectSyntax.encode id (ForcingDiagramPoset.conical V GV e)) (.imp (ConstructionProbeSharedIntersections.conditionalJoins V GV) (.imp (ConstructionCellRestriction.stages V GV e S) (.imp (ConstructionConservativeHull.closure V GV e retained) (.imp (ConstructionFirstAppearance.timeline V I R bottom S) (.imp (ConstructionFirstAppearance.indexGraph V I R bottom S index) (.imp (ConstructionStepCellSelection.graph w zero one V GV e I R S cells) (.imp (ConstructionStepCellSelection.atNew w zero one V GV e I R S cells) (.imp (ConstructionGlobalDependencies.graph zero V I R bottom S index cells deps) (.imp (ConstructionCountableConservativeHull.dependenciesClosed deps retained) (.imp (.mem (.bound top) (.bound I)) (.imp (.forallE (.imp (.mem (.bound 0) (.bound I.succ)) (ConstructionFutureLimit.closedLe R.succ 0 top.succ))) (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge S top V)) (.existsE (.existsE (resultFormula w.succ.succ zero.succ.succ V.succ.succ GV.succ.succ e.succ.succ I.succ.succ R.succ.succ bottom.succ.succ top.succ.succ S.succ.succ retained.succ.succ 1 0))))))))))))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,Project.Formula.isOmega,Project.Formula.isEmpty,ConstructionFutureLimit.closedLe_freeClosed,resultFormula_freeClosed,ConstructionProbeSharedIntersections.conditionalJoins_freeClosed,ConstructionCellRestriction.stages_freeClosed,ConstructionConservativeHull.closure_freeClosed,ConstructionFirstAppearance.timeline_freeClosed,ConstructionFirstAppearance.indexGraph_freeClosed,ConstructionStepCellSelection.graph_freeClosed,ConstructionStepCellSelection.atNew_freeClosed,ConstructionGlobalDependencies.graph_freeClosed,ConstructionCountableConservativeHull.dependenciesClosed_freeClosed]

theorem construction_models {m : Nat} (w zero one V GV e I R bottom top S index cells deps retained : Fin m) (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence (constructionSentence w zero one V GV e I R bottom top S index cells deps retained)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) (constructionSentence w zero one V GV e I R bottom top S index cells deps retained)]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,Project.Formula.satisfies_isOmega_iff,Project.Formula.satisfies_isEmpty_iff,GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,ForcingDiagramPoset.leftCancelMonoid_semantics (M := M),ForcingDiagramPoset.conical_semantics (M := M),ConstructionFutureLimit.closedLe_semantics hM,resultFormula_semantics hM,ConstructionProbeSharedIntersections.conditionalJoins_semantics hM,ConstructionCellRestriction.stages_semantics hM,ConstructionConservativeHull.closure_semantics hM,ConstructionFirstAppearance.timeline_semantics hM,ConstructionFirstAppearance.indexGraph_semantics hM,ConstructionStepCellSelection.graph_semantics hM,ConstructionStepCellSelection.atNew_semantics hM,ConstructionGlobalDependencies.graph_semantics hM,ConstructionCountableConservativeHull.dependenciesClosed_semantics hM]
  exact construction hM

theorem construction_kernel_certificate {m : Nat} (w zero one V GV e I R bottom top S index cells deps retained : Fin m) :
    FirstOrder.Derives nativeZF [] (Project.fo_sentence (constructionSentence w zero one V GV e I R bottom top S index cells deps retained)) :=
  ModelTransfer.derives (fun _ hM => construction_models w zero one V GV e I R bottom top S index cells deps retained hM)

/-- The source flattened index already has its actual top: the empty
WithTop code. Consume those original records instead of assuming a new top. -/
theorem actual_top (hM : FirstOrder.Theory.Models M nativeZF)
    {zero V I R S kappa traces Indices A r history outerF : M.Carrier .set}
    (hz : ∀ z, ¬ (Project.FirstOrderSemantics.reduct M).mem z zero)
    (hData : ConstructionBlockIndex.Data hM kappa traces Indices A r I R)
    (hGraph : ConstructionFlatStages.Graph history outerF kappa V zero traces I S) :
    (Project.FirstOrderSemantics.reduct M).mem zero I ∧
      (∀ i, (Project.FirstOrderSemantics.reduct M).mem i I → i = zero ∨ PureKuratowski.PairMember M i zero R) ∧
      PureKuratowski.PairMember M zero V S := by
  classical
  obtain ⟨_,_,_,_,_,hCarrier,_,hR⟩ := hData
  have hzI := (hCarrier zero).mpr (Or.inl hz)
  refine ⟨hzI,?_,(hGraph.2 zero V).mpr ⟨hzI,Or.inl ⟨hz,rfl⟩⟩⟩
  intro i hi
  by_cases he : i = zero
  · exact Or.inl he
  · exact Or.inr ((hR i zero).mpr ⟨hi,hzI,Or.inl ⟨fun hEmpty => he (ForcingWithTopCarrier.empty_unique hM hEmpty hz),hz⟩⟩)

/-- Reordered on the SAME actual BlockIndex and FlatStages; top membership,
maximality and terminal-stage value are eliminated by actual_top. -/
theorem actual (hM : FirstOrder.Theory.Models M nativeZF)
    {w zero one V GV e I R bottom S index cells deps retained kappa traces Indices A r history outerF : M.Carrier .set}
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
    (hData : ConstructionBlockIndex.Data hM kappa traces Indices A r I R)
    (hGraph : ConstructionFlatStages.Graph history outerF kappa V zero traces I S) :
    ∃ futures muls, Result hM w zero V GV e I R bottom zero S retained futures muls := by
  obtain ⟨htop,hTop,hTerminal⟩ := actual_top hM hz hData hGraph
  exact construction hM hw hz hzw hv hc hJ hStages hRet hT hIndex hCells hNew hGlobal hClosed htop hTop hTerminal

def actualSentence {m : Nat} (w zero one V GV e I R bottom S index cells deps retained kappa traces Indices A r history outerF : Fin m) : Project.Sentence where
  formula := Project.Formula.forallClosure m (.imp (Project.Formula.isOmega (.bound w)) (.imp (Project.Formula.isEmpty (.bound zero)) (.imp (.mem (.bound zero) (.bound w)) (.imp (ProjectSyntax.encode id (ForcingDiagramPoset.leftCancelMonoid V GV e)) (.imp (ProjectSyntax.encode id (ForcingDiagramPoset.conical V GV e)) (.imp (ConstructionProbeSharedIntersections.conditionalJoins V GV) (.imp (ConstructionCellRestriction.stages V GV e S) (.imp (ConstructionConservativeHull.closure V GV e retained) (.imp (ConstructionFirstAppearance.timeline V I R bottom S) (.imp (ConstructionFirstAppearance.indexGraph V I R bottom S index) (.imp (ConstructionStepCellSelection.graph w zero one V GV e I R S cells) (.imp (ConstructionStepCellSelection.atNew w zero one V GV e I R S cells) (.imp (ConstructionGlobalDependencies.graph zero V I R bottom S index cells deps) (.imp (ConstructionCountableConservativeHull.dependenciesClosed deps retained) (.imp (ConstructionBlockIndex.data kappa traces Indices A r I R) (.imp (ConstructionFlatStages.graph history outerF kappa V zero traces I S) (.existsE (.existsE (resultFormula w.succ.succ zero.succ.succ V.succ.succ GV.succ.succ e.succ.succ I.succ.succ R.succ.succ bottom.succ.succ zero.succ.succ S.succ.succ retained.succ.succ 1 0)))))))))))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,Project.Formula.isOmega,Project.Formula.isEmpty,resultFormula_freeClosed,ConstructionProbeSharedIntersections.conditionalJoins_freeClosed,ConstructionCellRestriction.stages_freeClosed,ConstructionConservativeHull.closure_freeClosed,ConstructionFirstAppearance.timeline_freeClosed,ConstructionFirstAppearance.indexGraph_freeClosed,ConstructionStepCellSelection.graph_freeClosed,ConstructionStepCellSelection.atNew_freeClosed,ConstructionGlobalDependencies.graph_freeClosed,ConstructionCountableConservativeHull.dependenciesClosed_freeClosed,ConstructionBlockIndex.data_freeClosed,ConstructionFlatStages.graph_freeClosed]

theorem actual_models {m : Nat} (w zero one V GV e I R bottom S index cells deps retained kappa traces Indices A r history outerF : Fin m) (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence (actualSentence w zero one V GV e I R bottom S index cells deps retained kappa traces Indices A r history outerF)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) (actualSentence w zero one V GV e I R bottom S index cells deps retained kappa traces Indices A r history outerF)]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,Project.Formula.satisfies_isOmega_iff,Project.Formula.satisfies_isEmpty_iff,GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),ForcingDiagramPoset.leftCancelMonoid_semantics (M := M),ForcingDiagramPoset.conical_semantics (M := M),resultFormula_semantics hM,ConstructionProbeSharedIntersections.conditionalJoins_semantics hM,ConstructionCellRestriction.stages_semantics hM,ConstructionConservativeHull.closure_semantics hM,ConstructionFirstAppearance.timeline_semantics hM,ConstructionFirstAppearance.indexGraph_semantics hM,ConstructionStepCellSelection.graph_semantics hM,ConstructionStepCellSelection.atNew_semantics hM,ConstructionGlobalDependencies.graph_semantics hM,ConstructionCountableConservativeHull.dependenciesClosed_semantics hM,ConstructionBlockIndex.data_semantics hM,ConstructionFlatStages.graph_semantics hM]
  exact actual hM

theorem actual_kernel_certificate {m : Nat} (w zero one V GV e I R bottom S index cells deps retained kappa traces Indices A r history outerF : Fin m) :
    FirstOrder.Derives nativeZF [] (Project.fo_sentence (actualSentence w zero one V GV e I R bottom S index cells deps retained kappa traces Indices A r history outerF)) :=
  ModelTransfer.derives (fun _ hM => actual_models w zero one V GV e I R bottom S index cells deps retained kappa traces Indices A r history outerF hM)

end PPAC.Migration.ConstructionReordered
