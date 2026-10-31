/- Pinned StableSelectors.conditionSelector/Selected. Combine actual rows,
least distinguishing bound and best pattern in ONE fixed internal order.
All witnesses are model sets. Canonical space/projection equality removes
any dependence on auxiliary construction witnesses. -/
import PPAC.Migration.ConstructionGermPatternOrder

namespace PPAC.Migration.ConstructionGermSelected
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ForcingSupportSize (MapsTo Injection)
open ForcingCohenCoordinates (Cartesian)
open ForcingCohenConditions (Condition)
open ConstructionGermEventual (Space Classes Projection Exact)
open ConstructionGermLeastBound (Least)
open ConstructionGermBestCoset (Best)
open ConstructionGermPatternOrder (Covers)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

theorem spaces_unique (hM : FirstOrder.Theory.Models M nativeZF)
    {w N alpha B A S E pr T A' S' E' pr' T' : M.Carrier .set}
    (hA : Space alpha B A) (hS : Space w A S) (hpr : MapsTo S E pr) (hE : Classes w S E)
    (hProj : Projection w S pr) (hT : Space N E T)
    (hA' : Space alpha B A') (hS' : Space w A' S') (hpr' : MapsTo S' E' pr') (hE' : Classes w S' E')
    (hProj' : Projection w S' pr') (hT' : Space N E' T') : A = A' ∧ S = S' ∧ E = E' ∧ pr = pr' ∧ T = T' := by
  have ea := ConstructionGermPatternOrder.function_space_unique hM hA' hA
  subst A'
  have es := ConstructionGermPatternOrder.function_space_unique hM hS' hS
  subst S'
  have ee := (ModelTransfer.extensionality hM).eq_of_same_members E' E (fun C => (hE' C).trans (hE C).symm)
  subst E'
  have ep : pr = pr' := by
    apply Structure.IsSetRelation.eq_of_pairMember_iff (ModelTransfer.project_models_iff.mp hM).1
      ((ForcingSupportSize.native_mapsTo hM S E pr).mp hpr).1.1
      ((ForcingSupportSize.native_mapsTo hM S E pr').mp hpr').1.1
    exact fun f C => (hProj f C).trans (hProj' f C).symm
  exact ⟨rfl,rfl,rfl,ep,ConstructionGermPatternOrder.function_space_unique hM hT hT'⟩

def Selected (w D chain H G N K C B lo hi det order p c : M.Carrier .set) : Prop :=
  ConstructionGermGoodDense.Good w D chain H G N K C B lo hi det p ∧ ∃ R alpha A S E pr T F,
    ConstructionCohenRows.Rows C B lo hi p R ∧ Least w D chain H G N K B det R alpha ∧
      Space alpha B A ∧ Space w A S ∧ MapsTo S E pr ∧ Classes w S E ∧ Projection w S pr ∧ Exact w pr ∧ Space N E T ∧
        ConstructionGermPattern.Pattern w D chain H G N alpha B A E T det R pr F ∧ Injection G T F ∧ Best G order F c

def selected {m : Nat} (w D chain H G N K C B lo hi det order p c : Fin m) : Project.Formula 1 m := (.conj (ConstructionGermGoodDense.good w D chain H G N K C B lo hi det p) (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.conj (ConstructionCohenRows.rows C.succ.succ.succ.succ.succ.succ.succ.succ B.succ.succ.succ.succ.succ.succ.succ.succ lo.succ.succ.succ.succ.succ.succ.succ.succ hi.succ.succ.succ.succ.succ.succ.succ.succ p.succ.succ.succ.succ.succ.succ.succ.succ 7) (.conj (ConstructionGermLeastBound.least w.succ.succ.succ.succ.succ.succ.succ.succ D.succ.succ.succ.succ.succ.succ.succ.succ chain.succ.succ.succ.succ.succ.succ.succ.succ H.succ.succ.succ.succ.succ.succ.succ.succ G.succ.succ.succ.succ.succ.succ.succ.succ N.succ.succ.succ.succ.succ.succ.succ.succ K.succ.succ.succ.succ.succ.succ.succ.succ B.succ.succ.succ.succ.succ.succ.succ.succ det.succ.succ.succ.succ.succ.succ.succ.succ 7 6) (.conj (ConstructionGermEventual.space 6 B.succ.succ.succ.succ.succ.succ.succ.succ 5) (.conj (ConstructionGermEventual.space w.succ.succ.succ.succ.succ.succ.succ.succ 5 4) (.conj (ProjectSyntax.encode id (Source.SetLanguage.mapsTo 2 4 3)) (.conj (ConstructionGermEventual.classes w.succ.succ.succ.succ.succ.succ.succ.succ 4 3) (.conj (ConstructionGermEventual.projection w.succ.succ.succ.succ.succ.succ.succ.succ 4 2) (.conj (ConstructionGermEventual.exactProjection w.succ.succ.succ.succ.succ.succ.succ.succ 2) (.conj (ConstructionGermEventual.space N.succ.succ.succ.succ.succ.succ.succ.succ 3 1) (.conj (ConstructionGermPattern.pattern w.succ.succ.succ.succ.succ.succ.succ.succ D.succ.succ.succ.succ.succ.succ.succ.succ chain.succ.succ.succ.succ.succ.succ.succ.succ H.succ.succ.succ.succ.succ.succ.succ.succ G.succ.succ.succ.succ.succ.succ.succ.succ N.succ.succ.succ.succ.succ.succ.succ.succ 6 B.succ.succ.succ.succ.succ.succ.succ.succ 5 3 1 det.succ.succ.succ.succ.succ.succ.succ.succ 7 2 0) (.conj (ProjectSyntax.encode id (Source.SetLanguage.injection 0 G.succ.succ.succ.succ.succ.succ.succ.succ 1)) (ConstructionGermBestCoset.best G.succ.succ.succ.succ.succ.succ.succ.succ order.succ.succ.succ.succ.succ.succ.succ.succ 0 c.succ.succ.succ.succ.succ.succ.succ.succ)))))))))))))))))))))

theorem selected_freeClosed {m : Nat} (w D chain H G N K C B lo hi det order p c : Fin m) : (selected w D chain H G N K C B lo hi det order p c).FreeClosed := by
  simp -implicitDefEqProofs [selected,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
    ConstructionGermGoodDense.good_freeClosed,ConstructionCohenRows.rows_freeClosed,ConstructionGermLeastBound.least_freeClosed,
    ConstructionGermEventual.space_freeClosed,ConstructionGermEventual.classes_freeClosed,ConstructionGermEventual.projection_freeClosed,
    ConstructionGermEventual.exactProjection_freeClosed,ConstructionGermPattern.pattern_freeClosed,ConstructionGermBestCoset.best_freeClosed]

theorem selected_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w D chain H G N K C B lo hi det order p c : Fin m) :
    Project.Formula.satisfies env (selected w D chain H G N K C B lo hi det order p c) ↔ Selected (env.bound w) (env.bound D) (env.bound chain) (env.bound H) (env.bound G) (env.bound N) (env.bound K) (env.bound C) (env.bound B) (env.bound lo) (env.bound hi) (env.bound det) (env.bound order) (env.bound p) (env.bound c) := by
  simp only [selected,Selected,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_exists_iff,
    ConstructionGermGoodDense.good_semantics hM,ConstructionCohenRows.rows_semantics hM,ConstructionGermLeastBound.least_semantics hM,
    ConstructionGermEventual.space_semantics hM,ConstructionGermEventual.classes_semantics hM,ConstructionGermEventual.projection_semantics hM,
    ConstructionGermEventual.exactProjection_semantics hM,ConstructionGermPattern.pattern_semantics hM,ConstructionGermBestCoset.best_semantics hM,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),ForcingSupportSize.mapsTo_semantics (M := M),ForcingSupportSize.injection_semantics (M := M)]
  rfl

theorem exists_selected (hM : FirstOrder.Theory.Models M nativeZF)
    {w D chain H G N K C B lo hi det order O p : M.Carrier .set}
    (hK : (Project.FirstOrderSemantics.reduct M).IsOrdinal K) (hCover : Covers w N B K O)
    (hOrder : (Project.FirstOrderSemantics.reduct M).IsSetCodedWellOrder (KuratowskiZF.interpretation hM) order O)
    (hNonempty : ∃ c, (Project.FirstOrderSemantics.reduct M).mem c G)
    (hGood : ConstructionGermGoodDense.Good w D chain H G N K C B lo hi det p) :
    ∃ c, Selected w D chain H G N K C B lo hi det order p c := by
  obtain ⟨R,alpha,hR,hLeast,_⟩ := ConstructionGermLeastBound.construction hM hK hGood
  obtain ⟨A,S,E,pr,T,F,hA,hS,hpr,hE,hProj,hExact,hT,hF,hInj⟩ := hLeast.2.1
  have hTO := hCover alpha T hLeast.1 ⟨A,S,E,hA,hS,hE,hT⟩
  obtain ⟨c,hBest⟩ := ConstructionGermBestCoset.exists_best hM hF.1 hTO hOrder hNonempty
  exact ⟨c,hGood,R,alpha,A,S,E,pr,T,F,hR,hLeast,hA,hS,hpr,hE,hProj,hExact,hT,hF,hInj,hBest⟩

theorem selected_mem {w D chain H G N K C B lo hi det order p c : M.Carrier .set}
    (h : Selected w D chain H G N K C B lo hi det order p c) : (Project.FirstOrderSemantics.reduct M).mem c G := by
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,hBest⟩ := h
  exact hBest.1

theorem selected_unique (hM : FirstOrder.Theory.Models M nativeZF)
    {w D chain H G N K C B lo hi det order O p c d : M.Carrier .set}
    (hK : (Project.FirstOrderSemantics.reduct M).IsOrdinal K) (hCover : Covers w N B K O)
    (hOrder : (Project.FirstOrderSemantics.reduct M).IsSetCodedWellOrder (KuratowskiZF.interpretation hM) order O)
    (hc : Selected w D chain H G N K C B lo hi det order p c)
    (hd : Selected w D chain H G N K C B lo hi det order p d) : c = d := by
  obtain ⟨_,R,alpha,A,S,E,pr,T,F,hR,hLeast,hA,hS,hpr,hE,hProj,_,hT,hF,hInj,hBest⟩ := hc
  obtain ⟨_,U,beta,A',S',E',pr',T',Q,hU,hLeast',hA',hS',hpr',hE',hProj',_,hT',hQ,_,hBest'⟩ := hd
  have eR := ConstructionGermLeastBound.rows_unique hM hU hR
  subst U
  have ea := ConstructionGermLeastBound.least_unique hK hLeast' hLeast
  subst beta
  obtain ⟨eA,eS,eE,epr,eT⟩ := spaces_unique hM hA hS hpr hE hProj hT hA' hS' hpr' hE' hProj' hT'
  subst A' S' E' pr' T'
  have eF : F = Q := by
    apply Structure.IsSetRelation.eq_of_pairMember_iff (ModelTransfer.project_models_iff.mp hM).1
      ((ForcingSupportSize.native_mapsTo hM G T F).mp hF.1).1.1
      ((ForcingSupportSize.native_mapsTo hM G T Q).mp hQ.1).1.1
    exact fun C P => (hF.2 C P).trans (hQ.2 C P).symm
  subst Q
  exact ConstructionGermBestCoset.best_unique hM hInj (hCover alpha T hLeast.1 ⟨A,S,E,hA,hS,hE,hT⟩) hOrder hBest hBest'

theorem extension_eq (hM : FirstOrder.Theory.Models M nativeZF)
    {w D I mul q root chain H G N X K C B S lo hi det order O p r c e : M.Carrier .set}
    (hH : ConstructionGermCosets.Carrier D I mul q root H) (hDet : MapsTo X I det)
    (hX : Cartesian N w X) (hC : Cartesian I K C) (hS : Cartesian C B S)
    (hK : (Project.FirstOrderSemantics.reduct M).IsOrdinal K) (hCover : Covers w N B K O)
    (hOrder : (Project.FirstOrderSemantics.reduct M).IsSetCodedWellOrder (KuratowskiZF.interpretation hM) order O)
    (hlo : ForcingWithTopCarrier.Empty lo) (hhi : (Project.FirstOrderSemantics.reduct M).SuccessorOf hi lo)
    (hB : (Project.FirstOrderSemantics.reduct M).SuccessorOf B hi)
    (hp : Condition S w p) (hr : Condition S w r) (hle : (Project.FirstOrderSemantics.reduct M).MemberSubset p r)
    (hc : Selected w D chain H G N K C B lo hi det order p c)
    (he : Selected w D chain H G N K C B lo hi det order r e) : e = c := by
  obtain ⟨hGood,R,alpha,A,Seq,E,pr,T,F,hR,hLeast,hA,hSeq,hpr,hE,hProj,hExact,hT,hF,hInj,hBest⟩ := hc
  obtain ⟨_,U,beta,A',Seq',E',pr',T',Q,hU,hLeast',hA',hSeq',hpr',hE',hProj',_,hT',hQ,_,hBest'⟩ := he
  have ea := ConstructionGermLeastBound.least_extension hM hH hDet hX hC hS hK hlo hhi hB hp hr hle hR hU hGood hLeast hLeast'
  subst beta
  obtain ⟨eA,eS,eE,epr,eT⟩ := spaces_unique hM hA hSeq hpr hE hProj hT hA' hSeq' hpr' hE' hProj' hT'
  subst A' Seq' E' pr' T'
  have hComplete := ConstructionGermLeastBound.complete_least hM hK hR hGood hLeast
  have hExtR := ConstructionGermPatternStability.rows_extend hM hlo hhi hB hS hp hR
  have hExtU : (Project.FirstOrderSemantics.reduct M).MemberSubset p U := fun z hz =>
    ConstructionGermPatternStability.rows_extend hM hlo hhi hB hS hr hU z (hle z hz)
  have eF := ConstructionGermPatternStability.pattern_eq hM hX hC hDet hH hR.1 hU.1 (hK.transitive alpha hLeast.1)
    hA hSeq hpr hExact hComplete hExtR hExtU hF hQ
  subst Q
  exact ConstructionGermBestCoset.best_unique hM hInj (hCover alpha T hLeast.1 ⟨A,Seq,E,hA,hSeq,hE,hT⟩) hOrder hBest' hBest

theorem selected_mono (hM : FirstOrder.Theory.Models M nativeZF)
    {w D I mul q root chain H G N X K C B S lo hi det order O p r c : M.Carrier .set}
    (hH : ConstructionGermCosets.Carrier D I mul q root H) (hDet : MapsTo X I det)
    (hX : Cartesian N w X) (hC : Cartesian I K C) (hS : Cartesian C B S)
    (hK : (Project.FirstOrderSemantics.reduct M).IsOrdinal K) (hCover : Covers w N B K O)
    (hOrder : (Project.FirstOrderSemantics.reduct M).IsSetCodedWellOrder (KuratowskiZF.interpretation hM) order O)
    (hlo : ForcingWithTopCarrier.Empty lo) (hhi : (Project.FirstOrderSemantics.reduct M).SuccessorOf hi lo)
    (hB : (Project.FirstOrderSemantics.reduct M).SuccessorOf B hi)
    (hp : Condition S w p) (hr : Condition S w r) (hle : (Project.FirstOrderSemantics.reduct M).MemberSubset p r)
    (hc : Selected w D chain H G N K C B lo hi det order p c) : Selected w D chain H G N K C B lo hi det order r c := by
  have hGoodR := ConstructionGermPatternStability.good_mono hM hH hDet hX hC hS hK hlo hhi hB hp hr hle hc.1
  obtain ⟨e,he⟩ := exists_selected hM hK hCover hOrder ⟨c,selected_mem hc⟩ hGoodR
  have eq := extension_eq hM hH hDet hX hC hS hK hCover hOrder hlo hhi hB hp hr hle hc he
  exact eq ▸ he

theorem selected_covariance (hM : FirstOrder.Theory.Models M nativeZF)
    {w D I mul unit q zero root vertices chain H G N X reps K C B lo hi det pi order O p r act c e : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hm : ForcingDiagramPoset.LeftCancelMonoid D mul unit)
    (hJ : ConstructionProbeSharedIntersections.ConditionalJoins D mul) (hq : Injection D I q)
    (hChain : ConstructionComponentCofinal.Chain w D I mul q zero root vertices chain)
    (hH : ConstructionGermCosets.Carrier D I mul q root H) (hG : ConstructionGermCosets.Classes w D chain H G)
    (hDet : ConstructionGermDetectors.Detectors D I chain X reps det)
    (hX : Cartesian N w X) (hC : Cartesian I K C)
    (hK : (Project.FirstOrderSemantics.reduct M).IsOrdinal K) (hCover : Covers w N B K O)
    (hOrder : (Project.FirstOrderSemantics.reduct M).IsSetCodedWellOrder (KuratowskiZF.interpretation hM) order O)
    (hpi : (Project.FirstOrderSemantics.reduct M).mem pi H) (hMove : ConstructionCohenCompatibility.Moved pi p r)
    (hAct : ConstructionGermLeftAction.Action w D I chain H G pi act)
    (hc : Selected w D chain H G N K C B lo hi det order p c)
    (he : Selected w D chain H G N K C B lo hi det order r e) : PureKuratowski.PairMember M c e act := by
  obtain ⟨_,R,alpha,A,Seq,E,pr,T,F,hR,hLeast,hA,hSeq,hpr,hE,hProj,_,hT,hF,hInj,hBest⟩ := hc
  obtain ⟨_,U,beta,A',Seq',E',pr',T',Q,hU,hLeast',hA',hSeq',hpr',hE',hProj',_,hT',hQ,_,hBest'⟩ := he
  have hRowsMove := ConstructionGermRowCovariance.rows_permute hM hC ((hH pi).mp hpi).1 hMove hR hU
  have ea := ConstructionGermLeastBound.least_covariance hM hw hm hJ hq hChain hH hG hDet hX hC hR.1 hU.1 hK hpi hRowsMove hLeast hLeast'
  subst beta
  obtain ⟨eA,eS,eE,epr,eT⟩ := spaces_unique hM hA hSeq hpr hE hProj hT hA' hSeq' hpr' hE' hProj' hT'
  subst A' Seq' E' pr' T'
  exact ConstructionGermBestCoset.pattern_covariance hM hm hJ hq hH hG hDet.1 hpi hRowsMove hAct hF hQ hInj
    (hCover alpha T hLeast.1 ⟨A,Seq,E,hA,hSeq,hE,hT⟩) hOrder hBest hBest'

theorem selected_permute (hM : FirstOrder.Theory.Models M nativeZF)
    {w D I mul unit q zero root vertices chain H G N X reps K C B lo hi det pi order O p r act c e : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hm : ForcingDiagramPoset.LeftCancelMonoid D mul unit)
    (hJ : ConstructionProbeSharedIntersections.ConditionalJoins D mul) (hq : Injection D I q)
    (hChain : ConstructionComponentCofinal.Chain w D I mul q zero root vertices chain)
    (hH : ConstructionGermCosets.Carrier D I mul q root H) (hG : ConstructionGermCosets.Classes w D chain H G)
    (hDet : ConstructionGermDetectors.Detectors D I chain X reps det)
    (hX : Cartesian N w X) (hC : Cartesian I K C)
    (hK : (Project.FirstOrderSemantics.reduct M).IsOrdinal K) (hCover : Covers w N B K O)
    (hOrder : (Project.FirstOrderSemantics.reduct M).IsSetCodedWellOrder (KuratowskiZF.interpretation hM) order O)
    (hlo : (Project.FirstOrderSemantics.reduct M).mem lo B) (hhi : (Project.FirstOrderSemantics.reduct M).mem hi B)
    (hpi : (Project.FirstOrderSemantics.reduct M).mem pi H) (hMove : ConstructionCohenCompatibility.Moved pi p r)
    (hAct : ConstructionGermLeftAction.Action w D I chain H G pi act)
    (hc : Selected w D chain H G N K C B lo hi det order p c) (hce : PureKuratowski.PairMember M c e act) :
    Selected w D chain H G N K C B lo hi det order r e := by
  have hGoodR := ConstructionGermPatternCovariance.good_permute hM hw hm hJ hq hChain hH hG hDet hX hC hK hlo hhi hpi hMove hc.1
  obtain ⟨d,hd⟩ := exists_selected hM hK hCover hOrder ⟨c,selected_mem hc⟩ hGoodR
  have hcd := selected_covariance hM hw hm hJ hq hChain hH hG hDet hX hC hK hCover hOrder hpi hMove hAct hc hd
  have eq := ForcingConditionGraphs.function_unique hAct.1.1.1 hcd hce
  exact eq ▸ hd

theorem selected_compatible (hM : FirstOrder.Theory.Models M nativeZF)
    {w D I mul q root chain H G N X K C B S lo hi det order O p r c e : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hH : ConstructionGermCosets.Carrier D I mul q root H) (hDet : MapsTo X I det)
    (hX : Cartesian N w X) (hC : Cartesian I K C) (hS : Cartesian C B S)
    (hK : (Project.FirstOrderSemantics.reduct M).IsOrdinal K) (hCover : Covers w N B K O)
    (hOrder : (Project.FirstOrderSemantics.reduct M).IsSetCodedWellOrder (KuratowskiZF.interpretation hM) order O)
    (hlo : ForcingWithTopCarrier.Empty lo) (hhi : (Project.FirstOrderSemantics.reduct M).SuccessorOf hi lo)
    (hB : (Project.FirstOrderSemantics.reduct M).SuccessorOf B hi)
    (hp : Condition S w p) (hr : Condition S w r) (hCompat : ConstructionCohenCompatibility.Compatible p r)
    (hc : Selected w D chain H G N K C B lo hi det order p c)
    (he : Selected w D chain H G N K C B lo hi det order r e) : c = e := by
  obtain ⟨u,hu,_,hpu,hru⟩ := ConstructionCohenCompatibility.exists_union hM hw hp hr hCompat
  have hc' := selected_mono hM hH hDet hX hC hS hK hCover hOrder hlo hhi hB hp hu hpu hc
  have he' := selected_mono hM hH hDet hX hC hS hK hCover hOrder hlo hhi hB hr hu hru he
  exact selected_unique hM hK hCover hOrder hc' he'

def uniquenessSentence {m : Nat} (w D chain H G N K C B lo hi det order O p c d : Fin m) : Project.Sentence where
  formula := Project.Formula.forallClosure m (.imp (Project.Formula.isOrdinal (.bound K)) (.imp (ConstructionGermPatternOrder.covers w N B K O) (.imp (Project.Formula.isSetCodedWellOrder PureKuratowskiProject.convention (.bound order) (.bound O)) (.imp (selected w D chain H G N K C B lo hi det order p c) (.imp (selected w D chain H G N K C B lo hi det order p d) (Project.Formula.extensionalEq (.bound c) (.bound d)))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,Project.Formula.isOrdinal,ConstructionGermPatternOrder.covers_freeClosed,selected_freeClosed,Project.Formula.extensionalEq]

theorem uniqueness_models {m : Nat} (w D chain H G N K C B lo hi det order O p c d : Fin m) (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence (uniquenessSentence w D chain H G N K C B lo hi det order O p c d)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) (uniquenessSentence w D chain H G N K C B lo hi det order O p c d)]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,Project.Term.eval_bound,Project.Formula.satisfies_isOrdinal_iff,ConstructionGermPatternOrder.covers_semantics hM,Project.Formula.satisfies_isSetCodedWellOrder_iff (KuratowskiZF.interpretation hM),selected_semantics hM,Project.Formula.satisfies_extensionalEq_iff_eq (ModelTransfer.extensionality hM)]
  exact selected_unique hM

theorem uniqueness_kernel_certificate {m : Nat} (w D chain H G N K C B lo hi det order O p c d : Fin m) :
    FirstOrder.Derives nativeZF [] (Project.fo_sentence (uniquenessSentence w D chain H G N K C B lo hi det order O p c d)) :=
  ModelTransfer.derives (fun _ hM => uniqueness_models w D chain H G N K C B lo hi det order O p c d hM)

def extensionSentence {m : Nat} (w D I mul q root chain H G N X K C B S lo hi det order O p r c e : Fin m) : Project.Sentence where
  formula := Project.Formula.forallClosure m (.imp (ConstructionGermCosets.carrier D I mul q root H) (.imp (ProjectSyntax.encode id (Source.SetLanguage.mapsTo det X I)) (.imp (ProjectSyntax.encode id (ForcingCohenCoordinates.cartesian N w X)) (.imp (ProjectSyntax.encode id (ForcingCohenCoordinates.cartesian I K C)) (.imp (ProjectSyntax.encode id (ForcingCohenCoordinates.cartesian C B S)) (.imp (Project.Formula.isOrdinal (.bound K)) (.imp (ConstructionGermPatternOrder.covers w N B K O) (.imp (Project.Formula.isSetCodedWellOrder PureKuratowskiProject.convention (.bound order) (.bound O)) (.imp (Project.Formula.isEmpty (.bound lo)) (.imp (Project.Formula.isSuccessor (.bound hi) (.bound lo)) (.imp (Project.Formula.isSuccessor (.bound B) (.bound hi)) (.imp (ProjectSyntax.encode id (ForcingCohenConditions.condition S w p)) (.imp (ProjectSyntax.encode id (ForcingCohenConditions.condition S w r)) (.imp (Project.Formula.subset (.bound p) (.bound r)) (.imp (selected w D chain H G N K C B lo hi det order p c) (.imp (selected w D chain H G N K C B lo hi det order r e) (Project.Formula.extensionalEq (.bound e) (.bound c))))))))))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ConstructionGermCosets.carrier_freeClosed,ProjectSyntax.freeClosed,Project.Formula.isOrdinal,ConstructionGermPatternOrder.covers_freeClosed,Project.Formula.isEmpty,Project.Formula.isSuccessor,Project.Formula.subset,selected_freeClosed,Project.Formula.extensionalEq]

theorem extension_models {m : Nat} (w D I mul q root chain H G N X K C B S lo hi det order O p r c e : Fin m) (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence (extensionSentence w D I mul q root chain H G N X K C B S lo hi det order O p r c e)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) (extensionSentence w D I mul q root chain H G N X K C B S lo hi det order O p r c e)]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,Project.Term.eval_bound,ConstructionGermCosets.carrier_semantics hM,GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),ForcingSupportSize.mapsTo_semantics (M := M),ForcingCohenCoordinates.cartesian_semantics (M := M),Project.Formula.satisfies_isOrdinal_iff,ConstructionGermPatternOrder.covers_semantics hM,Project.Formula.satisfies_isSetCodedWellOrder_iff (KuratowskiZF.interpretation hM),Project.Formula.satisfies_isEmpty_iff,Project.Formula.satisfies_isSuccessor_iff,ForcingCohenConditions.condition_semantics (M := M),Project.Formula.satisfies_subset_iff,selected_semantics hM,Project.Formula.satisfies_extensionalEq_iff_eq (ModelTransfer.extensionality hM)]
  exact extension_eq hM

theorem extension_kernel_certificate {m : Nat} (w D I mul q root chain H G N X K C B S lo hi det order O p r c e : Fin m) :
    FirstOrder.Derives nativeZF [] (Project.fo_sentence (extensionSentence w D I mul q root chain H G N X K C B S lo hi det order O p r c e)) :=
  ModelTransfer.derives (fun _ hM => extension_models w D I mul q root chain H G N X K C B S lo hi det order O p r c e hM)

def monotonicitySentence {m : Nat} (w D I mul q root chain H G N X K C B S lo hi det order O p r c : Fin m) : Project.Sentence where
  formula := Project.Formula.forallClosure m (.imp (ConstructionGermCosets.carrier D I mul q root H) (.imp (ProjectSyntax.encode id (Source.SetLanguage.mapsTo det X I)) (.imp (ProjectSyntax.encode id (ForcingCohenCoordinates.cartesian N w X)) (.imp (ProjectSyntax.encode id (ForcingCohenCoordinates.cartesian I K C)) (.imp (ProjectSyntax.encode id (ForcingCohenCoordinates.cartesian C B S)) (.imp (Project.Formula.isOrdinal (.bound K)) (.imp (ConstructionGermPatternOrder.covers w N B K O) (.imp (Project.Formula.isSetCodedWellOrder PureKuratowskiProject.convention (.bound order) (.bound O)) (.imp (Project.Formula.isEmpty (.bound lo)) (.imp (Project.Formula.isSuccessor (.bound hi) (.bound lo)) (.imp (Project.Formula.isSuccessor (.bound B) (.bound hi)) (.imp (ProjectSyntax.encode id (ForcingCohenConditions.condition S w p)) (.imp (ProjectSyntax.encode id (ForcingCohenConditions.condition S w r)) (.imp (Project.Formula.subset (.bound p) (.bound r)) (.imp (selected w D chain H G N K C B lo hi det order p c) (selected w D chain H G N K C B lo hi det order r c))))))))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ConstructionGermCosets.carrier_freeClosed,ProjectSyntax.freeClosed,Project.Formula.isOrdinal,ConstructionGermPatternOrder.covers_freeClosed,Project.Formula.isEmpty,Project.Formula.isSuccessor,Project.Formula.subset,selected_freeClosed]

theorem monotonicity_models {m : Nat} (w D I mul q root chain H G N X K C B S lo hi det order O p r c : Fin m) (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence (monotonicitySentence w D I mul q root chain H G N X K C B S lo hi det order O p r c)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) (monotonicitySentence w D I mul q root chain H G N X K C B S lo hi det order O p r c)]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,Project.Term.eval_bound,ConstructionGermCosets.carrier_semantics hM,GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),ForcingSupportSize.mapsTo_semantics (M := M),ForcingCohenCoordinates.cartesian_semantics (M := M),Project.Formula.satisfies_isOrdinal_iff,ConstructionGermPatternOrder.covers_semantics hM,Project.Formula.satisfies_isSetCodedWellOrder_iff (KuratowskiZF.interpretation hM),Project.Formula.satisfies_isEmpty_iff,Project.Formula.satisfies_isSuccessor_iff,ForcingCohenConditions.condition_semantics (M := M),Project.Formula.satisfies_subset_iff,selected_semantics hM]
  exact selected_mono hM

theorem monotonicity_kernel_certificate {m : Nat} (w D I mul q root chain H G N X K C B S lo hi det order O p r c : Fin m) :
    FirstOrder.Derives nativeZF [] (Project.fo_sentence (monotonicitySentence w D I mul q root chain H G N X K C B S lo hi det order O p r c)) :=
  ModelTransfer.derives (fun _ hM => monotonicity_models w D I mul q root chain H G N X K C B S lo hi det order O p r c hM)

def covarianceSentence {m : Nat} (w D I mul unit q zero root vertices chain H G N X reps K C B lo hi det pi order O p r act c e : Fin m) : Project.Sentence where
  formula := Project.Formula.forallClosure m (.imp (Project.Formula.isOmega (.bound w)) (.imp (ProjectSyntax.encode id (ForcingDiagramPoset.leftCancelMonoid D mul unit)) (.imp (ConstructionProbeSharedIntersections.conditionalJoins D mul) (.imp (ProjectSyntax.encode id (Source.SetLanguage.injection q D I)) (.imp (ConstructionComponentCofinal.chain w D I mul q zero root vertices chain) (.imp (ConstructionGermCosets.carrier D I mul q root H) (.imp (ConstructionGermCosets.classes w D chain H G) (.imp (ConstructionGermDetectors.detectors D I chain X reps det) (.imp (ProjectSyntax.encode id (ForcingCohenCoordinates.cartesian N w X)) (.imp (ProjectSyntax.encode id (ForcingCohenCoordinates.cartesian I K C)) (.imp (Project.Formula.isOrdinal (.bound K)) (.imp (ConstructionGermPatternOrder.covers w N B K O) (.imp (Project.Formula.isSetCodedWellOrder PureKuratowskiProject.convention (.bound order) (.bound O)) (.imp (.mem (.bound pi) (.bound H)) (.imp (ConstructionCohenCompatibility.moved pi p r) (.imp (ConstructionGermLeftAction.action w D I chain H G pi act) (.imp (selected w D chain H G N K C B lo hi det order p c) (.imp (selected w D chain H G N K C B lo hi det order r e) (ProjectSyntax.encode id (Source.SetLanguage.edge act c e))))))))))))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,Project.Formula.isOmega,ProjectSyntax.freeClosed,ConstructionProbeSharedIntersections.conditionalJoins_freeClosed,ConstructionComponentCofinal.chain_freeClosed,ConstructionGermCosets.carrier_freeClosed,ConstructionGermCosets.classes_freeClosed,ConstructionGermDetectors.detectors_freeClosed,Project.Formula.isOrdinal,ConstructionGermPatternOrder.covers_freeClosed,ConstructionCohenCompatibility.moved_freeClosed,ConstructionGermLeftAction.action_freeClosed,selected_freeClosed]

theorem covariance_models {m : Nat} (w D I mul unit q zero root vertices chain H G N X reps K C B lo hi det pi order O p r act c e : Fin m) (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence (covarianceSentence w D I mul unit q zero root vertices chain H G N X reps K C B lo hi det pi order O p r act c e)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) (covarianceSentence w D I mul unit q zero root vertices chain H G N X reps K C B lo hi det pi order O p r act c e)]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,Project.Term.eval_bound,Project.Formula.satisfies_isOmega_iff,GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),ForcingDiagramPoset.leftCancelMonoid_semantics (M := M),ConstructionProbeSharedIntersections.conditionalJoins_semantics hM,ForcingSupportSize.injection_semantics (M := M),ConstructionComponentCofinal.chain_semantics hM,ConstructionGermCosets.carrier_semantics hM,ConstructionGermCosets.classes_semantics hM,ConstructionGermDetectors.detectors_semantics hM,ForcingCohenCoordinates.cartesian_semantics (M := M),Project.Formula.satisfies_isOrdinal_iff,ConstructionGermPatternOrder.covers_semantics hM,Project.Formula.satisfies_isSetCodedWellOrder_iff (KuratowskiZF.interpretation hM),Project.Formula.satisfies_mem_iff,ConstructionCohenCompatibility.moved_semantics hM,ConstructionGermLeftAction.action_semantics hM,selected_semantics hM,KuratowskiZF.source_edge]
  exact selected_covariance hM

theorem covariance_kernel_certificate {m : Nat} (w D I mul unit q zero root vertices chain H G N X reps K C B lo hi det pi order O p r act c e : Fin m) :
    FirstOrder.Derives nativeZF [] (Project.fo_sentence (covarianceSentence w D I mul unit q zero root vertices chain H G N X reps K C B lo hi det pi order O p r act c e)) :=
  ModelTransfer.derives (fun _ hM => covariance_models w D I mul unit q zero root vertices chain H G N X reps K C B lo hi det pi order O p r act c e hM)

def permutationSentence {m : Nat} (w D I mul unit q zero root vertices chain H G N X reps K C B lo hi det pi order O p r act c e : Fin m) : Project.Sentence where
  formula := Project.Formula.forallClosure m (.imp (Project.Formula.isOmega (.bound w)) (.imp (ProjectSyntax.encode id (ForcingDiagramPoset.leftCancelMonoid D mul unit)) (.imp (ConstructionProbeSharedIntersections.conditionalJoins D mul) (.imp (ProjectSyntax.encode id (Source.SetLanguage.injection q D I)) (.imp (ConstructionComponentCofinal.chain w D I mul q zero root vertices chain) (.imp (ConstructionGermCosets.carrier D I mul q root H) (.imp (ConstructionGermCosets.classes w D chain H G) (.imp (ConstructionGermDetectors.detectors D I chain X reps det) (.imp (ProjectSyntax.encode id (ForcingCohenCoordinates.cartesian N w X)) (.imp (ProjectSyntax.encode id (ForcingCohenCoordinates.cartesian I K C)) (.imp (Project.Formula.isOrdinal (.bound K)) (.imp (ConstructionGermPatternOrder.covers w N B K O) (.imp (Project.Formula.isSetCodedWellOrder PureKuratowskiProject.convention (.bound order) (.bound O)) (.imp (.mem (.bound lo) (.bound B)) (.imp (.mem (.bound hi) (.bound B)) (.imp (.mem (.bound pi) (.bound H)) (.imp (ConstructionCohenCompatibility.moved pi p r) (.imp (ConstructionGermLeftAction.action w D I chain H G pi act) (.imp (selected w D chain H G N K C B lo hi det order p c) (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge act c e)) (selected w D chain H G N K C B lo hi det order r e)))))))))))))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,Project.Formula.isOmega,ProjectSyntax.freeClosed,ConstructionProbeSharedIntersections.conditionalJoins_freeClosed,ConstructionComponentCofinal.chain_freeClosed,ConstructionGermCosets.carrier_freeClosed,ConstructionGermCosets.classes_freeClosed,ConstructionGermDetectors.detectors_freeClosed,Project.Formula.isOrdinal,ConstructionGermPatternOrder.covers_freeClosed,ConstructionCohenCompatibility.moved_freeClosed,ConstructionGermLeftAction.action_freeClosed,selected_freeClosed]

theorem permutation_models {m : Nat} (w D I mul unit q zero root vertices chain H G N X reps K C B lo hi det pi order O p r act c e : Fin m) (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence (permutationSentence w D I mul unit q zero root vertices chain H G N X reps K C B lo hi det pi order O p r act c e)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) (permutationSentence w D I mul unit q zero root vertices chain H G N X reps K C B lo hi det pi order O p r act c e)]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,Project.Term.eval_bound,Project.Formula.satisfies_isOmega_iff,GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),ForcingDiagramPoset.leftCancelMonoid_semantics (M := M),ConstructionProbeSharedIntersections.conditionalJoins_semantics hM,ForcingSupportSize.injection_semantics (M := M),ConstructionComponentCofinal.chain_semantics hM,ConstructionGermCosets.carrier_semantics hM,ConstructionGermCosets.classes_semantics hM,ConstructionGermDetectors.detectors_semantics hM,ForcingCohenCoordinates.cartesian_semantics (M := M),Project.Formula.satisfies_isOrdinal_iff,ConstructionGermPatternOrder.covers_semantics hM,Project.Formula.satisfies_isSetCodedWellOrder_iff (KuratowskiZF.interpretation hM),Project.Formula.satisfies_mem_iff,ConstructionCohenCompatibility.moved_semantics hM,ConstructionGermLeftAction.action_semantics hM,selected_semantics hM,KuratowskiZF.source_edge]
  exact selected_permute hM

theorem permutation_kernel_certificate {m : Nat} (w D I mul unit q zero root vertices chain H G N X reps K C B lo hi det pi order O p r act c e : Fin m) :
    FirstOrder.Derives nativeZF [] (Project.fo_sentence (permutationSentence w D I mul unit q zero root vertices chain H G N X reps K C B lo hi det pi order O p r act c e)) :=
  ModelTransfer.derives (fun _ hM => permutation_models w D I mul unit q zero root vertices chain H G N X reps K C B lo hi det pi order O p r act c e hM)

def compatibilitySentence {m : Nat} (w D I mul q root chain H G N X K C B S lo hi det order O p r c e : Fin m) : Project.Sentence where
  formula := Project.Formula.forallClosure m (.imp (Project.Formula.isOmega (.bound w)) (.imp (ConstructionGermCosets.carrier D I mul q root H) (.imp (ProjectSyntax.encode id (Source.SetLanguage.mapsTo det X I)) (.imp (ProjectSyntax.encode id (ForcingCohenCoordinates.cartesian N w X)) (.imp (ProjectSyntax.encode id (ForcingCohenCoordinates.cartesian I K C)) (.imp (ProjectSyntax.encode id (ForcingCohenCoordinates.cartesian C B S)) (.imp (Project.Formula.isOrdinal (.bound K)) (.imp (ConstructionGermPatternOrder.covers w N B K O) (.imp (Project.Formula.isSetCodedWellOrder PureKuratowskiProject.convention (.bound order) (.bound O)) (.imp (Project.Formula.isEmpty (.bound lo)) (.imp (Project.Formula.isSuccessor (.bound hi) (.bound lo)) (.imp (Project.Formula.isSuccessor (.bound B) (.bound hi)) (.imp (ProjectSyntax.encode id (ForcingCohenConditions.condition S w p)) (.imp (ProjectSyntax.encode id (ForcingCohenConditions.condition S w r)) (.imp (ConstructionCompatiblePlacement.compatible p r) (.imp (selected w D chain H G N K C B lo hi det order p c) (.imp (selected w D chain H G N K C B lo hi det order r e) (Project.Formula.extensionalEq (.bound c) (.bound e)))))))))))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,Project.Formula.isOmega,ConstructionGermCosets.carrier_freeClosed,ProjectSyntax.freeClosed,Project.Formula.isOrdinal,ConstructionGermPatternOrder.covers_freeClosed,Project.Formula.isEmpty,Project.Formula.isSuccessor,ConstructionCompatiblePlacement.compatible_freeClosed,selected_freeClosed,Project.Formula.extensionalEq]

theorem compatibility_models {m : Nat} (w D I mul q root chain H G N X K C B S lo hi det order O p r c e : Fin m) (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence (compatibilitySentence w D I mul q root chain H G N X K C B S lo hi det order O p r c e)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) (compatibilitySentence w D I mul q root chain H G N X K C B S lo hi det order O p r c e)]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,Project.Term.eval_bound,Project.Formula.satisfies_isOmega_iff,ConstructionGermCosets.carrier_semantics hM,GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),ForcingSupportSize.mapsTo_semantics (M := M),ForcingCohenCoordinates.cartesian_semantics (M := M),Project.Formula.satisfies_isOrdinal_iff,ConstructionGermPatternOrder.covers_semantics hM,Project.Formula.satisfies_isSetCodedWellOrder_iff (KuratowskiZF.interpretation hM),Project.Formula.satisfies_isEmpty_iff,Project.Formula.satisfies_isSuccessor_iff,ForcingCohenConditions.condition_semantics (M := M),ConstructionCompatiblePlacement.compatible_semantics hM,selected_semantics hM,Project.Formula.satisfies_extensionalEq_iff_eq (ModelTransfer.extensionality hM)]
  exact selected_compatible hM

theorem compatibility_kernel_certificate {m : Nat} (w D I mul q root chain H G N X K C B S lo hi det order O p r c e : Fin m) :
    FirstOrder.Derives nativeZF [] (Project.fo_sentence (compatibilitySentence w D I mul q root chain H G N X K C B S lo hi det order O p r c e)) :=
  ModelTransfer.derives (fun _ hM => compatibility_models w D I mul q root chain H G N X K C B S lo hi det order O p r c e hM)

end PPAC.Migration.ConstructionGermSelected
