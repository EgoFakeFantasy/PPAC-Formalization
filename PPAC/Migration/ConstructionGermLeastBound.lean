/- Pinned GermSelectors.leastBound and StableSelectors.complete_least /
leastBound_extension. Separate the actual distinguishing bounds inside K,
then use the existing internal ordinal wellorder. All quantification is over
model sets; no host well-foundedness or standard-omega assumption. -/
import PPAC.Migration.ConstructionGermPatternCovariance

namespace PPAC.Migration.ConstructionGermLeastBound
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ForcingSupportSize (MapsTo Injection)
open ForcingCohenCoordinates (Cartesian)
open ConstructionGermCosets (Carrier Classes)
open ConstructionGermEventual (Space)
open ConstructionGermComplete (Complete)
open ConstructionFractionOrder (NatLe)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

def Distinguishes (w D chain H G N alpha B det R : M.Carrier .set) : Prop := ∃ A S E pr T F,
  Space alpha B A ∧ Space w A S ∧ MapsTo S E pr ∧ ConstructionGermEventual.Classes w S E ∧
    ConstructionGermEventual.Projection w S pr ∧ ConstructionGermEventual.Exact w pr ∧ Space N E T ∧
      ConstructionGermPattern.Pattern w D chain H G N alpha B A E T det R pr F ∧ Injection G T F

def distinguishes {m : Nat} (w D chain H G N alpha B det R : Fin m) : Project.Formula 1 m := (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.conj (ConstructionGermEventual.space alpha.succ.succ.succ.succ.succ.succ B.succ.succ.succ.succ.succ.succ 5) (.conj (ConstructionGermEventual.space w.succ.succ.succ.succ.succ.succ 5 4) (.conj (ProjectSyntax.encode id (Source.SetLanguage.mapsTo 2 4 3)) (.conj (ConstructionGermEventual.classes w.succ.succ.succ.succ.succ.succ 4 3) (.conj (ConstructionGermEventual.projection w.succ.succ.succ.succ.succ.succ 4 2) (.conj (ConstructionGermEventual.exactProjection w.succ.succ.succ.succ.succ.succ 2) (.conj (ConstructionGermEventual.space N.succ.succ.succ.succ.succ.succ 3 1) (.conj (ConstructionGermPattern.pattern w.succ.succ.succ.succ.succ.succ D.succ.succ.succ.succ.succ.succ chain.succ.succ.succ.succ.succ.succ H.succ.succ.succ.succ.succ.succ G.succ.succ.succ.succ.succ.succ N.succ.succ.succ.succ.succ.succ alpha.succ.succ.succ.succ.succ.succ B.succ.succ.succ.succ.succ.succ 5 3 1 det.succ.succ.succ.succ.succ.succ R.succ.succ.succ.succ.succ.succ 2 0) (ProjectSyntax.encode id (Source.SetLanguage.injection 0 G.succ.succ.succ.succ.succ.succ 1))))))))))))))))

theorem distinguishes_freeClosed {m : Nat} (w D chain H G N alpha B det R : Fin m) : (distinguishes w D chain H G N alpha B det R).FreeClosed := by
  simp -implicitDefEqProofs [distinguishes,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
    ConstructionGermEventual.space_freeClosed,ConstructionGermEventual.classes_freeClosed,
    ConstructionGermEventual.projection_freeClosed,ConstructionGermEventual.exactProjection_freeClosed,ConstructionGermPattern.pattern_freeClosed]

theorem distinguishes_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w D chain H G N alpha B det R : Fin m) :
    Project.Formula.satisfies env (distinguishes w D chain H G N alpha B det R) ↔
      Distinguishes (env.bound w) (env.bound D) (env.bound chain) (env.bound H) (env.bound G) (env.bound N) (env.bound alpha) (env.bound B) (env.bound det) (env.bound R) := by
  simp only [distinguishes,Distinguishes,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,
    ConstructionGermEventual.space_semantics hM,ConstructionGermEventual.classes_semantics hM,
    ConstructionGermEventual.projection_semantics hM,ConstructionGermEventual.exactProjection_semantics hM,
    ConstructionGermPattern.pattern_semantics hM,GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingSupportSize.mapsTo_semantics (M := M),ForcingSupportSize.injection_semantics (M := M)]
  rfl

def Least (w D chain H G N K B det R alpha : M.Carrier .set) : Prop :=
  (Project.FirstOrderSemantics.reduct M).mem alpha K ∧ Distinguishes w D chain H G N alpha B det R ∧
    ∀ beta, (Project.FirstOrderSemantics.reduct M).mem beta K →
      Distinguishes w D chain H G N beta B det R → NatLe alpha beta

def least {m : Nat} (w D chain H G N K B det R alpha : Fin m) : Project.Formula 1 m :=
  .conj (.mem (.bound alpha) (.bound K))
    (.conj (distinguishes w D chain H G N alpha B det R)
      (.forallE (.imp (.mem (.bound 0) (.bound K.succ))
        (.imp (distinguishes w.succ D.succ chain.succ H.succ G.succ N.succ 0 B.succ det.succ R.succ)
          (.disj (Project.Formula.extensionalEq (.bound alpha.succ) (.bound 0)) (.mem (.bound alpha.succ) (.bound 0)))))))

theorem least_freeClosed {m : Nat} (w D chain H G N K B det R alpha : Fin m) :
    (least w D chain H G N K B det R alpha).FreeClosed := by
  simp -implicitDefEqProofs [least,Definitional.Formula.FreeClosed,distinguishes_freeClosed,Project.Formula.extensionalEq]

theorem least_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w D chain H G N K B det R alpha : Fin m) :
    Project.Formula.satisfies env (least w D chain H G N K B det R alpha) ↔
      Least (env.bound w) (env.bound D) (env.bound chain) (env.bound H) (env.bound G) (env.bound N)
        (env.bound K) (env.bound B) (env.bound det) (env.bound R) (env.bound alpha) := by
  simp only [least,Least,NatLe,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_forall_iff,
    Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_disj_iff,Project.Formula.satisfies_mem_iff,
    Project.Formula.satisfies_extensionalEq_iff_eq (ModelTransfer.extensionality hM),Project.Term.eval_bound,distinguishes_semantics hM]
  rfl

theorem exists_least (hM : FirstOrder.Theory.Models M nativeZF)
    {w D chain H G N K B det R : M.Carrier .set}
    (hK : (Project.FirstOrderSemantics.reduct M).IsOrdinal K)
    (hExists : ∃ alpha, (Project.FirstOrderSemantics.reduct M).mem alpha K ∧ Distinguishes w D chain H G N alpha B det R) :
    ∃ alpha, Least w D chain H G N K B det R alpha := by
  let schema : Project.UnarySchema 9 := { body := distinguishes 1 2 3 4 5 6 0 7 8 9, freeClosed := distinguishes_freeClosed .. }
  let env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) 9 := {
    bound := Fin.cases w (Fin.cases D (Fin.cases chain (Fin.cases H (Fin.cases G (Fin.cases N
      (Fin.cases B (Fin.cases det (fun _ => R)))))))), free := fun _ => R }
  have he alpha : schema.denote env alpha ↔ Distinguishes w D chain H G N alpha B det R :=
    distinguishes_semantics hM (env.push alpha) 1 2 3 4 5 6 0 7 8 9
  obtain ⟨A,hA⟩ := ZF.separation_exists_d (ModelTransfer.project_models_iff.mp hM) schema env K
  obtain ⟨bound,hbound,hDist⟩ := hExists
  obtain ⟨alpha,ha,hmin⟩ := hK.wellOrder.least A (fun a ha => ((hA a).mp ha).1)
    ⟨bound,(hA bound).mpr ⟨hbound,(he bound).mpr hDist⟩⟩
  obtain ⟨haK,haDist⟩ := (hA alpha).mp ha
  refine ⟨alpha,haK,(he alpha).mp haDist,?_⟩
  intro beta hb hD
  rcases hmin beta ((hA beta).mpr ⟨hb,(he beta).mpr hD⟩) with eq | lt
  · exact Or.inl ((ModelTransfer.extensionality hM).eq_of_same_members alpha beta eq)
  · exact Or.inr lt

theorem least_unique {w D chain H G N K B det R alpha beta : M.Carrier .set}
    (hK : (Project.FirstOrderSemantics.reduct M).IsOrdinal K)
    (ha : Least w D chain H G N K B det R alpha) (hb : Least w D chain H G N K B det R beta) : alpha = beta := by
  rcases ha.2.2 beta hb.1 hb.2.1 with e | hab
  · exact e
  rcases hb.2.2 alpha ha.1 ha.2.1 with e | hba
  · exact e.symm
  exact (hK.wellOrder.linear.irrefl alpha ha.1 (hK.wellOrder.linear.trans alpha ha.1 beta hb.1 alpha ha.1 hab hba)).elim

theorem rows_unique (hM : FirstOrder.Theory.Models M nativeZF) {C B lo hi p R U : M.Carrier .set}
    (hR : ConstructionCohenRows.Rows C B lo hi p R) (hU : ConstructionCohenRows.Rows C B lo hi p U) : R = U := by
  apply Structure.IsSetRelation.eq_of_pairMember_iff (ModelTransfer.project_models_iff.mp hM).1
    ((ForcingSupportSize.native_mapsTo hM C B R).mp hR.1).1.1
    ((ForcingSupportSize.native_mapsTo hM C B U).mp hU.1).1.1
  exact fun a b => (hR.2 a b).trans (hU.2 a b).symm

theorem complete_least (hM : FirstOrder.Theory.Models M nativeZF)
    {w D chain H G N K C B lo hi det p R alpha : M.Carrier .set}
    (hK : (Project.FirstOrderSemantics.reduct M).IsOrdinal K)
    (hR : ConstructionCohenRows.Rows C B lo hi p R)
    (hGood : ConstructionGermGoodDense.Good w D chain H G N K C B lo hi det p)
    (hLeast : Least w D chain H G N K B det R alpha) : Complete w H N det alpha p := by
  obtain ⟨beta,U,A,S,E,pr,T,F,hbeta,hU,hA,hS,hpr,hE,hProj,hExact,hT,hF,hInj,hComplete⟩ := hGood
  have eq := rows_unique hM hU hR
  subst U
  have hDist : Distinguishes w D chain H G N beta B det R := ⟨A,S,E,pr,T,F,hA,hS,hpr,hE,hProj,hExact,hT,hF,hInj⟩
  rcases hLeast.2.2 beta hbeta hDist with eq | hlt
  · exact eq.symm ▸ hComplete
  · exact ConstructionGermComplete.downward hComplete ((hK.mem hbeta).transitive alpha hlt)

theorem construction (hM : FirstOrder.Theory.Models M nativeZF)
    {w D chain H G N K C B lo hi det p : M.Carrier .set}
    (hK : (Project.FirstOrderSemantics.reduct M).IsOrdinal K)
    (hGood : ConstructionGermGoodDense.Good w D chain H G N K C B lo hi det p) :
    ∃ R alpha, ConstructionCohenRows.Rows C B lo hi p R ∧ Least w D chain H G N K B det R alpha ∧ Complete w H N det alpha p := by
  have hGoodCopy := hGood
  obtain ⟨beta,R,A,S,E,pr,T,F,hbeta,hR,hA,hS,hpr,hE,hProj,hExact,hT,hF,hInj,_⟩ := hGoodCopy
  obtain ⟨alpha,hLeast⟩ := exists_least hM hK ⟨beta,hbeta,A,S,E,pr,T,F,hA,hS,hpr,hE,hProj,hExact,hT,hF,hInj⟩
  exact ⟨R,alpha,hR,hLeast,complete_least hM hK hR hGood hLeast⟩

theorem distinguishes_preserved (hM : FirstOrder.Theory.Models M nativeZF)
    {w D I mul q root chain H G N X K C B alpha det p R U : M.Carrier .set}
    (hX : Cartesian N w X) (hC : Cartesian I K C) (hDet : MapsTo X I det)
    (hH : Carrier D I mul q root H) (hR : MapsTo C B R) (hU : MapsTo C B U)
    (hAlpha : (Project.FirstOrderSemantics.reduct M).MemberSubset alpha K)
    (hComplete : Complete w H N det alpha p)
    (hExtendR : (Project.FirstOrderSemantics.reduct M).MemberSubset p R)
    (hExtendU : (Project.FirstOrderSemantics.reduct M).MemberSubset p U)
    (hDist : Distinguishes w D chain H G N alpha B det R) : Distinguishes w D chain H G N alpha B det U := by
  obtain ⟨A,S,E,pr,T,F,hA,hS,hpr,hE,hProj,hExact,hT,hF,hInj⟩ := hDist
  exact ⟨A,S,E,pr,T,F,hA,hS,hpr,hE,hProj,hExact,hT,
    ConstructionGermPatternStability.pattern_preserved hM hX hC hDet hH hR hU hAlpha hA hS hpr hExact hComplete hExtendR hExtendU hF,hInj⟩

theorem least_extension (hM : FirstOrder.Theory.Models M nativeZF)
    {w D I mul q root chain H G N X K C B S lo hi det p r R U alpha beta : M.Carrier .set}
    (hH : Carrier D I mul q root H) (hDet : MapsTo X I det)
    (hX : Cartesian N w X) (hC : Cartesian I K C) (hS : Cartesian C B S)
    (hK : (Project.FirstOrderSemantics.reduct M).IsOrdinal K)
    (hlo : ForcingWithTopCarrier.Empty lo) (hhi : (Project.FirstOrderSemantics.reduct M).SuccessorOf hi lo)
    (hB : (Project.FirstOrderSemantics.reduct M).SuccessorOf B hi)
    (hp : ForcingCohenConditions.Condition S w p) (hr : ForcingCohenConditions.Condition S w r)
    (hle : (Project.FirstOrderSemantics.reduct M).MemberSubset p r)
    (hR : ConstructionCohenRows.Rows C B lo hi p R) (hU : ConstructionCohenRows.Rows C B lo hi r U)
    (hGood : ConstructionGermGoodDense.Good w D chain H G N K C B lo hi det p)
    (hAlpha : Least w D chain H G N K B det R alpha) (hBeta : Least w D chain H G N K B det U beta) : beta = alpha := by
  have hComplete := complete_least hM hK hR hGood hAlpha
  have hExtR := ConstructionGermPatternStability.rows_extend hM hlo hhi hB hS hp hR
  have hExtU : (Project.FirstOrderSemantics.reduct M).MemberSubset p U := fun z hz =>
    ConstructionGermPatternStability.rows_extend hM hlo hhi hB hS hr hU z (hle z hz)
  have hDistU := distinguishes_preserved hM hX hC hDet hH hR.1 hU.1 (hK.transitive alpha hAlpha.1) hComplete hExtR hExtU hAlpha.2.1
  have hba := hBeta.2.2 alpha hAlpha.1 hDistU
  have hSub : (Project.FirstOrderSemantics.reduct M).MemberSubset beta alpha := by
    rcases hba with eq | lt
    · exact fun z hz => eq ▸ hz
    · exact (hK.mem hAlpha.1).transitive beta lt
  have hDistR := distinguishes_preserved hM hX hC hDet hH hU.1 hR.1 (hK.transitive beta hBeta.1)
    (ConstructionGermComplete.downward hComplete hSub) hExtU hExtR hBeta.2.1
  rcases hba with eq | hba
  · exact eq
  rcases hAlpha.2.2 beta hBeta.1 hDistR with eq | hab
  · exact eq.symm
  exact (hK.wellOrder.linear.irrefl alpha hAlpha.1
    (hK.wellOrder.linear.trans alpha hAlpha.1 beta hBeta.1 alpha hAlpha.1 hab hba)).elim

theorem distinguishes_moved_iff (hM : FirstOrder.Theory.Models M nativeZF)
    {w D I mul unit q zero root vertices chain H G N X reps K C B alpha det pi R U : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hm : ForcingDiagramPoset.LeftCancelMonoid D mul unit)
    (hJ : ConstructionProbeSharedIntersections.ConditionalJoins D mul) (hq : Injection D I q)
    (hChain : ConstructionComponentCofinal.Chain w D I mul q zero root vertices chain)
    (hH : Carrier D I mul q root H) (hG : Classes w D chain H G)
    (hDet : ConstructionGermDetectors.Detectors D I chain X reps det)
    (hX : Cartesian N w X) (hC : Cartesian I K C) (hR : MapsTo C B R) (hU : MapsTo C B U)
    (hAlpha : (Project.FirstOrderSemantics.reduct M).MemberSubset alpha K)
    (hpi : (Project.FirstOrderSemantics.reduct M).mem pi H) (hMove : ConstructionCohenCompatibility.Moved pi R U) :
    Distinguishes w D chain H G N alpha B det U ↔ Distinguishes w D chain H G N alpha B det R := by
  obtain ⟨act,hAct⟩ := ConstructionGermLeftAction.construction hM hw hm hJ hq hChain hH hG hpi
  constructor
  · rintro ⟨A,S,E,pr,T,Q,hA,hS,hpr,hE,hProj,hExact,hT,hQ,hInjQ⟩
    obtain ⟨F,hF⟩ := ConstructionGermPattern.exists_pattern hM hw hChain hDet hH hG hX hC hR hAlpha hA hS hT hpr hExact
    exact ⟨A,S,E,pr,T,F,hA,hS,hpr,hE,hProj,hExact,hT,hF,
      (ConstructionGermPatternCovariance.distinguishes_moveRows_iff hM hm hJ hq hH hG hDet.1 hpi hMove hAct hF hQ).mp hInjQ⟩
  · rintro ⟨A,S,E,pr,T,F,hA,hS,hpr,hE,hProj,hExact,hT,hF,hInjF⟩
    obtain ⟨Q,hQ⟩ := ConstructionGermPattern.exists_pattern hM hw hChain hDet hH hG hX hC hU hAlpha hA hS hT hpr hExact
    exact ⟨A,S,E,pr,T,Q,hA,hS,hpr,hE,hProj,hExact,hT,hQ,
      (ConstructionGermPatternCovariance.distinguishes_moveRows_iff hM hm hJ hq hH hG hDet.1 hpi hMove hAct hF hQ).mpr hInjF⟩

theorem least_covariance (hM : FirstOrder.Theory.Models M nativeZF)
    {w D I mul unit q zero root vertices chain H G N X reps K C B det pi R U alpha beta : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hm : ForcingDiagramPoset.LeftCancelMonoid D mul unit)
    (hJ : ConstructionProbeSharedIntersections.ConditionalJoins D mul) (hq : Injection D I q)
    (hChain : ConstructionComponentCofinal.Chain w D I mul q zero root vertices chain)
    (hH : Carrier D I mul q root H) (hG : Classes w D chain H G)
    (hDet : ConstructionGermDetectors.Detectors D I chain X reps det)
    (hX : Cartesian N w X) (hC : Cartesian I K C) (hR : MapsTo C B R) (hU : MapsTo C B U)
    (hK : (Project.FirstOrderSemantics.reduct M).IsOrdinal K)
    (hpi : (Project.FirstOrderSemantics.reduct M).mem pi H) (hMove : ConstructionCohenCompatibility.Moved pi R U)
    (hAlpha : Least w D chain H G N K B det R alpha) (hBeta : Least w D chain H G N K B det U beta) : beta = alpha := by
  have he a (ha : (Project.FirstOrderSemantics.reduct M).mem a K) :=
    distinguishes_moved_iff hM hw hm hJ hq hChain hH hG hDet hX hC hR hU (hK.transitive a ha) hpi hMove
  have hLeastU : Least w D chain H G N K B det U alpha :=
    ⟨hAlpha.1,(he alpha hAlpha.1).mpr hAlpha.2.1,fun b hb hDist => hAlpha.2.2 b hb ((he b hb).mp hDist)⟩
  exact least_unique hK hBeta hLeastU


def existenceSentence {m : Nat} (w D chain H G N K B det R : Fin m) : Project.Sentence where
  formula := Project.Formula.forallClosure m (.imp (Project.Formula.isOrdinal (.bound K)) (.imp (.existsE (.conj (.mem (.bound 0) (.bound K.succ)) (distinguishes w.succ D.succ chain.succ H.succ G.succ N.succ 0 B.succ det.succ R.succ))) (.existsE (least w.succ D.succ chain.succ H.succ G.succ N.succ K.succ B.succ det.succ R.succ 0))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,Project.Formula.isOrdinal,least_freeClosed,distinguishes_freeClosed]

theorem existence_models {m : Nat} (w D chain H G N K B det R : Fin m) (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence (existenceSentence w D chain H G N K B det R)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) (existenceSentence w D chain H G N K B det R)]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,Project.Formula.satisfies_isOrdinal_iff,least_semantics hM,distinguishes_semantics hM]
  exact exists_least hM

theorem existence_kernel_certificate {m : Nat} (w D chain H G N K B det R : Fin m) :
    FirstOrder.Derives nativeZF [] (Project.fo_sentence (existenceSentence w D chain H G N K B det R)) :=
  ModelTransfer.derives (fun _ hM => existence_models w D chain H G N K B det R hM)

def constructionSentence {m : Nat} (w D chain H G N K C B lo hi det p : Fin m) : Project.Sentence where
  formula := Project.Formula.forallClosure m (.imp (Project.Formula.isOrdinal (.bound K)) (.imp (ConstructionGermGoodDense.good w D chain H G N K C B lo hi det p) (.existsE (.existsE (.conj (ConstructionCohenRows.rows C.succ.succ B.succ.succ lo.succ.succ hi.succ.succ p.succ.succ 1) (.conj (least w.succ.succ D.succ.succ chain.succ.succ H.succ.succ G.succ.succ N.succ.succ K.succ.succ B.succ.succ det.succ.succ 1 0) (ConstructionGermComplete.complete w.succ.succ H.succ.succ N.succ.succ det.succ.succ 0 p.succ.succ)))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,Project.Formula.isOrdinal,ConstructionCohenRows.rows_freeClosed,ConstructionGermGoodDense.good_freeClosed,least_freeClosed,ConstructionGermComplete.complete_freeClosed]

theorem construction_models {m : Nat} (w D chain H G N K C B lo hi det p : Fin m) (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence (constructionSentence w D chain H G N K C B lo hi det p)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) (constructionSentence w D chain H G N K C B lo hi det p)]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,Project.Term.eval_bound,Project.Formula.satisfies_isOrdinal_iff,ConstructionCohenRows.rows_semantics hM,ConstructionGermGoodDense.good_semantics hM,least_semantics hM,ConstructionGermComplete.complete_semantics hM]
  exact construction hM

theorem construction_kernel_certificate {m : Nat} (w D chain H G N K C B lo hi det p : Fin m) :
    FirstOrder.Derives nativeZF [] (Project.fo_sentence (constructionSentence w D chain H G N K C B lo hi det p)) :=
  ModelTransfer.derives (fun _ hM => construction_models w D chain H G N K C B lo hi det p hM)

def completeSentence {m : Nat} (w D chain H G N K C B lo hi det p R alpha : Fin m) : Project.Sentence where
  formula := Project.Formula.forallClosure m (.imp (Project.Formula.isOrdinal (.bound K)) (.imp (ConstructionCohenRows.rows C B lo hi p R) (.imp (ConstructionGermGoodDense.good w D chain H G N K C B lo hi det p) (.imp (least w D chain H G N K B det R alpha) (ConstructionGermComplete.complete w H N det alpha p)))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,Project.Formula.isOrdinal,ConstructionCohenRows.rows_freeClosed,ConstructionGermGoodDense.good_freeClosed,least_freeClosed,ConstructionGermComplete.complete_freeClosed]

theorem complete_models {m : Nat} (w D chain H G N K C B lo hi det p R alpha : Fin m) (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence (completeSentence w D chain H G N K C B lo hi det p R alpha)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) (completeSentence w D chain H G N K C B lo hi det p R alpha)]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,Project.Term.eval_bound,Project.Formula.satisfies_isOrdinal_iff,ConstructionCohenRows.rows_semantics hM,ConstructionGermGoodDense.good_semantics hM,least_semantics hM,ConstructionGermComplete.complete_semantics hM]
  exact complete_least hM

theorem complete_kernel_certificate {m : Nat} (w D chain H G N K C B lo hi det p R alpha : Fin m) :
    FirstOrder.Derives nativeZF [] (Project.fo_sentence (completeSentence w D chain H G N K C B lo hi det p R alpha)) :=
  ModelTransfer.derives (fun _ hM => complete_models w D chain H G N K C B lo hi det p R alpha hM)

def extensionSentence {m : Nat} (w D I mul q root chain H G N X K C B S lo hi det p r R U alpha beta : Fin m) : Project.Sentence where
  formula := Project.Formula.forallClosure m (.imp (ConstructionGermCosets.carrier D I mul q root H) (.imp (ProjectSyntax.encode id (Source.SetLanguage.mapsTo det X I)) (.imp (ProjectSyntax.encode id (ForcingCohenCoordinates.cartesian N w X)) (.imp (ProjectSyntax.encode id (ForcingCohenCoordinates.cartesian I K C)) (.imp (ProjectSyntax.encode id (ForcingCohenCoordinates.cartesian C B S)) (.imp (Project.Formula.isOrdinal (.bound K)) (.imp (Project.Formula.isEmpty (.bound lo)) (.imp (Project.Formula.isSuccessor (.bound hi) (.bound lo)) (.imp (Project.Formula.isSuccessor (.bound B) (.bound hi)) (.imp (ProjectSyntax.encode id (ForcingCohenConditions.condition S w p)) (.imp (ProjectSyntax.encode id (ForcingCohenConditions.condition S w r)) (.imp (Project.Formula.subset (.bound p) (.bound r)) (.imp (ConstructionCohenRows.rows C B lo hi p R) (.imp (ConstructionCohenRows.rows C B lo hi r U) (.imp (ConstructionGermGoodDense.good w D chain H G N K C B lo hi det p) (.imp (least w D chain H G N K B det R alpha) (.imp (least w D chain H G N K B det U beta) (Project.Formula.extensionalEq (.bound beta) (.bound alpha)))))))))))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,Project.Formula.isOrdinal,Project.Formula.isEmpty,Project.Formula.isSuccessor,Project.Formula.subset,Project.Formula.extensionalEq,ProjectSyntax.freeClosed,ConstructionCohenRows.rows_freeClosed,ConstructionGermGoodDense.good_freeClosed,least_freeClosed,ConstructionGermCosets.carrier_freeClosed]

theorem extension_models {m : Nat} (w D I mul q root chain H G N X K C B S lo hi det p r R U alpha beta : Fin m) (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence (extensionSentence w D I mul q root chain H G N X K C B S lo hi det p r R U alpha beta)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) (extensionSentence w D I mul q root chain H G N X K C B S lo hi det p r R U alpha beta)]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,Project.Term.eval_bound,Project.Formula.satisfies_isOrdinal_iff,Project.Formula.satisfies_isEmpty_iff,Project.Formula.satisfies_isSuccessor_iff,Project.Formula.satisfies_subset_iff,Project.Formula.satisfies_extensionalEq_iff_eq (ModelTransfer.extensionality hM),GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),ConstructionCohenRows.rows_semantics hM,ConstructionGermGoodDense.good_semantics hM,least_semantics hM,ConstructionGermCosets.carrier_semantics hM,ForcingSupportSize.mapsTo_semantics (M := M),ForcingCohenCoordinates.cartesian_semantics (M := M),ForcingCohenConditions.condition_semantics (M := M)]
  exact least_extension hM

theorem extension_kernel_certificate {m : Nat} (w D I mul q root chain H G N X K C B S lo hi det p r R U alpha beta : Fin m) :
    FirstOrder.Derives nativeZF [] (Project.fo_sentence (extensionSentence w D I mul q root chain H G N X K C B S lo hi det p r R U alpha beta)) :=
  ModelTransfer.derives (fun _ hM => extension_models w D I mul q root chain H G N X K C B S lo hi det p r R U alpha beta hM)

def covarianceSentence {m : Nat} (w D I mul unit q zero root vertices chain H G N X reps K C B det pi R U alpha beta : Fin m) : Project.Sentence where
  formula := Project.Formula.forallClosure m (.imp (Project.Formula.isOmega (.bound w)) (.imp (ProjectSyntax.encode id (ForcingDiagramPoset.leftCancelMonoid D mul unit)) (.imp (ConstructionProbeSharedIntersections.conditionalJoins D mul) (.imp (ProjectSyntax.encode id (Source.SetLanguage.injection q D I)) (.imp (ConstructionComponentCofinal.chain w D I mul q zero root vertices chain) (.imp (ConstructionGermCosets.carrier D I mul q root H) (.imp (ConstructionGermCosets.classes w D chain H G) (.imp (ConstructionGermDetectors.detectors D I chain X reps det) (.imp (ProjectSyntax.encode id (ForcingCohenCoordinates.cartesian N w X)) (.imp (ProjectSyntax.encode id (ForcingCohenCoordinates.cartesian I K C)) (.imp (ProjectSyntax.encode id (Source.SetLanguage.mapsTo R C B)) (.imp (ProjectSyntax.encode id (Source.SetLanguage.mapsTo U C B)) (.imp (Project.Formula.isOrdinal (.bound K)) (.imp (.mem (.bound pi) (.bound H)) (.imp (ConstructionCohenCompatibility.moved pi R U) (.imp (least w D chain H G N K B det R alpha) (.imp (least w D chain H G N K B det U beta) (Project.Formula.extensionalEq (.bound beta) (.bound alpha)))))))))))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,Project.Formula.isOrdinal,Project.Formula.isOmega,Project.Formula.extensionalEq,ProjectSyntax.freeClosed,least_freeClosed,ConstructionGermCosets.carrier_freeClosed,ConstructionGermCosets.classes_freeClosed,ConstructionComponentCofinal.chain_freeClosed,ConstructionGermDetectors.detectors_freeClosed,ConstructionCohenCompatibility.moved_freeClosed,ConstructionProbeSharedIntersections.conditionalJoins_freeClosed]

theorem covariance_models {m : Nat} (w D I mul unit q zero root vertices chain H G N X reps K C B det pi R U alpha beta : Fin m) (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence (covarianceSentence w D I mul unit q zero root vertices chain H G N X reps K C B det pi R U alpha beta)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) (covarianceSentence w D I mul unit q zero root vertices chain H G N X reps K C B det pi R U alpha beta)]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,Project.Formula.satisfies_isOrdinal_iff,Project.Formula.satisfies_isOmega_iff,Project.Formula.satisfies_extensionalEq_iff_eq (ModelTransfer.extensionality hM),GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),least_semantics hM,ConstructionGermCosets.carrier_semantics hM,ConstructionGermCosets.classes_semantics hM,ConstructionComponentCofinal.chain_semantics hM,ConstructionGermDetectors.detectors_semantics hM,ConstructionCohenCompatibility.moved_semantics hM,ConstructionProbeSharedIntersections.conditionalJoins_semantics hM,ForcingSupportSize.mapsTo_semantics (M := M),ForcingSupportSize.injection_semantics (M := M),ForcingCohenCoordinates.cartesian_semantics (M := M),ForcingDiagramPoset.leftCancelMonoid_semantics (M := M)]
  exact least_covariance hM

theorem covariance_kernel_certificate {m : Nat} (w D I mul unit q zero root vertices chain H G N X reps K C B det pi R U alpha beta : Fin m) :
    FirstOrder.Derives nativeZF [] (Project.fo_sentence (covarianceSentence w D I mul unit q zero root vertices chain H G N X reps K C B det pi R U alpha beta)) :=
  ModelTransfer.derives (fun _ hM => covariance_models w D I mul unit q zero root vertices chain H G N X reps K C B det pi R U alpha beta hM)

end PPAC.Migration.ConstructionGermLeastBound
