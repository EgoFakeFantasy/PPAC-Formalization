/- Pinned ConcreteQuotients.Cell.descent_gate / Attachment.gateStep /
CellTower.finite_descent. Consume existing gate and finite-path proofs on the
actual set-coded BlockIndex; no ordinal reindexing or external well-foundedness. -/
import PPAC.Migration.ConstructionReordered
import PPAC.Migration.ConstructionFiniteDescent

namespace PPAC.Migration.ConstructionReorderedDescent
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ForcingDiagramPoset (LeftCancelMonoid Conical)
open ConstructionProbeSharedIntersections (ConditionalJoins)
open ConstructionCellRestriction (Cell Attachment Stages)
open ConstructionSelectedCellRestriction (Base)
open ConstructionCellDescent (GateRule OldGateStep)
open ConstructionFirstAppearance (Timeline Cover)
open ConstructionFiniteDescent (Inputs At Result atStage atStage_freeClosed atStage_semantics path_refl path_prepend)
open ConstructionProbePushout (Hom)
open ConstructionProbeConservative (Conservative)
open ConstructionProbeMappedPath (NodeMap)
open ForcingSupportSize (MapsTo)
open ForcingConditionGraphs (function_unique)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

theorem cell_gate (hM : FirstOrder.Theory.Models M nativeZF)
    {w zero D mul e W G unit O : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ z, ¬ (Project.FirstOrderSemantics.reduct M).mem z zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hJ : ConditionalJoins D mul) (hCell : Cell hM w zero D mul e W G unit O)
    (hCons : Conservative D W mul G O) : GateRule D W mul G O := by
  rcases hCell with h | h
  · obtain ⟨a,b,d,node,factor,terminal,target,L,C,projection,I,act,E,K,P,_,_,hA,_⟩ := h
    exact ConstructionCellDescent.probe_gate_rule hM hw hz hzw hA.monoid hA.alphabet
      hA.word hA.b_mem hA.multiplication hA.old_unit hA.old_graph hJ hCons
  · obtain ⟨n,P,C,L,projection,A,T,B,roots,_,_,_,hA⟩ := h
    exact ConstructionCellDescent.merger_gate_rule hM hw hz hzw hA.word
      hA.product_representatives hA.product_map hA.word_action hA.product hA.old_graph

/-- Lift the existing gateStep through the actual attachment isomorphism
and the already proved conservative inclusion into the same terminal monoid. -/
theorem attachment_gate (hM : FirstOrder.Theory.Models M nativeZF)
    {w zero V GV e D T PD PT GD GT idD it : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ z, ¬ (Project.FirstOrderSemantics.reduct M).mem z zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hv : LeftCancelMonoid V GV e)
    (hD : Base V GV e D PD GD idD) (hT : Base V GV e T PT GT it)
    (hAttach : Attachment hM w zero D GD e T GT) : OldGateStep V GV D T := by
  obtain ⟨W,G,unit,O,F,inv,hCell,hmW,hOld,hCons,hF,hInv,hInverse,hFixed,hRange⟩ := hAttach
  obtain ⟨hClosureT,_,_,hGT,hmT,_,hIdT,hIncT,hConsT,_⟩ := hT
  obtain ⟨_,_,_,_,_,_,hIdD,_,_,hJD⟩ := hD
  have hMap : MapsTo W V F := ⟨hF.1.1,fun x y hxy => hClosureT.1 y (hF.1.2 x y hxy)⟩
  have hComp : NodeMap F it F := by
    intro x y
    constructor
    · intro hxy
      exact ⟨y,hxy,(hIdT y y).mpr ⟨hF.1.2 x y hxy,rfl⟩⟩
    · rintro ⟨z,hxz,hzy⟩
      obtain ⟨_,rfl⟩ := (hIdT z y).mp hzy
      exact hxz
  have hFCons := ConstructionIntermediate.conservative_comp hmT hv
    (ConstructionIntermediate.iso_conservative hmW hmT hF hInv hInverse) hConsT hIncT.2.2 hMap hComp
  have hPres : ConstructionProbeLiftHom.PreservesProducts G GV F := by
    intro x y z fx fy fz hp hx hy hzv
    exact ((hGT fx fy fz).mp (hF.2.2 x y z fx fy fz hp hx hy hzv)).2.2
  have hDRange : ForcingSupportedNames.Range D idD D := by
    intro y
    constructor
    · intro hy
      exact ⟨y,hy,(hIdD y y).mpr ⟨hy,rfl⟩⟩
    · rintro ⟨x,hx,hxy⟩
      obtain ⟨_,rfl⟩ := (hIdD x y).mp hxy
      exact hx
  exact ConstructionCellDescent.attachment_gateStep hmW hv hCons.1 hOld.2.2 hFCons hPres
    (ConstructionIntermediate.old_node hOld.1 hMap hFixed hIdD) hDRange hRange
    (cell_gate hM hw hz hzw hJD hCell hCons)

/-- Reuse the finite path constructors and gate descent on the actual
internal set-coded well order. Bad stages are a separated internal set. -/
theorem finite_descent (hM : FirstOrder.Theory.Models M nativeZF)
    {w zero V GV e I R bottom stages base n A a : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ z, ¬ (Project.FirstOrderSemantics.reduct M).mem z zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hv : LeftCancelMonoid V GV e) (hc : Conical V GV e) (hJ : ConditionalJoins V GV)
    (hStages : Stages V GV e stages) (hT : Timeline hM V I R bottom stages)
    (hSteps : ConstructionReordered.Steps hM w zero V GV e I R stages)
    (hBottom : PureKuratowski.PairMember M bottom base stages)
    (hI : Inputs w V GV n A base)
    (ha : (Project.FirstOrderSemantics.reduct M).mem a I) :
    At w zero V GV n A base stages a := by
  classical
  let N := Project.FirstOrderSemantics.reduct M
  let env : SetTheory.Env N 8 := {
    bound := Fin.cases w (Fin.cases zero (Fin.cases V (Fin.cases GV
      (Fin.cases n (Fin.cases A (Fin.cases base (fun _ => stages)))))))
    free := fun _ => zero }
  let schema : Project.UnarySchema 8 := {
    body := atStage 1 2 3 4 5 6 7 8 0
    freeClosed := atStage_freeClosed _ _ _ _ _ _ _ _ _ }
  have he b : schema.denote env b ↔ At w zero V GV n A base stages b :=
    atStage_semantics hM (env.push b) 1 2 3 4 5 6 7 8 0
  obtain ⟨bad,hbad⟩ := ZF.separation_exists_d (ModelTransfer.project_models_iff.mp hM) schema.neg env I
  have hBad b : N.mem b bad ↔ N.mem b I ∧ ¬ At w zero V GV n A base stages b := by
    rw [hbad b]
    apply and_congr_right
    intro _
    change Project.Formula.satisfies (env.push b) (.neg schema.body) ↔ _
    rw [Project.Formula.satisfies_neg_iff]
    exact not_congr (he b)
  apply Classical.byContradiction
  intro hnot
  obtain ⟨j,hj,hmin⟩ := hT.1.least bad (fun k hk => ((hBad k).mp hk).1)
    ⟨a,(hBad a).mpr ⟨ha,hnot⟩⟩
  obtain ⟨hjI,hNotJ⟩ := (hBad j).mp hj
  have hIH : ∀ k, N.mem k I → PureKuratowski.PairMember M k j R →
      At w zero V GV n A base stages k := by
    intro k hk hkj
    apply Classical.byContradiction
    intro hnk
    rcases hmin k ((hBad k).mpr ⟨hk,hnk⟩) with heq | hjk
    · have heq' := (ModelTransfer.extensionality hM).eq_of_same_members j k heq
      subst k
      exact hT.1.linear.2.1.1 j hjI hkj
    · exact hT.1.linear.2.1.1 j hjI (hT.1.linear.2.1.2 j hjI k hk j hjI hjk hkj)
  apply hNotJ
  intro T p i x hjT hp hpx hx
  by_cases heq : j = bottom
  · subst j
    have ht := function_unique hT.2.1 hjT hBottom
    subst T
    exact ⟨p,i,x,hp,hpx,hx,path_refl hM hw hz hzw hp⟩
  by_cases hpred : ∃ k, Cover I R k j
  · obtain ⟨k,hkj⟩ := hpred
    obtain ⟨D,hkD,_⟩ := hT.2.1.2 k hkj.1
    by_cases hxD : N.mem x D
    · exact hIH k hkj.1 hkj.2.2.1 D p i x hkD hp hpx hxD
    obtain ⟨PD,GD,idD,hD⟩ := ConstructionFutureFamily.base_of_closed hM hv hc hJ (hStages k D hkD)
    obtain ⟨PT,GT,it,hBaseT⟩ := ConstructionFutureFamily.base_of_closed hM hv hc hJ (hStages j T hjT)
    rcases hSteps k j D T PD PT GD GT idD it (Or.inr hkj) hkD hjT hD hBaseT with heDT | hAttach
    · exact (hxD (heDT.symm ▸ hx)).elim
    have hBaseD : N.MemberSubset base D := by
      intro y hy
      obtain ⟨D',hkD',hyD⟩ := hT.2.2.2.2.2.1 bottom k y (hT.2.2.2.1 k hkj.1) ⟨base,hBottom,hy⟩
      exact (function_unique hT.2.1 hkD' hkD) ▸ hyD
    have hgate := attachment_gate hM hw hz hzw hv hD hBaseT hAttach
    obtain ⟨Nidx,nN,hNw,hN,hbound⟩ := hI.2.2.1 p i x hp hpx
    obtain ⟨g,hgD,_,hleast,hconsume⟩ := hgate x hx hxD ⟨nN,hBaseD nN (hI.1.2 Nidx nN hN),hbound⟩
    obtain ⟨q,l,y,hqy,hrep,hNy⟩ := hI.2.2.2 p i x Nidx nN hp hpx hNw hN
    obtain ⟨i',l',x',y',ni,nl,d,hpc,hqc,_,_,_,hd,hni,hnl,hnd,hxd⟩ := hrep.2.2
    obtain ⟨hiEq,hxEq⟩ := PureKuratowski.code_injective hpc hpx
    subst i' x'
    obtain ⟨hlEq,hyEq⟩ := PureKuratowski.code_injective hqc hqy
    subst l' y'
    have hdBase := hI.2.1 ni nl d (hI.1.2 i ni hni) (hI.1.2 l nl hnl) hd hnd
    have hgy := ConstructionProbeGates.divides_trans hv (hD.1.1 g hgD)
      (hleast nN (hBaseD nN (hI.1.2 Nidx nN hN)) hbound) hNy
    have hyD := hconsume d y (hBaseD d hdBase) hxd hgy
    obtain ⟨q',l',y',hq',hc',hy',hpath⟩ := hIH k hkj.1 hkj.2.2.1 D q l y hkD hrep.2.1 hqy hyD
    exact ⟨q',l',y',hq',hc',hy',path_prepend hM hw hrep hpath⟩
  · obtain ⟨k,hk,hkj,T',hkT',hxT'⟩ := hT.2.2.2.2.2.2.2 j hjI heq hpred x ⟨T,hjT,hx⟩
    exact hIH k hk hkj T' p i x hkT' hp hpx hxT'

/-- Native ZF proof on every actual internal index. The literal internal
finite path, including nonstandard finite lengths, is retained in the conclusion. -/
def sourceSentence {m : Nat} (w zero V GV e I R bottom stages base n A a : Fin m) : Project.Sentence where
  formula := Project.Formula.forallClosure m (.imp (Project.Formula.isOmega (.bound w)) (.imp (Project.Formula.isEmpty (.bound zero)) (.imp (.mem (.bound zero) (.bound w)) (.imp (ProjectSyntax.encode id (ForcingDiagramPoset.leftCancelMonoid V GV e)) (.imp (ProjectSyntax.encode id (ForcingDiagramPoset.conical V GV e)) (.imp (ConstructionProbeSharedIntersections.conditionalJoins V GV) (.imp (ConstructionCellRestriction.stages V GV e stages) (.imp (ConstructionFirstAppearance.timeline V I R bottom stages) (.imp (ConstructionReordered.stepsFormula w zero V GV e I R stages) (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge stages bottom base)) (.imp (ConstructionFiniteDescent.inputs w V GV n A base) (.imp (.mem (.bound a) (.bound I)) (atStage w zero V GV n A base stages a)))))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
      Project.Formula.isOmega,Project.Formula.isEmpty,atStage_freeClosed,
      ConstructionProbeSharedIntersections.conditionalJoins_freeClosed,ConstructionCellRestriction.stages_freeClosed,
      ConstructionFirstAppearance.timeline_freeClosed,ConstructionReordered.stepsFormula_freeClosed,
      ConstructionFiniteDescent.inputs_freeClosed]

theorem source_models {m : Nat} (w zero V GV e I R bottom stages base n A a : Fin m)
    (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence (sourceSentence w zero V GV e I R bottom stages base n A a)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM)
    (sourceSentence w zero V GV e I R bottom stages base n A a)]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_isOmega_iff,
    Project.Formula.satisfies_isEmpty_iff,Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,
    ForcingDiagramPoset.leftCancelMonoid_semantics (M := M),ForcingDiagramPoset.conical_semantics (M := M),
    ConstructionProbeSharedIntersections.conditionalJoins_semantics hM,ConstructionCellRestriction.stages_semantics hM,
    ConstructionFirstAppearance.timeline_semantics hM,ConstructionReordered.stepsFormula_semantics hM,
    ConstructionFiniteDescent.inputs_semantics hM,atStage_semantics hM]
  exact finite_descent hM

theorem source_kernel_certificate {m : Nat} (w zero V GV e I R bottom stages base n A a : Fin m) :
    FirstOrder.Derives nativeZF [] (Project.fo_sentence (sourceSentence w zero V GV e I R bottom stages base n A a)) :=
  ModelTransfer.derives (fun _ hM => source_models w zero V GV e I R bottom stages base n A a hM)

end PPAC.Migration.ConstructionReorderedDescent
