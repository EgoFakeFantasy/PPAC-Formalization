/- Pinned MonoidRounds.Round.step:93 / fromBase:103.
Pure native-ZF certificate for BOTH actual weighted successor operations,
their same actual fromBase graph and original request realizations. -/
import PPAC.Migration.ConstructionRoundStep

namespace PPAC.Migration.ConstructionRoundStepSyntax
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

def objectFields {m : Nat} (w Q R top D mul e mark H C : Fin m) : Project.Formula 1 m :=
  (.conj (ProjectSyntax.encode id (ForcingDiagramPoset.leftCancelMonoid D mul e)) (.conj (ProjectSyntax.encode
  id (ForcingDiagramPoset.conical D mul e)) (.conj (ConstructionProbeSharedIntersections.conditionalJoins D
  mul) (.conj (.mem (.bound mark) (.bound D)) (.conj (.neg (Project.Formula.extensionalEq (.bound mark)
  (.bound e))) (.conj (ProjectSyntax.encode id (Source.SetLanguage.mapsTo H D R)) (.conj
  (ConstructionCutWeights.rangeBound top H) (.conj (ProjectSyntax.encode id (Source.SetLanguage.mapsTo C D
  R)) (.conj (ConstructionProbeGateCap.bounds top C) (.conj (ConstructionProbeIntervalsSyntax.uniformMargins
  w Q D mul H C) (.conj (ConstructionDirectedHeightCost.exactMargins w Q D mul H C) (.existsE (.conj
  (ConstructionProbeLetters.representatives D.succ D.succ (0 : Fin (m+1))) (ProjectSyntax.encode id
  (Source.SetLanguage.mapsTo mul.succ (0 : Fin (m+1)) D.succ)))))))))))))))

theorem objectFields_freeClosed {m : Nat} (w Q R top D mul e mark H C : Fin m) :
    (objectFields w Q R top D mul e mark H C).FreeClosed := by
  simp -implicitDefEqProofs [objectFields,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,Project.Formula.extensionalEq,ConstructionProbeSharedIntersections.conditionalJoins_freeClosed,ConstructionCutWeights.rangeBound_freeClosed,ConstructionProbeGateCap.bounds_freeClosed,ConstructionProbeIntervalsSyntax.uniformMargins_freeClosed,ConstructionDirectedHeightCost.exactMargins_freeClosed,ConstructionProbeLetters.representatives_freeClosed]

theorem objectFields_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w Q R top D mul e mark H C : Fin m) :
    Project.Formula.satisfies env (objectFields w Q R top D mul e mark H C) ↔ ConstructionRoundFields.ObjectFields hM (env.bound w) (env.bound Q) (env.bound R) (env.bound top) (env.bound D) (env.bound mul) (env.bound e) (env.bound mark) (env.bound H) (env.bound C) := by
  simp only [objectFields,ConstructionRoundFields.ObjectFields,Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_neg_iff,Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),ForcingDiagramPoset.leftCancelMonoid_semantics (M := M),ForcingDiagramPoset.conical_semantics (M := M),ConstructionProbeSharedIntersections.conditionalJoins_semantics hM,Project.Formula.satisfies_extensionalEq_iff_eq (ModelTransfer.extensionality hM),ForcingSupportSize.mapsTo_semantics (M := M),ConstructionCutWeights.rangeBound_semantics hM,ConstructionProbeGateCap.bounds_semantics hM,ConstructionProbeIntervalsSyntax.uniformMargins_semantics hM,ConstructionDirectedHeightCost.exactMargins_semantics hM,ConstructionProbeLetters.representatives_semantics hM]
  rfl


def mapFields {m : Nat} (w Q D N mul mulN e eN mark markN H C HN CN f : Fin m) : Project.Formula 1 m :=
  (.conj (ConstructionProbeConservativeSyntax.conservative D N mul mulN f) (.conj
  (ConstructionProbeLiftHomSyntax.preservesProducts mul mulN f) (.conj (ProjectSyntax.encode id
  (Source.SetLanguage.edge f e eN)) (.conj (ProjectSyntax.encode id (Source.SetLanguage.edge f mark markN))
  (.conj (.forallE (.forallE (.forallE (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge
  f.succ.succ.succ (2 : Fin (m+3)) (1 : Fin (m+3)))) (.iff (ProjectSyntax.encode id (Source.SetLanguage.edge
  HN.succ.succ.succ (1 : Fin (m+3)) (0 : Fin (m+3)))) (ProjectSyntax.encode id (Source.SetLanguage.edge
  H.succ.succ.succ (2 : Fin (m+3)) (0 : Fin (m+3))))))))) (.conj (.forallE (.forallE (.forallE (.imp
  (ProjectSyntax.encode id (Source.SetLanguage.edge f.succ.succ.succ (2 : Fin (m+3)) (1 : Fin (m+3)))) (.iff
  (ProjectSyntax.encode id (Source.SetLanguage.edge CN.succ.succ.succ (1 : Fin (m+3)) (0 : Fin (m+3))))
  (ProjectSyntax.encode id (Source.SetLanguage.edge C.succ.succ.succ (2 : Fin (m+3)) (0 : Fin (m+3)))))))))
  (ConstructionDirectedHeightCost.oldSuprema w Q D N mul mulN C CN f)))))))

theorem mapFields_freeClosed {m : Nat} (w Q D N mul mulN e eN mark markN H C HN CN f : Fin m) :
    (mapFields w Q D N mul mulN e eN mark markN H C HN CN f).FreeClosed := by
  simp -implicitDefEqProofs [mapFields,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,ConstructionProbeConservativeSyntax.conservative_freeClosed,ConstructionProbeLiftHomSyntax.preservesProducts_freeClosed,ConstructionDirectedHeightCost.oldSuprema_freeClosed]

theorem mapFields_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w Q D N mul mulN e eN mark markN H C HN CN f : Fin m) :
    Project.Formula.satisfies env (mapFields w Q D N mul mulN e eN mark markN H C HN CN f) ↔ ConstructionRoundFields.MapFields hM (env.bound w) (env.bound Q) (env.bound D) (env.bound N) (env.bound mul) (env.bound mulN) (env.bound e) (env.bound eN) (env.bound mark) (env.bound markN) (env.bound H) (env.bound C) (env.bound HN) (env.bound CN) (env.bound f) := by
  simp only [mapFields,ConstructionRoundFields.MapFields,Project.Formula.satisfies_forall_iff,
    Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_iff_iff,
    
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,ConstructionProbeConservativeSyntax.conservative_semantics hM,ConstructionProbeLiftHomSyntax.preservesProducts_semantics hM,ConstructionDirectedHeightCost.oldSuprema_semantics hM]
  rfl


def profiles {m : Nat} (w D N mul mulN f : Fin m) : Project.Formula 1 m :=
  (.forallE (.forallE (.forallE (.forallE (.forallE (.imp (ConstructionPersistentProfiles.probeProfile
  w.succ.succ.succ.succ.succ D.succ.succ.succ.succ.succ mul.succ.succ.succ.succ.succ (4 : Fin (m+5)) (3 :
  Fin (m+5)) (2 : Fin (m+5)) (1 : Fin (m+5)) (0 : Fin (m+5))) (.existsE (.existsE (.existsE (.existsE
  (.existsE (.conj (ConstructionProbeMappedPathSyntax.nodeMap (0 : Fin (m+5)).succ.succ.succ.succ.succ
  f.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (4 : Fin (m+10))) (.conj (ProjectSyntax.encode id
  (Source.SetLanguage.edge f.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (4 : Fin
  (m+5)).succ.succ.succ.succ.succ (3 : Fin (m+10)))) (.conj (ProjectSyntax.encode id
  (Source.SetLanguage.edge f.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (3 : Fin
  (m+5)).succ.succ.succ.succ.succ (2 : Fin (m+10)))) (.conj (ProjectSyntax.encode id
  (Source.SetLanguage.edge f.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (2 : Fin
  (m+5)).succ.succ.succ.succ.succ (1 : Fin (m+10)))) (.conj (ProjectSyntax.encode id
  (Source.SetLanguage.edge f.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (1 : Fin
  (m+5)).succ.succ.succ.succ.succ (0 : Fin (m+10)))) (ConstructionPersistentProfiles.probeProfile
  w.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ N.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  mulN.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (3 : Fin (m+10)) (2 : Fin (m+10)) (1 : Fin (m+10))
  (0 : Fin (m+10)) (4 : Fin (m+10)))))))))))))))))))

theorem profiles_freeClosed {m : Nat} (w D N mul mulN f : Fin m) :
    (profiles w D N mul mulN f).FreeClosed := by
  simp -implicitDefEqProofs [profiles,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,ConstructionPersistentProfiles.probeProfile_freeClosed,ConstructionProbeMappedPathSyntax.nodeMap_freeClosed]

theorem profiles_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w D N mul mulN f : Fin m) :
    Project.Formula.satisfies env (profiles w D N mul mulN f) ↔ ConstructionRoundFields.Profiles (env.bound w) (env.bound D) (env.bound N) (env.bound mul) (env.bound mulN) (env.bound f) := by
  simp only [profiles,ConstructionRoundFields.Profiles,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_conj_iff,
    
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,ConstructionPersistentProfiles.probeProfile_semantics hM,ConstructionProbeMappedPathSyntax.nodeMap_semantics hM]
  rfl


def sizeBound {m : Nat} (w D N : Fin m) : Project.Formula 1 m :=
  (.forallE (.imp (Project.Formula.isInfiniteCardinal PureKuratowskiProject.convention (.bound w.succ) (.bound
  (0 : Fin (m+1)))) (.imp (ProjectSyntax.encode id (ForcingSupportSize.small D.succ (0 : Fin (m+1))))
  (ProjectSyntax.encode id (ForcingSupportSize.small N.succ (0 : Fin (m+1)))))))

theorem sizeBound_freeClosed {m : Nat} (w D N : Fin m) :
    (sizeBound w D N).FreeClosed := by
  simp -implicitDefEqProofs [sizeBound,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,Project.Formula.isInfiniteCardinal]

theorem sizeBound_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w D N : Fin m) :
    Project.Formula.satisfies env (sizeBound w D N) ↔ ConstructionRoundFields.SizeBound hM (env.bound w) (env.bound D) (env.bound N) := by
  simp only [sizeBound,ConstructionRoundFields.SizeBound,Project.Formula.satisfies_forall_iff,
    Project.Formula.satisfies_imp_iff,
    Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),Project.Formula.satisfies_isInfiniteCardinal_iff (KuratowskiZF.interpretation hM) (ModelTransfer.extensionality hM),ForcingSupportSize.small_semantics (M := M)]
  rfl


def successor {m : Nat} (w Q R top zero D mul e mark H C N mulN eN markN HN CN O : Fin m) : Project.Formula 1 m :=
  (.conj (objectFields w Q R top N mulN eN markN HN CN) (.conj (mapFields w Q D N mul mulN e eN mark markN H C
  HN CN O) (.conj (ConstructionProbeOldEmbeddingSyntax.oldGraph zero D O) (.conj
  (ConstructionPersistentProfiles.hasOldGates D N mul mulN O) (.conj (profiles w D N mul mulN O) (sizeBound
  w D N))))))

theorem successor_freeClosed {m : Nat} (w Q R top zero D mul e mark H C N mulN eN markN HN CN O : Fin m) :
    (successor w Q R top zero D mul e mark H C N mulN eN markN HN CN O).FreeClosed := by
  simp -implicitDefEqProofs [successor,Definitional.Formula.FreeClosed,objectFields_freeClosed,mapFields_freeClosed,ConstructionProbeOldEmbeddingSyntax.oldGraph_freeClosed,ConstructionPersistentProfiles.hasOldGates_freeClosed,profiles_freeClosed,sizeBound_freeClosed]

theorem successor_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w Q R top zero D mul e mark H C N mulN eN markN HN CN O : Fin m) :
    Project.Formula.satisfies env (successor w Q R top zero D mul e mark H C N mulN eN markN HN CN O) ↔ ConstructionRoundFields.Successor hM (env.bound w) (env.bound Q) (env.bound R) (env.bound top) (env.bound zero) (env.bound D) (env.bound mul) (env.bound e) (env.bound mark) (env.bound H) (env.bound C) (env.bound N) (env.bound mulN) (env.bound eN) (env.bound markN) (env.bound HN) (env.bound CN) (env.bound O) := by
  simp only [successor,ConstructionRoundFields.Successor,
    Project.Formula.satisfies_conj_iff,
    
    objectFields_semantics hM,mapFields_semantics hM,ConstructionProbeOldEmbeddingSyntax.oldGraph_semantics hM,ConstructionPersistentProfiles.hasOldGates_semantics hM,profiles_semantics hM,sizeBound_semantics hM]


def probeDone {m : Nat} (w N mulN markN O a b node : Fin m) : Project.Formula 1 m :=
  (.existsE (.existsE (.existsE (.existsE (.conj (ProjectSyntax.encode id (Source.SetLanguage.edge
  O.succ.succ.succ.succ a.succ.succ.succ.succ (2 : Fin (m+4)))) (.conj (ProjectSyntax.encode id
  (Source.SetLanguage.edge O.succ.succ.succ.succ b.succ.succ.succ.succ (1 : Fin (m+4)))) (.conj
  (ConstructionProbeMappedPathSyntax.nodeMap node.succ.succ.succ.succ O.succ.succ.succ.succ (0 : Fin (m+4)))
  (.conj (ConstructionPersistentProfiles.probeProfile w.succ.succ.succ.succ N.succ.succ.succ.succ
  mulN.succ.succ.succ.succ (2 : Fin (m+4)) (1 : Fin (m+4)) markN.succ.succ.succ.succ (3 : Fin (m+4)) (0 :
  Fin (m+4))) (.forallE (.neg (ProjectSyntax.encode id (Source.SetLanguage.edge O.succ.succ.succ.succ.succ
  (0 : Fin (m+5)) (3 : Fin (m+4)).succ))))))))))))

theorem probeDone_freeClosed {m : Nat} (w N mulN markN O a b node : Fin m) :
    (probeDone w N mulN markN O a b node).FreeClosed := by
  simp -implicitDefEqProofs [probeDone,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,ConstructionProbeMappedPathSyntax.nodeMap_freeClosed,ConstructionPersistentProfiles.probeProfile_freeClosed]

theorem probeDone_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w N mulN markN O a b node : Fin m) :
    Project.Formula.satisfies env (probeDone w N mulN markN O a b node) ↔ ConstructionRoundSuccessors.ProbeDone (env.bound w) (env.bound N) (env.bound mulN) (env.bound markN) (env.bound O) (env.bound a) (env.bound b) (env.bound node) := by
  simp only [probeDone,ConstructionRoundSuccessors.ProbeDone,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_neg_iff,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,ConstructionProbeMappedPathSyntax.nodeMap_semantics hM,ConstructionPersistentProfiles.probeProfile_semantics hM]
  rfl


def mergerDone {m : Nat} (n D N mul mulN P O roots : Fin m) : Project.Formula 1 m :=
  (.conj (ProjectSyntax.encode id (Source.SetLanguage.mapsTo roots n N)) (.conj (.forallE (.forallE (.forallE
  (.forallE (.forallE (.forallE (.forallE (.forallE (.forallE (.forallE (.imp (ProjectSyntax.encode id
  (Source.SetLanguage.edge roots.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (9 : Fin (m+10)) (5 : Fin
  (m+10)))) (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge
  roots.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (8 : Fin (m+10)) (4 : Fin (m+10)))) (.imp
  (ProjectSyntax.encode id (Source.SetLanguage.edge O.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (7 :
  Fin (m+10)) (3 : Fin (m+10)))) (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge
  O.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (6 : Fin (m+10)) (2 : Fin (m+10)))) (.imp
  (ProjectSyntax.encode id (ForcingDiagramOrder.product
  mulN.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (5 : Fin (m+10)) (3 : Fin (m+10)) (1 : Fin
  (m+10)))) (.imp (ProjectSyntax.encode id (ForcingDiagramOrder.product
  mulN.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (4 : Fin (m+10)) (2 : Fin (m+10)) (0 : Fin
  (m+10)))) (.iff (Project.Formula.extensionalEq (.bound (1 : Fin (m+10))) (.bound (0 : Fin (m+10))))
  (ConstructionMergerRelations.rel n.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  D.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ mul.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  P.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (9 : Fin (m+10)) (7 : Fin (m+10)) (8 : Fin (m+10)) (6
  : Fin (m+10)))))))))))))))))))) (.forallE (.forallE (.forallE (.imp (ProjectSyntax.encode id
  (Source.SetLanguage.edge roots.succ.succ.succ (2 : Fin (m+3)) (1 : Fin (m+3)))) (.neg
  (ProjectSyntax.encode id (Source.SetLanguage.edge O.succ.succ.succ (0 : Fin (m+3)) (1 : Fin
  (m+3)))))))))))

theorem mergerDone_freeClosed {m : Nat} (n D N mul mulN P O roots : Fin m) :
    (mergerDone n D N mul mulN P O roots).FreeClosed := by
  simp -implicitDefEqProofs [mergerDone,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,Project.Formula.extensionalEq,ConstructionMergerRelations.rel_freeClosed]

theorem mergerDone_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (n D N mul mulN P O roots : Fin m) :
    Project.Formula.satisfies env (mergerDone n D N mul mulN P O roots) ↔ ConstructionRoundSuccessors.MergerDone (env.bound n) (env.bound D) (env.bound N) (env.bound mul) (env.bound mulN) (env.bound P) (env.bound O) (env.bound roots) := by
  simp only [mergerDone,ConstructionRoundSuccessors.MergerDone,Project.Formula.satisfies_forall_iff,
    Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_iff_iff,
    Project.Formula.satisfies_neg_iff,Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,ForcingSupportSize.mapsTo_semantics (M := M),ForcingDiagramOrder.product_semantics (M := M),Project.Formula.satisfies_extensionalEq_iff_eq (ModelTransfer.extensionality hM),ConstructionMergerRelations.rel_semantics hM]
  rfl


def step {m : Nat} (w Q R top zero D mul e mark H C N mulN eN markN HN CN f W G unitW markW HL LC O baseW : Fin m) : Project.Formula 1 m :=
  (.conj (successor w Q R top zero N mulN eN markN HN CN W G unitW markW HL LC O) (.conj
  (ConstructionProbeMappedPathSyntax.nodeMap f O baseW) (.conj (mapFields w Q D W mul G e unitW mark markW H
  C HL LC baseW) (.imp (profiles w D N mul mulN f) (profiles w D W mul G baseW)))))

theorem step_freeClosed {m : Nat} (w Q R top zero D mul e mark H C N mulN eN markN HN CN f W G unitW markW HL LC O baseW : Fin m) :
    (step w Q R top zero D mul e mark H C N mulN eN markN HN CN f W G unitW markW HL LC O baseW).FreeClosed := by
  simp -implicitDefEqProofs [step,Definitional.Formula.FreeClosed,successor_freeClosed,ConstructionProbeMappedPathSyntax.nodeMap_freeClosed,mapFields_freeClosed,profiles_freeClosed]

theorem step_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w Q R top zero D mul e mark H C N mulN eN markN HN CN f W G unitW markW HL LC O baseW : Fin m) :
    Project.Formula.satisfies env (step w Q R top zero D mul e mark H C N mulN eN markN HN CN f W G unitW markW HL LC O baseW) ↔ ConstructionRoundStep.Step hM (env.bound w) (env.bound Q) (env.bound R) (env.bound top) (env.bound zero) (env.bound D) (env.bound mul) (env.bound e) (env.bound mark) (env.bound H) (env.bound C) (env.bound N) (env.bound mulN) (env.bound eN) (env.bound markN) (env.bound HN) (env.bound CN) (env.bound f) (env.bound W) (env.bound G) (env.bound unitW) (env.bound markW) (env.bound HL) (env.bound LC) (env.bound O) (env.bound baseW) := by
  simp only [step,ConstructionRoundStep.Step,
    Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_conj_iff,
    
    successor_semantics hM,ConstructionProbeMappedPathSyntax.nodeMap_semantics hM,mapFields_semantics hM,profiles_semantics hM]


def steps {m : Nat} (w Q R top zero D mul e mark H C N mulN eN markN HN CN f : Fin m) : Project.Formula 1 m :=
  (.conj (.forallE (.forallE (.forallE (.imp (.mem (.bound (1 : Fin (m+3))) (.bound D.succ.succ.succ)) (.imp
  (.neg (Project.Formula.extensionalEq (.bound (1 : Fin (m+3))) (.bound e.succ.succ.succ))) (.imp
  (ConstructionProbePath.path w.succ.succ.succ D.succ.succ.succ mul.succ.succ.succ e.succ.succ.succ
  zero.succ.succ.succ (2 : Fin (m+3)) (0 : Fin (m+3))) (.existsE (.existsE (.existsE (.existsE (.existsE
  (.existsE (.existsE (.existsE (.conj (step w.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  Q.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  R.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  top.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  zero.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  D.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  mul.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  e.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  mark.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  H.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  C.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  N.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  mulN.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  eN.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  markN.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  HN.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  CN.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  f.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (7 : Fin (m+11)) (6 : Fin (m+11)) (5 : Fin
  (m+11)) (4 : Fin (m+11)) (3 : Fin (m+11)) (2 : Fin (m+11)) (1 : Fin (m+11)) (0 : Fin (m+11))) (probeDone
  w.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (7 : Fin (m+11)) (6 : Fin (m+11)) (4 : Fin
  (m+11)) (0 : Fin (m+11)) (2 : Fin (m+3)).succ.succ.succ.succ.succ.succ.succ.succ (1 : Fin
  (m+3)).succ.succ.succ.succ.succ.succ.succ.succ (0 : Fin
  (m+3)).succ.succ.succ.succ.succ.succ.succ.succ)))))))))))))))) (.forallE (.forallE (.imp (.mem (.bound (1
  : Fin (m+2))) (.bound w.succ.succ)) (.imp (.existsE (.mem (.bound (0 : Fin (m+3))) (.bound (1 : Fin
  (m+2)).succ))) (.imp (ConstructionMergerRelations.prescription (1 : Fin (m+2)) D.succ.succ (0 : Fin
  (m+2))) (.imp (ConstructionMergerRelations.valid (1 : Fin (m+2)) D.succ.succ mul.succ.succ (0 : Fin
  (m+2))) (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.conj
  (step w.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  Q.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  R.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  top.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  zero.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  D.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  mul.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  e.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  mark.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  H.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  C.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  N.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  mulN.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  eN.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  markN.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  HN.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  CN.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  f.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (8 : Fin (m+11)) (7 : Fin (m+11)) (6 : Fin
  (m+11)) (5 : Fin (m+11)) (4 : Fin (m+11)) (3 : Fin (m+11)) (2 : Fin (m+11)) (1 : Fin (m+11))) (mergerDone
  (1 : Fin (m+2)).succ.succ.succ.succ.succ.succ.succ.succ.succ
  D.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (8 : Fin (m+11))
  mul.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (7 : Fin (m+11)) (0 : Fin
  (m+2)).succ.succ.succ.succ.succ.succ.succ.succ.succ (1 : Fin (m+11)) (0 : Fin (m+11))))))))))))))))))))

theorem steps_freeClosed {m : Nat} (w Q R top zero D mul e mark H C N mulN eN markN HN CN f : Fin m) :
    (steps w Q R top zero D mul e mark H C N mulN eN markN HN CN f).FreeClosed := by
  simp -implicitDefEqProofs [steps,Definitional.Formula.FreeClosed,Project.Formula.extensionalEq,ConstructionProbePath.path_freeClosed,step_freeClosed,probeDone_freeClosed,ConstructionMergerRelations.prescription_freeClosed,ConstructionMergerRelations.valid_freeClosed,mergerDone_freeClosed]

theorem steps_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w Q R top zero D mul e mark H C N mulN eN markN HN CN f : Fin m) :
    Project.Formula.satisfies env (steps w Q R top zero D mul e mark H C N mulN eN markN HN CN f) ↔ ConstructionRoundStep.Steps hM (env.bound w) (env.bound Q) (env.bound R) (env.bound top) (env.bound zero) (env.bound D) (env.bound mul) (env.bound e) (env.bound mark) (env.bound H) (env.bound C) (env.bound N) (env.bound mulN) (env.bound eN) (env.bound markN) (env.bound HN) (env.bound CN) (env.bound f) := by
  simp only [steps,ConstructionRoundStep.Steps,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_neg_iff,Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    Project.Formula.satisfies_extensionalEq_iff_eq (ModelTransfer.extensionality hM),ConstructionProbePath.path_semantics hM,step_semantics hM,probeDone_semantics hM,ConstructionMergerRelations.prescription_semantics hM,ConstructionMergerRelations.valid_semantics hM,mergerDone_semantics hM]
  rfl


def stepSentence : Project.Sentence where
  formula := (Project.Formula.forallClosure 20 (.imp (Project.Formula.isOmega (.bound (0 : Fin 20))) (.imp
    (Project.Formula.isEmpty (.bound (4 : Fin 20))) (.imp (.mem (.bound (4 : Fin 20)) (.bound (0 : Fin 20)))
    (.imp (ConstructionFractionOrder.carrier (0 : Fin 20) (1 : Fin 20)) (.imp (ConstructionRealCuts.cutCarrier
    (0 : Fin 20) (1 : Fin 20) (2 : Fin 20)) (.imp (ConstructionFractionOrder.coordinates (0 : Fin 20) (6 : Fin
    20) (5 : Fin 20) (5 : Fin 20)) (.imp (Project.Formula.isOrdinalOne (.bound (5 : Fin 20))) (.imp
    (ConstructionRealCuts.principal (0 : Fin 20) (1 : Fin 20) (6 : Fin 20) (3 : Fin 20)) (.imp (objectFields
    (0 : Fin 20) (1 : Fin 20) (2 : Fin 20) (3 : Fin 20) (7 : Fin 20) (8 : Fin 20) (9 : Fin 20) (10 : Fin 20)
    (11 : Fin 20) (12 : Fin 20)) (.imp (objectFields (0 : Fin 20) (1 : Fin 20) (2 : Fin 20) (3 : Fin 20) (13 :
    Fin 20) (14 : Fin 20) (15 : Fin 20) (16 : Fin 20) (17 : Fin 20) (18 : Fin 20)) (.imp (mapFields (0 : Fin
    20) (1 : Fin 20) (7 : Fin 20) (13 : Fin 20) (8 : Fin 20) (14 : Fin 20) (9 : Fin 20) (15 : Fin 20) (10 :
    Fin 20) (16 : Fin 20) (11 : Fin 20) (12 : Fin 20) (17 : Fin 20) (18 : Fin 20) (19 : Fin 20)) (steps (0 :
    Fin 20) (1 : Fin 20) (2 : Fin 20) (3 : Fin 20) (4 : Fin 20) (7 : Fin 20) (8 : Fin 20) (9 : Fin 20) (10 :
    Fin 20) (11 : Fin 20) (12 : Fin 20) (13 : Fin 20) (14 : Fin 20) (15 : Fin 20) (16 : Fin 20) (17 : Fin 20)
    (18 : Fin 20) (19 : Fin 20))))))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,
      Project.Formula.isOmega,Project.Formula.isEmpty,Project.Formula.isOrdinalOne,
      ConstructionFractionOrder.carrier_freeClosed,ConstructionRealCuts.cutCarrier_freeClosed,
      ConstructionFractionOrder.coordinates_freeClosed,ConstructionRealCuts.principal_freeClosed,
      objectFields_freeClosed,mapFields_freeClosed,steps_freeClosed]

theorem step_models (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence stepSentence).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) stepSentence]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_isOmega_iff,
    Project.Formula.satisfies_isEmpty_iff,Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    ConstructionFractionOrder.carrier_semantics hM,ConstructionRealCuts.cutCarrier_semantics hM,
    ConstructionFractionOrder.coordinates_semantics hM,Project.Formula.satisfies_isOrdinalOne_iff,
    ConstructionRealCuts.principal_semantics hM,objectFields_semantics hM,mapFields_semantics hM,steps_semantics hM]
  exact fun hw hz hzw hQ hR hu hone htop hObjD hObjN hf =>
    ConstructionRoundStep.steps hM hw hz hzw hQ hR hu hone htop hObjD hObjN hf

theorem step_kernel_certificate : FirstOrder.Derives nativeZF []
    (Project.fo_sentence stepSentence) := ModelTransfer.derives (fun _ hM => step_models hM)

end PPAC.Migration.ConstructionRoundStepSyntax
