/- Pinned MonoidTowers.DirectedColimit.lift/isColimit:147-168.
Pure object sentences quantify all internal cocones and actual lift graphs.
The final object Con sentence and tower/request schedule remain separate. -/
import PPAC.Migration.ConstructionDirectedLift
import PPAC.Migration.ConstructionDirectedObjectSyntax

namespace PPAC.Migration.ConstructionDirectedLiftSyntax
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ConstructionDirectedLift
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

def fac {m : Nat} (J Domains K projection lift : Fin m) : Project.Formula 1 m :=
  (.forallE (.forallE (.forallE (.forallE (.forallE (.forallE (.imp (.mem (.bound (5 : Fin (m+6))) (.bound
  J.succ.succ.succ.succ.succ.succ)) (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge
  Domains.succ.succ.succ.succ.succ.succ (5 : Fin (m+6)) (4 : Fin (m+6)))) (.imp (ProjectSyntax.encode id
  (Source.SetLanguage.edge K.succ.succ.succ.succ.succ.succ (5 : Fin (m+6)) (3 : Fin (m+6)))) (.imp (.mem
  (.bound (2 : Fin (m+6))) (.bound (4 : Fin (m+6)))) (.imp (ProjectSyntax.encode id
  (ForcingDiagramOrder.product projection.succ.succ.succ.succ.succ.succ (5 : Fin (m+6)) (2 : Fin (m+6)) (1 :
  Fin (m+6)))) (.iff (ProjectSyntax.encode id (Source.SetLanguage.edge lift.succ.succ.succ.succ.succ.succ (1
  : Fin (m+6)) (0 : Fin (m+6)))) (ProjectSyntax.encode id (Source.SetLanguage.edge (3 : Fin (m+6)) (2 : Fin
  (m+6)) (0 : Fin (m+6))))))))))))))))

theorem fac_freeClosed {m : Nat} (J Domains K projection lift : Fin m) :
    (fac J Domains K projection lift).FreeClosed := by
  simp -implicitDefEqProofs [fac,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed]

theorem fac_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (J Domains K projection lift : Fin m) :
    Project.Formula.satisfies env (fac J Domains K projection lift) ↔ Fac (env.bound J) (env.bound Domains) (env.bound K) (env.bound projection) (env.bound lift) := by
  simp only [fac,Fac,Project.Formula.satisfies_forall_iff,
    Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_iff_iff,
    Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,ForcingDiagramOrder.product_semantics (M := M)]
  rfl


def legs {m : Nat} (J Domains Muls Units K N GN uN : Fin m) : Project.Formula 1 m :=
  (.forallE (.forallE (.forallE (.forallE (.forallE (.imp (.mem (.bound (4 : Fin (m+5))) (.bound
  J.succ.succ.succ.succ.succ)) (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge
  Domains.succ.succ.succ.succ.succ (4 : Fin (m+5)) (3 : Fin (m+5)))) (.imp (ProjectSyntax.encode id
  (Source.SetLanguage.edge Muls.succ.succ.succ.succ.succ (4 : Fin (m+5)) (2 : Fin (m+5)))) (.imp
  (ProjectSyntax.encode id (Source.SetLanguage.edge Units.succ.succ.succ.succ.succ (4 : Fin (m+5)) (1 : Fin
  (m+5)))) (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge K.succ.succ.succ.succ.succ (4 : Fin
  (m+5)) (0 : Fin (m+5)))) (.conj (ConstructionProbeLiftHomSyntax.preservesProducts (2 : Fin (m+5))
  GN.succ.succ.succ.succ.succ (0 : Fin (m+5))) (.conj (ProjectSyntax.encode id (Source.SetLanguage.edge (0 :
  Fin (m+5)) (1 : Fin (m+5)) uN.succ.succ.succ.succ.succ)) (ConstructionProbeConservativeSyntax.conservative
  (3 : Fin (m+5)) N.succ.succ.succ.succ.succ (2 : Fin (m+5)) GN.succ.succ.succ.succ.succ (0 : Fin
  (m+5)))))))))))))))

theorem legs_freeClosed {m : Nat} (J Domains Muls Units K N GN uN : Fin m) :
    (legs J Domains Muls Units K N GN uN).FreeClosed := by
  simp -implicitDefEqProofs [legs,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,ConstructionProbeLiftHomSyntax.preservesProducts_freeClosed,ConstructionProbeConservativeSyntax.conservative_freeClosed]

theorem legs_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (J Domains Muls Units K N GN uN : Fin m) :
    Project.Formula.satisfies env (legs J Domains Muls Units K N GN uN) ↔ Legs (env.bound J) (env.bound Domains) (env.bound Muls) (env.bound Units) (env.bound K) (env.bound N) (env.bound GN) (env.bound uN) := by
  simp only [legs,Legs,Project.Formula.satisfies_forall_iff,
    Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,ConstructionProbeLiftHomSyntax.preservesProducts_semantics hM,ConstructionProbeConservativeSyntax.conservative_semantics hM]
  rfl


def weightedLegs {m : Nat} (J Domains Muls Heights Costs K HN CN N GN : Fin m) : Project.Formula 1 m :=
  (.forallE (.forallE (.forallE (.forallE (.forallE (.forallE (.imp (.mem (.bound (5 : Fin (m+6))) (.bound
  J.succ.succ.succ.succ.succ.succ)) (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge
  Domains.succ.succ.succ.succ.succ.succ (5 : Fin (m+6)) (4 : Fin (m+6)))) (.imp (ProjectSyntax.encode id
  (Source.SetLanguage.edge Muls.succ.succ.succ.succ.succ.succ (5 : Fin (m+6)) (3 : Fin (m+6)))) (.imp
  (ProjectSyntax.encode id (Source.SetLanguage.edge Heights.succ.succ.succ.succ.succ.succ (5 : Fin (m+6)) (2
  : Fin (m+6)))) (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge Costs.succ.succ.succ.succ.succ.succ
  (5 : Fin (m+6)) (1 : Fin (m+6)))) (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge
  K.succ.succ.succ.succ.succ.succ (5 : Fin (m+6)) (0 : Fin (m+6)))) (.conj (.forallE (.forallE (.forallE
  (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge (0 : Fin (m+6)).succ.succ.succ (2 : Fin (m+9)) (1
  : Fin (m+9)))) (.iff (ProjectSyntax.encode id (Source.SetLanguage.edge (2 : Fin (m+6)).succ.succ.succ (2 :
  Fin (m+9)) (0 : Fin (m+9)))) (ProjectSyntax.encode id (Source.SetLanguage.edge
  HN.succ.succ.succ.succ.succ.succ.succ.succ.succ (1 : Fin (m+9)) (0 : Fin (m+9))))))))) (.conj (.forallE
  (.forallE (.forallE (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge (0 : Fin (m+6)).succ.succ.succ
  (2 : Fin (m+9)) (1 : Fin (m+9)))) (.iff (ProjectSyntax.encode id (Source.SetLanguage.edge (1 : Fin
  (m+6)).succ.succ.succ (2 : Fin (m+9)) (0 : Fin (m+9)))) (ProjectSyntax.encode id (Source.SetLanguage.edge
  CN.succ.succ.succ.succ.succ.succ.succ.succ.succ (1 : Fin (m+9)) (0 : Fin (m+9))))))))) (.forallE (.forallE
  (.forallE (.forallE (.forallE (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge (0 : Fin
  (m+6)).succ.succ.succ.succ.succ (4 : Fin (m+11)) (2 : Fin (m+11)))) (.imp (ProjectSyntax.encode id
  (Source.SetLanguage.edge (0 : Fin (m+6)).succ.succ.succ.succ.succ (3 : Fin (m+11)) (1 : Fin (m+11))))
  (.imp (ConstructionProbeCostSupremum.cap (4 : Fin (m+6)).succ.succ.succ.succ.succ (3 : Fin
  (m+6)).succ.succ.succ.succ.succ (1 : Fin (m+6)).succ.succ.succ.succ.succ (4 : Fin (m+11)) (3 : Fin (m+11))
  (0 : Fin (m+11))) (ConstructionProbeCostSupremum.cap
  N.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  GN.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  CN.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (2 : Fin (m+11)) (1 : Fin (m+11)) (0 : Fin
  (m+11)))))))))))))))))))))))))

theorem weightedLegs_freeClosed {m : Nat} (J Domains Muls Heights Costs K HN CN N GN : Fin m) :
    (weightedLegs J Domains Muls Heights Costs K HN CN N GN).FreeClosed := by
  simp -implicitDefEqProofs [weightedLegs,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,ConstructionProbeCostSupremum.cap_freeClosed]

theorem weightedLegs_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (J Domains Muls Heights Costs K HN CN N GN : Fin m) :
    Project.Formula.satisfies env (weightedLegs J Domains Muls Heights Costs K HN CN N GN) ↔ WeightedLegs (env.bound J) (env.bound Domains) (env.bound Muls) (env.bound Heights) (env.bound Costs) (env.bound K) (env.bound HN) (env.bound CN) (env.bound N) (env.bound GN) := by
  simp only [weightedLegs,WeightedLegs,Project.Formula.satisfies_forall_iff,
    Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_iff_iff,
    Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,ConstructionProbeCostSupremum.cap_semantics hM]
  rfl


def markLegs {m : Nat} (J Marks K mN : Fin m) : Project.Formula 1 m :=
  (.forallE (.forallE (.forallE (.imp (.mem (.bound (2 : Fin (m+3))) (.bound J.succ.succ.succ)) (.imp
  (ProjectSyntax.encode id (Source.SetLanguage.edge Marks.succ.succ.succ (2 : Fin (m+3)) (1 : Fin (m+3))))
  (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge K.succ.succ.succ (2 : Fin (m+3)) (0 : Fin (m+3))))
  (ProjectSyntax.encode id (Source.SetLanguage.edge (0 : Fin (m+3)) (1 : Fin (m+3))
  mN.succ.succ.succ))))))))

theorem markLegs_freeClosed {m : Nat} (J Marks K mN : Fin m) :
    (markLegs J Marks K mN).FreeClosed := by
  simp -implicitDefEqProofs [markLegs,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed]

theorem markLegs_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (J Marks K mN : Fin m) :
    Project.Formula.satisfies env (markLegs J Marks K mN) ↔ MarkLegs (env.bound J) (env.bound Marks) (env.bound K) (env.bound mN) := by
  simp only [markLegs,MarkLegs,Project.Formula.satisfies_forall_iff,
    Project.Formula.satisfies_imp_iff,
    Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge]
  rfl


def liftLaws {m : Nat} (J Domains K projection L N G GN unit uN mark mN HL LC HN CN lift : Fin m) : Project.Formula 1 m :=
  (.conj (ProjectSyntax.encode id (Source.SetLanguage.mapsTo lift L N)) (.conj
  (ConstructionDirectedWeights.graph J Domains K projection lift) (.conj (fac J Domains K projection lift)
  (.conj (ConstructionProbeLiftHomSyntax.preservesProducts G GN lift) (.conj (ProjectSyntax.encode id
  (Source.SetLanguage.edge lift unit uN)) (.conj (ConstructionProbeConservativeSyntax.conservative L N G GN
  lift) (.conj (ProjectSyntax.encode id (Source.SetLanguage.edge lift mark mN)) (.conj (.forallE (.forallE
  (.forallE (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge lift.succ.succ.succ (2 : Fin (m+3)) (1 :
  Fin (m+3)))) (.iff (ProjectSyntax.encode id (Source.SetLanguage.edge HL.succ.succ.succ (2 : Fin (m+3)) (0
  : Fin (m+3)))) (ProjectSyntax.encode id (Source.SetLanguage.edge HN.succ.succ.succ (1 : Fin (m+3)) (0 :
  Fin (m+3))))))))) (.conj (.forallE (.forallE (.forallE (.imp (ProjectSyntax.encode id
  (Source.SetLanguage.edge lift.succ.succ.succ (2 : Fin (m+3)) (1 : Fin (m+3)))) (.iff (ProjectSyntax.encode
  id (Source.SetLanguage.edge LC.succ.succ.succ (2 : Fin (m+3)) (0 : Fin (m+3)))) (ProjectSyntax.encode id
  (Source.SetLanguage.edge CN.succ.succ.succ (1 : Fin (m+3)) (0 : Fin (m+3))))))))) (.conj (.forallE
  (.forallE (.forallE (.forallE (.forallE (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge
  lift.succ.succ.succ.succ.succ (4 : Fin (m+5)) (2 : Fin (m+5)))) (.imp (ProjectSyntax.encode id
  (Source.SetLanguage.edge lift.succ.succ.succ.succ.succ (3 : Fin (m+5)) (1 : Fin (m+5)))) (.imp
  (ConstructionProbeCostSupremum.cap L.succ.succ.succ.succ.succ G.succ.succ.succ.succ.succ
  LC.succ.succ.succ.succ.succ (4 : Fin (m+5)) (3 : Fin (m+5)) (0 : Fin (m+5)))
  (ConstructionProbeCostSupremum.cap N.succ.succ.succ.succ.succ GN.succ.succ.succ.succ.succ
  CN.succ.succ.succ.succ.succ (2 : Fin (m+5)) (1 : Fin (m+5)) (0 : Fin (m+5))))))))))) (.forallE (.imp
  (ProjectSyntax.encode id (Source.SetLanguage.mapsTo (0 : Fin (m+1)) L.succ N.succ)) (.imp (fac J.succ
  Domains.succ K.succ projection.succ (0 : Fin (m+1))) (Project.Formula.extensionalEq (.bound (0 : Fin
  (m+1))) (.bound lift.succ)))))))))))))))

theorem liftLaws_freeClosed {m : Nat} (J Domains K projection L N G GN unit uN mark mN HL LC HN CN lift : Fin m) :
    (liftLaws J Domains K projection L N G GN unit uN mark mN HL LC HN CN lift).FreeClosed := by
  simp -implicitDefEqProofs [liftLaws,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,ConstructionDirectedWeights.graph_freeClosed,fac_freeClosed,ConstructionProbeLiftHomSyntax.preservesProducts_freeClosed,ConstructionProbeConservativeSyntax.conservative_freeClosed,ConstructionProbeCostSupremum.cap_freeClosed,Project.Formula.extensionalEq]

theorem liftLaws_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (J Domains K projection L N G GN unit uN mark mN HL LC HN CN lift : Fin m) :
    Project.Formula.satisfies env (liftLaws J Domains K projection L N G GN unit uN mark mN HL LC HN CN lift) ↔ LiftLaws (env.bound J) (env.bound Domains) (env.bound K) (env.bound projection) (env.bound L) (env.bound N) (env.bound G) (env.bound GN) (env.bound unit) (env.bound uN) (env.bound mark) (env.bound mN) (env.bound HL) (env.bound LC) (env.bound HN) (env.bound CN) (env.bound lift) := by
  simp only [liftLaws,LiftLaws,Project.Formula.satisfies_forall_iff,
    Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_iff_iff,
    Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,ForcingSupportSize.mapsTo_semantics (M := M),ConstructionDirectedWeights.graph_semantics hM,fac_semantics hM,ConstructionProbeLiftHomSyntax.preservesProducts_semantics hM,ConstructionProbeConservativeSyntax.conservative_semantics hM,ConstructionProbeCostSupremum.cap_semantics hM,Project.Formula.satisfies_extensionalEq_iff_eq (ModelTransfer.extensionality hM)]
  rfl


def universalProperty {m : Nat} (J E Domains F Muls Units Heights Costs Marks L projection G unit mark HL LC : Fin m) : Project.Formula 1 m :=
  (.forallE (.forallE (.forallE (.forallE (.forallE (.forallE (.forallE (.imp
  (ConstructionDirectedWeightData.weightFamily J.succ.succ.succ.succ.succ.succ.succ
  Domains.succ.succ.succ.succ.succ.succ.succ (5 : Fin (m+7)) (6 : Fin (m+7))) (.imp
  (ConstructionDirectedWeightData.stable J.succ.succ.succ.succ.succ.succ.succ
  E.succ.succ.succ.succ.succ.succ.succ Domains.succ.succ.succ.succ.succ.succ.succ
  F.succ.succ.succ.succ.succ.succ.succ (6 : Fin (m+7))) (.imp (legs J.succ.succ.succ.succ.succ.succ.succ
  Domains.succ.succ.succ.succ.succ.succ.succ Muls.succ.succ.succ.succ.succ.succ.succ
  Units.succ.succ.succ.succ.succ.succ.succ (6 : Fin (m+7)) (5 : Fin (m+7)) (4 : Fin (m+7)) (3 : Fin (m+7)))
  (.imp (weightedLegs J.succ.succ.succ.succ.succ.succ.succ Domains.succ.succ.succ.succ.succ.succ.succ
  Muls.succ.succ.succ.succ.succ.succ.succ Heights.succ.succ.succ.succ.succ.succ.succ
  Costs.succ.succ.succ.succ.succ.succ.succ (6 : Fin (m+7)) (1 : Fin (m+7)) (0 : Fin (m+7)) (5 : Fin (m+7))
  (4 : Fin (m+7))) (.imp (markLegs J.succ.succ.succ.succ.succ.succ.succ
  Marks.succ.succ.succ.succ.succ.succ.succ (6 : Fin (m+7)) (2 : Fin (m+7))) (.existsE (liftLaws
  J.succ.succ.succ.succ.succ.succ.succ.succ Domains.succ.succ.succ.succ.succ.succ.succ.succ (6 : Fin
  (m+7)).succ projection.succ.succ.succ.succ.succ.succ.succ.succ L.succ.succ.succ.succ.succ.succ.succ.succ
  (5 : Fin (m+7)).succ G.succ.succ.succ.succ.succ.succ.succ.succ (4 : Fin (m+7)).succ
  unit.succ.succ.succ.succ.succ.succ.succ.succ (3 : Fin (m+7)).succ
  mark.succ.succ.succ.succ.succ.succ.succ.succ (2 : Fin (m+7)).succ
  HL.succ.succ.succ.succ.succ.succ.succ.succ LC.succ.succ.succ.succ.succ.succ.succ.succ (1 : Fin (m+7)).succ
  (0 : Fin (m+7)).succ (0 : Fin (m+8))))))))))))))))

theorem universalProperty_freeClosed {m : Nat} (J E Domains F Muls Units Heights Costs Marks L projection G unit mark HL LC : Fin m) :
    (universalProperty J E Domains F Muls Units Heights Costs Marks L projection G unit mark HL LC).FreeClosed := by
  simp -implicitDefEqProofs [universalProperty,Definitional.Formula.FreeClosed,ConstructionDirectedWeightData.weightFamily_freeClosed,ConstructionDirectedWeightData.stable_freeClosed,legs_freeClosed,weightedLegs_freeClosed,markLegs_freeClosed,liftLaws_freeClosed]

theorem universalProperty_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (J E Domains F Muls Units Heights Costs Marks L projection G unit mark HL LC : Fin m) :
    Project.Formula.satisfies env (universalProperty J E Domains F Muls Units Heights Costs Marks L projection G unit mark HL LC) ↔ Universal (env.bound J) (env.bound E) (env.bound Domains) (env.bound F) (env.bound Muls) (env.bound Units) (env.bound Heights) (env.bound Costs) (env.bound Marks) (env.bound L) (env.bound projection) (env.bound G) (env.bound unit) (env.bound mark) (env.bound HL) (env.bound LC) := by
  simp only [universalProperty,Universal,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_imp_iff,
    
    ConstructionDirectedWeightData.weightFamily_semantics hM,ConstructionDirectedWeightData.stable_semantics hM,legs_semantics hM,weightedLegs_semantics hM,markLegs_semantics hM,liftLaws_semantics hM]
  rfl


def universalSentence : Project.Sentence where
  formula := (Project.Formula.forallClosure 22 (.imp (.existsE (.mem (.bound (0 : Fin 23)) (.bound (4 : Fin 22).succ)))
    (.imp (ConstructionDirectedMonoidData.family (4 : Fin 22) (6 : Fin 22) (8 : Fin 22) (9 : Fin 22)) (.imp
    (ConstructionDirectedSystem.indexLaws (4 : Fin 22) (5 : Fin 22)) (.imp
    (ConstructionDirectedSystem.transitionLaws (4 : Fin 22) (5 : Fin 22) (6 : Fin 22) (7 : Fin 22)) (.imp
    (ConstructionDirectedConservativeData.conservativeTransitions (4 : Fin 22) (5 : Fin 22) (6 : Fin 22) (7 :
    Fin 22) (8 : Fin 22)) (.imp (ConstructionDirectedLimitCarrier.representatives (4 : Fin 22) (6 : Fin 22)
    (13 : Fin 22)) (.imp (ProjectSyntax.encode id (Source.SetLanguage.mapsTo (15 : Fin 22) (13 : Fin 22) (14 :
    Fin 22))) (.imp (ConstructionDirectedLimitCarrier.carrier (4 : Fin 22) (5 : Fin 22) (6 : Fin 22) (7 : Fin
    22) (13 : Fin 22) (14 : Fin 22)) (.imp (ConstructionDirectedLimitCarrier.projectionGraph (4 : Fin 22) (5 :
    Fin 22) (6 : Fin 22) (7 : Fin 22) (13 : Fin 22) (15 : Fin 22)) (.imp
    (ConstructionDirectedLimitCarrier.equalityLaw (4 : Fin 22) (5 : Fin 22) (6 : Fin 22) (7 : Fin 22) (15 :
    Fin 22)) (.imp (ProjectSyntax.encode id (Source.SetLanguage.mapsTo (17 : Fin 22) (16 : Fin 22) (14 : Fin
    22))) (.imp (ConstructionDirectedProduct.graph (4 : Fin 22) (6 : Fin 22) (8 : Fin 22) (15 : Fin 22) (17 :
    Fin 22)) (.imp (ProjectSyntax.encode id (ForcingDiagramPoset.leftCancelMonoid (14 : Fin 22) (17 : Fin 22)
    (18 : Fin 22))) (.imp (ConstructionDirectedMonoid.unitImage (4 : Fin 22) (6 : Fin 22) (9 : Fin 22) (15 :
    Fin 22) (18 : Fin 22)) (.imp (ConstructionDirectedMarks.markFamily (4 : Fin 22) (6 : Fin 22) (9 : Fin 22)
    (12 : Fin 22)) (.imp (ConstructionDirectedMarks.markImage (4 : Fin 22) (12 : Fin 22) (15 : Fin 22) (19 :
    Fin 22)) (.imp (ConstructionDirectedWeightData.weightFamily (4 : Fin 22) (6 : Fin 22) (2 : Fin 22) (10 :
    Fin 22)) (.imp (ConstructionDirectedWeightData.weightFamily (4 : Fin 22) (6 : Fin 22) (2 : Fin 22) (11 :
    Fin 22)) (.imp (ConstructionDirectedHeightCost.laws (0 : Fin 22) (1 : Fin 22) (2 : Fin 22) (3 : Fin 22) (4
    : Fin 22) (6 : Fin 22) (8 : Fin 22) (10 : Fin 22) (11 : Fin 22) (14 : Fin 22) (15 : Fin 22) (17 : Fin 22)
    (20 : Fin 22) (21 : Fin 22)) (universalProperty (4 : Fin 22) (5 : Fin 22) (6 : Fin 22) (7 : Fin 22) (8 :
    Fin 22) (9 : Fin 22) (10 : Fin 22) (11 : Fin 22) (12 : Fin 22) (14 : Fin 22) (15 : Fin 22) (17 : Fin 22)
    (18 : Fin 22) (19 : Fin 22) (20 : Fin 22) (21 : Fin 22))))))))))))))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,ConstructionDirectedMonoidData.family_freeClosed,ConstructionDirectedSystem.indexLaws_freeClosed,ConstructionDirectedSystem.transitionLaws_freeClosed,ConstructionDirectedConservativeData.conservativeTransitions_freeClosed,ConstructionDirectedLimitCarrier.representatives_freeClosed,ConstructionDirectedLimitCarrier.carrier_freeClosed,ConstructionDirectedLimitCarrier.projectionGraph_freeClosed,ConstructionDirectedLimitCarrier.equalityLaw_freeClosed,ConstructionDirectedProduct.graph_freeClosed,ConstructionDirectedMonoid.unitImage_freeClosed,ConstructionDirectedMarks.markFamily_freeClosed,ConstructionDirectedMarks.markImage_freeClosed,ConstructionDirectedWeightData.weightFamily_freeClosed,ConstructionDirectedHeightCost.laws_freeClosed,universalProperty_freeClosed]

theorem universal_models (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence universalSentence).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) universalSentence]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingSupportSize.mapsTo_semantics (M := M),ForcingDiagramPoset.leftCancelMonoid_semantics (M := M),
    ConstructionDirectedMonoidData.family_semantics hM,ConstructionDirectedSystem.indexLaws_semantics hM,ConstructionDirectedSystem.transitionLaws_semantics hM,ConstructionDirectedConservativeData.conservativeTransitions_semantics hM,ConstructionDirectedLimitCarrier.representatives_semantics hM,ConstructionDirectedLimitCarrier.carrier_semantics hM,ConstructionDirectedLimitCarrier.projectionGraph_semantics hM,ConstructionDirectedLimitCarrier.equalityLaw_semantics hM,ConstructionDirectedProduct.graph_semantics hM,ConstructionDirectedMonoid.unitImage_semantics hM,ConstructionDirectedMarks.markFamily_semantics hM,ConstructionDirectedMarks.markImage_semantics hM,ConstructionDirectedWeightData.weightFamily_semantics hM,ConstructionDirectedHeightCost.laws_semantics hM,universalProperty_semantics hM]
  intro hne hFam hE hT hCons hC hp hL hP hEq hG hGraph hMon hImage hMarks hMarkImage hWH hWC hWeights
  exact ConstructionDirectedLift.universal hM hne hFam hE hT hCons hC hp hL hP hEq hG hGraph hMon hImage hMarks hMarkImage hWH hWC hWeights

theorem universal_kernel_certificate : FirstOrder.Derives nativeZF []
    (Project.fo_sentence universalSentence) := ModelTransfer.derives (fun _ hM => universal_models hM)

end PPAC.Migration.ConstructionDirectedLiftSyntax
