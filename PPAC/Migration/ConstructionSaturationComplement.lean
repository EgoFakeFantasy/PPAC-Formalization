/- Pinned SaturatedMonoids.Saturation.complement_probes:180.
Consume the SAME final Probe family at a=unit, b=mark, using the existing
internal constant path. No new recursion or choice backend. -/
import PPAC.Migration.ConstructionSaturationMergers

namespace PPAC.Migration.ConstructionSaturationComplement
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ConstructionTowerHistory (Row)
open ForcingSupportSize (Injection)
open ForcingDiagramPoset (LeftCancelMonoid Conical)
open ConstructionBaseMonoid (Divides)
open ForcingDiagramOrder (Product)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

def Complement (K N mul mark : M.Carrier .set) : Prop :=
  ∃ Family, Injection K N Family ∧
    ∀ k p, PureKuratowski.PairMember M k p Family → ¬ Divides N mul mark p

theorem complement_probes (hM : FirstOrder.Theory.Models M nativeZF)
    {w K N mul e mark zero : M.Carrier .set}
    (hm : LeftCancelMonoid N mul e) (hc : Conical N mul e)
    (hmark : (Project.FirstOrderSemantics.reduct M).mem mark N) (hne : mark ≠ e)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hProbes : ∀ node, ConstructionProbePath.Path w N mul e zero e node →
      ConstructionSaturationProbes.Probes w K N mul mark e mark node) :
    Complement K N mul mark := by
  obtain ⟨node,_,_,hPath⟩ := ConstructionRequestCarrier.constant_node hM hm hzw
  obtain ⟨Family,hInjection,hProfiles,_⟩ := hProbes node hPath
  refine ⟨Family,hInjection,?_⟩
  intro k p hkp hd
  obtain ⟨x,hx,hmarkx⟩ := hd
  obtain ⟨_,_,_,_,_,ad,_,head,hpmark,_⟩ := hProfiles k p hkp
  have headmark := (hm.1.2 mark hmark ad).1.mp head
  subst ad
  obtain ⟨t,ht,hxt⟩ := (hm.2.1 x hx).1 mark hmark
  have hmarkt := (hm.2.2 mark x mark p t mark hmark hx hmark hmarkx hxt).mp hpmark
  have he : t = e := (hm.2.1 mark hmark).2.2 t e mark ht hm.1.1
    hmarkt ((hm.1.2 mark hmark mark).2.mpr rfl)
  exact hne (hc x mark hx hmark (he ▸ hxt)).2

def AllComplement (K history kappa : M.Carrier .set) : Prop :=
  ∀ N mul e mark H C incoming base,
    Row history kappa N mul e mark H C incoming base kappa → Complement K N mul mark

def AllHistoriesComplement (hM : FirstOrder.Theory.Models M nativeZF)
    (w Q R top D mul e mark H C zero one K mu kappa B : M.Carrier .set) : Prop :=
  ∀ history P F,
    ConstructionSaturationIteration.Recursive hM w Q R top D mul e mark H C zero one K mu B B history →
    ConstructionTowerTransitions.Matrix B history zero P F → AllComplement K history kappa

def ComplementTower (hM : FirstOrder.Theory.Models M nativeZF)
    (w Q R top D mul e mark H C zero one u K mu kappa B : M.Carrier .set) : Prop :=
  ConstructionSaturationMergers.MergerTower hM w Q R top D mul e mark H C zero one u K mu kappa B ∧
    AllHistoriesComplement hM w Q R top D mul e mark H C zero one K mu kappa B

theorem tower_complement (hM : FirstOrder.Theory.Models M nativeZF)
    (hOrder : Project.Gw_order_d (InnerModel.Js_lt_d (M := Project.FirstOrderSemantics.reduct M)))
    (hChoice : ConstructionDirectedCardinality.Choice (M := M))
    {w Q R top D mul e mark H C zero one u K mu kappa B : M.Carrier .set}
    (hTower : ConstructionSaturationMergers.MergerTower hM w Q R top D mul e mark H C zero one u K mu kappa B) :
    ComplementTower hM w Q R top D mul e mark H C zero one u K mu kappa B := by
  refine ⟨hTower,?_⟩
  intro history P F hRec hF N m v a W V incoming base hRow
  have hProbe := hTower.1
  have hCtx := hProbe.1.1.2.1
  have hData := hProbe.1.1.1
  have hV := (ConstructionSaturationIterationValidity.recursive_valid_small hM hOrder hChoice
    hCtx hRec (fun _ h => h)).1
  have hObj := (hV.2.1 kappa hData.2.2.2.1.predecessor_mem
    N m v a W V incoming base hRow).1
  exact complement_probes hM hObj.1 hObj.2.1 hObj.2.2.2.1 hObj.2.2.2.2.1
    hCtx.2.2.2.2.2.2.2.2.1
    (fun node hPath => hProbe.2 history P F hRec hF N m v a W V incoming base v a node
      hRow hObj.2.2.2.1 hObj.2.2.2.2.1 hPath)
theorem exists_complement_tower (hM : FirstOrder.Theory.Models M nativeZF)
    (hOrder : Project.Gw_order_d (InnerModel.Js_lt_d (M := Project.FirstOrderSemantics.reduct M)))
    (hChoice : ConstructionDirectedCardinality.Choice (M := M))
    {w Q R top D mul e mark H C zero one u K mu : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hQ : ConstructionFractionOrder.Carrier w Q)
    (hR : ConstructionRealCuts.CutCarrier hM w Q R)
    (hCoordinates : ConstructionFractionOrder.Coordinates w u one one)
    (hone : (Project.FirstOrderSemantics.reduct M).IsOrdinalOne one)
    (hTop : ConstructionRealCuts.Principal hM w Q u top)
    (hObj : ConstructionRoundFields.ObjectFields hM w Q R top D mul e mark H C)
    (hz : ∀ x, ¬ (Project.FirstOrderSemantics.reduct M).mem x zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hK : ∃ k, (Project.FirstOrderSemantics.reduct M).mem k K)
    (hmu : (Project.FirstOrderSemantics.reduct M).IsInfiniteCardinal (KuratowskiZF.interpretation hM) w mu)
    (hpow : (Project.FirstOrderSemantics.reduct M).IsCardinalExponentiation (KuratowskiZF.interpretation hM) mu mu w)
    (hD : ForcingSupportSize.Small D mu) (hKSmall : ForcingSupportSize.Small K mu) (hOmegaOne : ConstructionSaturationIndex.OmegaOneLe hM w mu) :
    ∃ kappa B, ComplementTower hM w Q R top D mul e mark H C zero one u K mu kappa B := by
  obtain ⟨kappa,B,hTower⟩ := ConstructionSaturationMergers.exists_merger_tower hM hOrder hChoice
    hw hQ hR hCoordinates hone hTop hObj hz hzw hK hmu hpow hD hKSmall hOmegaOne
  exact ⟨kappa,B,tower_complement hM hOrder hChoice hTower⟩


def complement {m : Nat} (K N mul mark : Fin m) : Project.Formula 1 m :=
  (.existsE (.conj (ProjectSyntax.encode id (Source.SetLanguage.injection (0 : Fin (m+1)) K.succ N.succ))
  (.forallE (.forallE (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge (0 : Fin (m+1)).succ.succ (1 :
  Fin (m+3)) (0 : Fin (m+3)))) (.neg (ProjectSyntax.encode id (ConstructionBaseMonoid.divides
  N.succ.succ.succ mul.succ.succ.succ mark.succ.succ.succ (0 : Fin (m+3))))))))))

theorem complement_freeClosed {m : Nat} (K N mul mark : Fin m) :
    (complement K N mul mark).FreeClosed := by
  simp -implicitDefEqProofs [complement,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed]

theorem complement_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (K N mul mark : Fin m) :
    Project.Formula.satisfies env (complement K N mul mark) ↔ Complement (env.bound K) (env.bound N) (env.bound mul) (env.bound mark) := by
  simp only [complement,Complement,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_neg_iff,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,ForcingSupportSize.injection_semantics (M := M),ConstructionBaseMonoid.divides_semantics (M := M)]
  rfl


def allComplement {m : Nat} (K history kappa : Fin m) : Project.Formula 1 m :=
  (.forallE (.forallE (.forallE (.forallE (.forallE (.forallE (.forallE (.forallE (.imp
  (ConstructionTowerHistory.row history.succ.succ.succ.succ.succ.succ.succ.succ
  kappa.succ.succ.succ.succ.succ.succ.succ.succ (7 : Fin (m+8)) (6 : Fin (m+8)) (5 : Fin (m+8)) (4 : Fin
  (m+8)) (3 : Fin (m+8)) (2 : Fin (m+8)) (1 : Fin (m+8)) (0 : Fin (m+8))
  kappa.succ.succ.succ.succ.succ.succ.succ.succ) (complement K.succ.succ.succ.succ.succ.succ.succ.succ (7 :
  Fin (m+8)) (6 : Fin (m+8)) (4 : Fin (m+8))))))))))))

theorem allComplement_freeClosed {m : Nat} (K history kappa : Fin m) :
    (allComplement K history kappa).FreeClosed := by
  simp -implicitDefEqProofs [allComplement,Definitional.Formula.FreeClosed,ConstructionTowerHistory.row_freeClosed,complement_freeClosed]

theorem allComplement_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (K history kappa : Fin m) :
    Project.Formula.satisfies env (allComplement K history kappa) ↔ AllComplement (env.bound K) (env.bound history) (env.bound kappa) := by
  simp only [allComplement,AllComplement,Project.Formula.satisfies_forall_iff,
    Project.Formula.satisfies_imp_iff,
    
    ConstructionTowerHistory.row_semantics hM,complement_semantics hM]
  rfl

def allHistoriesComplement {m : Nat} (w Q R top D mul e mark H C zero one K mu kappa B : Fin m) : Project.Formula 1 m :=
  (.forallE (.forallE (.forallE (.imp (ConstructionSaturationIteration.recursive w.succ.succ.succ
  Q.succ.succ.succ R.succ.succ.succ top.succ.succ.succ D.succ.succ.succ mul.succ.succ.succ e.succ.succ.succ
  mark.succ.succ.succ H.succ.succ.succ C.succ.succ.succ zero.succ.succ.succ one.succ.succ.succ
  K.succ.succ.succ mu.succ.succ.succ B.succ.succ.succ B.succ.succ.succ (2 : Fin (m+3))) (.imp
  (ConstructionTowerTransitions.matrix B.succ.succ.succ (2 : Fin (m+3)) zero.succ.succ.succ (1 : Fin (m+3))
  (0 : Fin (m+3))) (allComplement K.succ.succ.succ (2 : Fin (m+3)) kappa.succ.succ.succ))))))

theorem allHistoriesComplement_freeClosed {m : Nat} (w Q R top D mul e mark H C zero one K mu kappa B : Fin m) :
    (allHistoriesComplement w Q R top D mul e mark H C zero one K mu kappa B).FreeClosed := by
  simp -implicitDefEqProofs [allHistoriesComplement,Definitional.Formula.FreeClosed,ConstructionSaturationIteration.recursive_freeClosed,ConstructionTowerTransitions.matrix_freeClosed,allComplement_freeClosed]

theorem allHistoriesComplement_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w Q R top D mul e mark H C zero one K mu kappa B : Fin m) :
    Project.Formula.satisfies env (allHistoriesComplement w Q R top D mul e mark H C zero one K mu kappa B) ↔ AllHistoriesComplement hM (env.bound w) (env.bound Q) (env.bound R) (env.bound top) (env.bound D) (env.bound mul) (env.bound e) (env.bound mark) (env.bound H) (env.bound C) (env.bound zero) (env.bound one) (env.bound K) (env.bound mu) (env.bound kappa) (env.bound B) := by
  simp only [allHistoriesComplement,AllHistoriesComplement,Project.Formula.satisfies_forall_iff,
    Project.Formula.satisfies_imp_iff,
    
    ConstructionSaturationIteration.recursive_semantics hM,ConstructionTowerTransitions.matrix_semantics hM,allComplement_semantics hM]
  rfl


def complementTower {m : Nat} (w Q R top D mul e mark H C zero one u K mu kappa B : Fin m) : Project.Formula 1 m :=
  (.conj (ConstructionSaturationMergers.mergerTower w Q R top D mul e mark H C zero one u K mu kappa B)
  (allHistoriesComplement w Q R top D mul e mark H C zero one K mu kappa B))

theorem complementTower_freeClosed {m : Nat} (w Q R top D mul e mark H C zero one u K mu kappa B : Fin m) :
    (complementTower w Q R top D mul e mark H C zero one u K mu kappa B).FreeClosed := by
  simp -implicitDefEqProofs [complementTower,Definitional.Formula.FreeClosed,ConstructionSaturationMergers.mergerTower_freeClosed,allHistoriesComplement_freeClosed]

theorem complementTower_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w Q R top D mul e mark H C zero one u K mu kappa B : Fin m) :
    Project.Formula.satisfies env (complementTower w Q R top D mul e mark H C zero one u K mu kappa B) ↔ ComplementTower hM (env.bound w) (env.bound Q) (env.bound R) (env.bound top) (env.bound D) (env.bound mul) (env.bound e) (env.bound mark) (env.bound H) (env.bound C) (env.bound zero) (env.bound one) (env.bound u) (env.bound K) (env.bound mu) (env.bound kappa) (env.bound B) := by
  simp only [complementTower,ComplementTower,
    Project.Formula.satisfies_conj_iff,
    
    ConstructionSaturationMergers.mergerTower_semantics hM,allHistoriesComplement_semantics hM]

def constructionSentence : Project.Sentence where
  formula := (Project.Formula.forallClosure 15 (.imp (Project.Formula.isOmega (.bound (0 : Fin 15))) (.imp
    (ConstructionFractionOrder.carrier (0 : Fin 15) (1 : Fin 15)) (.imp (ConstructionRealCuts.cutCarrier (0
    : Fin 15) (1 : Fin 15) (2 : Fin 15)) (.imp (ConstructionFractionOrder.coordinates (0 : Fin 15) (12 : Fin
    15) (11 : Fin 15) (11 : Fin 15)) (.imp (Project.Formula.isOrdinalOne (.bound (11 : Fin 15))) (.imp
    (ConstructionRealCuts.principal (0 : Fin 15) (1 : Fin 15) (12 : Fin 15) (3 : Fin 15)) (.imp
    (ConstructionRoundStepSyntax.objectFields (0 : Fin 15) (1 : Fin 15) (2 : Fin 15) (3 : Fin 15) (4 : Fin
    15) (5 : Fin 15) (6 : Fin 15) (7 : Fin 15) (8 : Fin 15) (9 : Fin 15)) (.imp (Project.Formula.isEmpty
    (.bound (10 : Fin 15))) (.imp (.mem (.bound (10 : Fin 15)) (.bound (0 : Fin 15))) (.imp (.existsE (.mem
    (.bound (0 : Fin 16)) (.bound (13 : Fin 15).succ))) (.imp (Project.Formula.isInfiniteCardinal
    PureKuratowskiProject.convention (.bound (0 : Fin 15)) (.bound (14 : Fin 15))) (.imp
    (Project.Formula.isCardinalExponentiation PureKuratowskiProject.convention (.bound (14 : Fin 15))
    (.bound (14 : Fin 15)) (.bound (0 : Fin 15))) (.imp (ProjectSyntax.encode id (ForcingSupportSize.small
    (4 : Fin 15) (14 : Fin 15))) (.imp (ProjectSyntax.encode id (ForcingSupportSize.small (13 : Fin 15) (14
    : Fin 15))) (.imp (ConstructionSaturationIndex.omegaOneLe (0 : Fin 15) (14 : Fin 15)) (.existsE (.existsE (complementTower (0 : Fin
    15).succ.succ (1 : Fin 15).succ.succ (2 : Fin 15).succ.succ (3 : Fin 15).succ.succ (4 : Fin
    15).succ.succ (5 : Fin 15).succ.succ (6 : Fin 15).succ.succ (7 : Fin 15).succ.succ (8 : Fin
    15).succ.succ (9 : Fin 15).succ.succ (10 : Fin 15).succ.succ (11 : Fin 15).succ.succ (12 : Fin
    15).succ.succ (13 : Fin 15).succ.succ (14 : Fin 15).succ.succ (1 : Fin 17) (0 : Fin
    17))))))))))))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
      Project.Formula.isOmega,ConstructionFractionOrder.carrier_freeClosed,
      ConstructionRealCuts.cutCarrier_freeClosed,ConstructionFractionOrder.coordinates_freeClosed,
      Project.Formula.isOrdinalOne,ConstructionRealCuts.principal_freeClosed,
      ConstructionRoundStepSyntax.objectFields_freeClosed,Project.Formula.isEmpty,
      Project.Formula.isInfiniteCardinal,Project.Formula.isCardinalExponentiation,Project.Formula.isFunctionSpace,
      ConstructionSaturationIndex.omegaOneLe_freeClosed,complementTower_freeClosed]

theorem construction_models (hM : FirstOrder.Theory.Models M nativeZF)
    (hOrder : Project.Gw_order_d (InnerModel.Js_lt_d (M := Project.FirstOrderSemantics.reduct M)))
    (hChoice : ConstructionDirectedCardinality.Choice (M := M)) :
    (Project.fo_sentence constructionSentence).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) constructionSentence]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_isOmega_iff,Project.Formula.satisfies_isOrdinalOne_iff,
    Project.Formula.satisfies_isEmpty_iff,Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    Project.Formula.satisfies_isInfiniteCardinal_iff (KuratowskiZF.interpretation hM) (ModelTransfer.extensionality hM),
    Project.Formula.satisfies_isCardinalExponentiation_iff (KuratowskiZF.interpretation hM) (ModelTransfer.extensionality hM),
    ConstructionFractionOrder.carrier_semantics hM,ConstructionRealCuts.cutCarrier_semantics hM,
    ConstructionFractionOrder.coordinates_semantics hM,ConstructionRealCuts.principal_semantics hM,
    ConstructionRoundStepSyntax.objectFields_semantics hM,GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingSupportSize.small_semantics (M := M),ConstructionSaturationIndex.omegaOneLe_semantics hM,complementTower_semantics hM]
  exact fun hw hQ hR hCoordinates hone hTop hObj hz hzw hK hmu hpow hD hKSmall hOmegaOne =>
    exists_complement_tower hM hOrder hChoice hw hQ hR hCoordinates hone hTop hObj hz hzw hK hmu hpow hD hKSmall hOmegaOne

theorem construction_kernel_certificate : FirstOrder.Derives nativeZF []
    (Project.fo_sentence (ConstructibleGround.relative constructionSentence)) := by
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
  apply ConstructibleGround.relative_models hM constructionSentence
  exact (Project.FirstOrderSemantics.sentence_correct
    (ModelTransfer.extensionality hL) constructionSentence).mp
    (construction_models hL (ConstructionRoundSelection.l_order hM) hChoice)




end PPAC.Migration.ConstructionSaturationComplement
