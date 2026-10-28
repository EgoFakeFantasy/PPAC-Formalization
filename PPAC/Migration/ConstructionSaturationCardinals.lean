/- Pinned SaturatedMonoids.Saturation.target_cardinal:198/complement_cardinal:206.
Reuse native Separation, existing actual stage-size bounds and Cantor--Bernstein.
All cardinal witnesses are MODEL-INTERNAL bijection graphs, on the SAME tower. -/
import PPAC.Migration.ConstructionSaturationComplement

namespace PPAC.Migration.ConstructionSaturationCardinals
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ConstructionTowerHistory (Row)
open ForcingSupportSize (Small Injection)
open ConstructionBaseMonoid (Divides)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

def ComplementSet (N mul mark S : M.Carrier .set) : Prop :=
  ∀ x, (Project.FirstOrderSemantics.reduct M).mem x S ↔
    (Project.FirstOrderSemantics.reduct M).mem x N ∧ ¬ Divides N mul mark x

theorem exists_complement_set (hM : FirstOrder.Theory.Models M nativeZF)
    (N mul mark : M.Carrier .set) : ∃ S, ComplementSet N mul mark S := by
  let schema : Project.UnarySchema 3 := {
    body := .neg (ProjectSyntax.encode id (ConstructionBaseMonoid.divides
      (3 : Fin 4) (2 : Fin 4) (1 : Fin 4) (0 : Fin 4)))
    freeClosed := by simp [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed] }
  let env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) 3 :=
    { bound := Fin.cases mark (Fin.cases mul (fun _ => N)), free := fun _ => N }
  obtain ⟨S,hS⟩ := ZF.separation_exists_d (ModelTransfer.project_models_iff.mp hM) schema env N
  refine ⟨S,fun x => ?_⟩
  simpa only [schema,Project.Formula.satisfies_neg_iff,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ConstructionBaseMonoid.divides_semantics (M := M)] using! hS x

def Cardinals (hM : FirstOrder.Theory.Models M nativeZF)
    (N mul mark mu : M.Carrier .set) : Prop :=
  (Project.FirstOrderSemantics.reduct M).Equinumerous (KuratowskiZF.interpretation hM) N mu ∧
    ∃ S, ComplementSet N mul mark S ∧
      (Project.FirstOrderSemantics.reduct M).Equinumerous (KuratowskiZF.interpretation hM) S mu

theorem cardinals (hM : FirstOrder.Theory.Models M nativeZF)
    {K N mul mark mu : M.Carrier .set}
    (hSmall : Small N mu)
    (hK : (Project.FirstOrderSemantics.reduct M).Equinumerous (KuratowskiZF.interpretation hM) K mu)
    (hComp : ConstructionSaturationComplement.Complement K N mul mark) :
    Cardinals hM N mul mark mu := by
  have hZF := ModelTransfer.project_models_iff.mp hM
  let I := KuratowskiZF.interpretation hM
  obtain ⟨reverse,hReverse⟩ := Structure.Equinumerous.symm hZF I hK
  obtain ⟨Family,hFamily,hAvoid⟩ := hComp
  have hNative := (ForcingSupportSize.native_injection hM K N Family).mp hFamily
  have hLower := ZF.exists_compositionInjection hZF I hReverse.1 hNative
  have hN := ZF.equinumerous_of_cardinalLessOrEqual hZF I
    ((ForcingSupportSize.native_small hM N mu).mp hSmall) hLower
  obtain ⟨S,hS⟩ := exists_complement_set hM N mul mark
  have hSub : (Project.FirstOrderSemantics.reduct M).MemberSubset S N :=
    fun x hx => ((hS x).mp hx).1
  have hIntoS : Injection K S Family :=
    ⟨⟨hFamily.1.1,fun k x hkx => (hS x).mpr ⟨hFamily.1.2 k x hkx,hAvoid k x hkx⟩⟩,hFamily.2⟩
  have hSmallS := ForcingSupportSize.small_subset hM hSub hSmall
  have hLowerS := ZF.exists_compositionInjection hZF I hReverse.1
    ((ForcingSupportSize.native_injection hM K S Family).mp hIntoS)
  exact ⟨hN,S,hS,ZF.equinumerous_of_cardinalLessOrEqual hZF I
    ((ForcingSupportSize.native_small hM S mu).mp hSmallS) hLowerS⟩

def AllCardinals (hM : FirstOrder.Theory.Models M nativeZF)
    (mu history kappa : M.Carrier .set) : Prop :=
  ∀ N mul e mark H C incoming base,
    Row history kappa N mul e mark H C incoming base kappa → Cardinals hM N mul mark mu

def AllHistoriesCardinals (hM : FirstOrder.Theory.Models M nativeZF)
    (w Q R top D mul e mark H C zero one K mu kappa B : M.Carrier .set) : Prop :=
  ∀ history P F,
    ConstructionSaturationIteration.Recursive hM w Q R top D mul e mark H C zero one K mu B B history →
    ConstructionTowerTransitions.Matrix B history zero P F → AllCardinals hM mu history kappa

def CardinalTower (hM : FirstOrder.Theory.Models M nativeZF)
    (w Q R top D mul e mark H C zero one u K mu kappa B : M.Carrier .set) : Prop :=
  ConstructionSaturationComplement.ComplementTower hM w Q R top D mul e mark H C zero one u K mu kappa B ∧
    ((Project.FirstOrderSemantics.reduct M).Equinumerous (KuratowskiZF.interpretation hM) K mu →
      AllHistoriesCardinals hM w Q R top D mul e mark H C zero one K mu kappa B)

theorem tower_cardinals (hM : FirstOrder.Theory.Models M nativeZF)
    (hOrder : Project.Gw_order_d (InnerModel.Js_lt_d (M := Project.FirstOrderSemantics.reduct M)))
    (hChoice : ConstructionDirectedCardinality.Choice (M := M))
    {w Q R top D mul e mark H C zero one u K mu kappa B : M.Carrier .set}
    (hTower : ConstructionSaturationComplement.ComplementTower hM w Q R top D mul e mark H C zero one u K mu kappa B) :
    CardinalTower hM w Q R top D mul e mark H C zero one u K mu kappa B := by
  refine ⟨hTower,?_⟩
  intro hK history P F hRec hF N m v a W V incoming base hRow
  have hIndex := hTower.1.1.1.1
  have hCtx := hIndex.2.1
  have hData := hIndex.1
  have hSmall := (ConstructionSaturationIterationValidity.recursive_valid_small hM hOrder hChoice
    hCtx hRec (fun _ h => h)).2
  exact cardinals hM (hSmall kappa hData.2.2.2.1.predecessor_mem N
    ⟨N,m,v,a,W,V,incoming,base,kappa,hRow,rfl⟩) hK
    (hTower.2 history P F hRec hF N m v a W V incoming base hRow)
theorem exists_cardinal_tower (hM : FirstOrder.Theory.Models M nativeZF)
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
    ∃ kappa B, CardinalTower hM w Q R top D mul e mark H C zero one u K mu kappa B := by
  obtain ⟨kappa,B,hTower⟩ := ConstructionSaturationComplement.exists_complement_tower hM hOrder hChoice
    hw hQ hR hCoordinates hone hTop hObj hz hzw hK hmu hpow hD hKSmall hOmegaOne
  exact ⟨kappa,B,tower_cardinals hM hOrder hChoice hTower⟩


def complementSet {m : Nat} (N mul mark S : Fin m) : Project.Formula 1 m :=
  (.forallE (.iff (.mem (.bound (0 : Fin (m+1))) (.bound S.succ)) (.conj (.mem (.bound (0 : Fin (m+1)))
  (.bound N.succ)) (.neg (ProjectSyntax.encode id (ConstructionBaseMonoid.divides N.succ mul.succ mark.succ
  (0 : Fin (m+1))))))))

theorem complementSet_freeClosed {m : Nat} (N mul mark S : Fin m) :
    (complementSet N mul mark S).FreeClosed := by
  simp -implicitDefEqProofs [complementSet,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed]

theorem complementSet_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (N mul mark S : Fin m) :
    Project.Formula.satisfies env (complementSet N mul mark S) ↔ ComplementSet (env.bound N) (env.bound mul) (env.bound mark) (env.bound S) := by
  simp only [complementSet,ComplementSet,Project.Formula.satisfies_forall_iff,
    Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_iff_iff,
    Project.Formula.satisfies_neg_iff,Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),ConstructionBaseMonoid.divides_semantics (M := M)]
  rfl


def cardinalsF {m : Nat} (N mul mark mu : Fin m) : Project.Formula 1 m :=
  (.conj (Project.Formula.equinumerous PureKuratowskiProject.convention (.bound N) (.bound mu)) (.existsE
  (.conj (complementSet N.succ mul.succ mark.succ (0 : Fin (m+1))) (Project.Formula.equinumerous
  PureKuratowskiProject.convention (.bound (0 : Fin (m+1))) (.bound mu.succ)))))

theorem cardinalsF_freeClosed {m : Nat} (N mul mark mu : Fin m) :
    (cardinalsF N mul mark mu).FreeClosed := by
  simp -implicitDefEqProofs [cardinalsF,Definitional.Formula.FreeClosed,complementSet_freeClosed,Project.Formula.equinumerous]

theorem cardinalsF_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (N mul mark mu : Fin m) :
    Project.Formula.satisfies env (cardinalsF N mul mark mu) ↔ Cardinals hM (env.bound N) (env.bound mul) (env.bound mark) (env.bound mu) := by
  simp only [cardinalsF,Cardinals,Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_conj_iff,
    Project.Term.eval_bound,
    complementSet_semantics hM,Project.Formula.satisfies_equinumerous_iff (KuratowskiZF.interpretation hM) (ModelTransfer.extensionality hM)]
  rfl


def allCardinals {m : Nat} (mu history kappa : Fin m) : Project.Formula 1 m :=
  (.forallE (.forallE (.forallE (.forallE (.forallE (.forallE (.forallE (.forallE (.imp
  (ConstructionTowerHistory.row history.succ.succ.succ.succ.succ.succ.succ.succ
  kappa.succ.succ.succ.succ.succ.succ.succ.succ (7 : Fin (m+8)) (6 : Fin (m+8)) (5 : Fin (m+8)) (4 : Fin
  (m+8)) (3 : Fin (m+8)) (2 : Fin (m+8)) (1 : Fin (m+8)) (0 : Fin (m+8))
  kappa.succ.succ.succ.succ.succ.succ.succ.succ) (cardinalsF (7 : Fin (m+8)) (6 : Fin (m+8)) (4 : Fin (m+8))
  mu.succ.succ.succ.succ.succ.succ.succ.succ))))))))))

theorem allCardinals_freeClosed {m : Nat} (mu history kappa : Fin m) :
    (allCardinals mu history kappa).FreeClosed := by
  simp -implicitDefEqProofs [allCardinals,Definitional.Formula.FreeClosed,ConstructionTowerHistory.row_freeClosed,cardinalsF_freeClosed]

theorem allCardinals_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (mu history kappa : Fin m) :
    Project.Formula.satisfies env (allCardinals mu history kappa) ↔ AllCardinals hM (env.bound mu) (env.bound history) (env.bound kappa) := by
  simp only [allCardinals,AllCardinals,Project.Formula.satisfies_forall_iff,
    Project.Formula.satisfies_imp_iff,
    
    ConstructionTowerHistory.row_semantics hM,cardinalsF_semantics hM]
  rfl

def allHistoriesCardinals {m : Nat} (w Q R top D mul e mark H C zero one K mu kappa B : Fin m) : Project.Formula 1 m :=
  (.forallE (.forallE (.forallE (.imp (ConstructionSaturationIteration.recursive w.succ.succ.succ
  Q.succ.succ.succ R.succ.succ.succ top.succ.succ.succ D.succ.succ.succ mul.succ.succ.succ e.succ.succ.succ
  mark.succ.succ.succ H.succ.succ.succ C.succ.succ.succ zero.succ.succ.succ one.succ.succ.succ
  K.succ.succ.succ mu.succ.succ.succ B.succ.succ.succ B.succ.succ.succ (2 : Fin (m+3))) (.imp
  (ConstructionTowerTransitions.matrix B.succ.succ.succ (2 : Fin (m+3)) zero.succ.succ.succ (1 : Fin (m+3))
  (0 : Fin (m+3))) (allCardinals mu.succ.succ.succ (2 : Fin (m+3)) kappa.succ.succ.succ))))))

theorem allHistoriesCardinals_freeClosed {m : Nat} (w Q R top D mul e mark H C zero one K mu kappa B : Fin m) :
    (allHistoriesCardinals w Q R top D mul e mark H C zero one K mu kappa B).FreeClosed := by
  simp -implicitDefEqProofs [allHistoriesCardinals,Definitional.Formula.FreeClosed,ConstructionSaturationIteration.recursive_freeClosed,ConstructionTowerTransitions.matrix_freeClosed,allCardinals_freeClosed]

theorem allHistoriesCardinals_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w Q R top D mul e mark H C zero one K mu kappa B : Fin m) :
    Project.Formula.satisfies env (allHistoriesCardinals w Q R top D mul e mark H C zero one K mu kappa B) ↔ AllHistoriesCardinals hM (env.bound w) (env.bound Q) (env.bound R) (env.bound top) (env.bound D) (env.bound mul) (env.bound e) (env.bound mark) (env.bound H) (env.bound C) (env.bound zero) (env.bound one) (env.bound K) (env.bound mu) (env.bound kappa) (env.bound B) := by
  simp only [allHistoriesCardinals,AllHistoriesCardinals,Project.Formula.satisfies_forall_iff,
    Project.Formula.satisfies_imp_iff,
    
    ConstructionSaturationIteration.recursive_semantics hM,ConstructionTowerTransitions.matrix_semantics hM,allCardinals_semantics hM]
  rfl


def cardinalTower {m : Nat} (w Q R top D mul e mark H C zero one u K mu kappa B : Fin m) : Project.Formula 1 m :=
  (.conj (ConstructionSaturationComplement.complementTower w Q R top D mul e mark H C zero one u K mu kappa B)
  (.imp (Project.Formula.equinumerous PureKuratowskiProject.convention (.bound K) (.bound mu))
  (allHistoriesCardinals w Q R top D mul e mark H C zero one K mu kappa B)))

theorem cardinalTower_freeClosed {m : Nat} (w Q R top D mul e mark H C zero one u K mu kappa B : Fin m) :
    (cardinalTower w Q R top D mul e mark H C zero one u K mu kappa B).FreeClosed := by
  simp -implicitDefEqProofs [cardinalTower,Definitional.Formula.FreeClosed,ConstructionSaturationComplement.complementTower_freeClosed,allHistoriesCardinals_freeClosed,Project.Formula.equinumerous]

theorem cardinalTower_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w Q R top D mul e mark H C zero one u K mu kappa B : Fin m) :
    Project.Formula.satisfies env (cardinalTower w Q R top D mul e mark H C zero one u K mu kappa B) ↔ CardinalTower hM (env.bound w) (env.bound Q) (env.bound R) (env.bound top) (env.bound D) (env.bound mul) (env.bound e) (env.bound mark) (env.bound H) (env.bound C) (env.bound zero) (env.bound one) (env.bound u) (env.bound K) (env.bound mu) (env.bound kappa) (env.bound B) := by
  simp only [cardinalTower,CardinalTower,
    Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_conj_iff,
    Project.Term.eval_bound,
    ConstructionSaturationComplement.complementTower_semantics hM,allHistoriesCardinals_semantics hM,Project.Formula.satisfies_equinumerous_iff (KuratowskiZF.interpretation hM) (ModelTransfer.extensionality hM)]

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
    : Fin 15))) (.imp (ConstructionSaturationIndex.omegaOneLe (0 : Fin 15) (14 : Fin 15)) (.existsE (.existsE (cardinalTower (0 : Fin
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
      ConstructionSaturationIndex.omegaOneLe_freeClosed,cardinalTower_freeClosed]

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
    ForcingSupportSize.small_semantics (M := M),ConstructionSaturationIndex.omegaOneLe_semantics hM,cardinalTower_semantics hM]
  exact fun hw hQ hR hCoordinates hone hTop hObj hz hzw hK hmu hpow hD hKSmall hOmegaOne =>
    exists_cardinal_tower hM hOrder hChoice hw hQ hR hCoordinates hone hTop hObj hz hzw hK hmu hpow hD hKSmall hOmegaOne

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




end PPAC.Migration.ConstructionSaturationCardinals
