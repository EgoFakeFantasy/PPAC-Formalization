/- Pinned MonoidRounds.Round.underFunctor / fromBase_naturality and
ConstructionIteration: full invariants stated DIRECTLY on the SAME record
history. The recursive preservation proof is separate; validity is not
inferred merely from record/function typing or assumed output diagrams. -/
import PPAC.Migration.ConstructionTowerTransitions

namespace PPAC.Migration.ConstructionTowerValidity
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ConstructionTowerHistory (Row Records Field Charts Chart)
open ConstructionTowerTransitions (Before)
open ConstructionRoundFields (ObjectFields MapFields Profiles)
open ConstructionProbeMappedPath (NodeMap)
open ForcingConditionGraphs (FunctionOn function_unique)
open ForcingSupportSize (MapsTo)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

def Stage (hM : FirstOrder.Theory.Models M nativeZF)
    (w Q R top D mul e mark H C S i : M.Carrier .set) : Prop :=
  ∀ N m u a W V K f, Row S i N m u a W V K f i →
    ObjectFields hM w Q R top N m u a W V ∧
    MapFields hM w Q D N mul m e u mark a H C W V f ∧
    Profiles w D N mul m f ∧
    ∃ next identity, (Project.FirstOrderSemantics.reduct M).SuccessorOf next i ∧
      FunctionOn next K ∧ PureKuratowski.PairMember M i identity K ∧
      ForcingConditionGraphs.IdentityGraph N identity

def Homs (hM : FirstOrder.Theory.Models M nativeZF)
    (w Q J S : M.Carrier .set) : Prop :=
  ∀ i j D m e a H C K f N n u b W V L g t,
    (Project.FirstOrderSemantics.reduct M).mem i J →
    (Project.FirstOrderSemantics.reduct M).mem j J → Before i j →
    Row S i D m e a H C K f i → Row S j N n u b W V L g j →
    PureKuratowski.PairMember M i t L →
      MapFields hM w Q D N m n e u a b H C W V t ∧ Profiles w D N m n t

def Composition (J S : M.Carrier .set) : Prop :=
  ∀ i j k L K f g h,
    (Project.FirstOrderSemantics.reduct M).mem i J →
    (Project.FirstOrderSemantics.reduct M).mem j J →
    (Project.FirstOrderSemantics.reduct M).mem k J →
    Before i j → Before j k → Field 6 S j L → Field 6 S k K →
    PureKuratowski.PairMember M i f L → PureKuratowski.PairMember M j g K →
    PureKuratowski.PairMember M i h K → NodeMap f g h

def Natural (J S : M.Carrier .set) : Prop :=
  ∀ i j f g K t, (Project.FirstOrderSemantics.reduct M).mem i J →
    (Project.FirstOrderSemantics.reduct M).mem j J → Before i j →
    Field 7 S i f → Field 7 S j g → Field 6 S j K →
    PureKuratowski.PairMember M i t K → NodeMap f t g

def Valid (hM : FirstOrder.Theory.Models M nativeZF)
    (w Q R top D mul e mark H C J S : M.Carrier .set) : Prop :=
  Records J S ∧
  (∀ i, (Project.FirstOrderSemantics.reduct M).mem i J → Stage hM w Q R top D mul e mark H C S i) ∧
  Homs hM w Q J S ∧ Composition J S ∧ Natural J S

theorem incoming_rows (hM : FirstOrder.Theory.Models M nativeZF)
    {w Q R top D mul e mark H C J S : M.Carrier .set}
    (hV : Valid hM w Q R top D mul e mark H C J S) :
    ConstructionTowerTransitions.IncomingRows J S := by
  intro i K hi hK
  obtain ⟨N,m,u,a,W,V,L,f,hRow⟩ := hV.1.2 i hi
  have hL : Field 6 S i L := ⟨N,m,u,a,W,V,L,f,i,hRow,rfl⟩
  have he := ConstructionTowerHistory.field_unique 6 hV.1.1 hK hL
  subst K
  obtain ⟨_,_,_,next,identity,hSucc,hFn,_,_⟩ := hV.2.1 i hi N m u a W V L f hRow
  exact ⟨next,hSucc,hFn⟩

theorem stage_at (hM : FirstOrder.Theory.Models M nativeZF)
    {w Q R top D mul e mark H C J S
      Domains Muls Units Marks Heights Costs Incoming Origins Times : M.Carrier .set}
    (hV : Valid hM w Q R top D mul e mark H C J S)
    (hCharts : Charts J S Domains Muls Units Marks Heights Costs Incoming Origins Times)
    {i : M.Carrier .set} (hi : (Project.FirstOrderSemantics.reduct M).mem i J) :
    ∃ N m u a W V K f,
      Row S i N m u a W V K f i ∧
      PureKuratowski.PairMember M i N Domains ∧ PureKuratowski.PairMember M i m Muls ∧
      PureKuratowski.PairMember M i u Units ∧ PureKuratowski.PairMember M i a Marks ∧
      PureKuratowski.PairMember M i W Heights ∧ PureKuratowski.PairMember M i V Costs ∧
      PureKuratowski.PairMember M i K Incoming ∧ PureKuratowski.PairMember M i f Origins ∧
      ObjectFields hM w Q R top N m u a W V ∧
      MapFields hM w Q D N mul m e u mark a H C W V f ∧ Profiles w D N mul m f ∧
      ∃ next identity, (Project.FirstOrderSemantics.reduct M).SuccessorOf next i ∧
        FunctionOn next K ∧ PureKuratowski.PairMember M i identity K ∧
        ForcingConditionGraphs.IdentityGraph N identity := by
  obtain ⟨N,m,u,a,W,V,K,f,hRow⟩ := hV.1.2 i hi
  obtain ⟨hN,hm,hu,ha,hW,hV',hK,hf,_⟩ := ConstructionTowerHistory.charts_row hCharts hi hRow
  obtain ⟨hObj,hMap,hProf,hSelf⟩ := hV.2.1 i hi N m u a W V K f hRow
  exact ⟨N,m,u,a,W,V,K,f,hRow,hN,hm,hu,ha,hW,hV',hK,hf,hObj,hMap,hProf,hSelf⟩

theorem row_field (k : Fin 9) {S i D m e a H C K f : M.Carrier .set}
    (hRow : Row S i D m e a H C K f i) :
    Field k S i (match k.val with
      | 0 => D | 1 => m | 2 => e | 3 => a | 4 => H
      | 5 => C | 6 => K | 7 => f | _ => i) :=
  ⟨D,m,e,a,H,C,K,f,i,hRow,rfl⟩


def stage {m : Nat} (w Q R top D mul e mark H C S i : Fin m) : Project.Formula 1 m :=
  (.forallE (.forallE (.forallE (.forallE (.forallE (.forallE (.forallE (.forallE (.imp
  (ConstructionTowerHistory.row S.succ.succ.succ.succ.succ.succ.succ.succ
  i.succ.succ.succ.succ.succ.succ.succ.succ (7 : Fin (m+8)) (6 : Fin (m+8)) (5 : Fin (m+8)) (4 : Fin (m+8))
  (3 : Fin (m+8)) (2 : Fin (m+8)) (1 : Fin (m+8)) (0 : Fin (m+8)) i.succ.succ.succ.succ.succ.succ.succ.succ)
  (.conj (ConstructionRoundStepSyntax.objectFields w.succ.succ.succ.succ.succ.succ.succ.succ
  Q.succ.succ.succ.succ.succ.succ.succ.succ R.succ.succ.succ.succ.succ.succ.succ.succ
  top.succ.succ.succ.succ.succ.succ.succ.succ (7 : Fin (m+8)) (6 : Fin (m+8)) (5 : Fin (m+8)) (4 : Fin
  (m+8)) (3 : Fin (m+8)) (2 : Fin (m+8))) (.conj (ConstructionRoundStepSyntax.mapFields
  w.succ.succ.succ.succ.succ.succ.succ.succ Q.succ.succ.succ.succ.succ.succ.succ.succ
  D.succ.succ.succ.succ.succ.succ.succ.succ (7 : Fin (m+8)) mul.succ.succ.succ.succ.succ.succ.succ.succ (6 :
  Fin (m+8)) e.succ.succ.succ.succ.succ.succ.succ.succ (5 : Fin (m+8))
  mark.succ.succ.succ.succ.succ.succ.succ.succ (4 : Fin (m+8)) H.succ.succ.succ.succ.succ.succ.succ.succ
  C.succ.succ.succ.succ.succ.succ.succ.succ (3 : Fin (m+8)) (2 : Fin (m+8)) (0 : Fin (m+8))) (.conj
  (ConstructionRoundStepSyntax.profiles w.succ.succ.succ.succ.succ.succ.succ.succ
  D.succ.succ.succ.succ.succ.succ.succ.succ (7 : Fin (m+8)) mul.succ.succ.succ.succ.succ.succ.succ.succ (6 :
  Fin (m+8)) (0 : Fin (m+8))) (.existsE (.existsE (.conj (Project.Formula.isSuccessor (.bound (1 : Fin
  (m+10))) (.bound i.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ)) (.conj (ProjectSyntax.encode id
  (Source.SetLanguage.functionOn (3 : Fin (m+10)) (1 : Fin (m+10)))) (.conj (ProjectSyntax.encode id
  (Source.SetLanguage.edge (3 : Fin (m+10)) i.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (0 : Fin
  (m+10)))) (ProjectSyntax.encode id (ForcingConditionGraphs.identityGraph (9 : Fin (m+10)) (0 : Fin
  (m+10)))))))))))))))))))))

theorem stage_freeClosed {m : Nat} (w Q R top D mul e mark H C S i : Fin m) :
    (stage w Q R top D mul e mark H C S i).FreeClosed := by
  simp -implicitDefEqProofs [stage,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,ConstructionTowerHistory.row_freeClosed,ConstructionRoundStepSyntax.objectFields_freeClosed,ConstructionRoundStepSyntax.mapFields_freeClosed,ConstructionRoundStepSyntax.profiles_freeClosed,Project.Formula.isSuccessor]

theorem stage_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w Q R top D mul e mark H C S i : Fin m) :
    Project.Formula.satisfies env (stage w Q R top D mul e mark H C S i) ↔ Stage hM (env.bound w) (env.bound Q) (env.bound R) (env.bound top) (env.bound D) (env.bound mul) (env.bound e) (env.bound mark) (env.bound H) (env.bound C) (env.bound S) (env.bound i) := by
  simp only [stage,Stage,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_conj_iff,
    Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,ConstructionTowerHistory.row_semantics hM,ConstructionRoundStepSyntax.objectFields_semantics hM,ConstructionRoundStepSyntax.mapFields_semantics hM,ConstructionRoundStepSyntax.profiles_semantics hM,Project.Formula.satisfies_isSuccessor_iff,ForcingConditionGraphs.functionOn_semantics (M := M),ForcingConditionGraphs.identityGraph_semantics (M := M)]
  rfl


def homs {m : Nat} (w Q J S : Fin m) : Project.Formula 1 m :=
  (.forallE (.forallE (.forallE (.forallE (.forallE (.forallE (.forallE (.forallE (.forallE (.forallE
  (.forallE (.forallE (.forallE (.forallE (.forallE (.forallE (.forallE (.forallE (.forallE (.imp (.mem
  (.bound (18 : Fin (m+19))) (.bound
  J.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ)) (.imp
  (.mem (.bound (17 : Fin (m+19))) (.bound
  J.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ)) (.imp
  (ConstructionTowerTransitions.before (18 : Fin (m+19)) (17 : Fin (m+19))) (.imp
  (ConstructionTowerHistory.row
  S.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (18 : Fin
  (m+19)) (16 : Fin (m+19)) (15 : Fin (m+19)) (14 : Fin (m+19)) (13 : Fin (m+19)) (12 : Fin (m+19)) (11 :
  Fin (m+19)) (10 : Fin (m+19)) (9 : Fin (m+19)) (18 : Fin (m+19))) (.imp (ConstructionTowerHistory.row
  S.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (17 : Fin
  (m+19)) (8 : Fin (m+19)) (7 : Fin (m+19)) (6 : Fin (m+19)) (5 : Fin (m+19)) (4 : Fin (m+19)) (3 : Fin
  (m+19)) (2 : Fin (m+19)) (1 : Fin (m+19)) (17 : Fin (m+19))) (.imp (ProjectSyntax.encode id
  (Source.SetLanguage.edge (2 : Fin (m+19)) (18 : Fin (m+19)) (0 : Fin (m+19)))) (.conj
  (ConstructionRoundStepSyntax.mapFields
  w.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  Q.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (16 : Fin
  (m+19)) (8 : Fin (m+19)) (15 : Fin (m+19)) (7 : Fin (m+19)) (14 : Fin (m+19)) (6 : Fin (m+19)) (13 : Fin
  (m+19)) (5 : Fin (m+19)) (12 : Fin (m+19)) (11 : Fin (m+19)) (4 : Fin (m+19)) (3 : Fin (m+19)) (0 : Fin
  (m+19))) (ConstructionRoundStepSyntax.profiles
  w.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (16 : Fin
  (m+19)) (8 : Fin (m+19)) (15 : Fin (m+19)) (7 : Fin (m+19)) (0 : Fin (m+19)))))))))))))))))))))))))))))

theorem homs_freeClosed {m : Nat} (w Q J S : Fin m) :
    (homs w Q J S).FreeClosed := by
  simp -implicitDefEqProofs [homs,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,ConstructionTowerTransitions.before_freeClosed,ConstructionTowerHistory.row_freeClosed,ConstructionRoundStepSyntax.mapFields_freeClosed,ConstructionRoundStepSyntax.profiles_freeClosed]

theorem homs_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w Q J S : Fin m) :
    Project.Formula.satisfies env (homs w Q J S) ↔ Homs hM (env.bound w) (env.bound Q) (env.bound J) (env.bound S) := by
  simp only [homs,Homs,Project.Formula.satisfies_forall_iff,
    Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,ConstructionTowerTransitions.before_semantics hM,ConstructionTowerHistory.row_semantics hM,ConstructionRoundStepSyntax.mapFields_semantics hM,ConstructionRoundStepSyntax.profiles_semantics hM]
  rfl


def composition {m : Nat} (J S : Fin m) : Project.Formula 1 m :=
  (.forallE (.forallE (.forallE (.forallE (.forallE (.forallE (.forallE (.forallE (.imp (.mem (.bound (7 : Fin
  (m+8))) (.bound J.succ.succ.succ.succ.succ.succ.succ.succ)) (.imp (.mem (.bound (6 : Fin (m+8))) (.bound
  J.succ.succ.succ.succ.succ.succ.succ.succ)) (.imp (.mem (.bound (5 : Fin (m+8))) (.bound
  J.succ.succ.succ.succ.succ.succ.succ.succ)) (.imp (ConstructionTowerTransitions.before (7 : Fin (m+8)) (6
  : Fin (m+8))) (.imp (ConstructionTowerTransitions.before (6 : Fin (m+8)) (5 : Fin (m+8))) (.imp
  (ConstructionTowerHistory.field 6 S.succ.succ.succ.succ.succ.succ.succ.succ (6 : Fin (m+8)) (4 : Fin
  (m+8))) (.imp (ConstructionTowerHistory.field 6 S.succ.succ.succ.succ.succ.succ.succ.succ (5 : Fin (m+8))
  (3 : Fin (m+8))) (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge (4 : Fin (m+8)) (7 : Fin (m+8))
  (2 : Fin (m+8)))) (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge (3 : Fin (m+8)) (6 : Fin (m+8))
  (1 : Fin (m+8)))) (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge (3 : Fin (m+8)) (7 : Fin (m+8))
  (0 : Fin (m+8)))) (ConstructionProbeMappedPathSyntax.nodeMap (2 : Fin (m+8)) (1 : Fin (m+8)) (0 : Fin
  (m+8)))))))))))))))))))))

theorem composition_freeClosed {m : Nat} (J S : Fin m) :
    (composition J S).FreeClosed := by
  simp -implicitDefEqProofs [composition,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,ConstructionTowerTransitions.before_freeClosed,ConstructionTowerHistory.field_freeClosed,ConstructionProbeMappedPathSyntax.nodeMap_freeClosed]

theorem composition_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (J S : Fin m) :
    Project.Formula.satisfies env (composition J S) ↔ Composition (env.bound J) (env.bound S) := by
  simp only [composition,Composition,Project.Formula.satisfies_forall_iff,
    Project.Formula.satisfies_imp_iff,
    Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,ConstructionTowerTransitions.before_semantics hM,ConstructionTowerHistory.field_semantics hM,ConstructionProbeMappedPathSyntax.nodeMap_semantics hM]
  rfl


def natural {m : Nat} (J S : Fin m) : Project.Formula 1 m :=
  (.forallE (.forallE (.forallE (.forallE (.forallE (.forallE (.imp (.mem (.bound (5 : Fin (m+6))) (.bound
  J.succ.succ.succ.succ.succ.succ)) (.imp (.mem (.bound (4 : Fin (m+6))) (.bound
  J.succ.succ.succ.succ.succ.succ)) (.imp (ConstructionTowerTransitions.before (5 : Fin (m+6)) (4 : Fin
  (m+6))) (.imp (ConstructionTowerHistory.field 7 S.succ.succ.succ.succ.succ.succ (5 : Fin (m+6)) (3 : Fin
  (m+6))) (.imp (ConstructionTowerHistory.field 7 S.succ.succ.succ.succ.succ.succ (4 : Fin (m+6)) (2 : Fin
  (m+6))) (.imp (ConstructionTowerHistory.field 6 S.succ.succ.succ.succ.succ.succ (4 : Fin (m+6)) (1 : Fin
  (m+6))) (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge (1 : Fin (m+6)) (5 : Fin (m+6)) (0 : Fin
  (m+6)))) (ConstructionProbeMappedPathSyntax.nodeMap (3 : Fin (m+6)) (0 : Fin (m+6)) (2 : Fin
  (m+6))))))))))))))))

theorem natural_freeClosed {m : Nat} (J S : Fin m) :
    (natural J S).FreeClosed := by
  simp -implicitDefEqProofs [natural,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,ConstructionTowerTransitions.before_freeClosed,ConstructionTowerHistory.field_freeClosed,ConstructionProbeMappedPathSyntax.nodeMap_freeClosed]

theorem natural_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (J S : Fin m) :
    Project.Formula.satisfies env (natural J S) ↔ Natural (env.bound J) (env.bound S) := by
  simp only [natural,Natural,Project.Formula.satisfies_forall_iff,
    Project.Formula.satisfies_imp_iff,
    Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,ConstructionTowerTransitions.before_semantics hM,ConstructionTowerHistory.field_semantics hM,ConstructionProbeMappedPathSyntax.nodeMap_semantics hM]
  rfl


def valid {m : Nat} (w Q R top D mul e mark H C J S : Fin m) : Project.Formula 1 m :=
  (.conj (ConstructionTowerHistory.records J S) (.conj (.forallE (.imp (.mem (.bound (0 : Fin (m+1))) (.bound
  J.succ)) (stage w.succ Q.succ R.succ top.succ D.succ mul.succ e.succ mark.succ H.succ C.succ S.succ (0 :
  Fin (m+1))))) (.conj (homs w Q J S) (.conj (composition J S) (natural J S)))))

theorem valid_freeClosed {m : Nat} (w Q R top D mul e mark H C J S : Fin m) :
    (valid w Q R top D mul e mark H C J S).FreeClosed := by
  simp -implicitDefEqProofs [valid,Definitional.Formula.FreeClosed,ConstructionTowerHistory.records_freeClosed,stage_freeClosed,homs_freeClosed,composition_freeClosed,natural_freeClosed]

theorem valid_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w Q R top D mul e mark H C J S : Fin m) :
    Project.Formula.satisfies env (valid w Q R top D mul e mark H C J S) ↔ Valid hM (env.bound w) (env.bound Q) (env.bound R) (env.bound top) (env.bound D) (env.bound mul) (env.bound e) (env.bound mark) (env.bound H) (env.bound C) (env.bound J) (env.bound S) := by
  simp only [valid,Valid,Project.Formula.satisfies_forall_iff,
    Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    ConstructionTowerHistory.records_semantics hM,stage_semantics hM,homs_semantics hM,composition_semantics hM,natural_semantics hM]
  rfl


end PPAC.Migration.ConstructionTowerValidity
