/- Pinned ConstructionIteration limit case / Round.underFunctor:
instantiate the EXISTING canonical Under-base producer using the ACTUAL
record-history tables, with every weighted diagram premise derived from
pointwise validity. No given diagram/tower/limit in the public constructor. -/
import PPAC.Migration.ConstructionTowerDiagram

namespace PPAC.Migration.ConstructionTowerHistoryLimit
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ConstructionTowerValidity (Valid)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}
variable {w Q R top D mul e mark H C J S zero : M.Carrier .set}

def Value (hM : FirstOrder.Theory.Models M nativeZF)
    (w Q R top D mul e mark H C J S zero output : M.Carrier .set) : Prop :=
  ∃ Domains Muls Units Marks Heights Costs Incoming Origins Times E P F,
    ConstructionTowerHistory.Charts J S Domains Muls Units Marks Heights Costs Incoming Origins Times ∧
    ConstructionTowerTransitions.Order J E ∧ ConstructionTowerTransitions.Matrix J S zero P F ∧
    ConstructionTowerCanonicalLimit.Value hM J E Domains F Muls Units w Q R top Heights Costs Marks Origins
      D mul e mark H C output

theorem exists_value (hM : FirstOrder.Theory.Models M nativeZF)
    (hV : Valid hM w Q R top D mul e mark H C J S)
    (hJ : (Project.FirstOrderSemantics.reduct M).IsOrdinal J)
    (hne : ∃ i, (Project.FirstOrderSemantics.reduct M).mem i J)
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hQ : ConstructionFractionOrder.Carrier w Q)
    (hR : ConstructionRealCuts.CutCarrier hM w Q R) (hTop : ConstructionRealCuts.Cut hM w Q top)
    (zero : M.Carrier .set) :
    ∃ output, Value hM w Q R top D mul e mark H C J S zero output := by
  obtain ⟨Domains,Muls,Units,Marks,Heights,Costs,Incoming,Origins,Times,E,P,F,hCharts,hE,hF,hData⟩ :=
    ConstructionTowerDiagram.exists_data hM zero hJ hV
  obtain ⟨hIndex,hT,hFam,hHom,hCons,hWH,hWC,hSH,hSC,hHB,hCB,hUniform,hSup,hCon,hJoins,
    hMarks,hMarkStable,hProfiles,hOrigins,hNat,hOP⟩ := hData
  obtain ⟨output,hValue,_⟩ := ConstructionTowerCanonicalLimit.exists_value hM
    J E Domains F Muls Units w Q R top Heights Costs Marks Origins D mul e mark H C
    hne hIndex hT hFam hHom hCons hw hQ hR hTop hWH hWC hSH hSC hHB hCB hUniform hSup
    hCon hJoins hMarks hMarkStable hProfiles hOrigins hNat hOP hJ
  exact ⟨output,Domains,Muls,Units,Marks,Heights,Costs,Incoming,Origins,Times,E,P,F,hCharts,hE,hF,hValue⟩

theorem value_unique (hM : FirstOrder.Theory.Models M nativeZF)
    (hV : Valid hM w Q R top D mul e mark H C J S)
    (hJ : (Project.FirstOrderSemantics.reduct M).IsOrdinal J)
    (hne : ∃ i, (Project.FirstOrderSemantics.reduct M).mem i J)
    {x y : M.Carrier .set}
    (hx : Value hM w Q R top D mul e mark H C J S zero x)
    (hy : Value hM w Q R top D mul e mark H C J S zero y) : x = y := by
  obtain ⟨Domains,Muls,Units,Marks,Heights,Costs,Incoming,Origins,Times,E,P,F,hCharts,hE,hF,hx⟩ := hx
  obtain ⟨Domains',Muls',Units',Marks',Heights',Costs',Incoming',Origins',Times',E',P',F',hCharts',hE',hF',hy⟩ := hy
  have hChartsCopy := hCharts
  obtain ⟨cD,cm,ce,ca,cH,cC,cI,cO,cT⟩ := hCharts
  obtain ⟨cD',cm',ce',ca',cH',cC',cI',cO',cT'⟩ := hCharts'
  have eqDomains := ConstructionTowerHistory.chart_unique hM 0 cD' cD
  subst Domains'
  have eqMuls := ConstructionTowerHistory.chart_unique hM 1 cm' cm
  subst Muls'
  have eqUnits := ConstructionTowerHistory.chart_unique hM 2 ce' ce
  subst Units'
  have eqMarks := ConstructionTowerHistory.chart_unique hM 3 ca' ca
  subst Marks'
  have eqHeights := ConstructionTowerHistory.chart_unique hM 4 cH' cH
  subst Heights'
  have eqCosts := ConstructionTowerHistory.chart_unique hM 5 cC' cC
  subst Costs'
  have eqIncoming := ConstructionTowerHistory.chart_unique hM 6 cI' cI
  subst Incoming'
  have eqOrigins := ConstructionTowerHistory.chart_unique hM 7 cO' cO
  subst Origins'
  have eqTimes := ConstructionTowerHistory.chart_unique hM 8 cT' cT
  subst Times'
  have eqE := ConstructionTowerTransitions.order_unique hM hE' hE
  subst E'
  obtain ⟨eqP,eqF⟩ := ConstructionTowerTransitions.matrix_unique hM hF' hF
  subst P'; subst F'
  have hData := ConstructionTowerDiagram.data_of_valid hM hJ hV hChartsCopy hE hF
  exact ConstructionTowerCanonicalLimit.value_unique hM hne hData.2.2.1 hx hy


def value {m : Nat} (w Q R top D mul e mark H C J S zero output : Fin m) : Project.Formula 1 m :=
  (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE
  (.existsE (.existsE (.conj (ConstructionTowerHistory.charts
  J.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  S.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (11 : Fin (m+12)) (10 : Fin (m+12)) (9 : Fin
  (m+12)) (8 : Fin (m+12)) (7 : Fin (m+12)) (6 : Fin (m+12)) (5 : Fin (m+12)) (4 : Fin (m+12)) (3 : Fin
  (m+12))) (.conj (ConstructionTowerTransitions.order
  J.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (2 : Fin (m+12))) (.conj
  (ConstructionTowerTransitions.matrix J.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  S.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  zero.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (1 : Fin (m+12)) (0 : Fin (m+12)))
  (ConstructionTowerCanonicalLimit.value J.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (2 :
  Fin (m+12)) (11 : Fin (m+12)) (0 : Fin (m+12)) (10 : Fin (m+12)) (9 : Fin (m+12))
  w.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  Q.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  R.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  top.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (7 : Fin (m+12)) (6 : Fin (m+12)) (8 : Fin
  (m+12)) (4 : Fin (m+12)) D.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  mul.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  e.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  mark.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  H.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  C.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ
  output.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ))))))))))))))))

theorem value_freeClosed {m : Nat} (w Q R top D mul e mark H C J S zero output : Fin m) :
    (value w Q R top D mul e mark H C J S zero output).FreeClosed := by
  simp -implicitDefEqProofs [value,Definitional.Formula.FreeClosed,ConstructionTowerHistory.charts_freeClosed,ConstructionTowerTransitions.order_freeClosed,ConstructionTowerTransitions.matrix_freeClosed,ConstructionTowerCanonicalLimit.value_freeClosed]

theorem value_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w Q R top D mul e mark H C J S zero output : Fin m) :
    Project.Formula.satisfies env (value w Q R top D mul e mark H C J S zero output) ↔ Value hM (env.bound w) (env.bound Q) (env.bound R) (env.bound top) (env.bound D) (env.bound mul) (env.bound e) (env.bound mark) (env.bound H) (env.bound C) (env.bound J) (env.bound S) (env.bound zero) (env.bound output) := by
  simp only [value,Value,Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_conj_iff,
    
    ConstructionTowerHistory.charts_semantics hM,ConstructionTowerTransitions.order_semantics hM,ConstructionTowerTransitions.matrix_semantics hM,ConstructionTowerCanonicalLimit.value_semantics hM]
  rfl

def constructionSentence : Project.Sentence where
  formula := (Project.Formula.forallClosure 13 (.imp (ConstructionTowerValidity.valid (0 : Fin 13) (1 : Fin 13) (2 :
    Fin 13) (3 : Fin 13) (4 : Fin 13) (5 : Fin 13) (6 : Fin 13) (7 : Fin 13) (8 : Fin 13) (9 : Fin 13) (10
    : Fin 13) (11 : Fin 13)) (.imp (Project.Formula.isOrdinal (.bound (10 : Fin 13))) (.imp (.existsE
    (.mem (.bound (0 : Fin 14)) (.bound (10 : Fin 13).succ))) (.imp (Project.Formula.isOmega (.bound (0 :
    Fin 13))) (.imp (ConstructionFractionOrder.carrier (0 : Fin 13) (1 : Fin 13)) (.imp
    (ConstructionRealCuts.cutCarrier (0 : Fin 13) (1 : Fin 13) (2 : Fin 13)) (.imp
    (ConstructionRealCuts.cut (0 : Fin 13) (1 : Fin 13) (3 : Fin 13)) (.existsE (.conj (value (0 : Fin
    13).succ (1 : Fin 13).succ (2 : Fin 13).succ (3 : Fin 13).succ (4 : Fin 13).succ (5 : Fin 13).succ (6
    : Fin 13).succ (7 : Fin 13).succ (8 : Fin 13).succ (9 : Fin 13).succ (10 : Fin 13).succ (11 : Fin
    13).succ (12 : Fin 13).succ (0 : Fin 14)) (.forallE (.imp (value (0 : Fin 13).succ.succ (1 : Fin
    13).succ.succ (2 : Fin 13).succ.succ (3 : Fin 13).succ.succ (4 : Fin 13).succ.succ (5 : Fin
    13).succ.succ (6 : Fin 13).succ.succ (7 : Fin 13).succ.succ (8 : Fin 13).succ.succ (9 : Fin
    13).succ.succ (10 : Fin 13).succ.succ (11 : Fin 13).succ.succ (12 : Fin 13).succ.succ (0 : Fin 15))
    (Project.Formula.extensionalEq (.bound (0 : Fin 15)) (.bound (1 : Fin 15)))))))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,
      ConstructionTowerValidity.valid_freeClosed,Project.Formula.isOrdinal,Project.Formula.isOmega,
      ConstructionFractionOrder.carrier_freeClosed,ConstructionRealCuts.cutCarrier_freeClosed,
      ConstructionRealCuts.cut_freeClosed,value_freeClosed,Project.Formula.extensionalEq]

theorem construction_models (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence constructionSentence).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) constructionSentence]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_forall_iff,
    Project.Formula.satisfies_isOrdinal_iff,Project.Formula.satisfies_isOmega_iff,
    Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    Project.Formula.satisfies_extensionalEq_iff_eq (ModelTransfer.extensionality hM),
    ConstructionTowerValidity.valid_semantics hM,ConstructionFractionOrder.carrier_semantics hM,
    ConstructionRealCuts.cutCarrier_semantics hM,ConstructionRealCuts.cut_semantics hM,value_semantics hM]
  intro hV hJ hne hw hQ hR hTop
  obtain ⟨output,hout⟩ := exists_value hM hV hJ hne hw hQ hR hTop (bound 12)
  exact ⟨output,hout,fun other hOther => value_unique hM hV hJ hne hOther hout⟩

theorem construction_kernel_certificate : FirstOrder.Derives nativeZF []
    (Project.fo_sentence constructionSentence) := ModelTransfer.derives (fun _ hM => construction_models hM)

end PPAC.Migration.ConstructionTowerHistoryLimit
