/- Pinned SliceAssembly.presentation_reverse_injection:161-191.
Compose the ACTUAL source candidate function with the existing support
intersection and full assemble. Reuse existing binder/graph transports. -/
import PPAC.Migration.ForcingSliceAssembly

namespace PPAC.Migration.ForcingSlicePresentation
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open Source (Formula)
open Source.SetLanguage (args1 args2 args3)
open ForcingMapConditions (MapRel)
open ForcingFormula (Force)
open ForcingProductFamily (Presentation actionFormula)
open ForcingProductSymmetry (orderFormula orderFormula_semantics)
open ForcingPairUnion (domain domain_semantics)
open ForcingHS (HS)
open ForcingSupportedNames (Supported)
open ForcingSliceCandidate (unary_reindex four_map selected_transport separated_transport graph_transport)
open ForcingNonwellorderableImage (force_reindex pre_reindex)
open ForcingConcreteSystem (forcingRho)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 65536
set_option maxHeartbeats 400000
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

private abbrev MapForce {k : Nat} (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k)
    (G F mul : Fin k) (f X Y p : M.Carrier .set) (phi : Formula 3) : Prop :=
  Force (orderFormula (rho 0) mul) (domain rho G F) env (args3 f X Y) (env (rho 6)) p phi

private abbrev coreRho {k : Nat} (root : Fin 40 → Fin k) : Fin 7 → Fin k := fun j => root (forcingRho j)

/-- Bind the newly constructed condition/support/candidate-function while
retaining the SAME raw two-name parameters and constructor equations.
Only pull back the actual ParameterSpec; no parameter function is built. -/
theorem parameter_pullback {k l : Nat} (env : Fin k → M.Carrier .set) (other : Fin l → M.Carrier .set)
    (base : Fin k → Fin l) (he : ∀ j, other (base j) = env j) (rho : Fin 7 → Fin k)
    (G F S mul top O f s A X Y : Fin k) {i : M.Carrier .set} {v : Fin 2 → M.Carrier .set}
    (h : ForcingUniformMaximum.ParameterSpec other
      (ForcingSliceParameters.parameterFormula (fun j => base (rho j)) (base G) (base F) (base S) (base mul) (base top)
        (base O) (base f) (base s) (base A) (base X) (base Y)) i v) :
    ForcingUniformMaximum.ParameterSpec env (ForcingSliceParameters.parameterFormula rho G F S mul top O f s A X Y) i v := by
  obtain ⟨ci,hCi,Bi,hBi,hFixBi,hB,hYi,hFixYi,hYP,hSi,hFixSi,hSP⟩ :=
    (ForcingSliceParameters.parameter_spec_iff other (fun j => base (rho j)) (base G) (base F) (base S) (base mul) (base top)
      (base O) (base f) (base s) (base A) (base X) (base Y) i v).mp h
  let e1 : Fin (k+2) → M.Carrier .set := Fin.lastCases ci (Fin.lastCases i env)
  let e2 : Fin (l+2) → M.Carrier .set := Fin.lastCases ci (Fin.lastCases i other)
  let up1 : Fin k → Fin (k+2) := fun j => j.castSucc.castSucc
  let up2 : Fin l → Fin (l+2) := fun j => j.castSucc.castSucc
  let rr1 : Fin 7 → Fin (k+2) := fun j => up1 (rho j)
  let rr2 : Fin 7 → Fin (l+2) := fun j => up2 (base (rho j))
  let lift : Fin (k+2) → Fin (l+2) := Fin.lastCases (Fin.last (l+1))
    (Fin.lastCases (Fin.last l).castSucc (fun j => up2 (base j)))
  have hl (j : Fin (k+2)) : e2 (lift j) = e1 j := by
    refine Fin.lastCases ?_ (fun j => ?_) j
    · simp only [e1,e2,lift,Fin.lastCases_last]
    · refine Fin.lastCases ?_ (fun j => ?_) j
      · simp only [e1,e2,lift,Fin.lastCases_castSucc,Fin.lastCases_last]
      · simp only [e1,e2,lift,up2,Fin.lastCases_castSucc,he]
  have hbase (j : Fin k) : lift (up1 j) = up2 (base j) := by simp only [lift,up1,Fin.lastCases_castSucc]
  have hi : lift (Fin.last k).castSucc = (Fin.last l).castSucc := by simp only [lift,Fin.lastCases_castSucc,Fin.lastCases_last]
  have hc : lift (Fin.last (k+1)) = Fin.last (l+1) := by simp only [lift,Fin.lastCases_last]
  have hR (a b : M.Carrier .set) : MapRel (orderFormula (rr1 0) (up1 mul)) e1 a b ↔
      MapRel (orderFormula (rr2 0) (up2 (base mul))) e2 a b := by
    simp only [orderFormula_semantics,rr1,rr2,e1,e2,up1,up2,Fin.lastCases_castSucc,he]
  have hH (a : M.Carrier .set) : ForcingClassEvaluation.Predicate (domain rr1 (up1 G) (up1 F)) e1 a ↔
      ForcingClassEvaluation.Predicate (domain rr2 (up2 (base G)) (up2 (base F))) e2 a := by
    simp only [domain_semantics,rr1,rr2,e1,e2,up1,up2,Fin.lastCases_castSucc,he]
  have hQB (p x : M.Carrier .set) : MapRel
      (ForcingSliceGeometry.BPredicate rr1 (up1 G) (up1 F) (up1 mul) (up1 s) (up1 A) (up1 X) (Fin.last (k+1))) e1 p x ↔
      MapRel (ForcingSliceGeometry.BPredicate rr2 (up2 (base G)) (up2 (base F)) (up2 (base mul))
        (up2 (base s)) (up2 (base A)) (up2 (base X)) (Fin.last (l+1))) e2 p x := by
    simpa only [ForcingSliceGeometry.BPredicate,four_map,rr1,rr2,hbase,hc] using
      unary_reindex e1 e2 lift hl rr1 (up1 G) (up1 F) (up1 mul)
        (ForcingSliceGeometry.four (up1 s) (up1 A) (up1 X) (Fin.last (k+1))) ForcingSliceGeometry.bFormula p x
  have hQY (p x : M.Carrier .set) : MapRel
      (ForcingSliceGeometry.YPredicate rr1 (up1 G) (up1 F) (up1 mul) (up1 top) (up1 O) (up1 f) (up1 s) (up1 A) (up1 X) (up1 Y) (Fin.last k).castSucc) e1 p x ↔
      MapRel (ForcingSliceGeometry.YPredicate rr2 (up2 (base G)) (up2 (base F)) (up2 (base mul)) (up2 (base top))
        (up2 (base O)) (up2 (base f)) (up2 (base s)) (up2 (base A)) (up2 (base X)) (up2 (base Y)) (Fin.last l).castSucc) e2 p x := by
    simp only [ForcingSliceGeometry.yPredicate_semantics]
    simpa only [rr1,rr2,hbase,e1,e2,Fin.lastCases_castSucc,Fin.lastCases_last,he] using
      ForcingSliceCoverage.at_reindex e1 e2 lift hl rr1 (up1 G) (up1 F) (up1 mul) (up1 top) (up1 O)
        (up1 f) (up1 s) (up1 A) (up1 X) (up1 Y) p x i
  apply (ForcingSliceParameters.parameter_spec_iff env rho G F S mul top O f s A X Y i v).mpr
  refine ⟨ci,?_,Bi,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · simpa only [he] using hCi
  · simpa only [he] using hBi
  · simpa only [he] using hFixBi
  · simpa only [he] using selected_transport (fun a b => (hR a b).symm) (fun p x => (hQB p x).symm) hB
  · simpa only [he] using hYi
  · simpa only [he] using hFixYi
  · simpa only [he] using selected_transport (fun a b => (hR a b).symm) (fun p x => (hQY p x).symm) hYP
  · simpa only [he] using hSi
  · simpa only [he] using hFixSi
  · simpa only [he] using separated_transport (fun a b => (hR a b).symm) (fun a => (hH a).symm) hSP

/-- Exact pinned source composition: actual candidate function, actual support
intersection and full actual graph assembly. No candidate family or new
common support is supplied; the original SliceData parent support is retained. -/
theorem presentation_reverse_injection (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    (hOrder : Project.Gw_order_d (InnerModel.Js_lt_d (M := Project.FirstOrderSemantics.reduct M)))
    (hChoice : ConstructionDirectedCardinality.Choice (M := M))
    (env : Fin k → M.Carrier .set) (root : Fin 40 → Fin k)
    (S f s X Y O checkedO Cart : Fin k)
    (hCore : ForcingConcreteSystem.Core hM (fun j => env (root j)))
    (hS : ForcingConjugationGraph.Subgroup (env (root 27)) (env (root 34)) (env S))
    (hSF : (Project.FirstOrderSemantics.reduct M).mem (env S) (env (root 35)))
    (hOrd : ForcingRawRank.Ordinal (env O))
    (hNames : ∀ j, HS actionFormula (fun a => env (coreRho root a)) (env (root 34)) (env (coreRho root 6)) (env (root 35))
      (env (ForcingMapCalculus.five f s (root 37) X Y j)))
    (hFixed : ∀ j, ForcingSupportedNames.Supported (fun a => env (coreRho root a)) (env S)
      (env (ForcingMapCalculus.five f s (root 37) X Y j)))
    {p : M.Carrier .set}
    (hO : ForcingCheckName.Checked (env (root 1)) (env O) (env checkedO))
    (hCart : ForcingRelationGraph.Graph (orderFormula (coreRho root 0) (root 18)) ForcingCompletionGraph.trueRelation
      env (coreRho root 6) (root 1) (root 37) checkedO (env Cart))
    (hp : (Project.FirstOrderSemantics.reduct M).mem p (env (coreRho root 6)))
    (hs : MapForce env (coreRho root) (root 34) (root 35) (root 18) (env s) (env Cart) (env X) p (Source.SetLanguage.surjection 0 1 2))
    (hf : MapForce env (coreRho root) (root 34) (root 35) (root 18) (env f) (env X) (env Y) p (Source.SetLanguage.surjection 0 1 2)) :
    ForcingWellorderedTarget.Result env (coreRho root) (root 34) (root 35) (root 18) (env X) (env Y) p := by
  obtain ⟨q,Hq,choices,hq,hqp,hHq,hHqF,hChoices,hSelected⟩ := ForcingSliceCandidate.candidate_family hM hOrder hChoice
    env root S f s X Y O checkedO Cart hCore hS hSF hNames hFixed hO hCart hp hs hf
  have hCoreSaved := hCore
  obtain ⟨_ho,hm0,_hj,hPres0,hG,hFilter,hw,hMu,_hI,_hD,_hMergers,_hRow,_hc,ht,_rest⟩ := hCoreSaved
  have hPres : Presentation (env (coreRho root 0)) (env (root 27)) (env (root 14)) (env (root 3)) (env (root 39))
      (env (coreRho root 1)) (env (coreRho root 2)) (env (coreRho root 3)) (env (coreRho root 4)) (env (coreRho root 5)) (env (coreRho root 6)) := by
    simpa only [coreRho,forcingRho] using hPres0
  have hm : ForcingDiagramPoset.LeftCancelMonoid (env (coreRho root 0)) (env (root 18)) (env (root 19)) := by
    simpa only [coreRho,forcingRho] using hm0
  have hNormal := ForcingNormalFilter.is_normal hM hw hMu hG hFilter
  have hpre := ForcingProductPoset.preorder env (coreRho root 0) (root 18) (coreRho root 6) hm
    hPres.2.2.2.2.1 hPres.2.2.2.1 hPres.2.2.2.2.2
  obtain ⟨common,hCommon⟩ := KP.intersection_exists_d (ZF.modelsKP (ModelTransfer.project_models_iff.mp hM)) (env S) Hq
  have hCommonGroup := ForcingSupportIntersection.subgroup_intersection hM hG hS hHq hCommon
  have hCommonF := hNormal.2.2.1 (env S) Hq common hSF hHqF hCommon
  let e : Fin (k+3) → M.Carrier .set := Fin.lastCases common (Fin.lastCases choices (Fin.lastCases q env))
  let up : Fin k → Fin (k+3) := fun j => j.castSucc.castSucc.castSucc
  let rr : Fin 7 → Fin (k+3) := fun j => up (coreRho root j)
  let qi : Fin (k+3) := (Fin.last k).castSucc.castSucc
  let ci : Fin (k+3) := (Fin.last (k+1)).castSucc
  let Hi : Fin (k+3) := Fin.last (k+2)
  have he (j : Fin k) : e (up j) = env j := by simp only [e,up,Fin.lastCases_castSucc]
  have eq : e qi = q := by simp only [e,qi,Fin.lastCases_castSucc,Fin.lastCases_last]
  have ec : e ci = choices := by simp only [e,ci,Fin.lastCases_castSucc,Fin.lastCases_last]
  have eH : e Hi = common := by simp only [e,Hi,Fin.lastCases_last]
  have hR (a b : M.Carrier .set) : MapRel (orderFormula (coreRho root 0) (root 18)) env a b ↔
      MapRel (orderFormula (rr 0) (up (root 18))) e a b := by simp only [orderFormula_semantics,rr,he]
  have hTuple (j : Fin 5) : e (ForcingMapCalculus.five (up f) (up s) (up (root 37)) (up X) (up Y) j) =
      env (ForcingMapCalculus.five f s (root 37) X Y j) := by
    exact Fin.cases (he f) (Fin.cases (he s) (Fin.cases (he (root 37)) (Fin.cases (he X) (Fin.cases (he Y) (fun t => Fin.elim0 t))))) j
  have hNames' (j : Fin 5) : HS actionFormula (fun a => e (rr a)) (e (up (root 34))) (e (rr 6)) (e (up (root 35)))
      (e (ForcingMapCalculus.five (up f) (up s) (up (root 37)) (up X) (up Y) j)) := by
    simpa only [rr,he,hTuple] using hNames j
  have hFixed' (j : Fin 5) : Supported (fun a => e (rr a)) (e (up S))
      (e (ForcingMapCalculus.five (up f) (up s) (up (root 37)) (up X) (up Y) j)) := by
    simpa only [rr,he,hTuple] using hFixed j
  have hCart' : ForcingRelationGraph.Graph (orderFormula (rr 0) (up (root 18))) ForcingCompletionGraph.trueRelation
      e (rr 6) (up (root 1)) (up (root 37)) (up checkedO) (e (up Cart)) := by
    rw [he]
    apply graph_transport env e (coreRho root 6) (root 1) (root 37) checkedO (rr 6) (up (root 1)) (up (root 37)) (up checkedO)
      (by simp only [rr,he]) (he (root 1)) (he (root 37)) (he checkedO) hR ?_ hCart
    intro p' x y
    simp only [ForcingRelationGraphForcing.Holds,ForcingCompletionGraph.trueRelation,Formula.Realize]
  have hCandidates : ∀ i c, (Project.FirstOrderSemantics.reduct M).mem i (e (up O)) → PureKuratowski.PairMember M i c (e ci) →
      ForcingUniformMaximum.Selected e rr (up (root 34)) (up (root 35)) (up (root 18)) (e Hi) (e qi)
        (ForcingSliceParameters.parameterFormula rr (up (root 34)) (up (root 35)) (up S) (up (root 18)) (up (root 1))
          (up O) (up f) (up s) (up (root 37)) (up X) (up Y)) (Source.SetLanguage.injection 2 0 1) i c := by
    intro i c _hi hc
    have hSel := hSelected i c (by simpa only [ec] using hc)
    refine ⟨?_,?_,?_⟩
    · simpa only [rr,he] using hSel.1
    · intro pi hpi act hAct
      have hFix := hSel.2.1 pi ((hCommon pi).mp (by simpa only [eH] using hpi)).2 act
        (by simpa only [rr,he] using hAct)
      simpa only [rr,he] using hFix
    · intro v hv
      have hParam := parameter_pullback env e up he (coreRho root) (root 34) (root 35) S (root 18) (root 1) O f s (root 37) X Y hv
      have hForce := (force_reindex env e up he (coreRho root) (root 34) (root 35) (root 18)
        (Source.SetLanguage.injection 2 0 1) (Fin.lastCases c v) q).mp (hSel.2.2 v hParam)
      simpa only [rr,he,eH,eq] using hForce
  obtain ⟨graph,_hGraph,hGraphHS,_hGraphFix,hGraphForce⟩ := ForcingSliceAssembly.assemble hM e rr
    (up (root 27)) (up (root 14)) (up (root 3)) (up (root 39)) (up (root 34)) (up (root 35)) (up S) Hi (up (root 18)) (up (root 1))
    (up O) (up f) (up s) (up (root 37)) (up X) (up Y) (up checkedO) (up Cart) ci qi
    (by simpa only [rr,he] using hPres) (by simpa only [he] using hG) (by simpa only [he] using hNormal)
    (by simpa only [he] using hS) (by simpa only [he] using hSF)
    (by simpa only [he,eH] using hCommonGroup) (by simpa only [he,eH] using hCommonF)
    (by intro pi hpi; simpa only [he] using ((hCommon pi).mp (by simpa only [eH] using hpi)).1)
    (by simpa only [he] using ht) (pre_reindex env e up he (coreRho root) (root 18) hpre) hNames' hFixed'
    (by simpa only [he] using hOrd) (by simpa only [he] using hO) hCart'
    (by simpa only [he,ec] using hChoices) hCandidates (by simpa only [rr,he,eq] using hq)
    (by simpa only [rr,he,eq] using ((force_reindex env e up he (coreRho root) (root 34) (root 35) (root 18)
      (Source.SetLanguage.surjection 0 1 2) (args3 (env s) (env Cart) (env X)) q).mp
        (ForcingFormula.mono hM hpre _ _ hp hq hqp hs)))
    (by simpa only [rr,he,eq] using ((force_reindex env e up he (coreRho root) (root 34) (root 35) (root 18)
      (Source.SetLanguage.surjection 0 1 2) (args3 (env f) (env X) (env Y)) q).mp
        (ForcingFormula.mono hM hpre _ _ hp hq hqp hf)))
  refine ⟨q,hq,hqp,graph,?_,?_⟩
  · simpa only [rr,he] using hGraphHS
  · apply (force_reindex env e up he (coreRho root) (root 34) (root 35) (root 18)
      (Source.SetLanguage.injection 0 1 2) (args3 graph (env Y) (env X)) q).mpr
    simpa only [rr,he,eq] using hGraphForce

private theorem core_renamed_semantics (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    (env : Env (Project.FirstOrderSemantics.reduct M) k) (root : Fin 40 → Fin k) :
    Project.Formula.satisfies env (ForcingConcreteSystem.coreFormula.rename root) ↔
      ForcingConcreteSystem.Core hM (fun j => env.bound (root j)) := by
  rw [Project.Formula.satisfies_rename]
  exact ForcingConcreteSystem.coreFormula_semantics hM _

private theorem args3_map {k : Nat} (env : Fin k → M.Carrier .set) (f X Y : Fin k) :
    (fun j => env (args3 f X Y j)) = args3 (env f) (env X) (env Y) := by
  funext j
  exact Fin.cases rfl (Fin.cases rfl (Fin.cases rfl (fun t => Fin.elim0 t))) j

/-- Fixed source presentation reverse injection on the SAME actual Core.
The constructed candidate function, support intersection and graph are all
existentially eliminated, retaining every original condition and HS parent. -/
def sentence {k : Nat} (root : Fin 40 → Fin k) (S f s X Y O checkedO Cart p : Fin k) : Project.Sentence where
  formula :=
    let rho := coreRho root
    Project.Formula.forallClosure k
      ([ForcingConcreteSystem.coreFormula.rename root,
        ProjectSyntax.encode id (ForcingConjugationGraph.subgroup (root 27) (root 34) S),
        .mem (.bound S) (.bound (root 35)),
        ProjectSyntax.encode id (ForcingHS.hs actionFormula rho (root 34) (rho 6) (root 35) f),
        ProjectSyntax.encode id (ForcingHS.hs actionFormula rho (root 34) (rho 6) (root 35) s),
        ProjectSyntax.encode id (ForcingHS.hs actionFormula rho (root 34) (rho 6) (root 35) (root 37)),
        ProjectSyntax.encode id (ForcingHS.hs actionFormula rho (root 34) (rho 6) (root 35) X),
        ProjectSyntax.encode id (ForcingHS.hs actionFormula rho (root 34) (rho 6) (root 35) Y),
        ProjectSyntax.encode id (ForcingSupportingRoot.tupleSupported rho S (ForcingMapCalculus.five f s (root 37) X Y)),
        ProjectSyntax.encode id (OrdinalSyntax.ordinal O),
        ProjectSyntax.encode id (ForcingCheckName.checkName (root 1) O checkedO),
        ProjectSyntax.encode id (ForcingRelationGraph.graph (orderFormula (rho 0) (root 18)) ForcingCompletionGraph.trueRelation id
          (rho 6) (root 1) (root 37) checkedO Cart),
        .mem (.bound p) (.bound (rho 6)),
        ProjectSyntax.encode id (ForcingFormula.formula (orderFormula (rho 0) (root 18)) (domain rho (root 34) (root 35)) id
          (args3 s Cart X) (rho 6) p (Source.SetLanguage.surjection 0 1 2)),
        ProjectSyntax.encode id (ForcingFormula.formula (orderFormula (rho 0) (root 18)) (domain rho (root 34) (root 35)) id
          (args3 f X Y) (rho 6) p (Source.SetLanguage.surjection 0 1 2))].foldr Definitional.Formula.imp
        (ProjectSyntax.encode id (ForcingWellorderedTarget.resultFormula rho (root 34) (root 35) (root 18) X Y p)))
  freeClosed := by
    simp -implicitDefEqProofs [List.foldr,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
      Definitional.Formula.freeClosed_rename,ForcingConcreteSystem.coreFormula_freeClosed]

theorem models {k : Nat} (root : Fin 40 → Fin k) (S f s X Y O checkedO Cart p : Fin k)
    (hM : FirstOrder.Theory.Models M nativeZF)
    (hOrder : Project.Gw_order_d (InnerModel.Js_lt_d (M := Project.FirstOrderSemantics.reduct M)))
    (hChoice : ConstructionDirectedCardinality.Choice (M := M)) :
    (Project.fo_sentence (sentence root S f s X Y O checkedO Cart p)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM),SetTheory.Structure.satisfiesSentence_iff]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro env
  simp only [List.foldr,Project.Formula.satisfies_imp_iff,
    Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,core_renamed_semantics hM,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),ForcingConjugationGraph.subgroup_semantics,
    ForcingHS.hs_semantics,ForcingSupportingRoot.tupleSupported_semantics,ForcingRawRank.ordinal_semantics,ForcingCheckName.checkName_semantics,
    ForcingRelationGraph.graph_semantics,ForcingFormula.formula_semantics,
    ForcingWellorderedTarget.resultFormula_semantics,id_eq,args3_map]
  intro hCore hS hSF hfHS hsHS hAHS hXHS hYHS hFixed hOrd hO hCart hp hs hf
  have hNames : ∀ j, HS actionFormula (fun a => env (coreRho root a)) (env (root 34)) (env (coreRho root 6)) (env (root 35))
      (env (ForcingMapCalculus.five f s (root 37) X Y j)) := by
    intro j
    exact Fin.cases hfHS (Fin.cases hsHS (Fin.cases hAHS (Fin.cases hXHS (Fin.cases hYHS (fun t => Fin.elim0 t))))) j
  exact presentation_reverse_injection hM hOrder hChoice env root S f s X Y O checkedO Cart hCore hS hSF hOrd
    hNames hFixed hO hCart hp hs hf

/-- Ordinary nativeZF original-kernel derivation. The SAME completed L
interpretation discharges both background Choice and the L-order; neither
is an added external assumption of this object theorem. -/
theorem kernel_certificate {k : Nat} (root : Fin 40 → Fin k) (S f s X Y O checkedO Cart p : Fin k) :
    FirstOrder.Derives nativeZF [] (Project.fo_sentence (ConstructibleGround.relative
      (sentence root S f s X Y O checkedO Cart p))) := by
  apply ModelTransfer.derives
  intro N hN
  have hL := ConstructibleSource.model_zf hN
  have hRawChoice := (Project.FirstOrderSemantics.sentence_correct
    (ModelTransfer.extensionality hL) Axioms.choice).mp (ConstructibleSource.model_choice hN)
  obtain ⟨witness,_⟩ := ZF.exists_omega (ModelTransfer.project_models_iff.mp hL)
  let env : Env (Project.FirstOrderSemantics.reduct (ConstructibleSource.model hN)) 0 := ⟨Fin.elim0,fun _ => witness⟩
  have hSat : Project.Formula.satisfies env (ConstructionDirectedCardinality.choice (m := 0)) := by
    change Project.Formula.satisfies env (Axioms.choice.formula.rename Fin.elim0)
    rw [Project.Formula.satisfies_rename]
    exact hRawChoice env.free
  have hChoice := (ConstructionDirectedCardinality.choice_semantics hL env).mp hSat
  apply ConstructibleGround.relative_models hN
  exact (Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hL) _).mp
    (models root S f s X Y O checkedO Cart p hL (ConstructionRoundSelection.l_order hN) hChoice)


end PPAC.Migration.ForcingSlicePresentation
