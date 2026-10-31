/- Pinned CellReorder.future_cut (182-251). Internal least-counterexample
induction over the actual timeline, using native Separation and its internal
wellorder. No host WellFounded, choice of a family, or assumed final Square.
Consumer: source future/reordered and then GermSelectors. -/
import PPAC.Migration.ConstructionFutureSelected

namespace PPAC.Migration.ConstructionFutureInduction
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ConstructionSelectedCellRestriction (Base)
open ConstructionUnionPushout (Square)
open ConstructionConservativeHull (Closure)
open ConstructionCellRestriction (Stages)
open ConstructionFutureFamily (CutAt Cuts Suprema Products)
open ConstructionFirstAppearance (Timeline Cover NewAt Index)
open ConstructionIntermediate (Sup)
open ForcingConditionGraphs (function_unique)
open ForcingDiagramPoset (LeftCancelMonoid Conical)
open ConstructionProbeSharedIntersections (ConditionalJoins)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

/-- The precise induction assertion on the actual two carrier families. -/
def Good (V GV e cuts futures A C GA GC ia ic b : M.Carrier .set) : Prop :=
  ∀ B F, PureKuratowski.PairMember M b B cuts → PureKuratowski.PairMember M b F futures →
    ∃ PB GB ib PF GF iF, Base V GV e B PB GB ib ∧ Base V GV e F PF GF iF ∧
      Square A B C F GA GB GC GF e ia ib ic

def goodFormula {m : Nat} (V GV e cuts futures A C GA GC ia ic b : Fin m) : Project.Formula 1 m :=
  (.forallE (.forallE (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge cuts.succ.succ b.succ.succ 1)) (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge futures.succ.succ b.succ.succ 0)) (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.conj (ConstructionSelectedCellRestriction.baseFormula V.succ.succ.succ.succ.succ.succ.succ.succ GV.succ.succ.succ.succ.succ.succ.succ.succ e.succ.succ.succ.succ.succ.succ.succ.succ 7 5 4 3) (.conj (ConstructionSelectedCellRestriction.baseFormula V.succ.succ.succ.succ.succ.succ.succ.succ GV.succ.succ.succ.succ.succ.succ.succ.succ e.succ.succ.succ.succ.succ.succ.succ.succ 6 2 1 0) (ConstructionUnionPushout.square A.succ.succ.succ.succ.succ.succ.succ.succ 7 C.succ.succ.succ.succ.succ.succ.succ.succ 6 GA.succ.succ.succ.succ.succ.succ.succ.succ 4 GC.succ.succ.succ.succ.succ.succ.succ.succ 1 e.succ.succ.succ.succ.succ.succ.succ.succ ia.succ.succ.succ.succ.succ.succ.succ.succ 3 ic.succ.succ.succ.succ.succ.succ.succ.succ)))))))))))))

theorem goodFormula_freeClosed {m : Nat} (V GV e cuts futures A C GA GC ia ic b : Fin m) :
    (goodFormula V GV e cuts futures A C GA GC ia ic b).FreeClosed := by
  simp -implicitDefEqProofs [goodFormula,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
    ConstructionSelectedCellRestriction.baseFormula_freeClosed,ConstructionUnionPushout.square_freeClosed]

theorem goodFormula_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (V GV e cuts futures A C GA GC ia ic b : Fin m) :
    Project.Formula.satisfies env (goodFormula V GV e cuts futures A C GA GC ia ic b) ↔ Good (env.bound V) (env.bound GV) (env.bound e) (env.bound cuts) (env.bound futures) (env.bound A) (env.bound C) (env.bound GA) (env.bound GC) (env.bound ia) (env.bound ic) (env.bound b) := by
  simp only [goodFormula,Good,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_imp_iff,
    Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,
    ConstructionSelectedCellRestriction.baseFormula_semantics hM,ConstructionUnionPushout.square_semantics hM]
  rfl

/-- Discharge all strict-earlier hypotheses using the actual internal
wellorder minimum of a pure-formula counterexample subset of I. -/
theorem all_good (hM : FirstOrder.Theory.Models M nativeZF)
    {w zero one V GV e I R bottom S index cells deps retained a
      cuts futures cutMuls futureMuls A C PA PC GA GC ia ic : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ z, ¬ (Project.FirstOrderSemantics.reduct M).mem z zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hv : LeftCancelMonoid V GV e) (hc : Conical V GV e) (hJ : ConditionalJoins V GV)
    (hStages : Stages V GV e S) (hRet : Closure V GV e retained)
    (hT : Timeline hM V I R bottom S) (hIndex : Index V I R bottom S index)
    (hCells : ConstructionStepCellSelection.Graph hM w zero one V GV e I R S cells)
    (hNew : ConstructionStepCellSelection.AtNew hM w zero one V GV e I R S cells)
    (hGlobal : ConstructionGlobalDependencies.Graph zero V I R bottom S index cells deps)
    (hClosed : ConstructionCountableConservativeHull.DependenciesClosed deps retained)
    (hCuts : Cuts I retained S cuts) (hFutures : Suprema I V GV e C cuts futures)
    (hCM : Products I GV cuts cutMuls) (hFM : Products I GV futures futureMuls)
    (hA : Base V GV e A PA GA ia) (hC : Base V GV e C PC GC ic)
    (ha : (Project.FirstOrderSemantics.reduct M).mem a I)
    (haC : PureKuratowski.PairMember M a C S) (haA : CutAt retained S a A) :
    ∀ b, (Project.FirstOrderSemantics.reduct M).mem b I →
      (a = b ∨ PureKuratowski.PairMember M a b R) → Good V GV e cuts futures A C GA GC ia ic b := by
  classical
  let N := Project.FirstOrderSemantics.reduct M
  have hSup : ∀ b B F, PureKuratowski.PairMember M b B cuts →
      PureKuratowski.PairMember M b F futures → Sup V GV e C B F := by
    intro b B F hbB hbF
    obtain ⟨B',hbB',hSF⟩ := ((hFutures.2 b F).mp hbF).2
    exact (function_unique hCuts.1 hbB' hbB) ▸ hSF
  have hInitial : Good V GV e cuts futures A C GA GC ia ic a := by
    intro B F hbB hbF
    have heB := ConstructionFutureFamily.cut_unique hM hT.2.1 ((hCuts.2 a B).mp hbB).2 haA
    subst B
    have hAC : ConstructionRealCuts.Subset A C := by
      obtain ⟨D,haD,hCut⟩ := haA
      have heD := function_unique hT.2.1 haD haC
      subst D
      exact fun x hx => ((hCut x).mp hx).2
    obtain ⟨hSupC,hSquare⟩ := ConstructionFutureCut.initial hM hv hc hJ hA hC hAC
    have heF := ConstructionFutureFamily.sup_unique hM (hSup a A F hbB hbF) hSupC
    subst F
    exact ⟨PA,GA,ia,PC,GC,ic,hA,hC,hSquare⟩
  let schema : Project.UnarySchema 13 := {
    body := .conj (ConstructionFutureLimit.closedLe 4 5 0)
      (.neg (goodFormula 1 2 3 6 7 8 9 10 11 12 13 0))
    freeClosed := by
      simp only [Definitional.Formula.FreeClosed,ConstructionFutureLimit.closedLe_freeClosed,goodFormula_freeClosed,and_self] }
  let env : SetTheory.Env N 13 := {
    bound := Fin.cases V (Fin.cases GV (Fin.cases e (Fin.cases R (Fin.cases a
      (Fin.cases cuts (Fin.cases futures (Fin.cases A (Fin.cases C (Fin.cases GA
      (Fin.cases GC (Fin.cases ia (fun _ => ic))))))))))))
    free := fun _ => V }
  have he b : schema.denote env b ↔ (a = b ∨ PureKuratowski.PairMember M a b R) ∧
      ¬ Good V GV e cuts futures A C GA GC ia ic b := by
    change Project.Formula.satisfies (env.push b) schema.body ↔ _
    simp only [schema,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_neg_iff,
      ConstructionFutureLimit.closedLe_semantics hM,goodFormula_semantics hM]
    rfl
  obtain ⟨bad,hbad⟩ := ZF.separation_exists_d (ModelTransfer.project_models_iff.mp hM) schema env I
  have hBad b : N.mem b bad ↔ N.mem b I ∧
      (a = b ∨ PureKuratowski.PairMember M a b R) ∧ ¬ Good V GV e cuts futures A C GA GC ia ic b :=
    (hbad b).trans (and_congr_right fun _ => he b)
  intro b hb hab
  apply Classical.byContradiction
  intro hnot
  obtain ⟨j,hj,hmin⟩ := hT.1.least bad (fun k hk => ((hBad k).mp hk).1)
    ⟨b,(hBad b).mpr ⟨hb,hab,hnot⟩⟩
  obtain ⟨hjI,haj,hNotJ⟩ := (hBad j).mp hj
  have hIH : ∀ k, N.mem k I → PureKuratowski.PairMember M k j R →
      (a = k ∨ PureKuratowski.PairMember M a k R) → Good V GV e cuts futures A C GA GC ia ic k := by
    intro k hk hkj hak
    apply Classical.byContradiction
    intro hnk
    rcases hmin k ((hBad k).mpr ⟨hk,hak,hnk⟩) with heq | hjk
    · have heq' := (ModelTransfer.extensionality hM).eq_of_same_members j k heq
      subst k
      exact hT.1.linear.2.1.1 j hjI hkj
    · exact hT.1.linear.2.1.1 j hjI (hT.1.linear.2.1.2 j hjI k hk j hjI hjk hkj)
  apply hNotJ
  rcases haj with heq | haj
  · exact heq ▸ hInitial
  have hne : j ≠ bottom := by
    intro heq
    rcases hT.2.2.2.1 a ha with heq' | hba
    · have heja : j = a := heq.trans heq'
      exact hT.1.linear.2.1.1 a ha (heja ▸ haj)
    · have hja : PureKuratowski.PairMember M j a R := heq.symm ▸ hba
      exact hT.1.linear.2.1.1 a ha (hT.1.linear.2.1.2 a ha j hjI a ha haj hja)
  by_cases hp : ∃ i, Cover I R i j
  · obtain ⟨i,hij⟩ := hp
    have hai : a = i ∨ PureKuratowski.PairMember M a i R := by
      rcases hT.1.linear.2.2 a ha i hij.1 with heq | hai | hia
      · exact Or.inl ((ModelTransfer.extensionality hM).eq_of_same_members a i heq)
      · exact Or.inr hai
      · rcases ConstructionFirstAppearance.cover_le hM hT.1 hij ha hia with hja | hja
        · exact (hT.1.linear.2.1.1 a ha (hja ▸ haj)).elim
        · exact (hT.1.linear.2.1.1 a ha (hT.1.linear.2.1.2 a ha j hjI a ha haj hja)).elim
    obtain ⟨B,hiB,_⟩ := hCuts.1.2 i hij.1
    obtain ⟨P,hiP,_⟩ := hFutures.1.2 i hij.1
    obtain ⟨PB,GB,ib,PP,GP,ip,hBaseB,hBaseP,hSquare⟩ := hIH i hij.1 hij.2.2.1 hai B P hiB hiP
    have hCutB := ((hCuts.2 i B).mp hiB).2
    intro E F hjE hjF
    have hCutE := ((hCuts.2 j E).mp hjE).2
    have hSupF := hSup j E F hjE hjF
    by_cases hs : ∃ x, N.mem x retained ∧ NewAt I R S i x
    · obtain ⟨x,hx,hxi⟩ := hs
      obtain ⟨PE,GE,ie,PF,GF,iF,hBaseE,hBaseF,_,hOut⟩ := ConstructionFutureSelected.advance hM
        hw hz hzw hv hc hJ hStages hRet hT hIndex hCells hNew hGlobal hClosed hij hx hxi
        hA hBaseB hC hBaseP (hSup i B P hiB hiP) hSquare haC hai hCutB hCutE hSupF
      exact ⟨PE,GE,ie,PF,GF,iF,hBaseE,hBaseF,hOut⟩
    · have hBE := ConstructionFutureCut.omitted_cut hM hT hij hCutB hCutE
        (fun x hx hn => hs ⟨x,hx,hn⟩)
      subst E
      have hPF := ConstructionFutureFamily.sup_unique hM (hSup i B P hiB hiP) hSupF
      subst F
      exact ⟨PB,GB,ib,PP,GP,ip,hBaseB,hBaseP,hSquare⟩
  · intro B F hjB hjF
    have hEarlier : ConstructionFutureLimit.EarlierSquares V GV e I R a j cuts futures A C GA GC ia ic := by
      intro k B F hk hak hkj hkB hkF
      obtain ⟨PB,GB,ib,PF,GF,iF,hB,hF,hSq⟩ := hIH k hk hkj hak B F hkB hkF
      exact ⟨PB,PF,GB,GF,ib,iF,hB,hF,hSq⟩
    obtain ⟨PB,GB,ib,PF,GF,iF,hBaseB,hBaseF,_,hOut⟩ := ConstructionFutureLimit.limit hM
      hv hc hJ hT hStages hRet hA hC hCuts hFutures hCM hFM ha hjI haj hne hp hEarlier hjB hjF
    exact ⟨PB,GB,ib,PF,GF,iF,hBaseB,hBaseF,hOut⟩

/- Complete source future_cut, with actual families constructed internally. -/
theorem future_cut (hM : FirstOrder.Theory.Models M nativeZF)
    {w zero one V GV e I R bottom S index cells deps retained a b B
      A C PA PC GA GC ia ic : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ z, ¬ (Project.FirstOrderSemantics.reduct M).mem z zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hv : LeftCancelMonoid V GV e) (hc : Conical V GV e) (hJ : ConditionalJoins V GV)
    (hStages : Stages V GV e S) (hRet : Closure V GV e retained)
    (hT : Timeline hM V I R bottom S) (hIndex : Index V I R bottom S index)
    (hCells : ConstructionStepCellSelection.Graph hM w zero one V GV e I R S cells)
    (hNew : ConstructionStepCellSelection.AtNew hM w zero one V GV e I R S cells)
    (hGlobal : ConstructionGlobalDependencies.Graph zero V I R bottom S index cells deps)
    (hClosed : ConstructionCountableConservativeHull.DependenciesClosed deps retained)
    (hA : Base V GV e A PA GA ia) (hC : Base V GV e C PC GC ic)
    (ha : (Project.FirstOrderSemantics.reduct M).mem a I)
    (haC : PureKuratowski.PairMember M a C S) (haA : CutAt retained S a A)
    (hb : (Project.FirstOrderSemantics.reduct M).mem b I)
    (hab : a = b ∨ PureKuratowski.PairMember M a b R) (hbB : CutAt retained S b B) :
    ∃ F PB GB ib PF GF iF, Base V GV e B PB GB ib ∧ Base V GV e F PF GF iF ∧
      Sup V GV e C B F ∧ Square A B C F GA GB GC GF e ia ib ic := by
  obtain ⟨cuts,futures,cutMuls,futureMuls,hCuts,hFutures,hCM,hFM,_,_⟩ :=
    ConstructionFutureFamily.construction hM hv hc hJ hC hT.2.1 hStages hRet
      (ConstructionFutureLimit.timeline_mono hM hT)
  obtain ⟨B',hbB',_⟩ := hCuts.1.2 b hb
  have heB := ConstructionFutureFamily.cut_unique hM hT.2.1 ((hCuts.2 b B').mp hbB').2 hbB
  subst B'
  obtain ⟨F,hbF,_⟩ := hFutures.1.2 b hb
  obtain ⟨PB,GB,ib,PF,GF,iF,hBaseB,hBaseF,hSquare⟩ := all_good hM hw hz hzw hv hc hJ hStages hRet
    hT hIndex hCells hNew hGlobal hClosed hCuts hFutures hCM hFM hA hC ha haC haA b hb hab B F hbB' hbF
  obtain ⟨B',hbB'',hSup⟩ := ((hFutures.2 b F).mp hbF).2
  have heB := function_unique hCuts.1 hbB'' hbB'
  subst B'
  exact ⟨F,PB,GB,ib,PF,GF,iF,hBaseB,hBaseF,hSup,hSquare⟩

/-- Native ZF proof of the complete source future_cut instance. The
internal induction, carrier families, and target conservative Base are conclusions
or constructions, never assumed premises. -/
def futureCutSentence {m : Nat} (w zero one V GV e I R bottom S index cells deps retained a b B A C PA PC GA GC ia ic : Fin m) : Project.Sentence where
  formula := Project.Formula.forallClosure m (.imp (Project.Formula.isOmega (.bound w)) (.imp (Project.Formula.isEmpty (.bound zero)) (.imp (.mem (.bound zero) (.bound w)) (.imp (ProjectSyntax.encode id (ForcingDiagramPoset.leftCancelMonoid V GV e)) (.imp (ProjectSyntax.encode id (ForcingDiagramPoset.conical V GV e)) (.imp (ConstructionProbeSharedIntersections.conditionalJoins V GV) (.imp (ConstructionCellRestriction.stages V GV e S) (.imp (ConstructionConservativeHull.closure V GV e retained) (.imp (ConstructionFirstAppearance.timeline V I R bottom S) (.imp (ConstructionFirstAppearance.indexGraph V I R bottom S index) (.imp (ConstructionStepCellSelection.graph w zero one V GV e I R S cells) (.imp (ConstructionStepCellSelection.atNew w zero one V GV e I R S cells) (.imp (ConstructionGlobalDependencies.graph zero V I R bottom S index cells deps) (.imp (ConstructionCountableConservativeHull.dependenciesClosed deps retained) (.imp (ConstructionSelectedCellRestriction.baseFormula V GV e A PA GA ia) (.imp (ConstructionSelectedCellRestriction.baseFormula V GV e C PC GC ic) (.imp (.mem (.bound a) (.bound I)) (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge S a C)) (.imp (ConstructionFutureFamily.cutAt retained S a A) (.imp (.mem (.bound b) (.bound I)) (.imp (ConstructionFutureLimit.closedLe R a b) (.imp (ConstructionFutureFamily.cutAt retained S b B) (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.conj (ConstructionSelectedCellRestriction.baseFormula V.succ.succ.succ.succ.succ.succ.succ GV.succ.succ.succ.succ.succ.succ.succ e.succ.succ.succ.succ.succ.succ.succ B.succ.succ.succ.succ.succ.succ.succ 5 4 3) (.conj (ConstructionSelectedCellRestriction.baseFormula V.succ.succ.succ.succ.succ.succ.succ GV.succ.succ.succ.succ.succ.succ.succ e.succ.succ.succ.succ.succ.succ.succ 6 2 1 0) (.conj (ConstructionIntermediate.sup V.succ.succ.succ.succ.succ.succ.succ GV.succ.succ.succ.succ.succ.succ.succ e.succ.succ.succ.succ.succ.succ.succ C.succ.succ.succ.succ.succ.succ.succ B.succ.succ.succ.succ.succ.succ.succ 6) (ConstructionUnionPushout.square A.succ.succ.succ.succ.succ.succ.succ B.succ.succ.succ.succ.succ.succ.succ C.succ.succ.succ.succ.succ.succ.succ 6 GA.succ.succ.succ.succ.succ.succ.succ 4 GC.succ.succ.succ.succ.succ.succ.succ 1 e.succ.succ.succ.succ.succ.succ.succ ia.succ.succ.succ.succ.succ.succ.succ 3 ic.succ.succ.succ.succ.succ.succ.succ)))))))))))))))))))))))))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,Project.Formula.isOmega,Project.Formula.isEmpty,ConstructionProbeSharedIntersections.conditionalJoins_freeClosed,ConstructionCellRestriction.stages_freeClosed,ConstructionConservativeHull.closure_freeClosed,ConstructionFirstAppearance.timeline_freeClosed,ConstructionFirstAppearance.indexGraph_freeClosed,ConstructionStepCellSelection.graph_freeClosed,ConstructionStepCellSelection.atNew_freeClosed,ConstructionGlobalDependencies.graph_freeClosed,ConstructionCountableConservativeHull.dependenciesClosed_freeClosed,ConstructionSelectedCellRestriction.baseFormula_freeClosed,ConstructionFutureFamily.cutAt_freeClosed,ConstructionFutureLimit.closedLe_freeClosed,ConstructionIntermediate.sup_freeClosed,ConstructionUnionPushout.square_freeClosed]

theorem futureCut_models {m : Nat} (w zero one V GV e I R bottom S index cells deps retained a b B A C PA PC GA GC ia ic : Fin m) (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence (futureCutSentence w zero one V GV e I R bottom S index cells deps retained a b B A C PA PC GA GC ia ic)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) (futureCutSentence w zero one V GV e I R bottom S index cells deps retained a b B A C PA PC GA GC ia ic)]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,Project.Formula.satisfies_isOmega_iff,Project.Formula.satisfies_isEmpty_iff,GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,ForcingDiagramPoset.leftCancelMonoid_semantics (M := M),ForcingDiagramPoset.conical_semantics (M := M),ConstructionProbeSharedIntersections.conditionalJoins_semantics hM,ConstructionCellRestriction.stages_semantics hM,ConstructionConservativeHull.closure_semantics hM,ConstructionFirstAppearance.timeline_semantics hM,ConstructionFirstAppearance.indexGraph_semantics hM,ConstructionStepCellSelection.graph_semantics hM,ConstructionStepCellSelection.atNew_semantics hM,ConstructionGlobalDependencies.graph_semantics hM,ConstructionCountableConservativeHull.dependenciesClosed_semantics hM,ConstructionSelectedCellRestriction.baseFormula_semantics hM,ConstructionFutureFamily.cutAt_semantics hM,ConstructionFutureLimit.closedLe_semantics hM,ConstructionIntermediate.sup_semantics hM,ConstructionUnionPushout.square_semantics hM]
  exact future_cut hM

theorem futureCut_kernel_certificate {m : Nat} (w zero one V GV e I R bottom S index cells deps retained a b B A C PA PC GA GC ia ic : Fin m) :
    FirstOrder.Derives nativeZF [] (Project.fo_sentence (futureCutSentence w zero one V GV e I R bottom S index cells deps retained a b B A C PA PC GA GC ia ic)) :=
  ModelTransfer.derives (fun _ hM => futureCut_models w zero one V GV e I R bottom S index cells deps retained a b B A C PA PC GA GC ia ic hM)

end PPAC.Migration.ConstructionFutureInduction
