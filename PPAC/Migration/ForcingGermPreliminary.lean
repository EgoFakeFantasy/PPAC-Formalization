/- Pinned GermSelectors.Preliminary:38-45 and preliminary_mono/common/congr/restrict.
Literal HS names, persistent Selected, actual check names and the SAME rank
history/type and fixed ordinal-table entry. Reuse existing Links laws. -/
import PPAC.Migration.ForcingOrdinalTable
import PPAC.Migration.ForcingCodeRankConsumers

namespace PPAC.Migration.ForcingGermPreliminary
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ForcingProductSymmetry (orderFormula)
open ForcingPrincipalFilter (EqF)
open ForcingCodeLinks (Links)
open ForcingCheckName (Checked)
open ForcingClassEvaluation (Predicate)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 6000000
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

def Preliminary (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k) (I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab r : Fin k)
    (d vertex label tau : M.Carrier .set) : Prop :=
  (Project.FirstOrderSemantics.reduct M).mem label (env labelSet) ∧
    Predicate (ForcingPairUnion.domain rho G F) env tau ∧
    ∃ theta a na ntheta beta nbeta,
      ForcingOrdinalTable.Eligible hM (env labelSet) (env rankBound) theta ∧
      (Project.FirstOrderSemantics.reduct M).mem a (env codes) ∧
      PureKuratowski.PairMember M a na (env ranks) ∧
      ForcingOrdinalTable.Indices (env tab) theta label beta ∧
      Checked (env top) theta ntheta ∧ Checked (env top) beta nbeta ∧
      ForcingCodeSelection.IsSelected env rho I G F mul q bound labels E root w chain codes order a d ∧
      EqF (orderFormula (rho 0) mul) env (env (rho 6)) d (env r) (env selection) ntheta ∧
      EqF (orderFormula (rho 0) mul) env (env (rho 6)) d (env r) na nbeta ∧
      Links (orderFormula (rho 0) mul) env (env (rho 6)) (env w) (env (rho 0)) (env I) (env mul) (env q) (env chain) d vertex tau a

def preliminary {k m : Nat} (rho : Fin 7 → Fin k) (I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab r : Fin k)
    (base : Fin k → Fin m) (d vertex label tau : Fin m) : Project.Formula 1 m :=
  let up : Fin m → Fin (m+6) := fun i => i.succ.succ.succ.succ.succ.succ
  .conj (.mem (.bound label) (.bound (base labelSet)))
    (.conj (ProjectSyntax.encode id (MinimalPredicates.pred (ForcingPairUnion.domain rho G F) base tau))
      (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.conj (ForcingOrdinalTable.eligible (up (base labelSet)) (up (base rankBound)) 5)
        (.conj (.mem (.bound 4) (.bound (up (base codes))))
        (.conj (ProjectSyntax.encode id (Source.SetLanguage.edge (up (base ranks)) 4 3))
        (.conj (ForcingOrdinalTable.indices (up (base tab)) 5 (up label) 1)
        (.conj (ProjectSyntax.encode id (ForcingCheckName.checkName (up (base top)) 5 2))
        (.conj (ProjectSyntax.encode id (ForcingCheckName.checkName (up (base top)) 1 0))
        (.conj (ForcingCodeSelection.selected rho I G F mul q bound labels E root w chain codes order (fun i => up (base i)) 4 (up d))
        (.conj (ForcingPrincipalFilter.eqF (orderFormula (rho 0) mul) (fun i => up (base i)) (up (base (rho 6))) (up d) (up (base r)) (up (base selection)) 2)
        (.conj (ForcingPrincipalFilter.eqF (orderFormula (rho 0) mul) (fun i => up (base i)) (up (base (rho 6))) (up d) (up (base r)) 3 0)
        (ForcingCodeLinks.links (orderFormula (rho 0) mul) (fun i => up (base i)) (up (base (rho 6))) (up (base w)) (up (base (rho 0))) (up (base I)) (up (base mul)) (up (base q)) (up (base chain)) (up d) (up vertex) (up tau) 4)))))))))))))))))

theorem preliminary_freeClosed {k m : Nat} (rho : Fin 7 → Fin k) (I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab r : Fin k)
    (base : Fin k → Fin m) (d vertex label tau : Fin m) :
    (preliminary rho I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab r base d vertex label tau).FreeClosed := by
  simp -implicitDefEqProofs [preliminary,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
    ForcingOrdinalTable.eligible_freeClosed,ForcingOrdinalTable.indices_freeClosed,
    ForcingCodeSelection.selected_freeClosed,ForcingPrincipalFilter.eqF_freeClosed,ForcingCodeLinks.links_freeClosed]

theorem preliminary_semantics (hM : FirstOrder.Theory.Models M nativeZF) {k m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (rho : Fin 7 → Fin k) (I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab r : Fin k)
    (base : Fin k → Fin m) (d vertex label tau : Fin m) :
    Project.Formula.satisfies env (preliminary rho I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab r base d vertex label tau) ↔
      Preliminary hM (fun i => env.bound (base i)) rho I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab r (env.bound d) (env.bound vertex) (env.bound label) (env.bound tau) := by
  simp only [preliminary,Preliminary,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingClassEvaluation.predicate_semantics (M := M),ForcingOrdinalTable.eligible_semantics hM,
    ForcingOrdinalTable.indices_semantics hM,KuratowskiZF.source_edge,ForcingCheckName.checkName_semantics (M := M),
    ForcingCodeSelection.selected_semantics hM,ForcingPrincipalFilter.eqF_semantics hM,ForcingCodeLinks.links_semantics hM]
  rfl

theorem preliminary_mono (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k) (I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab r : Fin k)
    {K B one d e vertex label tau : M.Carrier .set}
    (hm : ForcingDiagramPoset.LeftCancelMonoid (env (rho 0)) (env mul) one)
    (hp : ForcingProductFamily.Presentation (env (rho 0)) (env I) K B (env w) (env (rho 1)) (env (rho 2))
      (env (rho 3)) (env (rho 4)) (env (rho 5)) (env (rho 6)))
    (he : (Project.FirstOrderSemantics.reduct M).mem e (env (rho 3)))
    (hr : ForcingSupportSize.Injection (env (rho 0)) (env I) (env r))
    (hde : ForcingPowerName.Subset d e) (h : Preliminary hM env rho I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab r d vertex label tau) :
    Preliminary hM env rho I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab r e vertex label tau := by
  obtain ⟨hj,hTau,theta,a,na,ntheta,beta,nbeta,hElig,ha,hRank,hIndex,hTheta,hBeta,hSel,hEqT,hEqR,hLink⟩ := h
  exact ⟨hj,hTau,theta,a,na,ntheta,beta,nbeta,hElig,ha,hRank,hIndex,hTheta,hBeta,ForcingCodeSelection.isSelected_mono hde hSel,
    ForcingPrincipalFilter.eqF_mono hM env rho mul hm hp he hr hde hEqT,
    ForcingPrincipalFilter.eqF_mono hM env rho mul hm hp he hr hde hEqR,
    ForcingCodeLinks.links_mono hM env rho mul hm hp he hde hLink⟩

theorem preliminary_common (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k) (I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab r : Fin k)
    {zero vertices d vertex label tau : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega (env w))
    (hChain : ConstructionComponentCofinal.Chain (env w) (env (rho 0)) (env I) (env mul) (env q) zero (env root) vertices (env chain))
    (h : Preliminary hM env rho I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab r d vertex label tau) :
    ConstructionComponentCofinal.EncodedCommon (env (rho 0)) (env I) (env mul) (env q) (env root) vertex := by
  obtain ⟨hj,hTau,theta,a,na,ntheta,beta,nbeta,hElig,ha,hRank,hIndex,hTheta,hBeta,hSel,hEqT,hEqR,hLink⟩ := h
  exact ForcingCodeLinks.links_common hM env rho mul hw hChain hLink

theorem preliminary_congr (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k) (I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab r : Fin k)
    {K B one d vertex label tau sigma localRoot index U : M.Carrier .set}
    (hm : ForcingDiagramPoset.LeftCancelMonoid (env (rho 0)) (env mul) one)
    (hp : ForcingProductFamily.Presentation (env (rho 0)) (env I) K B (env w) (env (rho 1)) (env (rho 2))
      (env (rho 3)) (env (rho 4)) (env (rho 5)) (env (rho 6)))
    (hd : (Project.FirstOrderSemantics.reduct M).mem d (env (rho 3)))
    (hc : ConstructionComponentCarrier.Code vertex localRoot index U)
    (hs : Predicate (ForcingPairUnion.domain rho G F) env sigma)
    (he : EqF (orderFormula (rho 0) mul) env (env (rho 6)) d localRoot tau sigma)
    (h : Preliminary hM env rho I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab r d vertex label tau) :
    Preliminary hM env rho I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab r d vertex label sigma := by
  obtain ⟨hj,hTau,theta,a,na,ntheta,beta,nbeta,hElig,ha,hRank,hIndex,hTheta,hBeta,hSel,hEqT,hEqR,hLink⟩ := h
  exact ⟨hj,hs,theta,a,na,ntheta,beta,nbeta,hElig,ha,hRank,hIndex,hTheta,hBeta,hSel,hEqT,hEqR,
    ForcingCodeLinks.links_congr hM env rho mul hm hp hd hc hLink he⟩

theorem preliminary_restrict (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k) (I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab r : Fin k)
    {K B one d vertex vertexT n label tau : M.Carrier .set}
    (hm : ForcingDiagramPoset.LeftCancelMonoid (env (rho 0)) (env mul) one)
    (hp : ForcingProductFamily.Presentation (env (rho 0)) (env I) K B (env w) (env (rho 1)) (env (rho 2))
      (env (rho 3)) (env (rho 4)) (env (rho 5)) (env (rho 6)))
    (hd : (Project.FirstOrderSemantics.reduct M).mem d (env (rho 3)))
    (hf : ConstructionComponentCofinal.EncodedArrow (env (rho 0)) (env I) (env mul) (env q) vertexT vertex n)
    (h : Preliminary hM env rho I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab r d vertex label tau) :
    Preliminary hM env rho I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab r d vertexT label tau := by
  obtain ⟨hj,hTau,theta,a,na,ntheta,beta,nbeta,hElig,ha,hRank,hIndex,hTheta,hBeta,hSel,hEqT,hEqR,hLink⟩ := h
  exact ⟨hj,hTau,theta,a,na,ntheta,beta,nbeta,hElig,ha,hRank,hIndex,hTheta,hBeta,hSel,hEqT,hEqR,
    ForcingCodeLinks.links_restrict hM env rho mul hm hp hd hf hLink⟩


def lawsSentence {k : Nat} (rho : Fin 7 → Fin k) (I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab r K B one zero vertices d e vertex vertexT n localRoot index U label tau sigma : Fin k) : Project.Sentence where
  formula := Project.Formula.forallClosure k (.imp (ProjectSyntax.encode id (ForcingDiagramPoset.leftCancelMonoid (rho 0) mul one))
    (.imp (ProjectSyntax.encode id (ForcingProductFamily.presentation (rho 0) I K B w (rho 1) (rho 2) (rho 3) (rho 4) (rho 5) (rho 6)))
    (.imp (Project.Formula.isOmega (.bound w))
    (.imp (ConstructionComponentCofinal.chain w (rho 0) I mul q zero root vertices chain)
    (.imp (ProjectSyntax.encode id (Source.SetLanguage.injection r (rho 0) I))
    (.imp (.mem (.bound d) (.bound (rho 3)))
    (.imp (.mem (.bound e) (.bound (rho 3)))
    (.imp (Project.Formula.subset (.bound d) (.bound e))
    (.imp (ConstructionComponentCarrier.code vertex localRoot index U)
    (.imp (preliminary rho I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab r id d vertex label tau)
    (.conj (ConstructionComponentCofinal.encodedCommon (rho 0) I mul q root vertex)
    (.conj (preliminary rho I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab r id e vertex label tau)
    (.conj (.imp (ProjectSyntax.encode id (MinimalPredicates.pred (ForcingPairUnion.domain rho G F) id sigma))
    (.imp (ForcingPrincipalFilter.eqF (orderFormula (rho 0) mul) id (rho 6) d localRoot tau sigma)
    (preliminary rho I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab r id d vertex label sigma)))
    (.imp (ConstructionComponentCofinal.encodedArrow (rho 0) I mul q vertexT vertex n)
    (preliminary rho I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab r id d vertexT label tau)))))))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
      ConstructionComponentCofinal.chain_freeClosed,ConstructionComponentCarrier.code_freeClosed,
      preliminary_freeClosed,ConstructionComponentCofinal.encodedCommon_freeClosed,
      ConstructionComponentCofinal.encodedArrow_freeClosed,ForcingPrincipalFilter.eqF_freeClosed]

theorem laws_models {k : Nat} (rho : Fin 7 → Fin k) (I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab r K B one zero vertices d e vertex vertexT n localRoot index U label tau sigma : Fin k)
    (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence (lawsSentence rho I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab r K B one zero vertices d e vertex vertexT n localRoot index U label tau sigma)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM)]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro env
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_mem_iff,Project.Formula.satisfies_subset_iff,Project.Formula.satisfies_isOmega_iff,
    Project.Term.eval_bound,GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingDiagramPoset.leftCancelMonoid_semantics (M := M),ForcingProductFamily.presentation_semantics (M := M),
    ConstructionComponentCofinal.chain_semantics hM,ForcingSupportSize.injection_semantics (M := M),
    ConstructionComponentCarrier.code_semantics hM,preliminary_semantics hM,
    ConstructionComponentCofinal.encodedCommon_semantics hM,ConstructionComponentCofinal.encodedArrow_semantics hM,
    ForcingPrincipalFilter.eqF_semantics hM,ForcingClassEvaluation.predicate_semantics (M := M)]
  intro hm hp hw hChain hr hd he hde hc hl
  exact ⟨preliminary_common hM env rho I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab r hw hChain hl,
    preliminary_mono hM env rho I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab r hm hp he hr hde hl,
    fun hs hf => preliminary_congr hM env rho I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab r hm hp hd hc hs hf hl,
    fun hf => preliminary_restrict hM env rho I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab r hm hp hd hf hl⟩

theorem laws_kernel_certificate {k : Nat} (rho : Fin 7 → Fin k) (I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab r K B one zero vertices d e vertex vertexT n localRoot index U label tau sigma : Fin k) :
    FirstOrder.Derives nativeZF [] (Project.fo_sentence (lawsSentence rho I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab r K B one zero vertices d e vertex vertexT n localRoot index U label tau sigma)) :=
  ModelTransfer.derives (fun _ hM => laws_models rho I G F mul q bound labels E root w chain codes order ranks selection top rankBound labelSet tab r K B one zero vertices d e vertex vertexT n localRoot index U label tau sigma hM)

end PPAC.Migration.ForcingGermPreliminary
