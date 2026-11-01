/- The actual AssignedGraphs.graphRelation, translated by the existing
ProjectDecode compiler. Reuse the existing AssignedGraph semantic laws;
no alternate assignment, graph relation, or proof kernel is introduced. -/
import PPAC.Migration.ForcingAssignedGraph
import PPAC.Migration.ForcingRelationGraphApplication
import PPAC.Migration.ForcingCodeSelection

namespace PPAC.Migration.ForcingAssignedRelation
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open Source (Formula)
open ForcingProductSymmetry (orderFormula)
open ForcingRelationGraphApplication (actionAt)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 32768
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

def relation {k : Nat} (rho : Fin 7 → Fin k)
    (I G F mul q bound labels E w top K B zero Q labelMap bit : Fin k) (families : Fin 16 → Fin k) : Formula (k+3) :=
  ProjectDecode.formula id
    (ForcingAssignedGraph.holds rho I G F mul q bound labels E w top K B zero Q labelMap bit families (fun j => j.castSucc.castSucc.castSucc) (Fin.last k).castSucc.castSucc (Fin.last (k+1)).castSucc (Fin.last (k+2)))
    (ForcingAssignedGraph.holds_freeClosed rho I G F mul q bound labels E w top K B zero Q labelMap bit families (fun j => j.castSucc.castSucc.castSucc) (Fin.last k).castSucc.castSucc (Fin.last (k+1)).castSucc (Fin.last (k+2)))

theorem relation_semantics (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k)
    (I G F mul q bound labels E w top K B zero Q labelMap bit : Fin k) (families : Fin 16 → Fin k) (p x y : M.Carrier .set) :
    ForcingRelationGraphForcing.Holds (relation rho I G F mul q bound labels E w top K B zero Q labelMap bit families) env p x y ↔
      ForcingAssignedGraph.Holds hM env rho I G F mul q bound labels E w top K B zero Q labelMap bit families p x y := by
  let ext : Fin (k+3) → M.Carrier .set := Fin.lastCases y (Fin.lastCases x (Fin.lastCases p env))
  exact (ForcingCodeSelection.decode_realizes hM id _ _ ext (fun _ => p)).trans (by
    simpa only [ext, id_eq, Fin.lastCases_last, Fin.lastCases_castSucc] using
      (ForcingAssignedGraph.holds_semantics hM (⟨ext, fun _ => p⟩ : SetTheory.Env (Project.FirstOrderSemantics.reduct M) (k+3))
        rho I G F mul q bound labels E w top K B zero Q labelMap bit families (fun j => j.castSucc.castSucc.castSucc) (Fin.last k).castSucc.castSucc (Fin.last (k+1)).castSucc (Fin.last (k+2))))

theorem monotone (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k)
    (I G F mul q bound labels E w top K B zero Q labelMap bit one : Fin k) (families : Fin 16 → Fin k)
    (hm : ForcingDiagramPoset.LeftCancelMonoid (env (rho 0)) (env mul) (env one))
    (hp : ForcingProductFamily.Presentation (env (rho 0)) (env I) (env K) (env B) (env w)
      (env (rho 1)) (env (rho 2)) (env (rho 3)) (env (rho 4)) (env (rho 5)) (env (rho 6))) :
    ForcingRelationGraphForcing.Monotone (orderFormula (rho 0) mul) (actionAt rho)
      (relation rho I G F mul q bound labels E w top K B zero Q labelMap bit families) env (env (rho 6)) (env G) (env F) := by
  intro p r x y _ hr hrp _ _ h
  exact (relation_semantics hM env rho I G F mul q bound labels E w top K B zero Q labelMap bit families r x y).mpr
    (ForcingAssignedGraph.holds_mono hM env rho I G F mul q bound labels E w top K B zero Q labelMap bit one families hm hp hr hrp
      ((relation_semantics hM env rho I G F mul q bound labels E w top K B zero Q labelMap bit families p x y).mp h))

theorem congruent (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k)
    (I G F mul q bound labels E w top K B zero Q labelMap bit one : Fin k) (families : Fin 16 → Fin k)
    (hm : ForcingDiagramPoset.LeftCancelMonoid (env (rho 0)) (env mul) (env one))
    (hp : ForcingProductFamily.Presentation (env (rho 0)) (env I) (env K) (env B) (env w)
      (env (rho 1)) (env (rho 2)) (env (rho 3)) (env (rho 4)) (env (rho 5)) (env (rho 6))) :
    ForcingRelationGraphForcing.Congruent (orderFormula (rho 0) mul) (actionAt rho)
      (relation rho I G F mul q bound labels E w top K B zero Q labelMap bit families) env (env (rho 6)) (env G) (env F) := by
  intro p x y x' y' _ _ _ _ hxx hyy
  exact (relation_semantics hM env rho I G F mul q bound labels E w top K B zero Q labelMap bit families p x y).trans
    ((ForcingAssignedGraph.holds_congr hM env rho I G F mul q bound labels E w top K B zero Q labelMap bit one families hm hp hxx hyy).trans
      (relation_semantics hM env rho I G F mul q bound labels E w top K B zero Q labelMap bit families p x' y').symm)

theorem regular (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k)
    (I G F mul q bound labels E w top K B zero Q labelMap bit one : Fin k) (families : Fin 16 → Fin k)
    (hm : ForcingDiagramPoset.LeftCancelMonoid (env (rho 0)) (env mul) (env one))
    (hp : ForcingProductFamily.Presentation (env (rho 0)) (env I) (env K) (env B) (env w)
      (env (rho 1)) (env (rho 2)) (env (rho 3)) (env (rho 4)) (env (rho 5)) (env (rho 6))) :
    ForcingRelationGraphForcing.Regular (orderFormula (rho 0) mul) (actionAt rho)
      (relation rho I G F mul q bound labels E w top K B zero Q labelMap bit families) env (env (rho 6)) (env G) (env F) := by
  intro p x y hpW _ _ hd
  apply (relation_semantics hM env rho I G F mul q bound labels E w top K B zero Q labelMap bit families p x y).mpr
  apply ForcingAssignedGraph.holds_regular hM env rho I G F mul q bound labels E w top K B zero Q labelMap bit one families hm hp hpW
  intro r hr hrp
  obtain ⟨s, _, hsr, hs⟩ := hd r hr hrp
  exact ⟨s, hsr, (relation_semantics hM env rho I G F mul q bound labels E w top K B zero Q labelMap bit families s x y).mp hs⟩

def lawsSentence {k : Nat} (rho : Fin 7 → Fin k)
    (I G F mul q bound labels E w top K B zero Q labelMap bit one : Fin k) (families : Fin 16 → Fin k) : Source.Sentence :=
  ((ForcingDiagramPoset.leftCancelMonoid (rho 0) mul one).imp
    ((ForcingProductFamily.presentation (rho 0) I K B w (rho 1) (rho 2) (rho 3) (rho 4) (rho 5) (rho 6)).imp
      ((ForcingRelationGraphForcing.monotone (orderFormula (rho 0) mul) (actionAt rho)
        (relation rho I G F mul q bound labels E w top K B zero Q labelMap bit families) id (rho 6) G F).conj
      ((ForcingRelationGraphForcing.congruent (orderFormula (rho 0) mul) (actionAt rho)
        (relation rho I G F mul q bound labels E w top K B zero Q labelMap bit families) id (rho 6) G F).conj
       (ForcingRelationGraphForcing.regular (orderFormula (rho 0) mul) (actionAt rho)
        (relation rho I G F mul q bound labels E w top K B zero Q labelMap bit families) id (rho 6) G F))))).close

theorem laws_models {k : Nat} (rho : Fin 7 → Fin k)
    (I G F mul q bound labels E w top K B zero Q labelMap bit one : Fin k) (families : Fin 16 → Fin k)
    (hM : FirstOrder.Theory.Models M nativeZF) :
    (Translation.sentence (lawsSentence rho I G F mul q bound labels E w top K B zero Q labelMap bit one families)).TrueIn M := by
  apply (Translation.realizes_sentence M _).mpr
  apply (GodelDefOutput.close_semantics _ _).mpr
  intro env hm hp
  have hm' := (ForcingDiagramPoset.leftCancelMonoid_semantics (M := M) env (rho 0) mul one).mp hm
  have hp' := (ForcingProductFamily.presentation_semantics (M := M) env (rho 0) I K B w (rho 1) (rho 2) (rho 3) (rho 4) (rho 5) (rho 6)).mp hp
  exact ⟨(ForcingRelationGraphForcing.monotone_semantics (M := M) env (orderFormula (rho 0) mul) (actionAt rho)
      (relation rho I G F mul q bound labels E w top K B zero Q labelMap bit families) id (rho 6) G F).mpr (monotone hM env rho I G F mul q bound labels E w top K B zero Q labelMap bit one families hm' hp'),
    (ForcingRelationGraphForcing.congruent_semantics (M := M) env (orderFormula (rho 0) mul) (actionAt rho)
      (relation rho I G F mul q bound labels E w top K B zero Q labelMap bit families) id (rho 6) G F).mpr (congruent hM env rho I G F mul q bound labels E w top K B zero Q labelMap bit one families hm' hp'),
    (ForcingRelationGraphForcing.regular_semantics (M := M) env (orderFormula (rho 0) mul) (actionAt rho)
      (relation rho I G F mul q bound labels E w top K B zero Q labelMap bit families) id (rho 6) G F).mpr (regular hM env rho I G F mul q bound labels E w top K B zero Q labelMap bit one families hm' hp')⟩

theorem laws_kernel_certificate {k : Nat} (rho : Fin 7 → Fin k)
    (I G F mul q bound labels E w top K B zero Q labelMap bit one : Fin k) (families : Fin 16 → Fin k) :
    FirstOrder.Derives nativeZF [] (Translation.sentence (lawsSentence rho I G F mul q bound labels E w top K B zero Q labelMap bit one families)) :=
  ModelTransfer.derives (fun _ hM => laws_models rho I G F mul q bound labels E w top K B zero Q labelMap bit one families hM)

end PPAC.Migration.ForcingAssignedRelation
