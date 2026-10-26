/- Pure object certificate for the actual unique Word height graph with
the pinned rawHeight old/cons equations. Cost and HeightCost are separate. -/
import PPAC.Migration.ConstructionProbeHeightFold

namespace PPAC.Migration.ConstructionProbeHeightFoldSyntax
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

def laws {m : Nat} (w D S zero W Q H O V L : Fin m) : Project.Formula 1 m :=
  (.conj (.forallE (.forallE (.forallE (.imp (ConstructionProbeRaw.old zero.succ.succ.succ D.succ.succ.succ (2 :
Fin (m+3)) (1 : Fin (m+3))) (.iff (ProjectSyntax.encode id (Source.SetLanguage.edge L.succ.succ.succ (1 : Fin
(m+3)) (0 : Fin (m+3)))) (ProjectSyntax.encode id (Source.SetLanguage.edge H.succ.succ.succ (2 : Fin (m+3)) (0
: Fin (m+3))))))))) (.forallE (.forallE (.forallE (.forallE (.imp (ConstructionProbeRaw.cons
w.succ.succ.succ.succ D.succ.succ.succ.succ S.succ.succ.succ.succ (3 : Fin (m+4)) (2 : Fin (m+4)) (1 : Fin
(m+4))) (.imp (.mem (.bound (1 : Fin (m+4))) (.bound W.succ.succ.succ.succ)) (.iff (ProjectSyntax.encode id
(Source.SetLanguage.edge L.succ.succ.succ.succ (1 : Fin (m+4)) (0 : Fin (m+4)))) (.existsE (.conj
(ProjectSyntax.encode id (Source.SetLanguage.edge L.succ.succ.succ.succ.succ (3 : Fin (m+5)) (0 : Fin (m+5))))
(ConstructionProbeHeightOperation.affine w.succ.succ.succ.succ.succ Q.succ.succ.succ.succ.succ
O.succ.succ.succ.succ.succ V.succ.succ.succ.succ.succ (4 : Fin (m+5)) (0 : Fin (m+5)) (1 : Fin
(m+5)))))))))))))

theorem laws_freeClosed {m : Nat} (w D S zero W Q H O V L : Fin m) :
    (laws w D S zero W Q H O V L).FreeClosed := by
  simp -implicitDefEqProofs [laws,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
    ConstructionProbeRaw.old_freeClosed,ConstructionProbeRaw.cons_freeClosed,ConstructionProbeHeightOperation.affine_freeClosed]

theorem laws_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w D S zero W Q H O V L : Fin m) :
    Project.Formula.satisfies env (laws w D S zero W Q H O V L) ↔
      ConstructionProbeHeightFold.Laws hM (env.bound w) (env.bound D) (env.bound S) (env.bound zero)
        (env.bound W) (env.bound Q) (env.bound H) (env.bound O) (env.bound V) (env.bound L) := by
  simp only [laws,ConstructionProbeHeightFold.Laws,Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_iff_iff,
    Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,
    ConstructionProbeRaw.old_semantics hM,ConstructionProbeRaw.cons_semantics hM,
    ConstructionProbeHeightOperation.affine_semantics hM]
  rfl

def constructionSentence : Project.Sentence where
  formula := Project.Formula.forallClosure 13
    (.imp (Project.Formula.isOmega (.bound (0 : Fin 13))) (.imp (Project.Formula.isEmpty (.bound (3 : Fin 13)))
(.imp (.mem (.bound (3 : Fin 13)) (.bound (0 : Fin 13))) (.imp (ConstructionFractionOrder.carrier (0 : Fin 13)
(8 : Fin 13)) (.imp (ConstructionRealCuts.cutCarrier (0 : Fin 13) (8 : Fin 13) (9 : Fin 13)) (.imp
(ProjectSyntax.encode id (Source.SetLanguage.mapsTo (10 : Fin 13) (1 : Fin 13) (9 : Fin 13))) (.imp
(ProjectSyntax.encode id (Source.SetLanguage.mapsTo (11 : Fin 13) (2 : Fin 13) (9 : Fin 13))) (.imp
(ProjectSyntax.encode id (Source.SetLanguage.mapsTo (12 : Fin 13) (2 : Fin 13) (9 : Fin 13))) (.imp
(ConstructionProbeWord.wordCarrier (0 : Fin 13) (1 : Fin 13) (2 : Fin 13) (4 : Fin 13) (5 : Fin 13) (6 : Fin
13) (7 : Fin 13)) (.existsE (.conj (ProjectSyntax.encode id (Source.SetLanguage.mapsTo (0 : Fin 14) (8 : Fin
14) (10 : Fin 14))) (.conj (laws (1 : Fin 14) (2 : Fin 14) (3 : Fin 14) (4 : Fin 14) (8 : Fin 14) (9 : Fin 14)
(11 : Fin 14) (12 : Fin 14) (13 : Fin 14) (0 : Fin 14)) (.forallE (.imp (ProjectSyntax.encode id
(Source.SetLanguage.mapsTo (0 : Fin 15) (9 : Fin 15) (11 : Fin 15))) (.imp (laws (2 : Fin 15) (3 : Fin 15) (4
: Fin 15) (5 : Fin 15) (9 : Fin 15) (10 : Fin 15) (12 : Fin 15) (13 : Fin 15) (14 : Fin 15) (0 : Fin 15))
(Project.Formula.extensionalEq (.bound (0 : Fin 15)) (.bound (1 : Fin 15))))))))))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
      ConstructionFractionOrder.carrier_freeClosed,ConstructionRealCuts.cutCarrier_freeClosed,
      ConstructionProbeWord.wordCarrier_freeClosed,laws_freeClosed]

theorem construction_models (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence constructionSentence).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) constructionSentence]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_isOmega_iff,
    Project.Formula.satisfies_isEmpty_iff,Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    ConstructionFractionOrder.carrier_semantics hM,ConstructionRealCuts.cutCarrier_semantics hM,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),ForcingSupportSize.mapsTo_semantics (M := M),
    ConstructionProbeWord.wordCarrier_semantics hM,Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_conj_iff,laws_semantics hM,
    Project.Formula.satisfies_extensionalEq_iff_eq (ModelTransfer.extensionality hM)]
  intro hw hz hzw hQ hR hH hO hV hW
  exact ConstructionProbeHeightFold.existsUnique_height hM hw hz hzw hQ hR hH hO hV hW

theorem construction_kernel_certificate : FirstOrder.Derives nativeZF []
    (Project.fo_sentence constructionSentence) := ModelTransfer.derives (fun _ hM => construction_models hM)

end PPAC.Migration.ConstructionProbeHeightFoldSyntax
