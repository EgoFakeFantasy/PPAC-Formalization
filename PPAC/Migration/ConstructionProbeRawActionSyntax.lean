/- Pinned ProbeWords.Raw.oldAct/headDiv: pure Project formulas, the actual
internal action graph, and its source laws in the native ZF derivation kernel. -/
import PPAC.Migration.ConstructionProbeRawAction

namespace PPAC.Migration.ConstructionProbeRawActionSyntax
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ConstructionProbeRaw
open ConstructionProbeRawAction
open ForcingDiagramOrder (Product product product_semantics)
open ForcingDiagramPoset (LeftCancelMonoid)
open ForcingSupportSize (MapsTo)
open ConstructionProbeLetters (Representatives exists_representatives representatives representatives_freeClosed representatives_semantics)
open ConstructionProbeAction (ActionLaws actionLaws actionLaws_freeClosed actionLaws_semantics)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

def oldAct {m : Nat} (w D S zero mul A b q r : Fin m) : Project.Formula 1 m :=
  (.conj (.mem (.bound b) (.bound D)) (.disj (.existsE (.existsE (.conj (old zero.succ.succ D.succ.succ 1
    q.succ.succ) (.conj (ProjectSyntax.encode id (product mul.succ.succ b.succ.succ 1 0)) (old zero.succ.succ
    D.succ.succ 0 r.succ.succ))))) (.existsE (.existsE (.existsE (.conj (cons w.succ.succ.succ
    D.succ.succ.succ S.succ.succ.succ 2 1 q.succ.succ.succ) (.conj (ProjectSyntax.encode id (product
    A.succ.succ.succ b.succ.succ.succ 2 0)) (cons w.succ.succ.succ D.succ.succ.succ S.succ.succ.succ 0 1
    r.succ.succ.succ))))))))

theorem oldAct_freeClosed {m : Nat} (w D S zero mul A b q r : Fin m) :
    (oldAct w D S zero mul A b q r).FreeClosed := by
  simp -implicitDefEqProofs [oldAct,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
    old_freeClosed,cons_freeClosed]

theorem oldAct_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w D S zero mul A b q r : Fin m) :
    Project.Formula.satisfies env (oldAct w D S zero mul A b q r) ↔
      OldAct (env.bound w) (env.bound D) (env.bound S) (env.bound zero)
        (env.bound mul) (env.bound A) (env.bound b) (env.bound q) (env.bound r) := by
  simp only [oldAct,OldAct,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_mem_iff,
    Project.Formula.satisfies_disj_iff,Project.Formula.satisfies_exists_iff,Project.Term.eval_bound,
    old_semantics hM,cons_semantics hM,GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    product_semantics (M := M)]
  rfl

def headDiv {m : Nat} (w D S zero mul A b q : Fin m) : Project.Formula 1 m :=
  (.disj (.existsE (.conj (old zero.succ D.succ 0 q.succ) (ProjectSyntax.encode id
    (ConstructionBaseMonoid.divides D.succ mul.succ b.succ 0)))) (.existsE (.existsE (.conj (cons w.succ.succ
    D.succ.succ S.succ.succ 1 0 q.succ.succ) (ConstructionProbeAlphabet.inCone S.succ.succ A.succ.succ
    b.succ.succ 1)))))

theorem headDiv_freeClosed {m : Nat} (w D S zero mul A b q : Fin m) :
    (headDiv w D S zero mul A b q).FreeClosed := by
  simp -implicitDefEqProofs [headDiv,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
    old_freeClosed,cons_freeClosed,ConstructionProbeAlphabet.inCone_freeClosed]

theorem headDiv_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w D S zero mul A b q : Fin m) :
    Project.Formula.satisfies env (headDiv w D S zero mul A b q) ↔
      HeadDiv (env.bound w) (env.bound D) (env.bound S) (env.bound zero)
        (env.bound mul) (env.bound A) (env.bound b) (env.bound q) := by
  simp only [headDiv,HeadDiv,Project.Formula.satisfies_disj_iff,Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_conj_iff,old_semantics hM,cons_semantics hM,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ConstructionBaseMonoid.divides_semantics (M := M),ConstructionProbeAlphabet.inCone_semantics hM]
  rfl

def actionPair {m : Nat} (w D S zero mul A p r : Fin m) : Project.Formula 1 m :=
  (.existsE (.existsE (.conj (ProjectSyntax.encode id (PairSyntax.ordered p.succ.succ 1 0)) (oldAct
    w.succ.succ D.succ.succ S.succ.succ zero.succ.succ mul.succ.succ A.succ.succ 1 0 r.succ.succ))))

theorem actionPair_freeClosed {m : Nat} (w D S zero mul A p r : Fin m) :
    (actionPair w D S zero mul A p r).FreeClosed := by
  simp -implicitDefEqProofs [actionPair,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
    oldAct_freeClosed]

theorem actionPair_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w D S zero mul A p r : Fin m) :
    Project.Formula.satisfies env (actionPair w D S zero mul A p r) ↔
      ∃ b q, PureKuratowski.Code M (env.bound p) b q ∧
        OldAct (env.bound w) (env.bound D) (env.bound S) (env.bound zero)
          (env.bound mul) (env.bound A) b q (env.bound r) := by
  simp only [actionPair,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_code,
    oldAct_semantics hM]
  rfl

def ActionGraph (w D S zero mul A B : M.Carrier .set) : Prop := ∀ b q r,
  Product B b q r ↔ OldAct w D S zero mul A b q r

theorem exists_action (hM : FirstOrder.Theory.Models M nativeZF)
    {w D S zero mul A e I R : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ z, ¬ (Project.FirstOrderSemantics.reduct M).mem z zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hm : LeftCancelMonoid D mul e) (hI : Representatives D S I) (hA : MapsTo I S A)
    (hR : Carrier w D S R) :
    ∃ J B, Representatives D R J ∧ MapsTo J R B ∧ ActionGraph w D S zero mul A B := by
  obtain ⟨J,hJ⟩ := exists_representatives hM D R
  let schema : Project.BinarySchema 6 := {
    body := actionPair 2 3 4 5 6 7 1 0
    freeClosed := actionPair_freeClosed _ _ _ _ _ _ _ _ }
  let env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) 6 :=
    { bound := Fin.cases w (Fin.cases D (Fin.cases S (Fin.cases zero (Fin.cases mul (fun _ => A))))),
      free := fun _ => w }
  have he : ∀ p r, schema.denote env p r ↔
      ∃ b q, PureKuratowski.Code M p b q ∧ OldAct w D S zero mul A b q r :=
    fun p r => actionPair_semantics hM ((env.push p).push r) 2 3 4 5 6 7 1 0
  obtain ⟨B,hB,hgraph⟩ := ZF.exists_setFunctionFromTo_of_denote (ModelTransfer.project_models_iff.mp hM)
    (KuratowskiZF.interpretation hM) schema env (source := J) (target := R) (by
      intro p hp
      obtain ⟨b,q,hb,hq,hcode⟩ := (hJ p).mp hp
      obtain ⟨r,hr⟩ := oldAct_total hM hw hz hzw hm hI hA hb ((hR q).mp hq)
      exact ⟨r,(he p r).mpr ⟨b,q,hcode,hr⟩⟩) (by
      intro p _ r r' hr hr'
      obtain ⟨b,q,hcode,hr⟩ := (he p r).mp hr
      obtain ⟨b',q',hcode',hr'⟩ := (he p r').mp hr'
      obtain ⟨rfl,rfl⟩ := PureKuratowski.code_injective hcode hcode'
      exact oldAct_unique hM hw hz hm hA hr hr') (by
      intro p r _ hr
      obtain ⟨b,q,_,hr⟩ := (he p r).mp hr
      exact (hR r).mpr (oldAct_raw hM hz hzw hr).2)
  refine ⟨J,B,hJ,(ForcingSupportSize.native_mapsTo hM J R B).mpr hB,fun b q r => ?_⟩
  constructor
  · rintro ⟨p,hcode,hpr⟩
    obtain ⟨_,hval⟩ := (hgraph p r).mp hpr
    obtain ⟨b',q',hcode',hr⟩ := (he p r).mp hval
    obtain ⟨rfl,rfl⟩ := PureKuratowski.code_injective hcode hcode'
    exact hr
  · intro hr
    obtain ⟨p,hcode⟩ := KuratowskiZF.exists_code hM b q
    exact ⟨p,hcode,(hgraph p r).mpr
      ⟨(hJ p).mpr ⟨b,q,hr.1,(hR q).mpr (oldAct_raw hM hz hzw hr).1,hcode⟩,
        (he p r).mpr ⟨b,q,hcode,hr⟩⟩⟩

def GraphLaws (w D S zero mul A e R B : M.Carrier .set) : Prop :=
  ActionLaws mul e R B ∧
  ∀ b q, (Project.FirstOrderSemantics.reduct M).mem b D →
    (HeadDiv w D S zero mul A b q ↔ ∃ r,
      (Project.FirstOrderSemantics.reduct M).mem r R ∧ Product B b r q)

theorem graph_laws (hM : FirstOrder.Theory.Models M nativeZF)
    {w D S zero mul A e R B : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ z, ¬ (Project.FirstOrderSemantics.reduct M).mem z zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hm : LeftCancelMonoid D mul e) (ha : ActionLaws mul e S A)
    (hR : Carrier w D S R) (hB : ActionGraph w D S zero mul A B) :
    GraphLaws w D S zero mul A e R B := by
  refine ⟨⟨?_,?_,?_⟩,?_⟩
  · intro q hq
    exact (hB e q q).mpr (oldAct_one hM hw hz hzw hm ha ((hR q).mp hq))
  · intro b a ba q r v hba har hbv
    exact (hB ba q v).mpr (oldAct_mul hM hw hz hm ha hba ((hB a q r).mp har) ((hB b r v).mp hbv))
  · intro b q r v hq hr
    exact oldAct_injective hM hw hz hm ha ((hB b q v).mp hq) ((hB b r v).mp hr)
  · intro b q hb
    refine (headDiv_iff hM hw hz hzw hb).trans ?_
    exact ⟨fun ⟨r,hr,ha⟩ => ⟨r,(hR r).mpr hr,(hB b r q).mpr ha⟩,
      fun ⟨r,hr,ha⟩ => ⟨r,(hR r).mp hr,(hB b r q).mp ha⟩⟩

def actionGraph {m : Nat} (w D S zero mul A B : Fin m) : Project.Formula 1 m :=
  (.forallE (.forallE (.forallE (.iff (ProjectSyntax.encode id (product B.succ.succ.succ 2 1 0)) (oldAct
    w.succ.succ.succ D.succ.succ.succ S.succ.succ.succ zero.succ.succ.succ mul.succ.succ.succ A.succ.succ.succ
    2 1 0)))))

theorem actionGraph_freeClosed {m : Nat} (w D S zero mul A B : Fin m) :
    (actionGraph w D S zero mul A B).FreeClosed := by
  simp -implicitDefEqProofs [actionGraph,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
    oldAct_freeClosed]

theorem actionGraph_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w D S zero mul A B : Fin m) :
    Project.Formula.satisfies env (actionGraph w D S zero mul A B) ↔
      ActionGraph (env.bound w) (env.bound D) (env.bound S) (env.bound zero)
        (env.bound mul) (env.bound A) (env.bound B) := by
  simp only [actionGraph,ActionGraph,Project.Formula.satisfies_forall_iff,
    Project.Formula.satisfies_iff_iff,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),product_semantics (M := M),
    oldAct_semantics hM]
  rfl

def graphLaws {m : Nat} (w D S zero mul A e R B : Fin m) : Project.Formula 1 m :=
  (.conj (actionLaws mul e R B) (.forallE (.forallE (.imp (.mem (.bound 1) (.bound D.succ.succ)) (.iff
    (headDiv w.succ.succ D.succ.succ S.succ.succ zero.succ.succ mul.succ.succ A.succ.succ 1 0) (.existsE
    (.conj (.mem (.bound 0) (.bound R.succ.succ.succ)) (ProjectSyntax.encode id (product B.succ.succ.succ 2 0
    1)))))))))

theorem graphLaws_freeClosed {m : Nat} (w D S zero mul A e R B : Fin m) :
    (graphLaws w D S zero mul A e R B).FreeClosed := by
  simp -implicitDefEqProofs [graphLaws,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
    actionLaws_freeClosed,headDiv_freeClosed]

theorem graphLaws_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w D S zero mul A e R B : Fin m) :
    Project.Formula.satisfies env (graphLaws w D S zero mul A e R B) ↔
      GraphLaws (env.bound w) (env.bound D) (env.bound S) (env.bound zero)
        (env.bound mul) (env.bound A) (env.bound e) (env.bound R) (env.bound B) := by
  simp only [graphLaws,GraphLaws,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_forall_iff,
    Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_iff_iff,Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,actionLaws_semantics hM,headDiv_semantics hM,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),product_semantics (M := M)]
  rfl

def constructionSentence : Project.Sentence where
  formula := Project.Formula.forallClosure 8
    (.imp (Project.Formula.isOmega (.bound 0))
      (.imp (Project.Formula.isEmpty (.bound 3))
        (.imp (.mem (.bound 3) (.bound 0))
          (.imp (ProjectSyntax.encode id (ForcingDiagramPoset.leftCancelMonoid (1 : Fin 8) 4 6))
            (.imp (representatives (1 : Fin 8) 2 7)
              (.imp (ProjectSyntax.encode id (Source.SetLanguage.mapsTo (5 : Fin 8) 7 2))
                (.imp (actionLaws (4 : Fin 8) 6 2 5)
                  (.existsE (.existsE (.existsE
                    (.conj (carrier (3 : Fin 11) 4 5 2)
                      (.conj (representatives (4 : Fin 11) 2 1)
                        (.conj (ProjectSyntax.encode id (Source.SetLanguage.mapsTo (0 : Fin 11) 1 2))
                          (.conj (actionGraph (3 : Fin 11) 4 5 6 7 8 0)
                            (graphLaws (3 : Fin 11) 4 5 6 7 8 9 2 0)))))))))))))))
  freeClosed := by simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,
    Project.Formula.isEmpty,ProjectSyntax.freeClosed,representatives_freeClosed,
    carrier_freeClosed,actionLaws_freeClosed,actionGraph_freeClosed,graphLaws_freeClosed]

theorem construction_models (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence constructionSentence).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) constructionSentence]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_isOmega_iff,
    Project.Formula.satisfies_isEmpty_iff,Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingDiagramPoset.leftCancelMonoid_semantics (M := M),representatives_semantics hM,
    ForcingSupportSize.mapsTo_semantics (M := M),actionLaws_semantics hM,
    Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,carrier_semantics hM,
    actionGraph_semantics hM,graphLaws_semantics hM]
  intro hw hz hzw hm hI hA ha
  obtain ⟨R,hR⟩ := exists_carrier hM hw (bound 1) (bound 2)
  obtain ⟨J,B,hJ,hB,hGraph⟩ := exists_action hM hw hz hzw hm hI hA hR
  exact ⟨R,J,B,hR,hJ,hB,hGraph,graph_laws hM hw hz hzw hm ha hR hGraph⟩

theorem construction_kernel_certificate : FirstOrder.Derives nativeZF []
    (Project.fo_sentence constructionSentence) := ModelTransfer.derives (fun _ hM => construction_models hM)

end PPAC.Migration.ConstructionProbeRawActionSyntax
