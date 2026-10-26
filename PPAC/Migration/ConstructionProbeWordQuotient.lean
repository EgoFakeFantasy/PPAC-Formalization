/- Pinned ProbeWords.Word.quotient: the unique internal preimage under oldAct.
The valid input domain is a separated subset of D x Word. No object choice. -/
import PPAC.Migration.ConstructionProbeWord

namespace PPAC.Migration.ConstructionProbeWordQuotient
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ConstructionProbeRawAction (OldAct HeadDiv oldAct_injective)
open ConstructionProbeRawActionSyntax (oldAct oldAct_freeClosed oldAct_semantics headDiv headDiv_freeClosed headDiv_semantics)
open ConstructionProbeReduced (reduced_oldAct)
open ConstructionProbeWord (WordCarrier wordCarrier wordCarrier_freeClosed wordCarrier_semantics exists_word_carrier)
open ForcingDiagramOrder (Product product product_semantics)
open ForcingDiagramPoset (LeftCancelMonoid)
open ForcingSupportSize (MapsTo)
open ConstructionProbeLetters (Representatives exists_representatives)
open ConstructionProbeAction (ActionLaws actionLaws actionLaws_freeClosed actionLaws_semantics)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

def QuotientValue (w D S zero mul A W a q r : M.Carrier .set) : Prop :=
  (Project.FirstOrderSemantics.reduct M).mem q W ∧
  (Project.FirstOrderSemantics.reduct M).mem r W ∧ OldAct w D S zero mul A a r q

theorem quotient_total (hM : FirstOrder.Theory.Models M nativeZF)
    {w D S zero mul A b W a q : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ z, ¬ (Project.FirstOrderSemantics.reduct M).mem z zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hW : WordCarrier w D S mul A b W)
    (ha : (Project.FirstOrderSemantics.reduct M).mem a D)
    (hq : (Project.FirstOrderSemantics.reduct M).mem q W)
    (hHead : HeadDiv w D S zero mul A a q) :
    ∃ r, QuotientValue w D S zero mul A W a q r := by
  obtain ⟨r,hr,hact⟩ := (ConstructionProbeWord.headDiv_iff hM hw hz hzw hW ha hq).mp hHead
  exact ⟨r,hq,hr,hact⟩

theorem quotient_unique (hM : FirstOrder.Theory.Models M nativeZF)
    {w D S zero mul A W e a q r r' : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ z, ¬ (Project.FirstOrderSemantics.reduct M).mem z zero)
    (hm : LeftCancelMonoid D mul e) (hALaws : ActionLaws mul e S A)
    (hr : QuotientValue w D S zero mul A W a q r)
    (hr' : QuotientValue w D S zero mul A W a q r') : r = r' :=
  oldAct_injective hM hw hz hm hALaws hr.2.2 hr'.2.2

theorem oldAct_quotient {w D S zero mul A W a q r : M.Carrier .set}
    (h : QuotientValue w D S zero mul A W a q r) : OldAct w D S zero mul A a r q := h.2.2

theorem quotient_oldAct_iff (hM : FirstOrder.Theory.Models M nativeZF)
    {w D S zero mul A W b e a q r t : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ z, ¬ (Project.FirstOrderSemantics.reduct M).mem z zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hm : LeftCancelMonoid D mul e) (hALaws : ActionLaws mul e S A)
    (hW : WordCarrier w D S mul A b W)
    (hq : (Project.FirstOrderSemantics.reduct M).mem q W)
    (hact : OldAct w D S zero mul A a q r) :
    QuotientValue w D S zero mul A W a r t ↔ t = q := by
  have hr : (Project.FirstOrderSemantics.reduct M).mem r W :=
    (hW r).mpr ((reduced_oldAct hM hw hz hzw hact).mpr ((hW q).mp hq))
  have hbase : QuotientValue w D S zero mul A W a r q := ⟨hr,hq,hact⟩
  exact ⟨fun ht => quotient_unique hM hw hz hm hALaws ht hbase,fun he => he.symm ▸ hbase⟩

def ValidPair (w D S zero mul A W p : M.Carrier .set) : Prop := ∃ a q,
  PureKuratowski.Code M p a q ∧ (Project.FirstOrderSemantics.reduct M).mem a D ∧
  (Project.FirstOrderSemantics.reduct M).mem q W ∧ HeadDiv w D S zero mul A a q

def QuotientDomain (w D S zero mul A W Q : M.Carrier .set) : Prop := ∀ p,
  (Project.FirstOrderSemantics.reduct M).mem p Q ↔ ValidPair w D S zero mul A W p

def quotientValue {m : Nat} (w D S zero mul A W a q r : Fin m) : Project.Formula 1 m :=
  (.conj (.mem (.bound q) (.bound W)) (.conj (.mem (.bound r) (.bound W)) (oldAct w D S zero mul A a r q)))

theorem quotientValue_freeClosed {m : Nat} (w D S zero mul A W a q r : Fin m) :
    (quotientValue w D S zero mul A W a q r).FreeClosed := by
  simp -implicitDefEqProofs [quotientValue,Definitional.Formula.FreeClosed,oldAct_freeClosed]

theorem quotientValue_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w D S zero mul A W a q r : Fin m) :
    Project.Formula.satisfies env (quotientValue w D S zero mul A W a q r) ↔
      QuotientValue (env.bound w) (env.bound D) (env.bound S) (env.bound zero) (env.bound mul)
        (env.bound A) (env.bound W) (env.bound a) (env.bound q) (env.bound r) := by
  simp only [quotientValue,QuotientValue,Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,oldAct_semantics hM]

def validPair {m : Nat} (w D S zero mul A W p : Fin m) : Project.Formula 1 m :=
  (.existsE (.existsE (.conj (ProjectSyntax.encode id (PairSyntax.ordered p.succ.succ 1 0)) (.conj (.mem
    (.bound 1) (.bound D.succ.succ)) (.conj (.mem (.bound 0) (.bound W.succ.succ)) (headDiv w.succ.succ
    D.succ.succ S.succ.succ zero.succ.succ mul.succ.succ A.succ.succ 1 0))))))

theorem validPair_freeClosed {m : Nat} (w D S zero mul A W p : Fin m) :
    (validPair w D S zero mul A W p).FreeClosed := by
  simp -implicitDefEqProofs [validPair,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
    headDiv_freeClosed]

theorem validPair_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w D S zero mul A W p : Fin m) :
    Project.Formula.satisfies env (validPair w D S zero mul A W p) ↔
      ValidPair (env.bound w) (env.bound D) (env.bound S) (env.bound zero) (env.bound mul)
        (env.bound A) (env.bound W) (env.bound p) := by
  simp only [validPair,ValidPair,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_code,
    headDiv_semantics hM]
  rfl

theorem exists_domain (hM : FirstOrder.Theory.Models M nativeZF) (w D S zero mul A W : M.Carrier .set) :
    ∃ Q, QuotientDomain w D S zero mul A W Q := by
  obtain ⟨J,hJ⟩ := exists_representatives hM D W
  let schema : Project.UnarySchema 7 := {
    body := validPair 1 2 3 4 5 6 7 0
    freeClosed := validPair_freeClosed _ _ _ _ _ _ _ _ }
  let env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) 7 :=
    { bound := Fin.cases w (Fin.cases D (Fin.cases S (Fin.cases zero (Fin.cases mul (Fin.cases A (fun _ => W)))))),
      free := fun _ => w }
  have he : ∀ p, schema.denote env p ↔ ValidPair w D S zero mul A W p :=
    fun p => validPair_semantics hM (env.push p) 1 2 3 4 5 6 7 0
  obtain ⟨Q,hQ⟩ := ZF.separation_exists_d (ModelTransfer.project_models_iff.mp hM) schema env J
  refine ⟨Q,fun p => (hQ p).trans ?_⟩
  constructor
  · exact fun h => (he p).mp h.2
  · intro h
    have hcopy := h
    obtain ⟨a,q,hcode,ha,hq,_⟩ := hcopy
    exact ⟨(hJ p).mpr ⟨a,q,ha,hq,hcode⟩,(he p).mpr h⟩

def quotientPair {m : Nat} (w D S zero mul A W p r : Fin m) : Project.Formula 1 m :=
  (.existsE (.existsE (.conj (ProjectSyntax.encode id (PairSyntax.ordered p.succ.succ 1 0)) (quotientValue
    w.succ.succ D.succ.succ S.succ.succ zero.succ.succ mul.succ.succ A.succ.succ W.succ.succ 1 0
    r.succ.succ))))

theorem quotientPair_freeClosed {m : Nat} (w D S zero mul A W p r : Fin m) :
    (quotientPair w D S zero mul A W p r).FreeClosed := by
  simp -implicitDefEqProofs [quotientPair,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
    quotientValue_freeClosed]

theorem quotientPair_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w D S zero mul A W p r : Fin m) :
    Project.Formula.satisfies env (quotientPair w D S zero mul A W p r) ↔
      ∃ a q, PureKuratowski.Code M (env.bound p) a q ∧
        QuotientValue (env.bound w) (env.bound D) (env.bound S) (env.bound zero) (env.bound mul)
          (env.bound A) (env.bound W) a q (env.bound r) := by
  simp only [quotientPair,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_code,
    quotientValue_semantics hM]
  rfl

def QuotientGraph (w D S zero mul A W G : M.Carrier .set) : Prop := ∀ a q r,
  Product G a q r ↔ QuotientValue w D S zero mul A W a q r

theorem exists_quotient_graph (hM : FirstOrder.Theory.Models M nativeZF)
    {w D S zero mul A b e W : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ z, ¬ (Project.FirstOrderSemantics.reduct M).mem z zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hm : LeftCancelMonoid D mul e) (hALaws : ActionLaws mul e S A)
    (hW : WordCarrier w D S mul A b W) :
    ∃ Q G, QuotientDomain w D S zero mul A W Q ∧ MapsTo Q W G ∧ QuotientGraph w D S zero mul A W G := by
  obtain ⟨Q,hQ⟩ := exists_domain hM w D S zero mul A W
  let schema : Project.BinarySchema 7 := {
    body := quotientPair 2 3 4 5 6 7 8 1 0
    freeClosed := quotientPair_freeClosed _ _ _ _ _ _ _ _ _ }
  let env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) 7 :=
    { bound := Fin.cases w (Fin.cases D (Fin.cases S (Fin.cases zero (Fin.cases mul (Fin.cases A (fun _ => W)))))),
      free := fun _ => w }
  have he : ∀ p r, schema.denote env p r ↔
      ∃ a q, PureKuratowski.Code M p a q ∧ QuotientValue w D S zero mul A W a q r :=
    fun p r => quotientPair_semantics hM ((env.push p).push r) 2 3 4 5 6 7 8 1 0
  obtain ⟨G,hG,hgraph⟩ := ZF.exists_setFunctionFromTo_of_denote (ModelTransfer.project_models_iff.mp hM)
    (KuratowskiZF.interpretation hM) schema env (source := Q) (target := W) (by
      intro p hp
      obtain ⟨a,q,hcode,ha,hq,hHead⟩ := (hQ p).mp hp
      obtain ⟨r,hr⟩ := quotient_total hM hw hz hzw hW ha hq hHead
      exact ⟨r,(he p r).mpr ⟨a,q,hcode,hr⟩⟩) (by
      intro p _ r r' hr hr'
      obtain ⟨a,q,hcode,hr⟩ := (he p r).mp hr
      obtain ⟨a',q',hcode',hr'⟩ := (he p r').mp hr'
      obtain ⟨rfl,rfl⟩ := PureKuratowski.code_injective hcode hcode'
      exact quotient_unique hM hw hz hm hALaws hr hr') (by
      intro p r _ hr
      obtain ⟨a,q,_,hr⟩ := (he p r).mp hr
      exact hr.2.1)
  refine ⟨Q,G,hQ,(ForcingSupportSize.native_mapsTo hM Q W G).mpr hG,fun a q r => ?_⟩
  constructor
  · rintro ⟨p,hcode,hpr⟩
    obtain ⟨_,hval⟩ := (hgraph p r).mp hpr
    obtain ⟨a',q',hcode',hr⟩ := (he p r).mp hval
    obtain ⟨rfl,rfl⟩ := PureKuratowski.code_injective hcode hcode'
    exact hr
  · intro hr
    have ha := hr.2.2.1
    have hHead := (ConstructionProbeWord.headDiv_iff hM hw hz hzw hW ha hr.1).mpr ⟨r,hr.2.1,hr.2.2⟩
    obtain ⟨p,hcode⟩ := KuratowskiZF.exists_code hM a q
    exact ⟨p,hcode,(hgraph p r).mpr
      ⟨(hQ p).mpr ⟨a,q,hcode,ha,hr.1,hHead⟩,(he p r).mpr ⟨a,q,hcode,hr⟩⟩⟩

def QuotientLaws (w D S zero mul A W G : M.Carrier .set) : Prop :=
  (∀ a q r, Product G a q r → OldAct w D S zero mul A a r q) ∧
  ∀ a q r t, (Project.FirstOrderSemantics.reduct M).mem q W →
    OldAct w D S zero mul A a q r → (Product G a r t ↔ t = q)

theorem quotient_laws (hM : FirstOrder.Theory.Models M nativeZF)
    {w D S zero mul A b e W G : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ z, ¬ (Project.FirstOrderSemantics.reduct M).mem z zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hm : LeftCancelMonoid D mul e) (hALaws : ActionLaws mul e S A)
    (hW : WordCarrier w D S mul A b W) (hG : QuotientGraph w D S zero mul A W G) :
    QuotientLaws w D S zero mul A W G := by
  refine ⟨fun a q r h => oldAct_quotient ((hG a q r).mp h),?_⟩
  intro a q r t hq hact
  exact (hG a r t).trans (quotient_oldAct_iff hM hw hz hzw hm hALaws hW hq hact)

def quotientDomain {m : Nat} (w D S zero mul A W Q : Fin m) : Project.Formula 1 m :=
  (.forallE (.iff (.mem (.bound 0) (.bound Q.succ)) (validPair w.succ D.succ S.succ zero.succ mul.succ A.succ
    W.succ 0)))

def quotientGraph {m : Nat} (w D S zero mul A W G : Fin m) : Project.Formula 1 m :=
  (.forallE (.forallE (.forallE (.iff (ProjectSyntax.encode id (product G.succ.succ.succ 2 1 0))
    (quotientValue w.succ.succ.succ D.succ.succ.succ S.succ.succ.succ zero.succ.succ.succ mul.succ.succ.succ
    A.succ.succ.succ W.succ.succ.succ 2 1 0)))))

def quotientLaws {m : Nat} (w D S zero mul A W G : Fin m) : Project.Formula 1 m :=
  (.conj (.forallE (.forallE (.forallE (.imp (ProjectSyntax.encode id (product G.succ.succ.succ 2 1 0))
    (oldAct w.succ.succ.succ D.succ.succ.succ S.succ.succ.succ zero.succ.succ.succ mul.succ.succ.succ
    A.succ.succ.succ 2 0 1))))) (.forallE (.forallE (.forallE (.forallE (.imp (.mem (.bound 2) (.bound
    W.succ.succ.succ.succ)) (.imp (oldAct w.succ.succ.succ.succ D.succ.succ.succ.succ S.succ.succ.succ.succ
    zero.succ.succ.succ.succ mul.succ.succ.succ.succ A.succ.succ.succ.succ 3 2 1) (.iff (ProjectSyntax.encode
    id (product G.succ.succ.succ.succ 3 1 0)) (Project.Formula.extensionalEq (.bound 0) (.bound 2))))))))))

theorem quotientDomain_freeClosed {m : Nat} (w D S zero mul A W Q : Fin m) :
    (quotientDomain w D S zero mul A W Q).FreeClosed := by
  simp -implicitDefEqProofs [quotientDomain,Definitional.Formula.FreeClosed,validPair_freeClosed]

theorem quotientGraph_freeClosed {m : Nat} (w D S zero mul A W G : Fin m) :
    (quotientGraph w D S zero mul A W G).FreeClosed := by
  simp -implicitDefEqProofs [quotientGraph,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
    quotientValue_freeClosed]

theorem quotientLaws_freeClosed {m : Nat} (w D S zero mul A W G : Fin m) :
    (quotientLaws w D S zero mul A W G).FreeClosed := by
  simp -implicitDefEqProofs [quotientLaws,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
    oldAct_freeClosed,Project.Formula.extensionalEq_freeClosed_iff]

theorem quotientDomain_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w D S zero mul A W Q : Fin m) :
    Project.Formula.satisfies env (quotientDomain w D S zero mul A W Q) ↔
      QuotientDomain (env.bound w) (env.bound D) (env.bound S) (env.bound zero) (env.bound mul)
        (env.bound A) (env.bound W) (env.bound Q) := by
  simp only [quotientDomain,QuotientDomain,Project.Formula.satisfies_forall_iff,
    Project.Formula.satisfies_iff_iff,Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    validPair_semantics hM]
  rfl

theorem quotientGraph_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w D S zero mul A W G : Fin m) :
    Project.Formula.satisfies env (quotientGraph w D S zero mul A W G) ↔
      QuotientGraph (env.bound w) (env.bound D) (env.bound S) (env.bound zero) (env.bound mul)
        (env.bound A) (env.bound W) (env.bound G) := by
  simp only [quotientGraph,QuotientGraph,Project.Formula.satisfies_forall_iff,
    Project.Formula.satisfies_iff_iff,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),product_semantics (M := M),
    quotientValue_semantics hM]
  rfl

theorem quotientLaws_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w D S zero mul A W G : Fin m) :
    Project.Formula.satisfies env (quotientLaws w D S zero mul A W G) ↔
      QuotientLaws (env.bound w) (env.bound D) (env.bound S) (env.bound zero) (env.bound mul)
        (env.bound A) (env.bound W) (env.bound G) := by
  simp only [quotientLaws,QuotientLaws,Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_imp_iff,
    Project.Formula.satisfies_iff_iff,Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    Project.Formula.satisfies_extensionalEq_iff_eq (ModelTransfer.extensionality hM),
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),product_semantics (M := M),
    oldAct_semantics hM]
  rfl

def constructionSentence : Project.Sentence where
  formula := Project.Formula.forallClosure 8
    (.imp (Project.Formula.isOmega (.bound 0))
      (.imp (Project.Formula.isEmpty (.bound 3))
        (.imp (.mem (.bound 3) (.bound 0))
          (.imp (ProjectSyntax.encode id (ForcingDiagramPoset.leftCancelMonoid (1 : Fin 8) 4 7))
            (.imp (actionLaws (4 : Fin 8) 7 2 5)
              (.imp (.mem (.bound 6) (.bound 1))
                (.existsE (.existsE (.existsE
                  (.conj (wordCarrier (3 : Fin 11) 4 5 7 8 9 2)
                    (.conj (quotientDomain (3 : Fin 11) 4 5 6 7 8 2 1)
                      (.conj (ProjectSyntax.encode id (Source.SetLanguage.mapsTo (0 : Fin 11) 1 2))
                        (.conj (quotientGraph (3 : Fin 11) 4 5 6 7 8 2 0)
                          (quotientLaws (3 : Fin 11) 4 5 6 7 8 2 0))))))))))))))
  freeClosed := by simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,
    Project.Formula.isEmpty,ProjectSyntax.freeClosed,actionLaws_freeClosed,wordCarrier_freeClosed,
    quotientDomain_freeClosed,quotientGraph_freeClosed,quotientLaws_freeClosed]

theorem construction_models (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence constructionSentence).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) constructionSentence]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_isOmega_iff,
    Project.Formula.satisfies_isEmpty_iff,Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingDiagramPoset.leftCancelMonoid_semantics (M := M),actionLaws_semantics hM,
    Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,wordCarrier_semantics hM,
    quotientDomain_semantics hM,ForcingSupportSize.mapsTo_semantics (M := M),
    quotientGraph_semantics hM,quotientLaws_semantics hM]
  intro hw hz hzw hm hALaws _hb
  obtain ⟨W,hW⟩ := exists_word_carrier hM hw (bound 1) (bound 2) (bound 4) (bound 5) (bound 6)
  obtain ⟨Q,G,hQ,hG,hGraph⟩ := exists_quotient_graph hM hw hz hzw hm hALaws hW
  exact ⟨W,Q,G,hW,hQ,hG,hGraph,quotient_laws hM hw hz hzw hm hALaws hW hGraph⟩

theorem construction_kernel_certificate : FirstOrder.Derives nativeZF []
    (Project.fo_sentence constructionSentence) := ModelTransfer.derives (fun _ hM => construction_models hM)

end PPAC.Migration.ConstructionProbeWordQuotient
