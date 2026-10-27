/- Pinned MergerWords.Word.act:105 / act_one:109 / act_mul:112 /
act_injective:179. Reuse the actual internal Raw carrier and constructors.
Raw.Cons appends the final internal letter, exactly source snoc; no reversal.
No opposite monoid or right-cancellation hypothesis is introduced.
Consumer: the original Word.product fold and product_left_cancel. -/
import PPAC.Migration.ConstructionMergerAction
import PPAC.Migration.ConstructionProbeHomEvaluation
import PPAC.Migration.ConstructionProbeEvaluationLaws

namespace PPAC.Migration.ConstructionMergerWordAction
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ConstructionProbeRaw (Raw Carrier Old Cons)
open ConstructionProbeLetters (Representatives exists_representatives)
open ConstructionProbeAction (projected projected_range)
open ConstructionMergerRelations (product_range)
open ConstructionMergerAction (RightFreeAction)
open ForcingDiagramOrder (Product product product_semantics)
open ForcingDiagramPoset (LeftCancelMonoid)
open ForcingSupportSize (MapsTo)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

def Act (w D L zero mul A q m out : M.Carrier .set) : Prop :=
  (Project.FirstOrderSemantics.reduct M).mem m D ∧
  ((∃ x xm, Old zero D x q ∧ Product mul x m xm ∧ Old zero D xm out) ∨
    ∃ s t sm, Cons w D L s t q ∧ Product A s m sm ∧ Cons w D L sm t out)

theorem act_raw (hM : FirstOrder.Theory.Models M nativeZF)
    {w D L zero mul A q m out : M.Carrier .set}
    (hz : ∀ p, ¬ (Project.FirstOrderSemantics.reduct M).mem p zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (h : Act w D L zero mul A q m out) : Raw w D L q ∧ Raw w D L out := by
  rcases h.2 with ⟨x,xm,hx,_,hxm⟩ | ⟨s,t,sm,hq,_,ho⟩
  · exact ⟨ConstructionProbeRaw.old_raw hM hz hzw hx,ConstructionProbeRaw.old_raw hM hz hzw hxm⟩
  · exact ⟨(ConstructionProbeRaw.cons_raw hq).2,(ConstructionProbeRaw.cons_raw ho).2⟩

theorem act_total (hM : FirstOrder.Theory.Models M nativeZF)
    {w D L zero mul A e K q m : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ p, ¬ (Project.FirstOrderSemantics.reduct M).mem p zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hm : LeftCancelMonoid D mul e) (hK : Representatives L D K) (hA : MapsTo K L A)
    (hq : Raw w D L q) (hmD : (Project.FirstOrderSemantics.reduct M).mem m D) :
    ∃ out, Act w D L zero mul A q m out := by
  rcases ConstructionProbeRaw.cases_raw hM hw hz hzw hq with ⟨x,hOld⟩ | ⟨s,t,hCons⟩
  · obtain ⟨xm,hxmD,hxm⟩ := (hm.2.1 x hOld.1).1 m hmD
    obtain ⟨out,hOut⟩ := ConstructionProbeRaw.exists_old hM (zero := zero) hxmD
    exact ⟨out,hmD,Or.inl ⟨x,xm,hOld,hxm,hOut⟩⟩
  · have hs : (Project.FirstOrderSemantics.reduct M).mem s L := by
      rcases hCons with ⟨_,_,_,_,_,_,_,_,_,_,_,hs,_,_,_⟩
      exact hs
    obtain ⟨sm,hsm,hProd⟩ := projected hM hK hA hs hmD
    obtain ⟨out,hOut⟩ := ConstructionProbeRaw.exists_cons hM hw hsm (ConstructionProbeRaw.cons_raw hCons).1
    exact ⟨out,hmD,Or.inr ⟨s,t,sm,hCons,hProd,hOut⟩⟩

theorem act_unique (hM : FirstOrder.Theory.Models M nativeZF)
    {w D L zero mul A e K q m out out' : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ p, ¬ (Project.FirstOrderSemantics.reduct M).mem p zero)
    (hm : LeftCancelMonoid D mul e) (hA : MapsTo K L A)
    (h : Act w D L zero mul A q m out) (h' : Act w D L zero mul A q m out') : out = out' := by
  rcases h.2 with ⟨x,xm,hOld,hProd,hOut⟩ | ⟨s,t,sm,hCons,hProd,hOut⟩ <;>
    rcases h'.2 with ⟨y,ym,hOld',hProd',hOut'⟩ | ⟨s',t',sm',hCons',hProd',hOut'⟩
  · have he := ConstructionProbeRaw.old_injective hOld hOld'
    subst y
    have hev := (hm.2.1 x hOld.1).2.1 m xm ym h.1 hProd hProd'
    subst ym
    exact ConstructionProbeRaw.old_unique hM hOut hOut'
  · exact (ConstructionProbeRaw.old_ne_cons hz hOld hCons').elim
  · exact (ConstructionProbeRaw.old_ne_cons hz hOld' hCons).elim
  · obtain ⟨rfl,rfl⟩ := ConstructionProbeRaw.cons_injective hM hw hCons hCons'
    have he := ConstructionProbeHomEvaluation.product_unique hM hA hProd hProd'
    subst sm'
    exact ConstructionProbeRaw.cons_unique hM hw hOut hOut'

theorem act_one (hM : FirstOrder.Theory.Models M nativeZF)
    {w D L zero mul A e q : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ p, ¬ (Project.FirstOrderSemantics.reduct M).mem p zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hm : LeftCancelMonoid D mul e) (hFree : RightFreeAction mul e L A)
    (hq : Raw w D L q) : Act w D L zero mul A q e q := by
  refine ⟨hm.1.1,?_⟩
  rcases ConstructionProbeRaw.cases_raw hM hw hz hzw hq with ⟨x,hOld⟩ | ⟨s,t,hCons⟩
  · exact Or.inl ⟨x,x,hOld,((hm.1.2 x hOld.1 x).2).mpr rfl,hOld⟩
  · have hs : (Project.FirstOrderSemantics.reduct M).mem s L := by
      rcases hCons with ⟨_,_,_,_,_,_,_,_,_,_,_,hs,_,_,_⟩
      exact hs
    exact Or.inr ⟨s,t,s,hCons,hFree.1 s hs,hCons⟩

theorem act_mul (hM : FirstOrder.Theory.Models M nativeZF)
    {w D L zero mul A e q x y xy u out : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ p, ¬ (Project.FirstOrderSemantics.reduct M).mem p zero)
    (hm : LeftCancelMonoid D mul e) (hFree : RightFreeAction mul e L A)
    (hxy : Product mul x y xy) (h : Act w D L zero mul A q x u)
    (h' : Act w D L zero mul A u y out) : Act w D L zero mul A q xy out := by
  refine ⟨product_range hm h.1 h'.1 hxy,?_⟩
  rcases h.2 with ⟨a,ax,hOld,hProd,hMid⟩ | ⟨s,t,sx,hCons,hProd,hMid⟩ <;>
    rcases h'.2 with ⟨b,byv,hMid',hProd',hOut⟩ | ⟨s',t',sy,hMid',hProd',hOut⟩
  · have he := ConstructionProbeRaw.old_injective hMid hMid'
    subst b
    exact Or.inl ⟨a,byv,hOld,(hm.2.2 a x y ax xy byv hOld.1 h.1 h'.1 hProd hxy).mp hProd',hOut⟩
  · exact (ConstructionProbeRaw.old_ne_cons hz hMid hMid').elim
  · exact (ConstructionProbeRaw.old_ne_cons hz hMid' hMid).elim
  · obtain ⟨rfl,rfl⟩ := ConstructionProbeRaw.cons_injective hM hw hMid hMid'
    exact Or.inr ⟨s,t,sy,hCons,hFree.2.1 s x y xy sx sy hxy hProd hProd',hOut⟩

theorem factor_injective (hM : FirstOrder.Theory.Models M nativeZF)
    {w D L zero mul A e q x y out : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ p, ¬ (Project.FirstOrderSemantics.reduct M).mem p zero)
    (hm : LeftCancelMonoid D mul e) (hFree : RightFreeAction mul e L A)
    (h : Act w D L zero mul A q x out) (h' : Act w D L zero mul A q y out) : x = y := by
  rcases h.2 with ⟨a,ax,hOld,hProd,hOut⟩ | ⟨s,t,sx,hCons,hProd,hOut⟩ <;>
    rcases h'.2 with ⟨b,byv,hOld',hProd',hOut'⟩ | ⟨s',t',sy,hCons',hProd',hOut'⟩
  · have he := ConstructionProbeRaw.old_injective hOld hOld'
    subst b
    have heOut := ConstructionProbeRaw.old_injective hOut hOut'
    exact (hm.2.1 a hOld.1).2.2 x y ax h.1 h'.1 hProd (heOut.symm ▸ hProd')
  · exact (ConstructionProbeRaw.old_ne_cons hz hOld hCons').elim
  · exact (ConstructionProbeRaw.old_ne_cons hz hOld' hCons).elim
  · obtain ⟨rfl,rfl⟩ := ConstructionProbeRaw.cons_injective hM hw hCons hCons'
    have heOut := (ConstructionProbeRaw.cons_injective hM hw hOut hOut').1
    exact hFree.2.2 s x y sx hProd (heOut.symm ▸ hProd')

def act {m0 : Nat} (w D L zero mul A q m out : Fin m0) : Project.Formula 1 m0 :=
  (.conj (.mem (.bound m) (.bound D)) (.disj (.existsE (.existsE (.conj (ConstructionProbeRaw.old
  zero.succ.succ D.succ.succ 1 q.succ.succ) (.conj (ProjectSyntax.encode id (ForcingDiagramOrder.product
  mul.succ.succ 1 m.succ.succ 0)) (ConstructionProbeRaw.old zero.succ.succ D.succ.succ 0 out.succ.succ)))))
  (.existsE (.existsE (.existsE (.conj (ConstructionProbeRaw.cons w.succ.succ.succ D.succ.succ.succ
  L.succ.succ.succ 2 1 q.succ.succ.succ) (.conj (ProjectSyntax.encode id (ForcingDiagramOrder.product
  A.succ.succ.succ 2 m.succ.succ.succ 0)) (ConstructionProbeRaw.cons w.succ.succ.succ D.succ.succ.succ
  L.succ.succ.succ 0 1 out.succ.succ.succ))))))))

theorem act_freeClosed {m0 : Nat} (w D L zero mul A q m out : Fin m0) : (act w D L zero mul A q m out).FreeClosed := by
  simp -implicitDefEqProofs [act,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,ConstructionProbeRaw.old_freeClosed,ConstructionProbeRaw.cons_freeClosed]

theorem act_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m0 : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m0) (w D L zero mul A q m out : Fin m0) :
    Project.Formula.satisfies env (act w D L zero mul A q m out) ↔ Act (env.bound w) (env.bound D) (env.bound L) (env.bound zero) (env.bound mul) (env.bound A) (env.bound q) (env.bound m) (env.bound out) := by
  simp only [act,Act,Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_disj_iff,
    Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,ConstructionProbeRaw.old_semantics hM,ConstructionProbeRaw.cons_semantics hM,GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),product_semantics (M := M)]
  rfl

def actPair {m0 : Nat} (w D L zero mul A p out : Fin m0) : Project.Formula 1 m0 :=
  (.existsE (.existsE (.conj (PureKuratowskiProject.code (.bound p.succ.succ) (.bound 1) (.bound 0)) (act
  w.succ.succ D.succ.succ L.succ.succ zero.succ.succ mul.succ.succ A.succ.succ 1 0 out.succ.succ))))

theorem actPair_freeClosed {m0 : Nat} (w D L zero mul A p out : Fin m0) : (actPair w D L zero mul A p out).FreeClosed := by
  simp -implicitDefEqProofs [actPair,Definitional.Formula.FreeClosed,PureKuratowskiProject.code,act_freeClosed]

theorem actPair_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m0 : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m0) (w D L zero mul A p out : Fin m0) :
    Project.Formula.satisfies env (actPair w D L zero mul A p out) ↔ (∃ q m, PureKuratowski.Code M (env.bound p) q m ∧ Act (env.bound w) (env.bound D) (env.bound L) (env.bound zero) (env.bound mul) (env.bound A) q m (env.bound out)) := by
  simp only [actPair,Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_conj_iff,
    Project.Term.eval_bound,KuratowskiZF.code_correct hM,act_semantics hM]
  rfl

def ActionTable (w D L zero mul A T : M.Carrier .set) : Prop := ∀ q m out,
  Product T q m out ↔ Act w D L zero mul A q m out

theorem exists_word_action (hM : FirstOrder.Theory.Models M nativeZF)
    {w D L zero mul A e K W : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ p, ¬ (Project.FirstOrderSemantics.reduct M).mem p zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hm : LeftCancelMonoid D mul e) (hK : Representatives L D K) (hA : MapsTo K L A)
    (hFree : RightFreeAction mul e L A) (hW : Carrier w D L W) :
    ∃ I T, Representatives W D I ∧ MapsTo I W T ∧ ActionTable w D L zero mul A T ∧
      RightFreeAction mul e W T := by
  obtain ⟨I,hI⟩ := exists_representatives hM W D
  let schema : Project.BinarySchema 6 := { body := actPair 2 3 4 5 6 7 1 0, freeClosed := actPair_freeClosed _ _ _ _ _ _ _ _ }
  let env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) 6 := {
    bound := Fin.cases w (Fin.cases D (Fin.cases L (Fin.cases zero (Fin.cases mul (fun _ => A))))), free := fun _ => w }
  have he : ∀ p out, schema.denote env p out ↔ ∃ q m, PureKuratowski.Code M p q m ∧ Act w D L zero mul A q m out :=
    fun p out => actPair_semantics hM ((env.push p).push out) 2 3 4 5 6 7 1 0
  obtain ⟨T,hT,hgraph⟩ := ZF.exists_setFunctionFromTo_of_denote (ModelTransfer.project_models_iff.mp hM)
    (KuratowskiZF.interpretation hM) schema env (source := I) (target := W) (by
      intro p hpI
      obtain ⟨q,m,hq,hmD,hcode⟩ := (hI p).mp hpI
      obtain ⟨out,hAct⟩ := act_total hM hw hz hzw hm hK hA ((hW q).mp hq) hmD
      exact ⟨out,(he p out).mpr ⟨q,m,hcode,hAct⟩⟩) (by
      intro p _ out out' ho ho'
      obtain ⟨q,m,hcode,ha⟩ := (he p out).mp ho
      obtain ⟨q',m',hcode',ha'⟩ := (he p out').mp ho'
      obtain ⟨rfl,rfl⟩ := PureKuratowski.code_injective hcode hcode'
      exact act_unique hM hw hz hm hA ha ha') (by
      intro p out _ ho
      obtain ⟨q,m,_,ha⟩ := (he p out).mp ho
      exact (hW out).mpr (act_raw hM hz hzw ha).2)
  have hTable : ActionTable w D L zero mul A T := by
    intro q m out
    constructor
    · rintro ⟨p,hcode,hpo⟩
      obtain ⟨_,hval⟩ := (hgraph p out).mp hpo
      obtain ⟨q',m',hcode',ha⟩ := (he p out).mp hval
      obtain ⟨rfl,rfl⟩ := PureKuratowski.code_injective hcode hcode'
      exact ha
    · intro ha
      obtain ⟨p,hcode⟩ := KuratowskiZF.exists_code hM q m
      exact ⟨p,hcode,(hgraph p out).mpr ⟨(hI p).mpr ⟨q,m,(hW q).mpr (act_raw hM hz hzw ha).1,ha.1,hcode⟩,
        (he p out).mpr ⟨q,m,hcode,ha⟩⟩⟩
  refine ⟨I,T,hI,(ForcingSupportSize.native_mapsTo hM I W T).mpr hT,hTable,?_,?_,?_⟩
  · exact fun q hq => (hTable q e q).mpr (act_one hM hw hz hzw hm hFree ((hW q).mp hq))
  · exact fun q x y xy u out hxy hxu hyout => (hTable q xy out).mpr
      (act_mul hM hw hz hm hFree hxy ((hTable q x u).mp hxu) ((hTable u y out).mp hyout))
  · exact fun q x y out hx hy => factor_injective hM hw hz hm hFree ((hTable q x out).mp hx) ((hTable q y out).mp hy)

theorem exists_system (hM : FirstOrder.Theory.Models M nativeZF)
    {w n D mul e P zero : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ p, ¬ (Project.FirstOrderSemantics.reduct M).mem p zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hm : LeftCancelMonoid D mul e) (hP : ConstructionMergerRelations.Prescription n D P)
    (hValid : ConstructionMergerRelations.Valid n D mul P) :
    ∃ C L projection K A W I T, Representatives n D C ∧ MapsTo C L projection ∧
      ConstructionMergerCopies.Copies n D mul P C L ∧ ConstructionMergerCopies.Projection n D mul P C projection ∧
      ConstructionMergerCopies.EqualityLaw n D mul P projection ∧ Representatives L D K ∧ MapsTo K L A ∧
      ConstructionMergerAction.ActionTable D mul projection A ∧ RightFreeAction mul e L A ∧
      ConstructionMergerAction.CopyLaw D mul projection A ∧ Carrier w D L W ∧
      Representatives W D I ∧ MapsTo I W T ∧ ActionTable w D L zero mul A T ∧ RightFreeAction mul e W T := by
  obtain ⟨C,L,projection,K,A,hC,hp,hL,hProjection,hEq,hK,hA,hTable,hFree,hCopy⟩ :=
    ConstructionMergerAction.exists_system hM hm hP hValid
  obtain ⟨W,hW⟩ := ConstructionProbeRaw.exists_carrier hM hw D L
  obtain ⟨I,T,hI,hT,hWordTable,hWordFree⟩ := exists_word_action hM hw hz hzw hm hK hA hFree hW
  exact ⟨C,L,projection,K,A,W,I,T,hC,hp,hL,hProjection,hEq,hK,hA,hTable,hFree,hCopy,hW,hI,hT,hWordTable,hWordFree⟩

def actionTable {m0 : Nat} (w D L zero mul A T : Fin m0) : Project.Formula 1 m0 :=
  (.forallE (.forallE (.forallE (.iff (ProjectSyntax.encode id (ForcingDiagramOrder.product T.succ.succ.succ
  2 1 0)) (act w.succ.succ.succ D.succ.succ.succ L.succ.succ.succ zero.succ.succ.succ mul.succ.succ.succ
  A.succ.succ.succ 2 1 0)))))

theorem actionTable_freeClosed {m0 : Nat} (w D L zero mul A T : Fin m0) :
    (actionTable w D L zero mul A T).FreeClosed := by
  simp -implicitDefEqProofs [actionTable,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,act_freeClosed]

theorem actionTable_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m0 : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m0) (w D L zero mul A T : Fin m0) :
    Project.Formula.satisfies env (actionTable w D L zero mul A T) ↔
      ActionTable (env.bound w) (env.bound D) (env.bound L) (env.bound zero) (env.bound mul) (env.bound A) (env.bound T) := by
  simp only [actionTable,ActionTable,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_iff_iff,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    product_semantics (M := M),act_semantics hM]
  rfl

end PPAC.Migration.ConstructionMergerWordAction
