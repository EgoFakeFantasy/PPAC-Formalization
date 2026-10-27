/- Pinned MergerWords.Word.product_left_cancel:190 / LeftCancelMonoid:210.
Use the original old/old, mixed-length and snoc/snoc argument on ALL internal
Raw words. Native omega addition cancellation replaces the source omega tactic;
no new arithmetic/checker backend, external length restriction or right cancel.
Consumer: actual MergerData monoid, conditional joins and conservative old map. -/
import PPAC.Migration.ConstructionMergerWordLength

namespace PPAC.Migration.ConstructionMergerWordCancellation
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ConstructionProbeRaw (Raw Carrier Old Cons)
open ConstructionProbeLetters (Representatives)
open ConstructionProbeAction (projected projected_range)
open ConstructionMergerWordAction (ActionTable)
open ConstructionMergerWordProduct (Laws)
open ConstructionMergerWordLength (Length exists_length length_unique cons_lengths act_length product_length)
open ConstructionMergerAction (RightFreeAction)
open ConstructionBaseMonoid (AdditionGraph)
open ForcingDiagramOrder (Product product product_semantics)
open ForcingDiagramPoset (LeftCancelMonoid Conical)
open ForcingSupportSize (MapsTo)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

theorem product_old_ne_snoc (hM : FirstOrder.Theory.Models M nativeZF)
    {w D L zero mul A W B H T plus left oldq snocq out m s t : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ p, ¬ (Project.FirstOrderSemantics.reduct M).mem p zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hW : Carrier w D L W) (hH : MapsTo B W H) (hAdd : AdditionGraph hM w plus)
    (hTable : ActionTable w D L zero mul A T) (hLaws : Laws w D L zero T H)
    (hl : (Project.FirstOrderSemantics.reduct M).mem left W) (hOld : Old zero D m oldq)
    (hCons : Cons w D L s t snocq) (hpOld : Product H left oldq out) (hpSnoc : Product H left snocq out) : False := by
  obtain ⟨a,ha⟩ := exists_length ((hW left).mp hl)
  obtain ⟨c,hc⟩ := exists_length ((hW out).mp (projected_range hH hpOld))
  have hAct := (hTable left m out).mp ((hLaws.1 m left oldq out hOld).mp hpOld)
  have heq := act_length hM hw hz hAct ha hc
  subst c
  obtain ⟨b,hb⟩ := exists_length (ConstructionProbeRaw.cons_raw hCons).2
  have hProdLen := product_length hM hw hz hzw hAdd hTable hLaws hl hpSnoc ha hb hc
  have hPlus := ConstructionBaseMonoid.leftCancelMonoid hM hw hAdd hz hzw
  have hZero := ((hPlus.1.2 a ha.1 a).2).mpr rfl
  have hbEq := (hPlus.2.1 a ha.1).2.2 b zero a hb.1 hzw hProdLen hZero
  obtain ⟨n,m',_,hLen,hSucc⟩ := cons_lengths hCons
  have heM := length_unique hM hw hLen hb
  exact hz n (hbEq ▸ heM ▸ hSucc.predecessor_mem)

def cancelAt {m0 : Nat} (W H q : Fin m0) : Project.Formula 1 m0 :=
  (.forallE (.forallE (.forallE (.imp (.mem (.bound 2) (.bound W.succ.succ.succ)) (.imp (.mem (.bound 1)
  (.bound W.succ.succ.succ)) (.imp (ProjectSyntax.encode id (ForcingDiagramOrder.product H.succ.succ.succ 2
  q.succ.succ.succ 0)) (.imp (ProjectSyntax.encode id (ForcingDiagramOrder.product H.succ.succ.succ 2 1 0))
  (Project.Formula.extensionalEq (.bound q.succ.succ.succ) (.bound 1)))))))))

theorem cancelAt_freeClosed {m0 : Nat} (W H q : Fin m0) : (cancelAt W H q).FreeClosed := by
  simp -implicitDefEqProofs [cancelAt,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,Project.Formula.extensionalEq]

theorem cancelAt_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m0 : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m0) (W H q : Fin m0) :
    Project.Formula.satisfies env (cancelAt W H q) ↔
      ∀ left right out, (Project.FirstOrderSemantics.reduct M).mem left (env.bound W) →
        (Project.FirstOrderSemantics.reduct M).mem right (env.bound W) →
        Product (env.bound H) left (env.bound q) out → Product (env.bound H) left right out → env.bound q = right := by
  simp only [cancelAt,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_imp_iff,
    Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    Project.Formula.satisfies_extensionalEq_iff_eq (ModelTransfer.extensionality hM),
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),product_semantics (M := M)]
  rfl

theorem product_left_cancel (hM : FirstOrder.Theory.Models M nativeZF)
    {w D L zero mul A e W B H T plus left q right out : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ p, ¬ (Project.FirstOrderSemantics.reduct M).mem p zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hW : Carrier w D L W) (hH : MapsTo B W H) (hAdd : AdditionGraph hM w plus)
    (hTable : ActionTable w D L zero mul A T) (hLaws : Laws w D L zero T H)
    (hFree : RightFreeAction mul e W T)
    (hl : (Project.FirstOrderSemantics.reduct M).mem left W)
    (hq : (Project.FirstOrderSemantics.reduct M).mem q W) (hr : (Project.FirstOrderSemantics.reduct M).mem right W)
    (hp : Product H left q out) (hp' : Product H left right out) : q = right := by
  let env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) 2 := {
    bound := Fin.cases W (fun _ => H),free := fun _ => w }
  let p : Project.UnarySchema 2 := { body := cancelAt 1 2 0,freeClosed := cancelAt_freeClosed _ _ _ }
  have he (q) : p.denote env q ↔ ∀ left right out,
      (Project.FirstOrderSemantics.reduct M).mem left W → (Project.FirstOrderSemantics.reduct M).mem right W →
      Product H left q out → Product H left right out → q = right := cancelAt_semantics hM (env.push q) 1 2 0
  have hAll := ConstructionProbeEvaluationLaws.raw_induction hM env p hw hz hzw (by
    intro m q hOld
    apply (he q).mpr
    intro left right out hl hr hp hp'
    rcases ConstructionProbeRaw.cases_raw hM hw hz hzw ((hW right).mp hr) with ⟨n,hRight⟩ | ⟨s,t,hRight⟩
    · have hmn := hFree.2.2 left m n out ((hLaws.1 m left q out hOld).mp hp) ((hLaws.1 n left right out hRight).mp hp')
      subst n
      exact ConstructionProbeRaw.old_unique hM hOld hRight
    · exact (product_old_ne_snoc hM hw hz hzw hW hH hAdd hTable hLaws hl hOld hRight hp hp').elim) (by
    intro s t q hCons ih
    apply (he q).mpr
    intro left right out hl hr hp hp'
    rcases ConstructionProbeRaw.cases_raw hM hw hz hzw ((hW right).mp hr) with ⟨n,hRight⟩ | ⟨d,v,hRight⟩
    · exact (product_old_ne_snoc hM hw hz hzw hW hH hAdd hTable hLaws hl hRight hCons hp' hp).elim
    · obtain ⟨rt,hrt,hOut⟩ := (hLaws.2 s t q left out hCons).mp hp
      obtain ⟨rv,hrv,hOut'⟩ := (hLaws.2 d v right left out hRight).mp hp'
      obtain ⟨rfl,rfl⟩ := ConstructionProbeRaw.cons_injective hM hw hOut hOut'
      have htv := (he t).mp ih left v rt hl ((hW v).mpr (ConstructionProbeRaw.cons_raw hRight).1) hrt hrv
      subst v
      exact ConstructionProbeRaw.cons_unique hM hw hCons hRight)
  exact (he q).mp (hAll q ((hW q).mp hq)) left right out hl hr hp hp'

theorem exists_system (hM : FirstOrder.Theory.Models M nativeZF)
    {w n D mul e P zero : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ p, ¬ (Project.FirstOrderSemantics.reduct M).mem p zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hm : LeftCancelMonoid D mul e) (hc : Conical D mul e)
    (hP : ConstructionMergerRelations.Prescription n D P) (hValid : ConstructionMergerRelations.Valid n D mul P) :
    ∃ C L projection K A W I T B H unit, (Representatives n D C ∧ MapsTo C L projection ∧
      ConstructionMergerCopies.Copies n D mul P C L ∧ ConstructionMergerCopies.Projection n D mul P C projection ∧
      ConstructionMergerCopies.EqualityLaw n D mul P projection ∧ Representatives L D K ∧ MapsTo K L A ∧
      ConstructionMergerAction.ActionTable D mul projection A ∧ ConstructionMergerAction.RightFreeAction mul e L A ∧
      ConstructionMergerAction.CopyLaw D mul projection A ∧ Carrier w D L W ∧
      Representatives W D I ∧ MapsTo I W T ∧ ConstructionMergerWordAction.ActionTable w D L zero mul A T ∧
      ConstructionMergerAction.RightFreeAction mul e W T ∧ Representatives W W B ∧ MapsTo B W H ∧ Laws w D L zero T H) ∧
      Old zero D e unit ∧ LeftCancelMonoid W H unit ∧ Conical W H unit := by
  obtain ⟨C,L,projection,K,A,W,I,T,B,H,unit,hParent,hOldUnit,hUnit,hAssoc,hCon⟩ :=
    ConstructionMergerWordMonoid.exists_system hM hw hz hzw hm hc hP hValid
  have hRetained := hParent
  obtain ⟨hC,hp,hL,hProjection,hEq,hK,hA,hTable,hFree,hCopy,hW,hI,hT,hWordTable,hWordFree,hB,hH,hLaws⟩ := hParent
  obtain ⟨plus,hPlus⟩ := ConstructionBaseMonoid.exists_additionGraph hM hw
  refine ⟨C,L,projection,K,A,W,I,T,B,H,unit,hRetained,hOldUnit,⟨hUnit,?_,hAssoc⟩,hCon⟩
  intro left hl
  refine ⟨?_,?_,?_⟩
  · exact fun right hr => projected hM hB hH hl hr
  · exact fun right out out' _ ho ho' => ConstructionProbeHomEvaluation.product_unique hM hH ho ho'
  · exact fun q right out hq hr hp hp' => product_left_cancel hM hw hz hzw hW hH hPlus hWordTable hLaws hWordFree hl hq hr hp hp'

end PPAC.Migration.ConstructionMergerWordCancellation
