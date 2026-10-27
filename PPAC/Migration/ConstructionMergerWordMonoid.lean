/- Pinned MergerWords.Word.product_act:122 / product_assoc:128 /
old_one_product:134 / Monoid:139 / factors_of_old:217 / IsConical:225.
Consume the ACTUAL action/product tables. Associativity and left unit use the
existing formula-indexed Raw induction, including nonstandard internal lengths.
Consumer: source Word left cancellation, conditional joins, weighted MergerData. -/
import PPAC.Migration.ConstructionMergerWordProduct

namespace PPAC.Migration.ConstructionMergerWordMonoid
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ConstructionProbeRaw (Raw Carrier Old Cons)
open ConstructionProbeLetters (Representatives)
open ConstructionProbeAction (projected projected_range)
open ConstructionProbeHomEvaluation (product_unique)
open ConstructionMergerAction (RightFreeAction)
open ConstructionMergerWordAction (ActionTable)
open ConstructionMergerWordProduct (Laws)
open ForcingDiagramOrder (Product product product_semantics)
open ForcingDiagramPoset (LeftCancelMonoid Unit Associative Conical)
open ForcingSupportSize (MapsTo)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

theorem product_act (hM : FirstOrder.Theory.Models M nativeZF)
    {w D L zero mul A e W I T B H left y m ly ym out1 out2 : M.Carrier .set}
    (hT : MapsTo I W T) (hH : MapsTo B W H) (hFree : RightFreeAction mul e W T)
    (hTable : ActionTable w D L zero mul A T) (hLaws : Laws w D L zero T H)
    (hLy : Product H left y ly) (hYm : Product T y m ym)
    (hLym : Product H left ym out1) (hLym' : Product T ly m out2) : out1 = out2 := by
  have hAct := (hTable y m ym).mp hYm
  rcases hAct.2 with ⟨n,nm,hOld,hProd,hOldYm⟩ | ⟨s,t,sm,hCons,hProd,hConsYm⟩
  · have hLn := (hLaws.1 n left y ly hOld).mp hLy
    have hLnm := (hLaws.1 nm left ym out1 hOldYm).mp hLym
    exact product_unique hM hT hLnm (hFree.2.1 left n m nm ly out2 hProd hLn hLym')
  · obtain ⟨v,hLv,hConsLy⟩ := (hLaws.2 s t y left ly hCons).mp hLy
    obtain ⟨v',hLv',hConsOut⟩ := (hLaws.2 sm t ym left out1 hConsYm).mp hLym
    have he := product_unique hM hH hLv hLv'
    subst v'
    have hActOut : ConstructionMergerWordAction.Act w D L zero mul A ly m out1 :=
      ⟨hAct.1,Or.inr ⟨s,v,sm,hConsLy,hProd,hConsOut⟩⟩
    exact product_unique hM hT ((hTable ly m out1).mpr hActOut) hLym'

def assocAt {m0 : Nat} (W H z : Fin m0) : Project.Formula 1 m0 :=
  (.forallE (.forallE (.forallE (.forallE (.forallE (.forallE (.imp (.mem (.bound 5) (.bound
  W.succ.succ.succ.succ.succ.succ)) (.imp (.mem (.bound 4) (.bound W.succ.succ.succ.succ.succ.succ)) (.imp
  (ProjectSyntax.encode id (ForcingDiagramOrder.product H.succ.succ.succ.succ.succ.succ 5 4 3)) (.imp
  (ProjectSyntax.encode id (ForcingDiagramOrder.product H.succ.succ.succ.succ.succ.succ 4
  z.succ.succ.succ.succ.succ.succ 2)) (.imp (ProjectSyntax.encode id (ForcingDiagramOrder.product
  H.succ.succ.succ.succ.succ.succ 3 z.succ.succ.succ.succ.succ.succ 1)) (.imp (ProjectSyntax.encode id
  (ForcingDiagramOrder.product H.succ.succ.succ.succ.succ.succ 5 2 0)) (Project.Formula.extensionalEq
  (.bound 1) (.bound 0))))))))))))))

theorem assocAt_freeClosed {m0 : Nat} (W H z : Fin m0) : (assocAt W H z).FreeClosed := by
  simp -implicitDefEqProofs [assocAt,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,Project.Formula.extensionalEq]

theorem assocAt_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m0 : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m0) (W H z : Fin m0) :
    Project.Formula.satisfies env (assocAt W H z) ↔ (∀ x y xy yz r s, (Project.FirstOrderSemantics.reduct M).mem x (env.bound W) → (Project.FirstOrderSemantics.reduct M).mem y (env.bound W) → Product (env.bound H) x y xy → Product (env.bound H) y (env.bound z) yz → Product (env.bound H) xy (env.bound z) r → Product (env.bound H) x yz s → r = s) := by
  simp only [assocAt,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_imp_iff,
    Project.Formula.satisfies_mem_iff,
    Project.Formula.satisfies_extensionalEq_iff_eq (ModelTransfer.extensionality hM),Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),product_semantics (M := M)]
  rfl

def unitAt {m0 : Nat} (H unit z : Fin m0) : Project.Formula 1 m0 :=
  (.forallE (.iff (ProjectSyntax.encode id (ForcingDiagramOrder.product H.succ unit.succ z.succ 0))
  (Project.Formula.extensionalEq (.bound 0) (.bound z.succ))))

theorem unitAt_freeClosed {m0 : Nat} (H unit z : Fin m0) : (unitAt H unit z).FreeClosed := by
  simp -implicitDefEqProofs [unitAt,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,Project.Formula.extensionalEq]

theorem unitAt_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m0 : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m0) (H unit z : Fin m0) :
    Project.Formula.satisfies env (unitAt H unit z) ↔ (∀ out, Product (env.bound H) (env.bound unit) (env.bound z) out ↔ out = env.bound z) := by
  simp only [unitAt,Project.Formula.satisfies_forall_iff,
    Project.Formula.satisfies_iff_iff,
    Project.Formula.satisfies_extensionalEq_iff_eq (ModelTransfer.extensionality hM),Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),product_semantics (M := M)]
  rfl

theorem associative (hM : FirstOrder.Theory.Models M nativeZF)
    {w D L zero mul A e W I T B H : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ p, ¬ (Project.FirstOrderSemantics.reduct M).mem p zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hW : Carrier w D L W) (hB : Representatives W W B) (hH : MapsTo B W H)
    (hT : MapsTo I W T) (hFree : RightFreeAction mul e W T)
    (hTable : ActionTable w D L zero mul A T) (hLaws : Laws w D L zero T H) : Associative W H := by
  let env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) 2 := {
    bound := Fin.cases W (fun _ => H),free := fun _ => w }
  let p : Project.UnarySchema 2 := { body := assocAt 1 2 0,freeClosed := assocAt_freeClosed _ _ _ }
  have he (z) : p.denote env z ↔ ∀ x y xy yz r s,
      (Project.FirstOrderSemantics.reduct M).mem x W → (Project.FirstOrderSemantics.reduct M).mem y W →
      Product H x y xy → Product H y z yz → Product H xy z r → Product H x yz s → r = s :=
    assocAt_semantics hM (env.push z) 1 2 0
  have hAll := ConstructionProbeEvaluationLaws.raw_induction hM env p hw hz hzw (by
    intro n q hOld
    apply (he q).mpr
    intro x y xy yz r s _ _ hxy hyq hxyq hxys
    exact (product_act hM hT hH hFree hTable hLaws hxy ((hLaws.1 n y q yz hOld).mp hyq)
      hxys ((hLaws.1 n xy q r hOld).mp hxyq)).symm) (by
    intro d t q hCons ih
    apply (he q).mpr
    intro x y xy yz r s hx hy hxy hyq hxyq hxys
    obtain ⟨yt,hyt,hConsY⟩ := (hLaws.2 d t q y yz hCons).mp hyq
    obtain ⟨rt,hxyt,hConsR⟩ := (hLaws.2 d t q xy r hCons).mp hxyq
    obtain ⟨st,hxyt',hConsS⟩ := (hLaws.2 d yt yz x s hConsY).mp hxys
    have hEq := (he t).mp ih x y xy yt rt st hx hy hxy hyt hxyt hxyt'
    subst st
    exact ConstructionProbeRaw.cons_unique hM hw hConsR hConsS)
  intro a b c ab bc z ha hb hc hab hbc
  have hAssoc := (he c).mp (hAll c ((hW c).mp hc))
  constructor
  · intro hzc
    obtain ⟨r,_,hr⟩ := projected hM hB hH ha (projected_range hH hbc)
    have heq := hAssoc a b ab bc z r ha hb hab hbc hzc hr
    exact heq.symm ▸ hr
  · intro haz
    obtain ⟨r,_,hr⟩ := projected hM hB hH (projected_range hH hab) hc
    have heq := hAssoc a b ab bc r z ha hb hab hbc hr haz
    exact heq ▸ hr

theorem unit_laws (hM : FirstOrder.Theory.Models M nativeZF)
    {w D L zero mul A e W I T H unit : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ p, ¬ (Project.FirstOrderSemantics.reduct M).mem p zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hm : LeftCancelMonoid D mul e) (hW : Carrier w D L W) (hT : MapsTo I W T)
    (hFree : RightFreeAction mul e W T) (hTable : ActionTable w D L zero mul A T)
    (hLaws : Laws w D L zero T H) (hUnit : Old zero D e unit) : Unit W H unit := by
  let env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) 2 := {
    bound := Fin.cases H (fun _ => unit),free := fun _ => w }
  let p : Project.UnarySchema 2 := { body := unitAt 1 2 0,freeClosed := unitAt_freeClosed _ _ _ }
  have he (z) : p.denote env z ↔ ∀ out, Product H unit z out ↔ out = z :=
    unitAt_semantics hM (env.push z) 1 2 0
  have hAll := ConstructionProbeEvaluationLaws.raw_induction hM env p hw hz hzw (by
    intro m q hOld
    have hTunit : Product T unit m q := (hTable unit m q).mpr
      ⟨hOld.1,Or.inl ⟨e,m,hUnit,((hm.1.2 m hOld.1 m).1).mpr rfl,hOld⟩⟩
    apply (he q).mpr
    intro out
    constructor
    · intro ho
      exact product_unique hM hT ((hLaws.1 m unit q out hOld).mp ho) hTunit
    · intro heq
      subst out
      exact (hLaws.1 m unit q q hOld).mpr hTunit) (by
    intro d t q hCons ih
    apply (he q).mpr
    intro out
    constructor
    · intro ho
      obtain ⟨v,hv,hvOut⟩ := (hLaws.2 d t q unit out hCons).mp ho
      have hvEq := ((he t).mp ih v).mp hv
      subst v
      exact ConstructionProbeRaw.cons_unique hM hw hvOut hCons
    · intro heq
      subst out
      exact (hLaws.2 d t q unit q hCons).mpr ⟨t,((he t).mp ih t).mpr rfl,hCons⟩)
  refine ⟨(hW unit).mpr (ConstructionProbeRaw.old_raw hM hz hzw hUnit),?_⟩
  intro x hx out
  refine ⟨(he x).mp (hAll x ((hW x).mp hx)) out,?_⟩
  constructor
  · intro ho
    exact product_unique hM hT ((hLaws.1 e x unit out hUnit).mp ho) (hFree.1 x hx)
  · intro heq
    subst out
    exact (hLaws.1 e x unit x hUnit).mpr (hFree.1 x hx)

theorem factors_of_old (hM : FirstOrder.Theory.Models M nativeZF)
    {w D L zero mul A W B H T left right out a : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ p, ¬ (Project.FirstOrderSemantics.reduct M).mem p zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hW : Carrier w D L W) (hB : Representatives W W B) (hH : MapsTo B W H)
    (hTable : ActionTable w D L zero mul A T) (hLaws : Laws w D L zero T H)
    (hOld : Old zero D a out) (hp : Product H left right out) :
    ∃ x y, Old zero D x left ∧ Old zero D y right ∧ Product mul x y a := by
  have hr := (ConstructionProbeAction.projected_indices hB hH hp).2
  rcases ConstructionProbeRaw.cases_raw hM hw hz hzw ((hW right).mp hr) with ⟨y,hY⟩ | ⟨s,t,hCons⟩
  · have hAct := (hTable left y out).mp ((hLaws.1 y left right out hY).mp hp)
    rcases hAct.2 with ⟨x,xy,hX,hProd,hOut⟩ | ⟨s,t,sm,_,_,hOut⟩
    · have heq := ConstructionProbeRaw.old_injective hOut hOld
      subst xy
      exact ⟨x,y,hX,hY,hProd⟩
    · exact (ConstructionProbeRaw.old_ne_cons hz hOld hOut).elim
  · obtain ⟨v,_,hOut⟩ := (hLaws.2 s t right left out hCons).mp hp
    exact (ConstructionProbeRaw.old_ne_cons hz hOld hOut).elim

theorem conical (hM : FirstOrder.Theory.Models M nativeZF)
    {w D L zero mul A e W B H T unit : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ p, ¬ (Project.FirstOrderSemantics.reduct M).mem p zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hW : Carrier w D L W) (hB : Representatives W W B) (hH : MapsTo B W H)
    (hTable : ActionTable w D L zero mul A T) (hLaws : Laws w D L zero T H)
    (hc : Conical D mul e) (hUnit : Old zero D e unit) : Conical W H unit := by
  intro left right _ _ hp
  obtain ⟨x,y,hX,hY,hProd⟩ := factors_of_old hM hw hz hzw hW hB hH hTable hLaws hUnit hp
  obtain ⟨rfl,rfl⟩ := hc x y hX.1 hY.1 hProd
  exact ⟨ConstructionProbeRaw.old_unique hM hX hUnit,ConstructionProbeRaw.old_unique hM hY hUnit⟩

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
      Old zero D e unit ∧ Unit W H unit ∧ Associative W H ∧ Conical W H unit := by
  obtain ⟨C,L,projection,K,A,W,I,T,B,H,hAll⟩ := ConstructionMergerWordProduct.exists_system hM hw hz hzw hm hP hValid
  have hParent := hAll
  obtain ⟨hC,hp,hL,hProjection,hEq,hK,hA,hTable,hFree,hCopy,hW,hI,hT,hWordTable,hWordFree,hB,hH,hLaws⟩ := hAll
  obtain ⟨unit,hUnit⟩ := ConstructionProbeRaw.exists_old hM (zero := zero) hm.1.1
  exact ⟨C,L,projection,K,A,W,I,T,B,H,unit,hParent,hUnit,
    unit_laws hM hw hz hzw hm hW hT hWordFree hWordTable hLaws hUnit,
    associative hM hw hz hzw hW hB hH hT hWordFree hWordTable hLaws,
    conical hM hw hz hzw hW hB hH hWordTable hLaws hc hUnit⟩

end PPAC.Migration.ConstructionMergerWordMonoid
