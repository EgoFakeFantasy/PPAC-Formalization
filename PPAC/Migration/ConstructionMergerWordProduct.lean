/- Pinned MergerWords.Word.product:118 / mul_old:146 / mul_snoc:147.
Construct the actual product by the EXISTING internal evalHom; old coefficients
use the actual Word right-action row and each new letter uses actual Raw.Cons.
No new recursion/sequence/parser backend or supplied multiplication graph. -/
import PPAC.Migration.ConstructionMergerWordOperation

namespace PPAC.Migration.ConstructionMergerWordProduct
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ConstructionProbeRaw (Raw Carrier Old Cons)
open ConstructionProbeLetters (Representatives exists_representatives)
open ConstructionProbeHomEvaluation (Eval)
open ConstructionMergerWordOperation (Initial Graph initial initial_freeClosed initial_semantics)
open ConstructionRealCuts (Subset)
open ForcingDiagramOrder (Product product product_semantics)
open ForcingSupportSize (MapsTo)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

def Value (hM : FirstOrder.Theory.Models M nativeZF) (w D L W N G Id T left right out : M.Carrier .set) : Prop :=
  (Project.FirstOrderSemantics.reduct M).mem left W ∧ (Project.FirstOrderSemantics.reduct M).mem right W ∧
    ∃ F, MapsTo D W F ∧ Initial D T left F ∧ Eval hM w D L N G F Id right out

theorem value_range (hM : FirstOrder.Theory.Models M nativeZF)
    {w D L W N J G Id T left right out : M.Carrier .set}
    (hG : MapsTo J W G) (hv : Value hM w D L W N G Id T left right out) :
    (Project.FirstOrderSemantics.reduct M).mem out W := by
  obtain ⟨_,_,F,hF,_,he⟩ := hv
  exact ConstructionProbeHeightFold.eval_range hM hF hG he

theorem value_total (hM : FirstOrder.Theory.Models M nativeZF)
    {w D L W N J G Id I T left right : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w) (hW : Carrier w D L W)
    (hJ : Representatives N N J) (hG : MapsTo J W G) (hWN : Subset W N) (hId : MapsTo L N Id)
    (hI : Representatives W D I) (hT : MapsTo I W T)
    (hl : (Project.FirstOrderSemantics.reduct M).mem left W) (hr : (Project.FirstOrderSemantics.reduct M).mem right W) :
    ∃ out, Value hM w D L W N G Id T left right out := by
  obtain ⟨F,hF,hInitial⟩ := ConstructionMergerWordOperation.exists_initial hM hI hT hl
  have hGN : MapsTo J N G := ⟨hG.1,fun p y hy => hWN y (hG.2 p y hy)⟩
  have hFN : MapsTo D N F := ⟨hF.1,fun m y hy => hWN y (hF.2 m y hy)⟩
  obtain ⟨out,he⟩ := ConstructionProbeHomEvaluation.eval_total hM hw hJ hGN hFN hId ((hW right).mp hr)
  exact ⟨out,hl,hr,F,hF,hInitial,he⟩

theorem value_unique (hM : FirstOrder.Theory.Models M nativeZF)
    {w D L W N J G Id T left right out out' : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hJ : Representatives N N J) (hG : MapsTo J W G) (hWN : Subset W N) (hId : MapsTo L N Id)
    (hv : Value hM w D L W N G Id T left right out) (hv' : Value hM w D L W N G Id T left right out') : out = out' := by
  obtain ⟨_,_,F,hF,hInitial,he⟩ := hv
  obtain ⟨_,_,F',hF',hInitial',he'⟩ := hv'
  have hEq := ConstructionMergerWordOperation.initial_unique hM hF hF' hInitial hInitial'
  subst F'
  have hGN : MapsTo J N G := ⟨hG.1,fun p y hy => hWN y (hG.2 p y hy)⟩
  have hFN : MapsTo D N F := ⟨hF.1,fun m y hy => hWN y (hF.2 m y hy)⟩
  exact ConstructionProbeHomEvaluation.eval_unique hM hw hJ hGN hFN hId he he'

theorem value_old_iff (hM : FirstOrder.Theory.Models M nativeZF)
    {w D L zero W N J G Id I T left right out x : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ p, ¬ (Project.FirstOrderSemantics.reduct M).mem p zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w) (hW : Carrier w D L W)
    (hJ : Representatives N N J) (hG : MapsTo J W G) (hWN : Subset W N) (hId : MapsTo L N Id)
    (hI : Representatives W D I) (hT : MapsTo I W T) (hOld : Old zero D x right) :
    Value hM w D L W N G Id T left right out ↔ Product T left x out := by
  constructor
  · rintro ⟨_,_,F,_,hInitial,he⟩
    exact ((hInitial x out).mp (ConstructionProbeHomEvaluation.eval_old_forward hM hw hz hOld he)).2
  · intro hTx
    have hl := (ConstructionProbeAction.projected_indices hI hT hTx).1
    obtain ⟨F,hF,hInitial⟩ := ConstructionMergerWordOperation.exists_initial hM hI hT hl
    have hGN : MapsTo J N G := ⟨hG.1,fun p y hy => hWN y (hG.2 p y hy)⟩
    have hFN : MapsTo D N F := ⟨hF.1,fun m y hy => hWN y (hF.2 m y hy)⟩
    exact ⟨hl,(hW right).mpr (ConstructionProbeRaw.old_raw hM hz hzw hOld),F,hF,hInitial,
      (ConstructionProbeHomEvaluation.eval_old_iff hM hw hz hzw hJ hGN hFN hId hOld).mpr ((hInitial x out).mpr ⟨hOld.1,hTx⟩)⟩

theorem value_snoc_iff (hM : FirstOrder.Theory.Models M nativeZF)
    {w D L W N J G Id T default left s t q out : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w) (hW : Carrier w D L W)
    (hJ : Representatives N N J) (hG : MapsTo J W G) (hWN : Subset W N) (hLN : Subset L N)
    (hId : MapsTo L N Id) (hi : ForcingConditionGraphs.IdentityGraph L Id)
    (hg : Graph w D L W default N G) (hCons : Cons w D L s t q) :
    Value hM w D L W N G Id T left q out ↔
      ∃ v, Value hM w D L W N G Id T left t v ∧ Cons w D L s v out := by
  have hs : (Project.FirstOrderSemantics.reduct M).mem s L := by
    rcases hCons with ⟨_,_,_,_,_,_,_,_,_,_,_,hs,_,_,_⟩
    exact hs
  have hGN : MapsTo J N G := ⟨hG.1,fun p y hy => hWN y (hG.2 p y hy)⟩
  constructor
  · rintro ⟨hl,_,F,hF,hInitial,he⟩
    have hFN : MapsTo D N F := ⟨hF.1,fun m y hy => hWN y (hF.2 m y hy)⟩
    obtain ⟨v,hv,hStep⟩ := (ConstructionProbeHomEvaluation.eval_cons_iff hM hw hJ hGN hFN hId hCons).mp he
    have hvW := ConstructionProbeHeightFold.eval_range hM hF hG hv
    exact ⟨v,⟨hl,(hW t).mpr (ConstructionProbeRaw.cons_raw hCons).1,F,hF,hInitial,hv⟩,
      (ConstructionMergerWordOperation.prepend_iff hLN hWN hi hg hs hvW).mp hStep⟩
  · rintro ⟨v,hv,hSnoc⟩
    have hvW := value_range hM hG hv
    obtain ⟨hl,_,F,hF,hInitial,he⟩ := hv
    have hFN : MapsTo D N F := ⟨hF.1,fun m y hy => hWN y (hF.2 m y hy)⟩
    exact ⟨hl,(hW q).mpr (ConstructionProbeRaw.cons_raw hCons).2,F,hF,hInitial,
      (ConstructionProbeHomEvaluation.eval_cons_iff hM hw hJ hGN hFN hId hCons).mpr ⟨v,he,
        (ConstructionMergerWordOperation.prepend_iff hLN hWN hi hg hs hvW).mpr hSnoc⟩⟩

def value {m0 : Nat} (w D L W N G Id T left right out : Fin m0) : Project.Formula 1 m0 :=
  (.conj (.mem (.bound left) (.bound W)) (.conj (.mem (.bound right) (.bound W)) (.existsE (.conj
  (ProjectSyntax.encode id (Source.SetLanguage.mapsTo 0 D.succ W.succ)) (.conj (initial D.succ T.succ
  left.succ 0) (ConstructionProbeHomEvaluationSyntax.eval w.succ D.succ L.succ N.succ G.succ 0 Id.succ
  right.succ out.succ))))))

theorem value_freeClosed {m0 : Nat} (w D L W N G Id T left right out : Fin m0) : (value w D L W N G Id T left right out).FreeClosed := by
  simp -implicitDefEqProofs [value,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,initial_freeClosed,ConstructionProbeHomEvaluationSyntax.eval_freeClosed]

theorem value_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m0 : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m0) (w D L W N G Id T left right out : Fin m0) :
    Project.Formula.satisfies env (value w D L W N G Id T left right out) ↔ Value hM (env.bound w) (env.bound D) (env.bound L) (env.bound W) (env.bound N) (env.bound G) (env.bound Id) (env.bound T) (env.bound left) (env.bound right) (env.bound out) := by
  simp only [value,Value,Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_conj_iff,Project.Term.eval_bound,Project.Formula.satisfies_mem_iff,GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),ForcingSupportSize.mapsTo_semantics (M := M),initial_semantics hM,ConstructionProbeHomEvaluationSyntax.eval_semantics hM]
  rfl

def pairValue {m0 : Nat} (w D L W N G Id T p out : Fin m0) : Project.Formula 1 m0 :=
  (.existsE (.existsE (.conj (PureKuratowskiProject.code (.bound p.succ.succ) (.bound 1) (.bound 0)) (value
  w.succ.succ D.succ.succ L.succ.succ W.succ.succ N.succ.succ G.succ.succ Id.succ.succ T.succ.succ 1 0
  out.succ.succ))))

theorem pairValue_freeClosed {m0 : Nat} (w D L W N G Id T p out : Fin m0) : (pairValue w D L W N G Id T p out).FreeClosed := by
  simp -implicitDefEqProofs [pairValue,Definitional.Formula.FreeClosed,value_freeClosed,PureKuratowskiProject.code]

theorem pairValue_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m0 : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m0) (w D L W N G Id T p out : Fin m0) :
    Project.Formula.satisfies env (pairValue w D L W N G Id T p out) ↔ (∃ left right, PureKuratowski.Code M (env.bound p) left right ∧ Value hM (env.bound w) (env.bound D) (env.bound L) (env.bound W) (env.bound N) (env.bound G) (env.bound Id) (env.bound T) left right (env.bound out)) := by
  simp only [pairValue,Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_conj_iff,Project.Term.eval_bound,KuratowskiZF.code_correct hM,value_semantics hM]
  rfl

def ProductGraph (hM : FirstOrder.Theory.Models M nativeZF) (w D L W N G Id T H : M.Carrier .set) : Prop := ∀ left right out,
  Product H left right out ↔ Value hM w D L W N G Id T left right out

def Laws (w D L zero T H : M.Carrier .set) : Prop :=
  (∀ x left right out, Old zero D x right → (Product H left right out ↔ Product T left x out)) ∧
  (∀ s t q left out, Cons w D L s t q →
    (Product H left q out ↔ ∃ v, Product H left t v ∧ Cons w D L s v out))

theorem exists_graph (hM : FirstOrder.Theory.Models M nativeZF)
    {w D L W N J G Id I T : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w) (hW : Carrier w D L W)
    (hJ : Representatives N N J) (hG : MapsTo J W G) (hWN : Subset W N) (hId : MapsTo L N Id)
    (hI : Representatives W D I) (hT : MapsTo I W T) :
    ∃ B H, Representatives W W B ∧ MapsTo B W H ∧ ProductGraph hM w D L W N G Id T H := by
  obtain ⟨B,hB⟩ := exists_representatives hM W W
  let schema : Project.BinarySchema 8 := {
    body := pairValue 2 3 4 5 6 7 8 9 1 0
    freeClosed := pairValue_freeClosed _ _ _ _ _ _ _ _ _ _ }
  let env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) 8 := {
    bound := Fin.cases w (Fin.cases D (Fin.cases L (Fin.cases W (Fin.cases N (Fin.cases G (Fin.cases Id (fun _ => T))))))), free := fun _ => w }
  have he (p out : M.Carrier .set) : schema.denote env p out ↔
      ∃ left right, PureKuratowski.Code M p left right ∧ Value hM w D L W N G Id T left right out :=
    pairValue_semantics hM ((env.push p).push out) 2 3 4 5 6 7 8 9 1 0
  obtain ⟨H,hH,hg⟩ := ZF.exists_setFunctionFromTo_of_denote (ModelTransfer.project_models_iff.mp hM)
    (KuratowskiZF.interpretation hM) schema env (source := B) (target := W) (by
      intro p hp
      obtain ⟨left,right,hl,hr,hcode⟩ := (hB p).mp hp
      obtain ⟨out,hv⟩ := value_total hM hw hW hJ hG hWN hId hI hT hl hr
      exact ⟨out,(he p out).mpr ⟨left,right,hcode,hv⟩⟩) (by
      intro p _ out out' ho ho'
      obtain ⟨left,right,hcode,hv⟩ := (he p out).mp ho
      obtain ⟨left',right',hcode',hv'⟩ := (he p out').mp ho'
      obtain ⟨rfl,rfl⟩ := PureKuratowski.code_injective hcode hcode'
      exact value_unique hM hw hJ hG hWN hId hv hv') (by
      intro p out _ ho
      obtain ⟨left,right,_,hv⟩ := (he p out).mp ho
      exact value_range hM hG hv)
  refine ⟨B,H,hB,(ForcingSupportSize.native_mapsTo hM B W H).mpr hH,?_⟩
  intro left right out
  constructor
  · rintro ⟨p,hcode,hpo⟩
    obtain ⟨_,hval⟩ := (hg p out).mp hpo
    obtain ⟨left',right',hcode',hv⟩ := (he p out).mp hval
    obtain ⟨rfl,rfl⟩ := PureKuratowski.code_injective hcode hcode'
    exact hv
  · intro hv
    obtain ⟨p,hcode⟩ := KuratowskiZF.exists_code hM left right
    exact ⟨p,hcode,(hg p out).mpr ⟨(hB p).mpr ⟨left,right,hv.1,hv.2.1,hcode⟩,(he p out).mpr ⟨left,right,hcode,hv⟩⟩⟩

theorem product_laws (hM : FirstOrder.Theory.Models M nativeZF)
    {w D L zero W N J G Id I T H default : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ p, ¬ (Project.FirstOrderSemantics.reduct M).mem p zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w) (hW : Carrier w D L W)
    (hJ : Representatives N N J) (hG : MapsTo J W G) (hWN : Subset W N) (hLN : Subset L N)
    (hId : MapsTo L N Id) (hi : ForcingConditionGraphs.IdentityGraph L Id)
    (hg : Graph w D L W default N G) (hI : Representatives W D I) (hT : MapsTo I W T)
    (hGraph : ProductGraph hM w D L W N G Id T H) : Laws w D L zero T H := by
  constructor
  · exact fun x left right out hOld => (hGraph left right out).trans
      (value_old_iff hM hw hz hzw hW hJ hG hWN hId hI hT hOld)
  · intro s t q left out hCons
    exact (hGraph left q out).trans ((value_snoc_iff hM hw hW hJ hG hWN hLN hId hi hg hCons).trans
      (exists_congr fun v => and_congr_left (fun _ => (hGraph left t v).symm)))

theorem exists_product (hM : FirstOrder.Theory.Models M nativeZF)
    {w D L zero W e I T : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ p, ¬ (Project.FirstOrderSemantics.reduct M).mem p zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w) (hW : Carrier w D L W)
    (he : (Project.FirstOrderSemantics.reduct M).mem e D) (hI : Representatives W D I) (hT : MapsTo I W T) :
    ∃ B H, Representatives W W B ∧ MapsTo B W H ∧ Laws w D L zero T H := by
  obtain ⟨default,hDefault⟩ := ConstructionProbeRaw.exists_old hM (zero := zero) he
  have hd : (Project.FirstOrderSemantics.reduct M).mem default W := (hW default).mpr (ConstructionProbeRaw.old_raw hM hz hzw hDefault)
  obtain ⟨N,hN⟩ := KP.exists_unionOfTwo (ZF.modelsKP (ModelTransfer.project_models_iff.mp hM)) L W
  have hLN : Subset L N := fun s hs => (hN s).mpr (Or.inl hs)
  have hWN : Subset W N := fun q hq => (hN q).mpr (Or.inr hq)
  obtain ⟨J,G,hJ,hG,hg⟩ := ConstructionMergerWordOperation.exists_operation hM hw hW hd N
  obtain ⟨Id,hIdPerm,hi⟩ := ForcingConditionGraphs.exists_identity hM L
  have hId : MapsTo L N Id := ⟨hIdPerm.1.1,fun s a ha => hLN a (hIdPerm.1.2 s a ha)⟩
  obtain ⟨B,H,hB,hH,hGraph⟩ := exists_graph hM hw hW hJ hG hWN hId hI hT
  exact ⟨B,H,hB,hH,product_laws hM hw hz hzw hW hJ hG hWN hLN hId hi hg hI hT hGraph⟩

theorem exists_system (hM : FirstOrder.Theory.Models M nativeZF)
    {w n D mul e P zero : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ p, ¬ (Project.FirstOrderSemantics.reduct M).mem p zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hm : ForcingDiagramPoset.LeftCancelMonoid D mul e) (hP : ConstructionMergerRelations.Prescription n D P)
    (hValid : ConstructionMergerRelations.Valid n D mul P) :
    ∃ C L projection K A W I T B H, Representatives n D C ∧ MapsTo C L projection ∧
      ConstructionMergerCopies.Copies n D mul P C L ∧ ConstructionMergerCopies.Projection n D mul P C projection ∧
      ConstructionMergerCopies.EqualityLaw n D mul P projection ∧ Representatives L D K ∧ MapsTo K L A ∧
      ConstructionMergerAction.ActionTable D mul projection A ∧ ConstructionMergerAction.RightFreeAction mul e L A ∧
      ConstructionMergerAction.CopyLaw D mul projection A ∧ Carrier w D L W ∧
      Representatives W D I ∧ MapsTo I W T ∧ ConstructionMergerWordAction.ActionTable w D L zero mul A T ∧
      ConstructionMergerAction.RightFreeAction mul e W T ∧ Representatives W W B ∧ MapsTo B W H ∧ Laws w D L zero T H := by
  obtain ⟨C,L,projection,K,A,W,I,T,hC,hp,hL,hProjection,hEq,hK,hA,hTable,hFree,hCopy,hW,hI,hT,hWordTable,hWordFree⟩ :=
    ConstructionMergerWordAction.exists_system hM hw hz hzw hm hP hValid
  obtain ⟨B,H,hB,hH,hLaws⟩ := exists_product hM hw hz hzw hW hm.1.1 hI hT
  exact ⟨C,L,projection,K,A,W,I,T,B,H,hC,hp,hL,hProjection,hEq,hK,hA,hTable,hFree,hCopy,hW,hI,hT,hWordTable,hWordFree,hB,hH,hLaws⟩

def laws {m0 : Nat} (w D L zero T H : Fin m0) : Project.Formula 1 m0 :=
  (.conj (.forallE (.forallE (.forallE (.forallE (.imp (ConstructionProbeRaw.old zero.succ.succ.succ.succ
  D.succ.succ.succ.succ 3 1) (.iff (ProjectSyntax.encode id (ForcingDiagramOrder.product
  H.succ.succ.succ.succ 2 1 0)) (ProjectSyntax.encode id (ForcingDiagramOrder.product T.succ.succ.succ.succ
  2 3 0)))))))) (.forallE (.forallE (.forallE (.forallE (.forallE (.imp (ConstructionProbeRaw.cons
  w.succ.succ.succ.succ.succ D.succ.succ.succ.succ.succ L.succ.succ.succ.succ.succ 4 3 2) (.iff
  (ProjectSyntax.encode id (ForcingDiagramOrder.product H.succ.succ.succ.succ.succ 1 2 0)) (.existsE (.conj
  (ProjectSyntax.encode id (ForcingDiagramOrder.product H.succ.succ.succ.succ.succ.succ 2 4 0))
  (ConstructionProbeRaw.cons w.succ.succ.succ.succ.succ.succ D.succ.succ.succ.succ.succ.succ
  L.succ.succ.succ.succ.succ.succ 5 0 1)))))))))))

theorem laws_freeClosed {m0 : Nat} (w D L zero T H : Fin m0) : (laws w D L zero T H).FreeClosed := by
  simp -implicitDefEqProofs [laws,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,ConstructionProbeRaw.old_freeClosed,ConstructionProbeRaw.cons_freeClosed]

theorem laws_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m0 : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m0) (w D L zero T H : Fin m0) :
    Project.Formula.satisfies env (laws w D L zero T H) ↔ Laws (env.bound w) (env.bound D) (env.bound L) (env.bound zero) (env.bound T) (env.bound H) := by
  simp only [laws,Laws,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_iff_iff,Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_conj_iff,
    ConstructionProbeRaw.old_semantics hM,ConstructionProbeRaw.cons_semantics hM,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),product_semantics (M := M)]
  rfl

end PPAC.Migration.ConstructionMergerWordProduct
