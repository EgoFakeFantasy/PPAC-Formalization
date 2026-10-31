/- Pinned GermSelectors.rawPattern:413-414.
Actual N -> Eventual(alpha -> B) function, obtained from the detector graph,
label action and total rows. Native unique-function constructors perform
all internal lambda abstraction; no host Type choice of sequences. -/
import PPAC.Migration.ConstructionCohenRows
import PPAC.Migration.ConstructionGermEventual

namespace PPAC.Migration.ConstructionGermRawPattern
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ForcingSupportSize (MapsTo)
open ForcingCohenCoordinates (Cartesian)
open ConstructionGermEventual (Space Classes Projection Exact)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

def Value (det g R delta n b v : M.Carrier .set) : Prop := ∃ t x y a,
  PureKuratowski.Code M t delta n ∧ PureKuratowski.PairMember M t x det ∧
    PureKuratowski.PairMember M x y g ∧ PureKuratowski.Code M a y b ∧ PureKuratowski.PairMember M a v R

def value {m : Nat} (det g R delta n b v : Fin m) : Project.Formula 1 m :=
  .existsE (.existsE (.existsE (.existsE
    (.conj (PureKuratowskiProject.code (.bound 3) (.bound delta.succ.succ.succ.succ) (.bound n.succ.succ.succ.succ))
      (.conj (ProjectSyntax.encode id (Source.SetLanguage.edge det.succ.succ.succ.succ 3 2))
        (.conj (ProjectSyntax.encode id (Source.SetLanguage.edge g.succ.succ.succ.succ 2 1))
          (.conj (PureKuratowskiProject.code (.bound 0) (.bound 1) (.bound b.succ.succ.succ.succ))
            (ProjectSyntax.encode id (Source.SetLanguage.edge R.succ.succ.succ.succ 0 v.succ.succ.succ.succ)))))))))

theorem value_freeClosed {m : Nat} (det g R delta n b v : Fin m) : (value det g R delta n b v).FreeClosed := by
  simp -implicitDefEqProofs [value,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,PureKuratowskiProject.code]

theorem value_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (det g R delta n b v : Fin m) :
    Project.Formula.satisfies env (value det g R delta n b v) ↔
      Value (env.bound det) (env.bound g) (env.bound R) (env.bound delta) (env.bound n) (env.bound b) (env.bound v) := by
  simp only [value,Value,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,
    KuratowskiZF.code_correct hM,Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge]
  rfl

theorem value_unique (hM : FirstOrder.Theory.Models M nativeZF) {X I C B det g R delta n b v v' : M.Carrier .set}
    (hdet : MapsTo X I det) (hg : MapsTo I I g) (hR : MapsTo C B R)
    (hv : Value det g R delta n b v) (hv' : Value det g R delta n b v') : v = v' := by
  obtain ⟨t,x,y,a,ht,htx,hxy,ha,hav⟩ := hv
  obtain ⟨t',x',y',a',ht',htx',hxy',ha',hav'⟩ := hv'
  have et := KuratowskiZF.code_unique hM ht ht'
  subst t'
  have ex := ForcingConditionGraphs.function_unique hdet.1 htx htx'
  subst x'
  have ey := ForcingConditionGraphs.function_unique hg.1 hxy hxy'
  subst y'
  have ea := KuratowskiZF.code_unique hM ha ha'
  subst a'
  exact ForcingConditionGraphs.function_unique hR.1 hav hav'

theorem value_exists (hM : FirstOrder.Theory.Models M nativeZF) {w N X I K C B det g R delta n b : M.Carrier .set}
    (hX : Cartesian N w X) (hC : Cartesian I K C)
    (hdet : MapsTo X I det) (hg : MapsTo I I g) (hR : MapsTo C B R)
    (hd : (Project.FirstOrderSemantics.reduct M).mem delta N)
    (hn : (Project.FirstOrderSemantics.reduct M).mem n w)
    (hb : (Project.FirstOrderSemantics.reduct M).mem b K) : ∃ v, Value det g R delta n b v := by
  obtain ⟨t,ht⟩ := KuratowskiZF.exists_code hM delta n
  obtain ⟨x,htx,_⟩ := hdet.1.2 t ((hX t).mpr ⟨delta,hd,n,hn,ht⟩)
  obtain ⟨y,hxy,_⟩ := hg.1.2 x (hdet.2 t x htx)
  obtain ⟨a,ha⟩ := KuratowskiZF.exists_code hM y b
  obtain ⟨v,hav,_⟩ := hR.1.2 a ((hC a).mpr ⟨y,hg.2 x y hxy,b,hb,ha⟩)
  exact ⟨v,t,x,y,a,ht,htx,hxy,ha,hav⟩

def Slice (alpha B det g R delta n F : M.Carrier .set) : Prop := MapsTo alpha B F ∧ ∀ b v,
  PureKuratowski.PairMember M b v F ↔ (Project.FirstOrderSemantics.reduct M).mem b alpha ∧ Value det g R delta n b v

def slice {m : Nat} (alpha B det g R delta n F : Fin m) : Project.Formula 1 m := .conj
  (ProjectSyntax.encode id (Source.SetLanguage.mapsTo F alpha B))
  (.forallE (.forallE (.iff (ProjectSyntax.encode id (Source.SetLanguage.edge F.succ.succ 1 0))
    (.conj (.mem (.bound 1) (.bound alpha.succ.succ))
      (value det.succ.succ g.succ.succ R.succ.succ delta.succ.succ n.succ.succ 1 0)))))

theorem slice_freeClosed {m : Nat} (alpha B det g R delta n F : Fin m) : (slice alpha B det g R delta n F).FreeClosed := by
  simp -implicitDefEqProofs [slice,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,value_freeClosed]

theorem slice_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (alpha B det g R delta n F : Fin m) :
    Project.Formula.satisfies env (slice alpha B det g R delta n F) ↔
      Slice (env.bound alpha) (env.bound B) (env.bound det) (env.bound g) (env.bound R) (env.bound delta) (env.bound n) (env.bound F) := by
  simp only [slice,Slice,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_forall_iff,
    Project.Formula.satisfies_iff_iff,Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,value_semantics hM,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,ForcingSupportSize.mapsTo_semantics (M := M)]
  rfl

theorem slice_unique (hM : FirstOrder.Theory.Models M nativeZF) {alpha B det g R delta n F G : M.Carrier .set}
    (hF : Slice alpha B det g R delta n F) (hG : Slice alpha B det g R delta n G) : F = G := by
  apply Structure.IsSetRelation.eq_of_pairMember_iff (ModelTransfer.project_models_iff.mp hM).1
    ((ForcingSupportSize.native_mapsTo hM alpha B F).mp hF.1).1.1
    ((ForcingSupportSize.native_mapsTo hM alpha B G).mp hG.1).1.1
  intro b v
  exact (hF.2 b v).trans (hG.2 b v).symm

theorem exists_slice (hM : FirstOrder.Theory.Models M nativeZF) {w N X I K C B det g R alpha delta n : M.Carrier .set}
    (hX : Cartesian N w X) (hC : Cartesian I K C)
    (hdet : MapsTo X I det) (hg : MapsTo I I g) (hR : MapsTo C B R)
    (hAlpha : (Project.FirstOrderSemantics.reduct M).MemberSubset alpha K)
    (hd : (Project.FirstOrderSemantics.reduct M).mem delta N)
    (hn : (Project.FirstOrderSemantics.reduct M).mem n w) : ∃ F, Slice alpha B det g R delta n F := by
  let schema : Project.BinarySchema 5 := { body := value 2 3 4 5 6 1 0, freeClosed := value_freeClosed .. }
  let env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) 5 := {
    bound := Fin.cases det (Fin.cases g (Fin.cases R (Fin.cases delta (fun _ => n)))), free := fun _ => R }
  have he b v : schema.denote env b v ↔ Value det g R delta n b v := value_semantics hM ((env.push b).push v) 2 3 4 5 6 1 0
  obtain ⟨F,hF,hEdge⟩ := ZF.exists_setFunctionFromTo_of_denote (ModelTransfer.project_models_iff.mp hM)
    (KuratowskiZF.interpretation hM) schema env (source := alpha) (target := B) (by
      intro b hb
      obtain ⟨v,hv⟩ := value_exists hM hX hC hdet hg hR hd hn (hAlpha b hb)
      exact ⟨v,(he b v).mpr hv⟩)
    (fun b _ v v' hv hv' => value_unique hM hdet hg hR ((he b v).mp hv) ((he b v').mp hv')) (by
      intro b v _ hv
      obtain ⟨_,_,_,a,_,_,_,_,hav⟩ := (he b v).mp hv
      exact hR.2 a v hav)
  exact ⟨F,(ForcingSupportSize.native_mapsTo hM alpha B F).mpr hF,
    fun b v => (hEdge b v).trans (and_congr Iff.rfl (he b v))⟩

def Sequence (w alpha B A det g R delta s : M.Carrier .set) : Prop := MapsTo w A s ∧ ∀ n F,
  PureKuratowski.PairMember M n F s ↔ (Project.FirstOrderSemantics.reduct M).mem n w ∧ Slice alpha B det g R delta n F

def sequence {m : Nat} (w alpha B A det g R delta s : Fin m) : Project.Formula 1 m := .conj
  (ProjectSyntax.encode id (Source.SetLanguage.mapsTo s w A))
  (.forallE (.forallE (.iff (ProjectSyntax.encode id (Source.SetLanguage.edge s.succ.succ 1 0))
    (.conj (.mem (.bound 1) (.bound w.succ.succ))
      (slice alpha.succ.succ B.succ.succ det.succ.succ g.succ.succ R.succ.succ delta.succ.succ 1 0)))))

theorem sequence_freeClosed {m : Nat} (w alpha B A det g R delta s : Fin m) : (sequence w alpha B A det g R delta s).FreeClosed := by
  simp -implicitDefEqProofs [sequence,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,slice_freeClosed]

theorem sequence_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w alpha B A det g R delta s : Fin m) :
    Project.Formula.satisfies env (sequence w alpha B A det g R delta s) ↔
      Sequence (env.bound w) (env.bound alpha) (env.bound B) (env.bound A) (env.bound det) (env.bound g) (env.bound R) (env.bound delta) (env.bound s) := by
  simp only [sequence,Sequence,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_forall_iff,
    Project.Formula.satisfies_iff_iff,Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,slice_semantics hM,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,ForcingSupportSize.mapsTo_semantics (M := M)]
  rfl

theorem sequence_unique (hM : FirstOrder.Theory.Models M nativeZF) {w alpha B A det g R delta s t : M.Carrier .set}
    (hs : Sequence w alpha B A det g R delta s) (ht : Sequence w alpha B A det g R delta t) : s = t := by
  apply Structure.IsSetRelation.eq_of_pairMember_iff (ModelTransfer.project_models_iff.mp hM).1
    ((ForcingSupportSize.native_mapsTo hM w A s).mp hs.1).1.1
    ((ForcingSupportSize.native_mapsTo hM w A t).mp ht.1).1.1
  intro n F
  exact (hs.2 n F).trans (ht.2 n F).symm

theorem exists_sequence (hM : FirstOrder.Theory.Models M nativeZF) {w N X I K C B A det g R alpha delta : M.Carrier .set}
    (hX : Cartesian N w X) (hC : Cartesian I K C)
    (hdet : MapsTo X I det) (hg : MapsTo I I g) (hR : MapsTo C B R)
    (hAlpha : (Project.FirstOrderSemantics.reduct M).MemberSubset alpha K)
    (hA : Space alpha B A) (hd : (Project.FirstOrderSemantics.reduct M).mem delta N) :
    ∃ s, Sequence w alpha B A det g R delta s := by
  let schema : Project.BinarySchema 6 := { body := slice 2 3 4 5 6 7 1 0, freeClosed := slice_freeClosed .. }
  let env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) 6 := {
    bound := Fin.cases alpha (Fin.cases B (Fin.cases det (Fin.cases g (Fin.cases R (fun _ => delta))))), free := fun _ => R }
  have he n F : schema.denote env n F ↔ Slice alpha B det g R delta n F := slice_semantics hM ((env.push n).push F) 2 3 4 5 6 7 1 0
  obtain ⟨s,hs,hEdge⟩ := ZF.exists_setFunctionFromTo_of_denote (ModelTransfer.project_models_iff.mp hM)
    (KuratowskiZF.interpretation hM) schema env (source := w) (target := A) (by
      intro n hn
      obtain ⟨F,hF⟩ := exists_slice hM hX hC hdet hg hR hAlpha hd hn
      exact ⟨F,(he n F).mpr hF⟩)
    (fun n _ F G hF hG => slice_unique hM ((he n F).mp hF) ((he n G).mp hG))
    (fun n F _ hF => (hA F).mpr ((he n F).mp hF).1)
  exact ⟨s,(ForcingSupportSize.native_mapsTo hM w A s).mpr hs,
    fun n F => (hEdge n F).trans (and_congr Iff.rfl (he n F))⟩

def At (w alpha B A det g R pr delta E : M.Carrier .set) : Prop := ∃ s,
  Sequence w alpha B A det g R delta s ∧ PureKuratowski.PairMember M s E pr

def atFormula {m : Nat} (w alpha B A det g R pr delta E : Fin m) : Project.Formula 1 m := .existsE (.conj
  (sequence w.succ alpha.succ B.succ A.succ det.succ g.succ R.succ delta.succ 0)
  (ProjectSyntax.encode id (Source.SetLanguage.edge pr.succ 0 E.succ)))

theorem atFormula_freeClosed {m : Nat} (w alpha B A det g R pr delta E : Fin m) : (atFormula w alpha B A det g R pr delta E).FreeClosed := by
  simp -implicitDefEqProofs [atFormula,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,sequence_freeClosed]

theorem atFormula_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w alpha B A det g R pr delta E : Fin m) :
    Project.Formula.satisfies env (atFormula w alpha B A det g R pr delta E) ↔
      At (env.bound w) (env.bound alpha) (env.bound B) (env.bound A) (env.bound det) (env.bound g) (env.bound R) (env.bound pr) (env.bound delta) (env.bound E) := by
  simp only [atFormula,At,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,
    sequence_semantics hM,GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge]
  rfl

def RawPattern (w N alpha B A Q det g R pr P : M.Carrier .set) : Prop := MapsTo N Q P ∧ ∀ delta E,
  PureKuratowski.PairMember M delta E P ↔ (Project.FirstOrderSemantics.reduct M).mem delta N ∧ At w alpha B A det g R pr delta E

def rawPattern {m : Nat} (w N alpha B A Q det g R pr P : Fin m) : Project.Formula 1 m := .conj
  (ProjectSyntax.encode id (Source.SetLanguage.mapsTo P N Q))
  (.forallE (.forallE (.iff (ProjectSyntax.encode id (Source.SetLanguage.edge P.succ.succ 1 0))
    (.conj (.mem (.bound 1) (.bound N.succ.succ))
      (atFormula w.succ.succ alpha.succ.succ B.succ.succ A.succ.succ det.succ.succ g.succ.succ R.succ.succ pr.succ.succ 1 0)))))

theorem rawPattern_freeClosed {m : Nat} (w N alpha B A Q det g R pr P : Fin m) : (rawPattern w N alpha B A Q det g R pr P).FreeClosed := by
  simp -implicitDefEqProofs [rawPattern,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,atFormula_freeClosed]

theorem rawPattern_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w N alpha B A Q det g R pr P : Fin m) :
    Project.Formula.satisfies env (rawPattern w N alpha B A Q det g R pr P) ↔
      RawPattern (env.bound w) (env.bound N) (env.bound alpha) (env.bound B) (env.bound A) (env.bound Q) (env.bound det) (env.bound g) (env.bound R) (env.bound pr) (env.bound P) := by
  simp only [rawPattern,RawPattern,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_forall_iff,
    Project.Formula.satisfies_iff_iff,Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,atFormula_semantics hM,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,ForcingSupportSize.mapsTo_semantics (M := M)]
  rfl

theorem exists_rawPattern (hM : FirstOrder.Theory.Models M nativeZF) {w N X I K C B A S Q det g R pr alpha : M.Carrier .set}
    (hX : Cartesian N w X) (hC : Cartesian I K C)
    (hdet : MapsTo X I det) (hg : MapsTo I I g) (hR : MapsTo C B R)
    (hAlpha : (Project.FirstOrderSemantics.reduct M).MemberSubset alpha K)
    (hA : Space alpha B A) (hS : Space w A S) (hpr : MapsTo S Q pr) :
    ∃ P, RawPattern w N alpha B A Q det g R pr P := by
  let schema : Project.BinarySchema 8 := { body := atFormula 2 3 4 5 6 7 8 9 1 0, freeClosed := atFormula_freeClosed .. }
  let env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) 8 := {
    bound := Fin.cases w (Fin.cases alpha (Fin.cases B (Fin.cases A (Fin.cases det (Fin.cases g (Fin.cases R (fun _ => pr))))))), free := fun _ => R }
  have he delta E : schema.denote env delta E ↔ At w alpha B A det g R pr delta E :=
    atFormula_semantics hM ((env.push delta).push E) 2 3 4 5 6 7 8 9 1 0
  obtain ⟨P,hP,hEdge⟩ := ZF.exists_setFunctionFromTo_of_denote (ModelTransfer.project_models_iff.mp hM)
    (KuratowskiZF.interpretation hM) schema env (source := N) (target := Q) (by
      intro delta hd
      obtain ⟨s,hs⟩ := exists_sequence hM hX hC hdet hg hR hAlpha hA hd
      obtain ⟨E,hsE,_⟩ := hpr.1.2 s ((hS s).mpr hs.1)
      exact ⟨E,(he delta E).mpr ⟨s,hs,hsE⟩⟩) (by
      intro delta _ E F hE hF
      obtain ⟨s,hs,hsE⟩ := (he delta E).mp hE
      obtain ⟨t,ht,htF⟩ := (he delta F).mp hF
      have e := sequence_unique hM hs ht
      subst t
      exact ForcingConditionGraphs.function_unique hpr.1 hsE htF) (by
      intro delta E _ hE
      obtain ⟨s,_,hsE⟩ := (he delta E).mp hE
      exact hpr.2 s E hsE)
  exact ⟨P,(ForcingSupportSize.native_mapsTo hM N Q P).mpr hP,
    fun delta E => (hEdge delta E).trans (and_congr Iff.rfl (he delta E))⟩

theorem construction (hM : FirstOrder.Theory.Models M nativeZF) {w N X I K C B det g R alpha : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hX : Cartesian N w X) (hC : Cartesian I K C)
    (hdet : MapsTo X I det) (hg : MapsTo I I g) (hR : MapsTo C B R)
    (hAlpha : (Project.FirstOrderSemantics.reduct M).MemberSubset alpha K) :
    ∃ A S Q pr P, Space alpha B A ∧ Space w A S ∧ MapsTo S Q pr ∧ Classes w S Q ∧
      Projection w S pr ∧ Exact w pr ∧ RawPattern w N alpha B A Q det g R pr P := by
  obtain ⟨A,hA⟩ := ZF.exists_functionSpace (ModelTransfer.project_models_iff.mp hM) (KuratowskiZF.interpretation hM) alpha B
  have hA' : Space alpha B A := fun F => (hA F).trans (ForcingSupportSize.native_mapsTo hM alpha B F).symm
  obtain ⟨S,Q,pr,hS,hpr,hQ,hProj,hExact⟩ := ConstructionGermEventual.construction hM A hw
  obtain ⟨P,hP⟩ := exists_rawPattern hM hX hC hdet hg hR hAlpha hA' hS hpr
  exact ⟨A,S,Q,pr,P,hA',hS,hpr,hQ,hProj,hExact,hP⟩

def constructionSentence {m : Nat} (w N X I K C B det g R alpha : Fin m) : Project.Sentence where
  formula := Project.Formula.forallClosure m (.imp (Project.Formula.isOmega (.bound w)) (.imp (ProjectSyntax.encode id (ForcingCohenCoordinates.cartesian N w X)) (.imp (ProjectSyntax.encode id (ForcingCohenCoordinates.cartesian I K C)) (.imp (ProjectSyntax.encode id (Source.SetLanguage.mapsTo det X I)) (.imp (ProjectSyntax.encode id (Source.SetLanguage.mapsTo g I I)) (.imp (ProjectSyntax.encode id (Source.SetLanguage.mapsTo R C B)) (.imp (Project.Formula.subset (.bound alpha) (.bound K)) (.existsE (.existsE (.existsE (.existsE (.existsE (.conj (ConstructionGermEventual.space alpha.succ.succ.succ.succ.succ B.succ.succ.succ.succ.succ 4) (.conj (ConstructionGermEventual.space w.succ.succ.succ.succ.succ 4 3) (.conj (ProjectSyntax.encode id (Source.SetLanguage.mapsTo 1 3 2)) (.conj (ConstructionGermEventual.classes w.succ.succ.succ.succ.succ 3 2) (.conj (ConstructionGermEventual.projection w.succ.succ.succ.succ.succ 3 1) (.conj (ConstructionGermEventual.exactProjection w.succ.succ.succ.succ.succ 1) (rawPattern w.succ.succ.succ.succ.succ N.succ.succ.succ.succ.succ alpha.succ.succ.succ.succ.succ B.succ.succ.succ.succ.succ 4 2 det.succ.succ.succ.succ.succ g.succ.succ.succ.succ.succ R.succ.succ.succ.succ.succ 1 0)))))))))))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,Project.Formula.isOmega,Project.Formula.subset,
      ProjectSyntax.freeClosed,ConstructionGermEventual.space_freeClosed,ConstructionGermEventual.classes_freeClosed,
      ConstructionGermEventual.projection_freeClosed,ConstructionGermEventual.exactProjection_freeClosed,rawPattern_freeClosed]

theorem construction_models {m : Nat} (w N X I K C B det g R alpha : Fin m) (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence (constructionSentence w N X I K C B det g R alpha)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) (constructionSentence w N X I K C B det g R alpha)]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_isOmega_iff,Project.Formula.satisfies_subset_iff,Project.Term.eval_bound,
    ConstructionGermEventual.space_semantics hM,ConstructionGermEventual.classes_semantics hM,
    ConstructionGermEventual.projection_semantics hM,ConstructionGermEventual.exactProjection_semantics hM,rawPattern_semantics hM,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),ForcingSupportSize.mapsTo_semantics (M := M),
    ForcingCohenCoordinates.cartesian_semantics (M := M)]
  exact construction hM

theorem construction_kernel_certificate {m : Nat} (w N X I K C B det g R alpha : Fin m) :
    FirstOrder.Derives nativeZF [] (Project.fo_sentence (constructionSentence w N X I K C B det g R alpha)) :=
  ModelTransfer.derives (fun _ hM => construction_models w N X I K C B det g R alpha hM)

end PPAC.Migration.ConstructionGermRawPattern
