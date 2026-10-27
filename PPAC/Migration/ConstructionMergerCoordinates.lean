/- Pinned MergerCones.HasRep:94, coordHeight/coordCost:96/100,
coordHeight_copy/coordCost_copy:106/112 and hasRep_of_reaches:152.
Actual coordinate graphs on n x SAME prescribed copies. Retain exact default
zero/one branches. Native definable functions and copy injectivity suffice;
no internal choice family or new recursion backend. -/
import PPAC.Migration.ConstructionMergerRoots
import PPAC.Migration.ConstructionProbeParent

namespace PPAC.Migration.ConstructionMergerCoordinates
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ConstructionProbeLetters (Representatives)
open ConstructionProbeAction (projected_indices projected_range)
open ConstructionMergerCopies (EqualityLaw copy_injective)
open ConstructionMergerAction (CopyLaw)
open ConstructionMergerCopyCones (Reaches reaches_copy_iff)
open ForcingSupportSize (MapsTo)
open ForcingDiagramOrder (Product product product_semantics)
open ForcingDiagramPoset (LeftCancelMonoid)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

def HasRep (projection i z : M.Carrier .set) : Prop := ∃ x, Product projection i x z

def Value (projection G default i z c : M.Carrier .set) : Prop :=
  (∃ x, Product projection i x z ∧ PureKuratowski.PairMember M x c G) ∨
    (¬ HasRep projection i z ∧ c = default)

def Graph (n L projection G default T : M.Carrier .set) : Prop := ∀ i z c,
  Product T i z c ↔ (Project.FirstOrderSemantics.reduct M).mem i n ∧
    (Project.FirstOrderSemantics.reduct M).mem z L ∧ Value projection G default i z c

theorem hasRep_of_reaches {n D mul e C L projection A i z v : M.Carrier .set}
    (hm : LeftCancelMonoid D mul e) (hC : Representatives n D C) (hp : MapsTo C L projection)
    (hCopy : CopyLaw D mul projection A) (hz : HasRep projection i z) (hzv : Reaches D A z v) :
    HasRep projection i v := by
  obtain ⟨x,hx⟩ := hz
  obtain ⟨_,xm,_,_,hxm⟩ := (reaches_copy_iff hm hC hp hCopy hx).mp hzv
  exact ⟨xm,hxm⟩

theorem value_total {n D C L R projection G default i z : M.Carrier .set}
    (hC : Representatives n D C) (hp : MapsTo C L projection)
    (hG : MapsTo D R G) : ∃ c, Value projection G default i z c := by
  by_cases h : HasRep projection i z
  · obtain ⟨x,hx⟩ := h
    obtain ⟨c,hc,_⟩ := hG.1.2 x (projected_indices hC hp hx).2
    exact ⟨c,Or.inl ⟨x,hx,hc⟩⟩
  · exact ⟨default,Or.inr ⟨h,rfl⟩⟩

theorem value_unique {n D mul P C L R projection G default i z c d : M.Carrier .set}
    (hC : Representatives n D C) (hp : MapsTo C L projection)
    (hEq : EqualityLaw n D mul P projection) (hG : MapsTo D R G)
    (hc : Value projection G default i z c) (hd : Value projection G default i z d) : c = d := by
  rcases hc with ⟨x,hx,hxc⟩ | ⟨hn,hc⟩
  · rcases hd with ⟨y,hy,hyd⟩ | ⟨hn,_⟩
    · have he := copy_injective hC hp hEq hx hy
      subst y
      exact ForcingConditionGraphs.function_unique hG.1 hxc hyd
    · exact (hn ⟨x,hx⟩).elim
  · rcases hd with ⟨x,hx,_⟩ | ⟨_,hd⟩
    · exact (hn ⟨x,hx⟩).elim
    · exact hc.trans hd.symm

theorem value_range {D R projection G default i z c : M.Carrier .set}
    (hG : MapsTo D R G) (hDefault : (Project.FirstOrderSemantics.reduct M).mem default R)
    (hc : Value projection G default i z c) : (Project.FirstOrderSemantics.reduct M).mem c R := by
  rcases hc with ⟨x,_,hx⟩ | ⟨_,rfl⟩
  · exact hG.2 x c hx
  · exact hDefault

theorem value_copy_iff {n D mul P C L projection G default i x z c : M.Carrier .set}
    (hC : Representatives n D C) (hp : MapsTo C L projection)
    (hEq : EqualityLaw n D mul P projection) (hx : Product projection i x z) :
    Value projection G default i z c ↔ PureKuratowski.PairMember M x c G := by
  constructor
  · rintro (⟨y,hy,hyc⟩ | ⟨hn,_⟩)
    · have he := copy_injective hC hp hEq hy hx
      exact he ▸ hyc
    · exact (hn ⟨x,hx⟩).elim
  · exact fun h => Or.inl ⟨x,hx,h⟩

def hasRep {m0 : Nat} (projection i z : Fin m0) : Project.Formula 1 m0 :=
  .existsE (ProjectSyntax.encode id (ForcingDiagramOrder.product projection.succ i.succ 0 z.succ))

theorem hasRep_freeClosed {m0 : Nat} (projection i z : Fin m0) : (hasRep projection i z).FreeClosed := by
  simp -implicitDefEqProofs [hasRep,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed]

theorem hasRep_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m0 : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m0) (projection i z : Fin m0) :
    Project.Formula.satisfies env (hasRep projection i z) ↔ HasRep (env.bound projection) (env.bound i) (env.bound z) := by
  simp only [hasRep,HasRep,Project.Formula.satisfies_exists_iff,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),product_semantics (M := M)]
  rfl

def value {m0 : Nat} (projection G default i z c : Fin m0) : Project.Formula 1 m0 :=
  .disj (.existsE (.conj (ProjectSyntax.encode id (ForcingDiagramOrder.product projection.succ i.succ 0 z.succ))
    (ProjectSyntax.encode id (Source.SetLanguage.edge G.succ 0 c.succ))))
    (.conj (.neg (hasRep projection i z)) (Project.Formula.extensionalEq (.bound c) (.bound default)))

theorem value_freeClosed {m0 : Nat} (projection G default i z c : Fin m0) : (value projection G default i z c).FreeClosed := by
  simp -implicitDefEqProofs [value,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,hasRep_freeClosed,Project.Formula.extensionalEq]

theorem value_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m0 : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m0) (projection G default i z c : Fin m0) :
    Project.Formula.satisfies env (value projection G default i z c) ↔ Value (env.bound projection) (env.bound G) (env.bound default) (env.bound i) (env.bound z) (env.bound c) := by
  simp only [value,Value,Project.Formula.satisfies_disj_iff,Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_neg_iff,
    Project.Formula.satisfies_extensionalEq_iff_eq (ModelTransfer.extensionality hM),Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),product_semantics (M := M),KuratowskiZF.source_edge,hasRep_semantics hM]
  rfl

def graph {m0 : Nat} (n L projection G default T : Fin m0) : Project.Formula 1 m0 :=
  .forallE (.forallE (.forallE (.iff (ProjectSyntax.encode id (ForcingDiagramOrder.product T.succ.succ.succ 2 1 0))
    (.conj (.mem (.bound 2) (.bound n.succ.succ.succ)) (.conj (.mem (.bound 1) (.bound L.succ.succ.succ))
      (value projection.succ.succ.succ G.succ.succ.succ default.succ.succ.succ 2 1 0))))))

theorem graph_freeClosed {m0 : Nat} (n L projection G default T : Fin m0) : (graph n L projection G default T).FreeClosed := by
  simp -implicitDefEqProofs [graph,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,value_freeClosed]

theorem graph_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m0 : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m0) (n L projection G default T : Fin m0) :
    Project.Formula.satisfies env (graph n L projection G default T) ↔ Graph (env.bound n) (env.bound L) (env.bound projection) (env.bound G) (env.bound default) (env.bound T) := by
  simp only [graph,Graph,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_iff_iff,
    Project.Formula.satisfies_mem_iff,Project.Formula.satisfies_conj_iff,Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),product_semantics (M := M),value_semantics hM]
  rfl

theorem exists_graph (hM : FirstOrder.Theory.Models M nativeZF)
    {n D mul P C L R projection G default J : M.Carrier .set}
    (hC : Representatives n D C) (hp : MapsTo C L projection) (hEq : EqualityLaw n D mul P projection)
    (hG : MapsTo D R G) (hDefault : (Project.FirstOrderSemantics.reduct M).mem default R)
    (hJ : Representatives n L J) : ∃ T, MapsTo J R T ∧ Graph n L projection G default T := by
  let schema : Project.BinarySchema 3 := {
    body := .existsE (.existsE (.conj (PureKuratowskiProject.code (.bound 3) (.bound 1) (.bound 0))
      (value 4 5 6 1 0 2))),freeClosed := by
        simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,PureKuratowskiProject.code,value_freeClosed] }
  let env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) 3 := {
    bound := Fin.cases projection (Fin.cases G (fun _ => default)),free := fun _ => n }
  have he (p c) : schema.denote env p c ↔ ∃ i z, PureKuratowski.Code M p i z ∧ Value projection G default i z c := by
    change Project.Formula.satisfies ((env.push p).push c) schema.body ↔ _
    simp only [schema,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,
      Project.Term.eval_bound,KuratowskiZF.code_correct hM,value_semantics hM]
    rfl
  obtain ⟨T,hT,hgraph⟩ := ZF.exists_setFunctionFromTo_of_denote (ModelTransfer.project_models_iff.mp hM)
    (KuratowskiZF.interpretation hM) schema env (source := J) (target := R) (by
      intro p hpJ
      obtain ⟨i,z,_,_,hcode⟩ := (hJ p).mp hpJ
      obtain ⟨c,hc⟩ := value_total hC hp hG (default := default) (i := i) (z := z)
      exact ⟨c,(he p c).mpr ⟨i,z,hcode,hc⟩⟩) (by
      intro p _ c d hc hd
      obtain ⟨i,z,hcode,hv⟩ := (he p c).mp hc
      obtain ⟨i',z',hcode',hv'⟩ := (he p d).mp hd
      obtain ⟨rfl,rfl⟩ := PureKuratowski.code_injective hcode hcode'
      exact value_unique hC hp hEq hG hv hv') (by
      intro p c _ hc
      obtain ⟨i,z,_,hv⟩ := (he p c).mp hc
      exact value_range hG hDefault hv)
  have hMap : MapsTo J R T := (ForcingSupportSize.native_mapsTo hM J R T).mpr hT
  refine ⟨T,hMap,?_⟩
  intro i z c
  constructor
  · rintro ⟨p,hcode,hpc⟩
    have hDom := (hJ p).mp (ForcingConditionGraphs.function_input hMap.1 hpc)
    obtain ⟨i',z',hi,hz,hcode'⟩ := hDom
    obtain ⟨rfl,rfl⟩ := PureKuratowski.code_injective hcode hcode'
    obtain ⟨_,hDenote⟩ := (hgraph p c).mp hpc
    obtain ⟨i',z',hcode',hv⟩ := (he p c).mp hDenote
    obtain ⟨rfl,rfl⟩ := PureKuratowski.code_injective hcode hcode'
    exact ⟨hi,hz,hv⟩
  · rintro ⟨hi,hz,hv⟩
    obtain ⟨p,hcode⟩ := KuratowskiZF.exists_code hM i z
    exact ⟨p,hcode,(hgraph p c).mpr ⟨(hJ p).mpr ⟨i,z,hi,hz,hcode⟩,(he p c).mpr ⟨i,z,hcode,hv⟩⟩⟩

theorem graph_copy_iff {n D mul P C L projection G default T i x z c : M.Carrier .set}
    (hC : Representatives n D C) (hp : MapsTo C L projection) (hEq : EqualityLaw n D mul P projection)
    (hG : Graph n L projection G default T) (hx : Product projection i x z) :
    Product T i z c ↔ PureKuratowski.PairMember M x c G := by
  have hi := (projected_indices hC hp hx).1
  have hz := projected_range hp hx
  exact (hG i z c).trans ⟨fun h => (value_copy_iff hC hp hEq hx).mp h.2.2,
    fun h => ⟨hi,hz,(value_copy_iff hC hp hEq hx).mpr h⟩⟩

end PPAC.Migration.ConstructionMergerCoordinates
