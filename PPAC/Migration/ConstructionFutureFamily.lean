/- Pinned CellReorder.future_cut: its actual restricted-stage and
intermediate supremum families. Collect unique definable carriers and
multiplication graphs using the existing native constructors. Do not assume
Choice or that an ordinary supremum is already a conservative subobject. -/
import PPAC.Migration.ConstructionIntermediate

namespace PPAC.Migration.ConstructionFutureFamily
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ConstructionConservativeHull (Closure ProductGraph)
open ConstructionCellGeneration (Submonoid)
open ConstructionIntermediate (Sup)
open ConstructionSelectedCellRestriction (Base)
open ConstructionCellRestriction (Stages)
open ConstructionRealCuts (Subset)
open ForcingSupportSize (MapsTo)
open ForcingConditionGraphs (FunctionOn IdentityGraph function_input function_unique)
open ConstructionProbeLetters (Representatives)
open ForcingDiagramPoset (LeftCancelMonoid Conical)
open ConstructionProbeSharedIntersections (ConditionalJoins)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

/-- Native Separation gives the literal retained intersection. -/
theorem intersection_exists (hM : FirstOrder.Theory.Models M nativeZF) (retained D : M.Carrier .set) :
    ∃ C, ∀ x, (Project.FirstOrderSemantics.reduct M).mem x C ↔
      (Project.FirstOrderSemantics.reduct M).mem x retained ∧ (Project.FirstOrderSemantics.reduct M).mem x D := by
  let schema : Project.UnarySchema 1 := {
    body := .mem (.bound 0) (.bound 1)
    freeClosed := by simp [Definitional.Formula.FreeClosed] }
  let env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) 1 := {bound := fun _ => retained,free := fun _ => D}
  obtain ⟨C,hC⟩ := ZF.separation_exists_d (ModelTransfer.project_models_iff.mp hM) schema env D
  have he x : schema.denote env x ↔ (Project.FirstOrderSemantics.reduct M).mem x retained := by
    change Project.Formula.satisfies (env.push x) (.mem (.bound 0) (.bound 1)) ↔ _
    simp only [Project.Formula.satisfies_mem_iff,Project.Term.eval_bound]
    rfl
  exact ⟨C,fun x => (hC x).trans ⟨fun h => ⟨(he x).mp h.2,h.1⟩,fun h => ⟨h.2,(he x).mpr h.1⟩⟩⟩

def CutAt (retained S i C : M.Carrier .set) : Prop := ∃ D,
  PureKuratowski.PairMember M i D S ∧ ∀ x, (Project.FirstOrderSemantics.reduct M).mem x C ↔
    (Project.FirstOrderSemantics.reduct M).mem x retained ∧ (Project.FirstOrderSemantics.reduct M).mem x D

theorem cut_exists (hM : FirstOrder.Theory.Models M nativeZF)
    {I S retained i : M.Carrier .set} (hS : FunctionOn I S)
    (hi : (Project.FirstOrderSemantics.reduct M).mem i I) : ∃ C, CutAt retained S i C := by
  obtain ⟨D,hD,_⟩ := hS.2 i hi
  obtain ⟨C,hC⟩ := intersection_exists hM retained D
  exact ⟨C,D,hD,hC⟩

theorem cut_unique (hM : FirstOrder.Theory.Models M nativeZF)
    {I S retained i C C' : M.Carrier .set} (hS : FunctionOn I S)
    (hC : CutAt retained S i C) (hC' : CutAt retained S i C') : C = C' := by
  obtain ⟨D,hD,hC⟩ := hC
  obtain ⟨D',hD',hC'⟩ := hC'
  have he := function_unique hS hD hD'
  subst D'
  exact (ModelTransfer.extensionality hM).eq_of_same_members C C' (fun x => (hC x).trans (hC' x).symm)

theorem cut_closed {V GV e S retained i C : M.Carrier .set}
    (hStages : Stages V GV e S) (hRet : Closure V GV e retained)
    (hC : CutAt retained S i C) : Closure V GV e C := by
  obtain ⟨D,hD,hC⟩ := hC
  exact ConstructionCellRestriction.intersection_closed hRet (hStages i D hD) hC

/-- The pre-existing actual subobject producer, at the specified carrier. -/
theorem base_of_closed (hM : FirstOrder.Theory.Models M nativeZF)
    {V GV e C : M.Carrier .set} (hv : LeftCancelMonoid V GV e) (hc : Conical V GV e)
    (hJ : ConditionalJoins V GV) (hC : Closure V GV e C) : ∃ P G inc, Base V GV e C P G inc := by
  obtain ⟨P,G,inc,hP,hG,hProduct,hm,hcon,hId,hHom,hCons,hJoin⟩ :=
    ConstructionConservativeHull.exists_submonoid hM hv hc hJ hC
  exact ⟨P,G,inc,hC,hP,hG,hProduct,hm,hcon,hId,hHom,hCons,hJoin⟩

theorem sup_unique (hM : FirstOrder.Theory.Models M nativeZF)
    {V GV e A B F F' : M.Carrier .set} (hF : Sup V GV e A B F) (hF' : Sup V GV e A B F') : F = F' :=
  (ModelTransfer.extensionality hM).eq_of_same_members F F' (fun x =>
    ⟨hF.2.2.2 F' hF'.1 hF'.2.1 hF'.2.2.1 x,hF'.2.2.2 F hF.1 hF.2.1 hF.2.2.1 x⟩)

/-- Ordinary generated supremum, using the existing complete closure constructor. -/
theorem sup_exists (hM : FirstOrder.Theory.Models M nativeZF)
    {V GV e A B PA PB GA GB ia ib : M.Carrier .set}
    (hv : LeftCancelMonoid V GV e) (hA : Base V GV e A PA GA ia) (hB : Base V GV e B PB GB ib) :
    ∃ F, Sup V GV e A B F := by
  have hWhole : Submonoid V GV e V := by
    refine ⟨fun _ h => h,hv.1.1,?_⟩
    intro x y z hx hy hp
    obtain ⟨t,ht,hpt⟩ := (hv.2.1 x hx).1 y hy
    exact ((hv.2.1 x hx).2.1 y t z hy hpt hp) ▸ ht
  have hIdA := hA.2.2.2.2.2.2.1
  have hIdB := hB.2.2.2.2.2.2.1
  have hAMap := hA.2.2.2.2.2.2.2.1.1
  have hBMap := hB.2.2.2.2.2.2.2.1.1
  obtain ⟨F,hF,hAF,hBF,_,hLeast⟩ := ConstructionCellGeneration.exists_closure hM A hWhole hAMap hBMap
  refine ⟨F,hF,?_,?_,?_⟩
  · intro x hx
    exact hAF x x hx ((hIdA x x).mpr ⟨hx,rfl⟩)
  · intro x hx
    exact hBF.2 x x ((hIdB x x).mpr ⟨hx,rfl⟩)
  · intro S hS hAS hBS
    apply hLeast S hS
    · intro x y hx hxy
      exact ((hIdA x y).mp hxy).2 ▸ hAS x hx
    · refine ⟨hBMap.1,?_⟩
      intro x y hxy
      obtain ⟨hx,rfl⟩ := (hIdB x y).mp hxy
      exact hBS x hx

def SupAt (V GV e A Cuts i F : M.Carrier .set) : Prop :=
  ∃ B, PureKuratowski.PairMember M i B Cuts ∧ Sup V GV e A B F

/-- Exact typed multiplication restriction, including the absence of junk rows. -/
def Multiplication (V GV G : M.Carrier .set) : Prop :=
  ∃ P, Representatives V V P ∧ MapsTo P V G ∧ ProductGraph V GV G

theorem multiplication_exists (hM : FirstOrder.Theory.Models M nativeZF)
    {V GV e F : M.Carrier .set} (hv : LeftCancelMonoid V GV e) (hF : Submonoid V GV e F) :
    ∃ G, Multiplication F GV G := by
  obtain ⟨P,G,hP,hG,hProduct⟩ := ConstructionCellGeneration.exists_product hM
    (fun x y hx hy => (hv.2.1 x hx).1 y hy)
    (fun x y z t hx hy hp hq => (hv.2.1 x hx).2.1 y z t hy hp hq) hF
  exact ⟨G,P,hP,hG,hProduct⟩

theorem multiplication_unique (hM : FirstOrder.Theory.Models M nativeZF)
    {F GV G H : M.Carrier .set} (hG : Multiplication F GV G) (hH : Multiplication F GV H) : G = H := by
  obtain ⟨P,hP,hPG,hG⟩ := hG
  obtain ⟨Q,hQ,hQH,hH⟩ := hH
  have forward {P G H : M.Carrier .set} (hP : Representatives F F P) (hPG : MapsTo P F G)
      (hG : ProductGraph F GV G) (hH : ProductGraph F GV H) :
      ∀ p z, PureKuratowski.PairMember M p z G → PureKuratowski.PairMember M p z H := by
    intro p z hpz
    obtain ⟨x,y,_,_,hxy⟩ := (hP p).mp (function_input hPG.1 hpz)
    obtain ⟨q,hxy',hqz⟩ := (hH x y z).mpr ((hG x y z).mp ⟨p,hxy,hpz⟩)
    have he := KuratowskiZF.code_unique hM hxy' hxy
    exact he ▸ hqz
  exact SetTheory.Structure.IsSetRelation.eq_of_pairMember_iff (ModelTransfer.extensionality hM)
    ((ForcingSupportSize.native_mapsTo hM P F G).mp hPG).1.1
    ((ForcingSupportSize.native_mapsTo hM Q F H).mp hQH).1.1
    (fun p z => ⟨forward hP hPG hG hH p z,forward hQ hQH hH hG p z⟩)

def MulAt (GV Domains i G : M.Carrier .set) : Prop :=
  ∃ D, PureKuratowski.PairMember M i D Domains ∧ Multiplication D GV G

def cutAt {m : Nat} (retained S i C : Fin m) : Project.Formula 1 m :=
  (.existsE (.conj (ProjectSyntax.encode id (Source.SetLanguage.edge S.succ i.succ 0)) (ConstructionAttachmentCoefficients.intersection C.succ retained.succ 0)))

theorem cutAt_freeClosed {m : Nat} (retained S i C : Fin m) : (cutAt retained S i C).FreeClosed := by
  simp -implicitDefEqProofs [cutAt,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,ConstructionAttachmentCoefficients.intersection_freeClosed]

theorem cutAt_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (retained S i C : Fin m) :
    Project.Formula.satisfies env (cutAt retained S i C) ↔ CutAt (env.bound retained) (env.bound S) (env.bound i) (env.bound C) := by
  simp only [cutAt,CutAt,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,ConstructionAttachmentCoefficients.intersection_semantics]
  rfl

def supAt {m : Nat} (V GV e A Cuts i F : Fin m) : Project.Formula 1 m :=
  (.existsE (.conj (ProjectSyntax.encode id (Source.SetLanguage.edge Cuts.succ i.succ 0)) (ConstructionIntermediate.sup V.succ GV.succ e.succ A.succ 0 F.succ)))

theorem supAt_freeClosed {m : Nat} (V GV e A Cuts i F : Fin m) : (supAt V GV e A Cuts i F).FreeClosed := by
  simp -implicitDefEqProofs [supAt,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,ConstructionIntermediate.sup_freeClosed]

theorem supAt_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (V GV e A Cuts i F : Fin m) :
    Project.Formula.satisfies env (supAt V GV e A Cuts i F) ↔ SupAt (env.bound V) (env.bound GV) (env.bound e) (env.bound A) (env.bound Cuts) (env.bound i) (env.bound F) := by
  simp only [supAt,SupAt,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,ConstructionIntermediate.sup_semantics hM]
  rfl

def multiplication {m : Nat} (D GV G : Fin m) : Project.Formula 1 m :=
  (.existsE (.conj (ConstructionProbeLetters.representatives D.succ D.succ 0) (.conj (ProjectSyntax.encode id (Source.SetLanguage.mapsTo G.succ 0 D.succ)) (ConstructionConservativeHull.productGraph D.succ GV.succ G.succ))))

theorem multiplication_freeClosed {m : Nat} (D GV G : Fin m) : (multiplication D GV G).FreeClosed := by
  simp -implicitDefEqProofs [multiplication,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,ConstructionProbeLetters.representatives_freeClosed,ConstructionConservativeHull.productGraph_freeClosed]

theorem multiplication_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (D GV G : Fin m) :
    Project.Formula.satisfies env (multiplication D GV G) ↔ Multiplication (env.bound D) (env.bound GV) (env.bound G) := by
  simp only [multiplication,Multiplication,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),ConstructionProbeLetters.representatives_semantics hM,ForcingSupportSize.mapsTo_semantics (M := M),ConstructionConservativeHull.productGraph_semantics hM]
  rfl

def mulAt {m : Nat} (GV Domains i G : Fin m) : Project.Formula 1 m :=
  (.existsE (.conj (ProjectSyntax.encode id (Source.SetLanguage.edge Domains.succ i.succ 0)) (multiplication 0 GV.succ G.succ)))

theorem mulAt_freeClosed {m : Nat} (GV Domains i G : Fin m) : (mulAt GV Domains i G).FreeClosed := by
  simp -implicitDefEqProofs [mulAt,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,multiplication_freeClosed]

theorem mulAt_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (GV Domains i G : Fin m) :
    Project.Formula.satisfies env (mulAt GV Domains i G) ↔ MulAt (env.bound GV) (env.bound Domains) (env.bound i) (env.bound G) := by
  simp only [mulAt,MulAt,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,multiplication_semantics hM]
  rfl

def Cuts (I retained S Cuts : M.Carrier .set) : Prop := FunctionOn I Cuts ∧ ∀ i x,
  PureKuratowski.PairMember M i x Cuts ↔ (Project.FirstOrderSemantics.reduct M).mem i I ∧ CutAt retained S i x

def Suprema (I V GV e A Cuts Futures : M.Carrier .set) : Prop := FunctionOn I Futures ∧ ∀ i x,
  PureKuratowski.PairMember M i x Futures ↔ (Project.FirstOrderSemantics.reduct M).mem i I ∧ SupAt V GV e A Cuts i x

def Products (I GV Domains Muls : M.Carrier .set) : Prop := FunctionOn I Muls ∧ ∀ i x,
  PureKuratowski.PairMember M i x Muls ↔ (Project.FirstOrderSemantics.reduct M).mem i I ∧ MulAt GV Domains i x

theorem supAt_exists (hM : FirstOrder.Theory.Models M nativeZF)
    {I V GV e A PA GA ia Cuts i : M.Carrier .set}
    (hv : LeftCancelMonoid V GV e) (hc : Conical V GV e) (hJ : ConditionalJoins V GV)
    (hA : Base V GV e A PA GA ia) (hCuts : FunctionOn I Cuts) (hStages : Stages V GV e Cuts)
    (hi : (Project.FirstOrderSemantics.reduct M).mem i I) : ∃ F, SupAt V GV e A Cuts i F := by
  obtain ⟨B,hB,_⟩ := hCuts.2 i hi
  obtain ⟨PB,GB,ib,hBase⟩ := base_of_closed hM hv hc hJ (hStages i B hB)
  obtain ⟨F,hF⟩ := sup_exists hM hv hA hBase
  exact ⟨F,B,hB,hF⟩

theorem supAt_unique (hM : FirstOrder.Theory.Models M nativeZF)
    {I V GV e A Cuts i F F' : M.Carrier .set} (hCuts : FunctionOn I Cuts)
    (hF : SupAt V GV e A Cuts i F) (hF' : SupAt V GV e A Cuts i F') : F = F' := by
  obtain ⟨B,hB,hF⟩ := hF
  obtain ⟨B',hB',hF'⟩ := hF'
  have he := function_unique hCuts hB hB'
  subst B'
  exact sup_unique hM hF hF'

theorem mulAt_exists (hM : FirstOrder.Theory.Models M nativeZF)
    {I V GV e Domains i : M.Carrier .set} (hv : LeftCancelMonoid V GV e)
    (hD : FunctionOn I Domains) (hSub : ∀ i D, PureKuratowski.PairMember M i D Domains → Submonoid V GV e D)
    (hi : (Project.FirstOrderSemantics.reduct M).mem i I) : ∃ G, MulAt GV Domains i G := by
  obtain ⟨D,hD,_⟩ := hD.2 i hi
  obtain ⟨G,hG⟩ := multiplication_exists hM hv (hSub i D hD)
  exact ⟨G,D,hD,hG⟩

theorem mulAt_unique (hM : FirstOrder.Theory.Models M nativeZF)
    {I GV Domains i G G' : M.Carrier .set} (hD : FunctionOn I Domains)
    (hG : MulAt GV Domains i G) (hG' : MulAt GV Domains i G') : G = G' := by
  obtain ⟨D,hD',hG⟩ := hG
  obtain ⟨D',hD'',hG'⟩ := hG'
  have he := function_unique hD hD' hD''
  subst D'
  exact multiplication_unique hM hG hG'

theorem exists_cuts (hM : FirstOrder.Theory.Models M nativeZF)
    {I retained S : M.Carrier .set}
    (hS : FunctionOn I S) : ∃ graph, Cuts I retained S graph := by
  let schema : Project.BinarySchema 2 := {body := cutAt 2 3 1 0,freeClosed := cutAt_freeClosed ..}
  let env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) 2 := {bound := Fin.cases retained (fun _ => S),free := fun _ => I}
  have he i x : schema.denote env i x ↔ CutAt retained S i x :=
    cutAt_semantics hM ((env.push i).push x) 2 3 1 0
  have ht : ∀ i, (Project.FirstOrderSemantics.reduct M).mem i I → ∃ x, schema.denote env i x := by
    intro i hi
    obtain ⟨x,hx⟩ := cut_exists hM hS hi
    exact ⟨x,(he i x).mpr hx⟩
  have hu : ∀ i, (Project.FirstOrderSemantics.reduct M).mem i I → ∀ x y,
      schema.denote env i x → schema.denote env i y → x = y :=
    fun _ _ _ _ hx hy => cut_unique hM hS ((he _ _).mp hx) ((he _ _).mp hy)
  have hZF := ModelTransfer.project_models_iff.mp hM
  obtain ⟨images,himages⟩ := ZF.exists_functionalImageOn hZF schema env I ht hu
  obtain ⟨graph,hg,hgraph⟩ := ZF.exists_setFunctionFromTo_of_denote hZF (KuratowskiZF.interpretation hM)
    schema env ht hu (fun i x hi hx => (himages x).mpr ⟨i,hi,hx⟩)
  exact ⟨graph,((ForcingSupportSize.native_mapsTo hM I images graph).mpr hg).1,
    fun i x => (hgraph i x).trans (and_congr_right fun _ => he i x)⟩

theorem exists_suprema (hM : FirstOrder.Theory.Models M nativeZF)
    {I V GV e A PA GA ia Cuts : M.Carrier .set}
    (hv : LeftCancelMonoid V GV e) (hc : Conical V GV e) (hJ : ConditionalJoins V GV)
    (hA : Base V GV e A PA GA ia) (hCuts : FunctionOn I Cuts) (hStages : Stages V GV e Cuts) : ∃ graph, Suprema I V GV e A Cuts graph := by
  let schema : Project.BinarySchema 5 := {body := supAt 2 3 4 5 6 1 0,freeClosed := supAt_freeClosed ..}
  let env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) 5 := {bound := Fin.cases V (Fin.cases GV (Fin.cases e (Fin.cases A (fun _ => Cuts)))),free := fun _ => I}
  have he i x : schema.denote env i x ↔ SupAt V GV e A Cuts i x :=
    supAt_semantics hM ((env.push i).push x) 2 3 4 5 6 1 0
  have ht : ∀ i, (Project.FirstOrderSemantics.reduct M).mem i I → ∃ x, schema.denote env i x := by
    intro i hi
    obtain ⟨x,hx⟩ := supAt_exists hM hv hc hJ hA hCuts hStages hi
    exact ⟨x,(he i x).mpr hx⟩
  have hu : ∀ i, (Project.FirstOrderSemantics.reduct M).mem i I → ∀ x y,
      schema.denote env i x → schema.denote env i y → x = y :=
    fun _ _ _ _ hx hy => supAt_unique hM hCuts ((he _ _).mp hx) ((he _ _).mp hy)
  have hZF := ModelTransfer.project_models_iff.mp hM
  obtain ⟨images,himages⟩ := ZF.exists_functionalImageOn hZF schema env I ht hu
  obtain ⟨graph,hg,hgraph⟩ := ZF.exists_setFunctionFromTo_of_denote hZF (KuratowskiZF.interpretation hM)
    schema env ht hu (fun i x hi hx => (himages x).mpr ⟨i,hi,hx⟩)
  exact ⟨graph,((ForcingSupportSize.native_mapsTo hM I images graph).mpr hg).1,
    fun i x => (hgraph i x).trans (and_congr_right fun _ => he i x)⟩

theorem exists_products (hM : FirstOrder.Theory.Models M nativeZF)
    {I V GV e Domains : M.Carrier .set}
    (hv : LeftCancelMonoid V GV e) (hD : FunctionOn I Domains)
    (hSub : ∀ i D, PureKuratowski.PairMember M i D Domains → Submonoid V GV e D) : ∃ graph, Products I GV Domains graph := by
  let schema : Project.BinarySchema 2 := {body := mulAt 2 3 1 0,freeClosed := mulAt_freeClosed ..}
  let env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) 2 := {bound := Fin.cases GV (fun _ => Domains),free := fun _ => I}
  have he i x : schema.denote env i x ↔ MulAt GV Domains i x :=
    mulAt_semantics hM ((env.push i).push x) 2 3 1 0
  have ht : ∀ i, (Project.FirstOrderSemantics.reduct M).mem i I → ∃ x, schema.denote env i x := by
    intro i hi
    obtain ⟨x,hx⟩ := mulAt_exists hM hv hD hSub hi
    exact ⟨x,(he i x).mpr hx⟩
  have hu : ∀ i, (Project.FirstOrderSemantics.reduct M).mem i I → ∀ x y,
      schema.denote env i x → schema.denote env i y → x = y :=
    fun _ _ _ _ hx hy => mulAt_unique hM hD ((he _ _).mp hx) ((he _ _).mp hy)
  have hZF := ModelTransfer.project_models_iff.mp hM
  obtain ⟨images,himages⟩ := ZF.exists_functionalImageOn hZF schema env I ht hu
  obtain ⟨graph,hg,hgraph⟩ := ZF.exists_setFunctionFromTo_of_denote hZF (KuratowskiZF.interpretation hM)
    schema env ht hu (fun i x hi hx => (himages x).mpr ⟨i,hi,hx⟩)
  exact ⟨graph,((ForcingSupportSize.native_mapsTo hM I images graph).mpr hg).1,
    fun i x => (hgraph i x).trans (and_congr_right fun _ => he i x)⟩

theorem cuts_stages {I V GV e S retained CutsGraph : M.Carrier .set}
    (hCuts : Cuts I retained S CutsGraph) (hS : Stages V GV e S) (hRet : Closure V GV e retained) :
    Stages V GV e CutsGraph := by
  intro i C hiC
  exact cut_closed hS hRet ((hCuts.2 i C).mp hiC).2

theorem suprema_submonoids {I V GV e A CutsGraph Futures : M.Carrier .set}
    (hF : Suprema I V GV e A CutsGraph Futures) :
    ∀ i F, PureKuratowski.PairMember M i F Futures → Submonoid V GV e F := by
  intro i F hiF
  obtain ⟨_,_,hSup⟩ := ((hF.2 i F).mp hiF).2
  exact hSup.1

theorem cuts_mono {I R S retained CutsGraph : M.Carrier .set}
    (hCuts : Cuts I retained S CutsGraph) (hMono : ConstructionBlockStages.MonotoneImages I R S) :
    ConstructionBlockStages.MonotoneImages I R CutsGraph := by
  intro i j C D hi hj hij hiC hjD
  obtain ⟨Ci,hiCi,hC⟩ := ((hCuts.2 i C).mp hiC).2
  obtain ⟨Dj,hjDj,hD⟩ := ((hCuts.2 j D).mp hjD).2
  intro x hx
  obtain ⟨hxRet,hxCi⟩ := (hC x).mp hx
  exact (hD x).mpr ⟨hxRet,hMono i j Ci Dj hi hj hij hiCi hjDj x hxCi⟩

theorem suprema_mono {I R V GV e A CutsGraph Futures : M.Carrier .set}
    (hF : Suprema I V GV e A CutsGraph Futures) (hMono : ConstructionBlockStages.MonotoneImages I R CutsGraph) :
    ConstructionBlockStages.MonotoneImages I R Futures := by
  intro i j F G hi hj hij hiF hjG
  obtain ⟨B,hiB,hLocalF⟩ := ((hF.2 i F).mp hiF).2
  obtain ⟨C,hjC,hG⟩ := ((hF.2 j G).mp hjG).2
  exact hLocalF.2.2.2 G hG.1 hG.2.1 (fun x hx => hG.2.2.1 x (hMono i j B C hi hj hij hiB hjC x hx))

/-- The actual four internal families needed at future_cut's limit. The
supremum carriers are only asserted to be ordinary submonoids here; the
full induction must still prove their conservative closure and Square. -/
theorem construction (hM : FirstOrder.Theory.Models M nativeZF)
    {I R V GV e A PA GA ia S retained : M.Carrier .set}
    (hv : LeftCancelMonoid V GV e) (hc : Conical V GV e) (hJ : ConditionalJoins V GV)
    (hA : Base V GV e A PA GA ia) (hS : FunctionOn I S) (hStages : Stages V GV e S)
    (hRet : Closure V GV e retained) (hMono : ConstructionBlockStages.MonotoneImages I R S) :
    ∃ CutsGraph Futures CutMuls FutureMuls,
      Cuts I retained S CutsGraph ∧ Suprema I V GV e A CutsGraph Futures ∧
      Products I GV CutsGraph CutMuls ∧ Products I GV Futures FutureMuls ∧
      ConstructionBlockStages.MonotoneImages I R CutsGraph ∧ ConstructionBlockStages.MonotoneImages I R Futures := by
  obtain ⟨CutsGraph,hCuts⟩ := exists_cuts hM hS
  have hClosed := cuts_stages hCuts hStages hRet
  obtain ⟨Futures,hFutures⟩ := exists_suprema hM hv hc hJ hA hCuts.1 hClosed
  obtain ⟨CutMuls,hCutMuls⟩ := exists_products hM hv hCuts.1 (fun i D hD =>
    ⟨(hClosed i D hD).1,(hClosed i D hD).2.1,(hClosed i D hD).2.2.1⟩)
  obtain ⟨FutureMuls,hFutureMuls⟩ := exists_products hM hv hFutures.1 (suprema_submonoids hFutures)
  have hCutsMono := cuts_mono hCuts hMono
  exact ⟨CutsGraph,Futures,CutMuls,FutureMuls,hCuts,hFutures,hCutMuls,hFutureMuls,hCutsMono,suprema_mono hFutures hCutsMono⟩

def cutsFormula {m : Nat} (I retained S CutsGraph : Fin m) : Project.Formula 1 m :=
  .conj (ProjectSyntax.encode id (Source.SetLanguage.functionOn CutsGraph I))
    (.forallE (.forallE (.iff (ProjectSyntax.encode id (Source.SetLanguage.edge CutsGraph.succ.succ 1 0))
      (.conj (.mem (.bound 1) (.bound I.succ.succ)) (cutAt retained.succ.succ S.succ.succ 1 0)))))

theorem cutsFormula_freeClosed {m : Nat} (I retained S CutsGraph : Fin m) : (cutsFormula I retained S CutsGraph).FreeClosed := by
  simp -implicitDefEqProofs [cutsFormula,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,cutAt_freeClosed]

theorem cutsFormula_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (I retained S CutsGraph : Fin m) :
    Project.Formula.satisfies env (cutsFormula I retained S CutsGraph) ↔ Cuts (env.bound I) (env.bound retained) (env.bound S) (env.bound CutsGraph) := by
  simp only [cutsFormula,Cuts,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_forall_iff,
    Project.Formula.satisfies_iff_iff,Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingConditionGraphs.functionOn_semantics (M := M),KuratowskiZF.source_edge,cutAt_semantics hM]
  rfl

def supremaFormula {m : Nat} (I V GV e A CutsGraph Futures : Fin m) : Project.Formula 1 m :=
  .conj (ProjectSyntax.encode id (Source.SetLanguage.functionOn Futures I))
    (.forallE (.forallE (.iff (ProjectSyntax.encode id (Source.SetLanguage.edge Futures.succ.succ 1 0))
      (.conj (.mem (.bound 1) (.bound I.succ.succ)) (supAt V.succ.succ GV.succ.succ e.succ.succ A.succ.succ CutsGraph.succ.succ 1 0)))))

theorem supremaFormula_freeClosed {m : Nat} (I V GV e A CutsGraph Futures : Fin m) : (supremaFormula I V GV e A CutsGraph Futures).FreeClosed := by
  simp -implicitDefEqProofs [supremaFormula,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,supAt_freeClosed]

theorem supremaFormula_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (I V GV e A CutsGraph Futures : Fin m) :
    Project.Formula.satisfies env (supremaFormula I V GV e A CutsGraph Futures) ↔ Suprema (env.bound I) (env.bound V) (env.bound GV) (env.bound e) (env.bound A) (env.bound CutsGraph) (env.bound Futures) := by
  simp only [supremaFormula,Suprema,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_forall_iff,
    Project.Formula.satisfies_iff_iff,Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingConditionGraphs.functionOn_semantics (M := M),KuratowskiZF.source_edge,supAt_semantics hM]
  rfl

def productsFormula {m : Nat} (I GV Domains Muls : Fin m) : Project.Formula 1 m :=
  .conj (ProjectSyntax.encode id (Source.SetLanguage.functionOn Muls I))
    (.forallE (.forallE (.iff (ProjectSyntax.encode id (Source.SetLanguage.edge Muls.succ.succ 1 0))
      (.conj (.mem (.bound 1) (.bound I.succ.succ)) (mulAt GV.succ.succ Domains.succ.succ 1 0)))))

theorem productsFormula_freeClosed {m : Nat} (I GV Domains Muls : Fin m) : (productsFormula I GV Domains Muls).FreeClosed := by
  simp -implicitDefEqProofs [productsFormula,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,mulAt_freeClosed]

theorem productsFormula_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (I GV Domains Muls : Fin m) :
    Project.Formula.satisfies env (productsFormula I GV Domains Muls) ↔ Products (env.bound I) (env.bound GV) (env.bound Domains) (env.bound Muls) := by
  simp only [productsFormula,Products,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_forall_iff,
    Project.Formula.satisfies_iff_iff,Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingConditionGraphs.functionOn_semantics (M := M),KuratowskiZF.source_edge,mulAt_semantics hM]
  rfl

/-- All four families are existentially quantified internal sets. -/
def constructionSentence {m : Nat} (I R V GV e A PA GA ia S retained : Fin m) : Project.Sentence where
  formula := Project.Formula.forallClosure m
    (.imp (ProjectSyntax.encode id (ForcingDiagramPoset.leftCancelMonoid V GV e)) (.imp (ProjectSyntax.encode id (ForcingDiagramPoset.conical V GV e)) (.imp (ConstructionProbeSharedIntersections.conditionalJoins V GV) (.imp (ConstructionSelectedCellRestriction.baseFormula V GV e A PA GA ia) (.imp (ProjectSyntax.encode id (Source.SetLanguage.functionOn S I)) (.imp (ConstructionCellRestriction.stages V GV e S) (.imp (ConstructionConservativeHull.closure V GV e retained) (.imp (ConstructionBlockStages.monotoneImages I R S) (.existsE (.existsE (.existsE (.existsE (.conj (cutsFormula I.succ.succ.succ.succ retained.succ.succ.succ.succ S.succ.succ.succ.succ 3) (.conj (supremaFormula I.succ.succ.succ.succ V.succ.succ.succ.succ GV.succ.succ.succ.succ e.succ.succ.succ.succ A.succ.succ.succ.succ 3 2) (.conj (productsFormula I.succ.succ.succ.succ GV.succ.succ.succ.succ 3 1) (.conj (productsFormula I.succ.succ.succ.succ GV.succ.succ.succ.succ 2 0) (.conj (ConstructionBlockStages.monotoneImages I.succ.succ.succ.succ R.succ.succ.succ.succ 3) (ConstructionBlockStages.monotoneImages I.succ.succ.succ.succ R.succ.succ.succ.succ 2))))))))))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
      ConstructionProbeSharedIntersections.conditionalJoins_freeClosed,ConstructionSelectedCellRestriction.baseFormula_freeClosed,
      ConstructionCellRestriction.stages_freeClosed,ConstructionConservativeHull.closure_freeClosed,
      ConstructionBlockStages.monotoneImages_freeClosed,cutsFormula_freeClosed,supremaFormula_freeClosed,productsFormula_freeClosed]

theorem construction_models {m : Nat} (I R V GV e A PA GA ia S retained : Fin m) (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence (constructionSentence I R V GV e A PA GA ia S retained)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) (constructionSentence I R V GV e A PA GA ia S retained)]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),ForcingDiagramPoset.leftCancelMonoid_semantics (M := M),
    ForcingDiagramPoset.conical_semantics (M := M),ConstructionProbeSharedIntersections.conditionalJoins_semantics hM,
    ConstructionSelectedCellRestriction.baseFormula_semantics hM,ForcingConditionGraphs.functionOn_semantics (M := M),
    ConstructionCellRestriction.stages_semantics hM,ConstructionConservativeHull.closure_semantics hM,
    ConstructionBlockStages.monotoneImages_semantics hM,cutsFormula_semantics hM,supremaFormula_semantics hM,productsFormula_semantics hM]
  exact construction hM

theorem construction_kernel_certificate {m : Nat} (I R V GV e A PA GA ia S retained : Fin m) :
    FirstOrder.Derives nativeZF [] (Project.fo_sentence (constructionSentence I R V GV e A PA GA ia S retained)) :=
  ModelTransfer.derives (fun _ hM => construction_models I R V GV e A PA GA ia S retained hM)

end PPAC.Migration.ConstructionFutureFamily
