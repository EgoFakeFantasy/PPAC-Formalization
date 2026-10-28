/- Pinned ComponentGluing.vertexFiber/arrowMap/arrowMap_bijective/arrowMap_comp/
arrowMap_id:227-291. The fibers are collected over the existing internal vertex
carrier; arrow maps are literal restrictions from the same actual System.
Consumer: ComponentGluing.Matches/gluingSetoid/Glued, not a new proof route. -/
import PPAC.Migration.ForcingSystemFibers
import PPAC.Migration.ConstructionComponentCofinal

namespace PPAC.Migration.ForcingComponentFibers
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ForcingSupportSize (MapsTo Injection)
open ConstructionComponentCarrier (Code EncodedVertex)
open ConstructionComponentCofinal (EncodedArrow)
open ForcingSystemFibers (Fiber)
open ForcingEligibleRestriction (Restricts)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

def VertexFiber (D mul objects maps v X : M.Carrier .set) : Prop :=
  ∃ r a U Or, Code v r a U ∧ PureKuratowski.PairMember M r Or objects ∧
    Fiber D mul objects maps r Or a U X

theorem vertexFiber_unique (hM : FirstOrder.Theory.Models M nativeZF)
    {D mul diagrams image objects maps v X Y : M.Carrier .set}
    (hObj : MapsTo diagrams image objects)
    (hX : VertexFiber D mul objects maps v X) (hY : VertexFiber D mul objects maps v Y) : X = Y := by
  obtain ⟨r,a,U,Or,hv,hr,hX⟩ := hX
  obtain ⟨s,b,V,Os,hw,hs,hY⟩ := hY
  obtain ⟨rfl,rfl,rfl⟩ := ConstructionComponentCarrier.code_injective hv hw
  have he := ForcingConditionGraphs.function_unique hObj.1 hr hs
  subst Os
  exact (ModelTransfer.extensionality hM).eq_of_same_members X Y (fun x => (hX x).trans (hY x).symm)

theorem exists_vertexFiber (hM : FirstOrder.Theory.Models M nativeZF)
    {D I mul q diagrams image objects maps v : M.Carrier .set}
    (hDiagrams : ForcingDiagramCarrier.Carrier D I diagrams) (hObj : MapsTo diagrams image objects)
    (hv : EncodedVertex D I mul q v) : ∃ X, VertexFiber D mul objects maps v X := by
  obtain ⟨r,a,U,hCode,hv⟩ := hv
  obtain ⟨Or,hr,_⟩ := hObj.1.2 r ((hDiagrams r).mpr hv.1)
  obtain ⟨X,hX⟩ := ForcingSystemFibers.exists_fiber hM D mul objects maps r Or a U
  exact ⟨X,r,a,U,Or,hCode,hr,hX⟩

def Family (D mul objects maps vertices fibers : M.Carrier .set) : Prop := ∀ v X,
  PureKuratowski.PairMember M v X fibers ↔
    (Project.FirstOrderSemantics.reduct M).mem v vertices ∧ VertexFiber D mul objects maps v X

/-- No independent bijection is chosen: b is exactly f restricted to Y. -/
def ArrowMap (maps v w X Y b : M.Carrier .set) : Prop :=
  ∃ r a U s c V z f, Code v r a U ∧ Code w s c V ∧
    PureKuratowski.Code M z s r ∧ PureKuratowski.PairMember M z f maps ∧
    Restricts b f Y ∧ Injection Y X b ∧
    ∀ x, (Project.FirstOrderSemantics.reduct M).mem x X →
      ∃ y, (Project.FirstOrderSemantics.reduct M).mem y Y ∧ PureKuratowski.PairMember M y x b

theorem exists_arrowMap (hM : FirstOrder.Theory.Models M nativeZF)
    {D I mul e q diagrams objImage objects S mapImage maps v w n X Y : M.Carrier .set}
    (hm : ForcingDiagramPoset.LeftCancelMonoid D mul e)
    (hJ : ConstructionProbeSharedIntersections.ConditionalJoins D mul)
    (hDiagrams : ForcingDiagramCarrier.Carrier D I diagrams) (hObj : MapsTo diagrams objImage objects)
    (hS : ForcingEligibleMapFamily.Arrows D mul diagrams S) (hMaps : MapsTo S mapImage maps)
    (hSys : ForcingEligibleSystem.System D objects maps)
    (hArrow : EncodedArrow D I mul q v w n)
    (hX : VertexFiber D mul objects maps v X) (hY : VertexFiber D mul objects maps w Y) :
    ∃ b, ArrowMap maps v w X Y b := by
  obtain ⟨r,a,U,s,c,V,hv,hw,hVertex,hTarget,hArrow⟩ := hArrow
  obtain ⟨r',a',U',Or,hv',hr,hX⟩ := hX
  obtain ⟨s',c',V',Os,hw',hs,hY⟩ := hY
  obtain ⟨rfl,rfl,rfl⟩ := ConstructionComponentCarrier.code_injective hv hv'
  obtain ⟨rfl,rfl,rfl⟩ := ConstructionComponentCarrier.code_injective hw hw'
  obtain ⟨z,f,hz,hf,_⟩ := ForcingSystemAvailability.exists_map hM hObj hS hMaps hSys hr hs
    ⟨n,hVertex.2.2.1 n hArrow.1,hArrow.2.1⟩
  obtain ⟨b,hb,hR,hOnto⟩ := ForcingSystemFibers.fiber_bijection hM hm hJ hDiagrams hObj hS hMaps hSys
    hr hs hTarget.2.2.2.1 (ConstructionComponentVertices.index_mul hm hVertex hTarget hArrow)
    hArrow.2.1 hz hf hVertex.2.2 hArrow.1 hArrow.2.2 hX hY
  exact ⟨b,r,a,U,s,c,V,z,f,hv,hw,hz,hf,hR,hb,hOnto⟩

theorem arrowMap_unique (hM : FirstOrder.Theory.Models M nativeZF)
    {maps S image v w X Y b c : M.Carrier .set}
    (hMaps : MapsTo S image maps)
    (hb : ArrowMap maps v w X Y b) (hc : ArrowMap maps v w X Y c) : b = c := by
  obtain ⟨r,a,U,s,d,V,z,f,hv,hw,hz,hf,hb,hInj,_⟩ := hb
  obtain ⟨r',a',U',s',d',V',z',f',hv',hw',hz',hf',hc,hInj',_⟩ := hc
  obtain ⟨rfl,rfl,rfl⟩ := ConstructionComponentCarrier.code_injective hv hv'
  obtain ⟨rfl,rfl,rfl⟩ := ConstructionComponentCarrier.code_injective hw hw'
  have ez := KuratowskiZF.code_unique hM hz hz'
  subst z'
  have ef := ForcingConditionGraphs.function_unique hMaps.1 hf hf'
  subst f'
  have hn := (ForcingSupportSize.native_mapsTo hM Y X b).mp hInj.1
  have hn' := (ForcingSupportSize.native_mapsTo hM Y X c).mp hInj'.1
  exact SetTheory.Structure.IsSetRelation.eq_of_pairMember_iff (ModelTransfer.extensionality hM)
    hn.1.1 hn'.1.1 (fun x y => (hb x y).trans (hc x y).symm)

theorem arrowMap_id {D mul objects maps v X b : M.Carrier .set}
    (hSys : ForcingEligibleSystem.System D objects maps)
    (hX : VertexFiber D mul objects maps v X) (hb : ArrowMap maps v v X X b) :
    ForcingConditionGraphs.IdentityGraph X b := by
  obtain ⟨r,a,U,Or,hv,hr,hX⟩ := hX
  obtain ⟨r',a',U',s',c',V',z,f,hv',hw',hz,hf,hR,_,_⟩ := hb
  obtain ⟨rfl,rfl,rfl⟩ := ConstructionComponentCarrier.code_injective hv hv'
  obtain ⟨rfl,rfl,rfl⟩ := ConstructionComponentCarrier.code_injective hv hw'
  exact ForcingEligibleRestriction.restrict_refl (hSys.2.1 r Or z f hr hz hf)
    (fun x hx => ((hX x).mp hx).1) hR

theorem arrowMap_comp {D mul objects maps v w t X Y Z b c d : M.Carrier .set}
    (hSys : ForcingEligibleSystem.System D objects maps)
    (hX : VertexFiber D mul objects maps v X) (hY : VertexFiber D mul objects maps w Y)
    (hZ : VertexFiber D mul objects maps t Z)
    (hb : ArrowMap maps v w X Y b) (hc : ArrowMap maps w t Y Z c)
    (hd : ArrowMap maps v t X Z d) : ForcingConditionGraphs.CompositionGraph Z b c d := by
  obtain ⟨r,a,U,Or,hv,hr,_⟩ := hX
  obtain ⟨s,j,V,Os,hw,hs,_⟩ := hY
  obtain ⟨p,k,W,Op,ht,hp,hZ⟩ := hZ
  obtain ⟨r',a',U',s',j',V',z1,f,hv',hw',hz1,hf,hb,_,_⟩ := hb
  obtain ⟨rfl,rfl,rfl⟩ := ConstructionComponentCarrier.code_injective hv hv'
  obtain ⟨rfl,rfl,rfl⟩ := ConstructionComponentCarrier.code_injective hw hw'
  obtain ⟨s',j',V',p',k',W',z2,g,hw',ht',hz2,hg,hc,hcMap,_⟩ := hc
  obtain ⟨rfl,rfl,rfl⟩ := ConstructionComponentCarrier.code_injective hw hw'
  obtain ⟨rfl,rfl,rfl⟩ := ConstructionComponentCarrier.code_injective ht ht'
  obtain ⟨r',a',U',p',k',W',z3,h,hv',ht',hz3,hh,hd,_,_⟩ := hd
  obtain ⟨rfl,rfl,rfl⟩ := ConstructionComponentCarrier.code_injective hv hv'
  obtain ⟨rfl,rfl,rfl⟩ := ConstructionComponentCarrier.code_injective ht ht'
  exact ForcingEligibleRestriction.restrict_comp
    (hSys.2.2.1 p s r Op Os Or z2 z1 z3 g f h hp hs hr hz2 hz1 hz3 hg hf hh)
    (fun x hx => ((hZ x).mp hx).1) hc hb hd hcMap.1

def vertexFiber {m : Nat} (D mul objects maps v X : Fin m) : Project.Formula 1 m :=
  .existsE (.existsE (.existsE (.existsE
    (.conj (ConstructionComponentCarrier.code v.succ.succ.succ.succ 3 2 1)
      (.conj (ProjectSyntax.encode id (Source.SetLanguage.edge objects.succ.succ.succ.succ 3 0))
        (ProjectSyntax.encode id (ForcingSystemFibers.fiber D.succ.succ.succ.succ mul.succ.succ.succ.succ
          objects.succ.succ.succ.succ maps.succ.succ.succ.succ 3 0 2 1 X.succ.succ.succ.succ)))))))

theorem vertexFiber_freeClosed {m : Nat} (D mul objects maps v X : Fin m) :
    (vertexFiber D mul objects maps v X).FreeClosed := by
  simp -implicitDefEqProofs [vertexFiber,Definitional.Formula.FreeClosed,
    ConstructionComponentCarrier.code_freeClosed,ProjectSyntax.freeClosed]

theorem vertexFiber_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (D mul objects maps v X : Fin m) :
    Project.Formula.satisfies env (vertexFiber D mul objects maps v X) ↔
      VertexFiber (env.bound D) (env.bound mul) (env.bound objects) (env.bound maps) (env.bound v) (env.bound X) := by
  simp only [vertexFiber,VertexFiber,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,
    ConstructionComponentCarrier.code_semantics hM,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,
    ForcingSystemFibers.fiber_semantics (M := M)]
  rfl

theorem exists_family (hM : FirstOrder.Theory.Models M nativeZF)
    {D I mul q diagrams objImage objects maps vertices : M.Carrier .set}
    (hDiagrams : ForcingDiagramCarrier.Carrier D I diagrams) (hObj : MapsTo diagrams objImage objects)
    (hVertices : ConstructionComponentCarrier.Carrier D I mul q vertices) :
    ∃ image fibers, MapsTo vertices image fibers ∧ Family D mul objects maps vertices fibers := by
  let schema : Project.BinarySchema 4 := {
    body := vertexFiber 2 3 4 5 1 0
    freeClosed := vertexFiber_freeClosed _ _ _ _ _ _ }
  let env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) 4 := {
    bound := Fin.cases D (Fin.cases mul (Fin.cases objects (fun _ => maps))), free := fun _ => vertices }
  have hRel : ∀ v X, schema.denote env v X ↔ VertexFiber D mul objects maps v X := by
    intro v X
    simpa only [schema,env,Project.BinarySchema.denote] using!
      vertexFiber_semantics hM ((env.push v).push X) (2 : Fin 6) 3 4 5 1 0
  have ht : ∀ v, (Project.FirstOrderSemantics.reduct M).mem v vertices → ∃ X, schema.denote env v X := by
    intro v hv
    obtain ⟨X,hX⟩ := exists_vertexFiber hM hDiagrams hObj ((hVertices v).mp hv)
    exact ⟨X,(hRel v X).mpr hX⟩
  have hu : ∀ v X Y, schema.denote env v X → schema.denote env v Y → X = Y :=
    fun v X Y hX hY => vertexFiber_unique hM hObj ((hRel v X).mp hX) ((hRel v Y).mp hY)
  obtain ⟨image,hImage⟩ := ZF.exists_functionalImage (ModelTransfer.project_models_iff.mp hM) schema env vertices ht hu
  obtain ⟨fibers,hMap,hEdge⟩ := ZF.exists_setFunctionFromTo_of_denote (ModelTransfer.project_models_iff.mp hM)
    (KuratowskiZF.interpretation hM) schema env ht (fun v _ X Y hX hY => hu v X Y hX hY)
    (fun v X hv hX => (hImage X).mpr ⟨v,hv,hX⟩)
  exact ⟨image,fibers,(ForcingSupportSize.native_mapsTo hM vertices image fibers).mpr hMap,
    fun v X => (hEdge v X).trans (and_congr Iff.rfl (hRel v X))⟩

def Coherent (D I mul q objects maps : M.Carrier .set) : Prop :=
  (∀ v w n X Y, EncodedArrow D I mul q v w n → VertexFiber D mul objects maps v X →
    VertexFiber D mul objects maps w Y → ∃ b, ArrowMap maps v w X Y b) ∧
  (∀ v X b, VertexFiber D mul objects maps v X → ArrowMap maps v v X X b →
    ForcingConditionGraphs.IdentityGraph X b) ∧
  (∀ v w t X Y Z b c d, VertexFiber D mul objects maps v X → VertexFiber D mul objects maps w Y →
    VertexFiber D mul objects maps t Z → ArrowMap maps v w X Y b → ArrowMap maps w t Y Z c →
    ArrowMap maps v t X Z d → ForcingConditionGraphs.CompositionGraph Z b c d)

theorem coherent_of_system (hM : FirstOrder.Theory.Models M nativeZF)
    {D I mul e q diagrams objImage objects S mapImage maps : M.Carrier .set}
    (hm : ForcingDiagramPoset.LeftCancelMonoid D mul e)
    (hJ : ConstructionProbeSharedIntersections.ConditionalJoins D mul)
    (hDiagrams : ForcingDiagramCarrier.Carrier D I diagrams) (hObj : MapsTo diagrams objImage objects)
    (hS : ForcingEligibleMapFamily.Arrows D mul diagrams S) (hMaps : MapsTo S mapImage maps)
    (hSys : ForcingEligibleSystem.System D objects maps) : Coherent D I mul q objects maps :=
  ⟨fun _ _ _ _ _ hA hX hY => exists_arrowMap hM hm hJ hDiagrams hObj hS hMaps hSys hA hX hY,
    fun _ _ _ hX hb => arrowMap_id hSys hX hb,
    fun _ _ _ _ _ _ _ _ _ hX hY hZ hb hc hd => arrowMap_comp hSys hX hY hZ hb hc hd⟩

def arrowMap {m : Nat} (maps v w X Y b : Fin m) : Project.Formula 1 m :=
  (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.conj (ConstructionComponentCarrier.code v.succ.succ.succ.succ.succ.succ.succ.succ 7 6 5) (.conj (ConstructionComponentCarrier.code w.succ.succ.succ.succ.succ.succ.succ.succ 4 3 2) (.conj (ProjectSyntax.encode id (PairSyntax.ordered 1 4 7)) (.conj (ProjectSyntax.encode id (Source.SetLanguage.edge maps.succ.succ.succ.succ.succ.succ.succ.succ 1 0)) (.conj (ProjectSyntax.encode id (RestrictionSyntax.edgeLaw b.succ.succ.succ.succ.succ.succ.succ.succ 0 Y.succ.succ.succ.succ.succ.succ.succ.succ)) (.conj (ProjectSyntax.encode id (Source.SetLanguage.injection b.succ.succ.succ.succ.succ.succ.succ.succ Y.succ.succ.succ.succ.succ.succ.succ.succ X.succ.succ.succ.succ.succ.succ.succ.succ)) (.forallE (.imp (.mem (.bound 0) (.bound X.succ.succ.succ.succ.succ.succ.succ.succ.succ)) (.existsE (.conj (.mem (.bound 0) (.bound Y.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ)) (ProjectSyntax.encode id (Source.SetLanguage.edge b.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ 0 1))))))))))))))))))))

theorem arrowMap_freeClosed {m : Nat} (maps v w X Y b : Fin m) :
    (arrowMap maps v w X Y b).FreeClosed := by
  simp -implicitDefEqProofs [arrowMap,Definitional.Formula.FreeClosed,
    ConstructionComponentCarrier.code_freeClosed,ProjectSyntax.freeClosed]

theorem arrowMap_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (maps v w X Y b : Fin m) :
    Project.Formula.satisfies env (arrowMap maps v w X Y b) ↔
      ArrowMap (env.bound maps) (env.bound v) (env.bound w) (env.bound X) (env.bound Y) (env.bound b) := by
  simp only [arrowMap,ArrowMap,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_mem_iff,
    ConstructionComponentCarrier.code_semantics hM,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,KuratowskiZF.source_code,
    ForcingEligibleRestriction.edgeLaw_semantics (M := M),ForcingSupportSize.injection_semantics (M := M),Project.Term.eval_bound]
  rfl

def family {m : Nat} (D mul objects maps vertices fibers : Fin m) : Project.Formula 1 m :=
  (.forallE (.forallE (.iff (ProjectSyntax.encode id (Source.SetLanguage.edge fibers.succ.succ 1 0)) (.conj (.mem (.bound 1) (.bound vertices.succ.succ)) (vertexFiber D.succ.succ mul.succ.succ objects.succ.succ maps.succ.succ 1 0)))))

theorem family_freeClosed {m : Nat} (D mul objects maps vertices fibers : Fin m) :
    (family D mul objects maps vertices fibers).FreeClosed := by
  simp -implicitDefEqProofs [family,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,vertexFiber_freeClosed]

theorem family_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (D mul objects maps vertices fibers : Fin m) :
    Project.Formula.satisfies env (family D mul objects maps vertices fibers) ↔
      Family (env.bound D) (env.bound mul) (env.bound objects) (env.bound maps) (env.bound vertices) (env.bound fibers) := by
  simp only [family,Family,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_iff_iff,
    Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,vertexFiber_semantics hM]
  rfl

def coherent {m : Nat} (D I mul q objects maps : Fin m) : Project.Formula 1 m :=
  (.conj (.forallE (.forallE (.forallE (.forallE (.forallE (.imp (ConstructionComponentCofinal.encodedArrow D.succ.succ.succ.succ.succ I.succ.succ.succ.succ.succ mul.succ.succ.succ.succ.succ q.succ.succ.succ.succ.succ 4 3 2) (.imp (vertexFiber D.succ.succ.succ.succ.succ mul.succ.succ.succ.succ.succ objects.succ.succ.succ.succ.succ maps.succ.succ.succ.succ.succ 4 1) (.imp (vertexFiber D.succ.succ.succ.succ.succ mul.succ.succ.succ.succ.succ objects.succ.succ.succ.succ.succ maps.succ.succ.succ.succ.succ 3 0) (.existsE (arrowMap maps.succ.succ.succ.succ.succ.succ 5 4 2 1 0)))))))))) (.conj (.forallE (.forallE (.forallE (.imp (vertexFiber D.succ.succ.succ mul.succ.succ.succ objects.succ.succ.succ maps.succ.succ.succ 2 1) (.imp (arrowMap maps.succ.succ.succ 2 2 1 1 0) (ProjectSyntax.encode id (ForcingConditionGraphs.identityGraph 1 0))))))) (.forallE (.forallE (.forallE (.forallE (.forallE (.forallE (.forallE (.forallE (.forallE (.imp (vertexFiber D.succ.succ.succ.succ.succ.succ.succ.succ.succ mul.succ.succ.succ.succ.succ.succ.succ.succ.succ objects.succ.succ.succ.succ.succ.succ.succ.succ.succ maps.succ.succ.succ.succ.succ.succ.succ.succ.succ 8 5) (.imp (vertexFiber D.succ.succ.succ.succ.succ.succ.succ.succ.succ mul.succ.succ.succ.succ.succ.succ.succ.succ.succ objects.succ.succ.succ.succ.succ.succ.succ.succ.succ maps.succ.succ.succ.succ.succ.succ.succ.succ.succ 7 4) (.imp (vertexFiber D.succ.succ.succ.succ.succ.succ.succ.succ.succ mul.succ.succ.succ.succ.succ.succ.succ.succ.succ objects.succ.succ.succ.succ.succ.succ.succ.succ.succ maps.succ.succ.succ.succ.succ.succ.succ.succ.succ 6 3) (.imp (arrowMap maps.succ.succ.succ.succ.succ.succ.succ.succ.succ 8 7 5 4 2) (.imp (arrowMap maps.succ.succ.succ.succ.succ.succ.succ.succ.succ 7 6 4 3 1) (.imp (arrowMap maps.succ.succ.succ.succ.succ.succ.succ.succ.succ 8 6 5 3 0) (ProjectSyntax.encode id (ForcingConditionGraphs.compositionGraph 3 2 1 0)))))))))))))))))))

theorem coherent_freeClosed {m : Nat} (D I mul q objects maps : Fin m) :
    (coherent D I mul q objects maps).FreeClosed := by
  simp -implicitDefEqProofs [coherent,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
    vertexFiber_freeClosed,arrowMap_freeClosed,ConstructionComponentCofinal.encodedArrow_freeClosed]

theorem coherent_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (D I mul q objects maps : Fin m) :
    Project.Formula.satisfies env (coherent D I mul q objects maps) ↔
      Coherent (env.bound D) (env.bound I) (env.bound mul) (env.bound q) (env.bound objects) (env.bound maps) := by
  simp only [coherent,Coherent,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_imp_iff,
    Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,
    vertexFiber_semantics hM,arrowMap_semantics hM,ConstructionComponentCofinal.encodedArrow_semantics hM,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingConditionGraphs.identityGraph_semantics (M := M),ForcingConditionGraphs.compositionGraph_semantics (M := M)]
  rfl

/-- From the same actual System: one set of all vertices, one exact fiber
function on that set, and literal restriction maps with both coherence laws. -/
def constructionSentence {k : Nat} (D I mul e q diagrams objImage objects S mapImage maps : Fin k) : Project.Sentence where
  formula := Project.Formula.forallClosure k
    (.imp (ProjectSyntax.encode id (ForcingDiagramPoset.leftCancelMonoid D mul e))
    (.imp (ConstructionProbeSharedIntersections.conditionalJoins D mul)
    (.imp (ProjectSyntax.encode id (ForcingDiagramCarrier.carrier D I diagrams))
    (.imp (ProjectSyntax.encode id (Source.SetLanguage.mapsTo objects diagrams objImage))
    (.imp (ProjectSyntax.encode id (ForcingEligibleMapFamily.arrows D mul diagrams S))
    (.imp (ProjectSyntax.encode id (Source.SetLanguage.mapsTo maps S mapImage))
    (.imp (ForcingEligibleSystem.system D objects maps)
    (.existsE (.existsE (.existsE
      (.conj (ConstructionComponentCarrier.carrier D.succ.succ.succ I.succ.succ.succ mul.succ.succ.succ q.succ.succ.succ 2)
      (.conj (ProjectSyntax.encode id (Source.SetLanguage.mapsTo 0 2 1))
      (.conj (family D.succ.succ.succ mul.succ.succ.succ objects.succ.succ.succ maps.succ.succ.succ 2 0)
        (coherent D.succ.succ.succ I.succ.succ.succ mul.succ.succ.succ q.succ.succ.succ objects.succ.succ.succ maps.succ.succ.succ))))))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
      ConstructionProbeSharedIntersections.conditionalJoins_freeClosed,ForcingEligibleSystem.system_freeClosed,
      ConstructionComponentCarrier.carrier_freeClosed,family_freeClosed,coherent_freeClosed]

theorem construction_models {k : Nat} (D I mul e q diagrams objImage objects S mapImage maps : Fin k)
    (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence (constructionSentence D I mul e q diagrams objImage objects S mapImage maps)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM)
    (constructionSentence D I mul e q diagrams objImage objects S mapImage maps)]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_conj_iff,GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingDiagramPoset.leftCancelMonoid_semantics (M := M),ConstructionProbeSharedIntersections.conditionalJoins_semantics hM,
    ForcingDiagramCarrier.carrier_semantics (M := M),ForcingSupportSize.mapsTo_semantics (M := M),
    ForcingEligibleMapFamily.arrows_semantics (M := M),ForcingEligibleSystem.system_semantics hM,
    ConstructionComponentCarrier.carrier_semantics hM,family_semantics hM,coherent_semantics hM]
  intro hm hJ hDiagrams hObj hS hMaps hSys
  obtain ⟨vertices,hVertices⟩ := ConstructionComponentCarrier.exists_carrier hM (bound D) (bound I) (bound mul) (bound q)
  obtain ⟨image,fibers,hFibers,hFamily⟩ := exists_family hM hDiagrams hObj hVertices
  exact ⟨vertices,image,fibers,hVertices,hFibers,hFamily,
    coherent_of_system hM hm hJ hDiagrams hObj hS hMaps hSys⟩

theorem construction_kernel_certificate {k : Nat} (D I mul e q diagrams objImage objects S mapImage maps : Fin k) :
    FirstOrder.Derives nativeZF []
      (Project.fo_sentence (constructionSentence D I mul e q diagrams objImage objects S mapImage maps)) :=
  ModelTransfer.derives (fun _ hM => construction_models D I mul e q diagrams objImage objects S mapImage maps hM)

end PPAC.Migration.ForcingComponentFibers
