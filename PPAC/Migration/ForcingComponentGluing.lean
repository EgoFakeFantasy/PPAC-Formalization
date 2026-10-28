/- Pinned ComponentGluing.gluingSetoid/Glued/toGlued:349-400.
The quotient uses the actual Matches relation on the entire chosen component.
Only existing native Separation/functional image/set-function constructors are
used. Consumers: ConcreteSystem.gluedLabel_cardinal, QuotientTransport and
CodeLinks; no host Quotient replaces the internal construction. -/
import PPAC.Migration.ForcingComponentMatches

namespace PPAC.Migration.ForcingComponentGluing
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ForcingSupportSize (MapsTo Injection)
open ConstructionComponentCarrier (EncodedVertex)
open ConstructionComponentCofinal (EncodedArrow EncodedCommon)
open ForcingComponentFibers (VertexFiber ArrowMap Coherent)
open ForcingComponentMatches (Point Matches Related Laws)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

def ComponentPoint (D I mul q objects maps root p : M.Carrier .set) : Prop :=
  Point D I mul q objects maps p ∧ ∃ v x, PureKuratowski.Code M p v x ∧ EncodedCommon D I mul q root v

def Component (D I mul q objects maps root P : M.Carrier .set) : Prop := ∀ p,
  (Project.FirstOrderSemantics.reduct M).mem p P ↔ ComponentPoint D I mul q objects maps root p

def Class (D I mul q objects maps P p C : M.Carrier .set) : Prop := ∀ r,
  (Project.FirstOrderSemantics.reduct M).mem r C ↔
    (Project.FirstOrderSemantics.reduct M).mem r P ∧ Matches D I mul q objects maps p r

def Classes (D I mul q objects maps P Q : M.Carrier .set) : Prop := ∀ C,
  (Project.FirstOrderSemantics.reduct M).mem C Q ↔
    ∃ p, (Project.FirstOrderSemantics.reduct M).mem p P ∧ Class D I mul q objects maps P p C

def Projection (D I mul q objects maps P pr : M.Carrier .set) : Prop := ∀ p C,
  PureKuratowski.PairMember M p C pr ↔
    (Project.FirstOrderSemantics.reduct M).mem p P ∧ Class D I mul q objects maps P p C

theorem class_unique (hM : FirstOrder.Theory.Models M nativeZF)
    {D I mul q objects maps P p C E : M.Carrier .set}
    (hC : Class D I mul q objects maps P p C) (hE : Class D I mul q objects maps P p E) : C = E :=
  (ModelTransfer.extensionality hM).eq_of_same_members C E (fun r => (hC r).trans (hE r).symm)

theorem class_eq_iff (hM : FirstOrder.Theory.Models M nativeZF)
    {D I mul q objects maps root P p r C E : M.Carrier .set}
    (hL : Laws D I mul q objects maps) (hP : Component D I mul q objects maps root P)
    (hr : (Project.FirstOrderSemantics.reduct M).mem r P)
    (hC : Class D I mul q objects maps P p C) (hE : Class D I mul q objects maps P r E) :
    C = E ↔ Matches D I mul q objects maps p r := by
  constructor
  · intro he
    have hself := (hE r).mpr ⟨hr,hL.1 r ((hP r).mp hr).1⟩
    exact ((hC r).mp (he.symm ▸ hself)).2
  · intro h
    apply (ModelTransfer.extensionality hM).eq_of_same_members
    intro s
    rw [hC s,hE s]
    exact and_congr_right fun _ => ⟨
      fun hs => hL.2.2.1 r p s (hL.2.1 p r h) hs,
      fun hs => hL.2.2.1 p r s h hs⟩

theorem common_between (hM : FirstOrder.Theory.Models M nativeZF)
    {D I mul e q root v w : M.Carrier .set}
    (hm : ForcingDiagramPoset.LeftCancelMonoid D mul e)
    (hJ : ConstructionProbeSharedIntersections.ConditionalJoins D mul)
    (hv : EncodedCommon D I mul q root v) (hw : EncodedCommon D I mul q root w) :
    EncodedCommon D I mul q v w := by
  obtain ⟨r,a,U,s,b,V,hroot,hv,hr,hs,hvC⟩ := hv
  obtain ⟨r',a',U',t,c,W,hroot',hw,_,ht,hwC⟩ := hw
  obtain ⟨rfl,rfl,rfl⟩ := ConstructionComponentCarrier.code_injective hroot hroot'
  exact ⟨s,b,V,t,c,W,hv,hw,hs,ht,ConstructionComponentVertices.common_trans hM hm hJ hs hr ht
    (ConstructionComponentVertices.common_symm hvC) hwC⟩

def ToGlued (w X Q pr b : M.Carrier .set) : Prop := MapsTo X Q b ∧ ∀ x C,
  PureKuratowski.PairMember M x C b ↔ (Project.FirstOrderSemantics.reduct M).mem x X ∧
    ∃ p, PureKuratowski.Code M p w x ∧ PureKuratowski.PairMember M p C pr

def componentPoint {m : Nat} (D I mul q objects maps root p : Fin m) : Project.Formula 1 m :=
  (.conj (ForcingComponentMatches.point D I mul q objects maps p) (.existsE (.existsE (.conj (ProjectSyntax.encode id (PairSyntax.ordered p.succ.succ 1 0)) (ConstructionComponentCofinal.encodedCommon D.succ.succ I.succ.succ mul.succ.succ q.succ.succ root.succ.succ 1)))))

theorem componentPoint_freeClosed {m : Nat} (D I mul q objects maps root p : Fin m) :
    (componentPoint D I mul q objects maps root p).FreeClosed := by
  simp -implicitDefEqProofs [componentPoint,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,ForcingComponentMatches.point_freeClosed,ConstructionComponentCofinal.encodedCommon_freeClosed]

theorem componentPoint_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (D I mul q objects maps root p : Fin m) :
    Project.Formula.satisfies env (componentPoint D I mul q objects maps root p) ↔
      ComponentPoint (env.bound D) (env.bound I) (env.bound mul) (env.bound q) (env.bound objects) (env.bound maps) (env.bound root) (env.bound p) := by
  simp only [componentPoint,ComponentPoint,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_code,ForcingComponentMatches.point_semantics hM,ConstructionComponentCofinal.encodedCommon_semantics hM]
  rfl

def component {m : Nat} (D I mul q objects maps root P : Fin m) : Project.Formula 1 m :=
  (.forallE (.iff (.mem (.bound 0) (.bound P.succ)) (componentPoint D.succ I.succ mul.succ q.succ objects.succ maps.succ root.succ 0)))

theorem component_freeClosed {m : Nat} (D I mul q objects maps root P : Fin m) :
    (component D I mul q objects maps root P).FreeClosed := by
  simp -implicitDefEqProofs [component,Definitional.Formula.FreeClosed,componentPoint_freeClosed]

theorem component_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (D I mul q objects maps root P : Fin m) :
    Project.Formula.satisfies env (component D I mul q objects maps root P) ↔
      Component (env.bound D) (env.bound I) (env.bound mul) (env.bound q) (env.bound objects) (env.bound maps) (env.bound root) (env.bound P) := by
  simp only [component,Component,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_iff_iff,Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,componentPoint_semantics hM]
  rfl

def eqClass {m : Nat} (D I mul q objects maps P p C : Fin m) : Project.Formula 1 m :=
  (.forallE (.iff (.mem (.bound 0) (.bound C.succ)) (.conj (.mem (.bound 0) (.bound P.succ)) (ForcingComponentMatches.matching D.succ I.succ mul.succ q.succ objects.succ maps.succ p.succ 0))))

theorem eqClass_freeClosed {m : Nat} (D I mul q objects maps P p C : Fin m) :
    (eqClass D I mul q objects maps P p C).FreeClosed := by
  simp -implicitDefEqProofs [eqClass,Definitional.Formula.FreeClosed,ForcingComponentMatches.matching_freeClosed]

theorem eqClass_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (D I mul q objects maps P p C : Fin m) :
    Project.Formula.satisfies env (eqClass D I mul q objects maps P p C) ↔
      Class (env.bound D) (env.bound I) (env.bound mul) (env.bound q) (env.bound objects) (env.bound maps) (env.bound P) (env.bound p) (env.bound C) := by
  simp only [eqClass,Class,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_iff_iff,Project.Formula.satisfies_mem_iff,Project.Formula.satisfies_conj_iff,Project.Term.eval_bound,ForcingComponentMatches.matching_semantics hM]
  rfl

def classes {m : Nat} (D I mul q objects maps P Q : Fin m) : Project.Formula 1 m :=
  (.forallE (.iff (.mem (.bound 0) (.bound Q.succ)) (.existsE (.conj (.mem (.bound 0) (.bound P.succ.succ)) (eqClass D.succ.succ I.succ.succ mul.succ.succ q.succ.succ objects.succ.succ maps.succ.succ P.succ.succ 0 1)))))

theorem classes_freeClosed {m : Nat} (D I mul q objects maps P Q : Fin m) :
    (classes D I mul q objects maps P Q).FreeClosed := by
  simp -implicitDefEqProofs [classes,Definitional.Formula.FreeClosed,eqClass_freeClosed]

theorem classes_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (D I mul q objects maps P Q : Fin m) :
    Project.Formula.satisfies env (classes D I mul q objects maps P Q) ↔
      Classes (env.bound D) (env.bound I) (env.bound mul) (env.bound q) (env.bound objects) (env.bound maps) (env.bound P) (env.bound Q) := by
  simp only [classes,Classes,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_iff_iff,Project.Formula.satisfies_mem_iff,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,Project.Term.eval_bound,eqClass_semantics hM]
  rfl

def projection {m : Nat} (D I mul q objects maps P pr : Fin m) : Project.Formula 1 m :=
  (.forallE (.forallE (.iff (ProjectSyntax.encode id (Source.SetLanguage.edge pr.succ.succ 1 0)) (.conj (.mem (.bound 1) (.bound P.succ.succ)) (eqClass D.succ.succ I.succ.succ mul.succ.succ q.succ.succ objects.succ.succ maps.succ.succ P.succ.succ 1 0)))))

theorem projection_freeClosed {m : Nat} (D I mul q objects maps P pr : Fin m) :
    (projection D I mul q objects maps P pr).FreeClosed := by
  simp -implicitDefEqProofs [projection,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,eqClass_freeClosed]

theorem projection_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (D I mul q objects maps P pr : Fin m) :
    Project.Formula.satisfies env (projection D I mul q objects maps P pr) ↔
      Projection (env.bound D) (env.bound I) (env.bound mul) (env.bound q) (env.bound objects) (env.bound maps) (env.bound P) (env.bound pr) := by
  simp only [projection,Projection,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_iff_iff,Project.Formula.satisfies_mem_iff,Project.Formula.satisfies_conj_iff,Project.Term.eval_bound,GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,eqClass_semantics hM]
  rfl

def toGlued {m : Nat} (w X Q pr b : Fin m) : Project.Formula 1 m :=
  (.conj (ProjectSyntax.encode id (Source.SetLanguage.mapsTo b X Q)) (.forallE (.forallE (.iff (ProjectSyntax.encode id (Source.SetLanguage.edge b.succ.succ 1 0)) (.conj (.mem (.bound 1) (.bound X.succ.succ)) (.existsE (.conj (ProjectSyntax.encode id (PairSyntax.ordered 0 w.succ.succ.succ 2)) (ProjectSyntax.encode id (Source.SetLanguage.edge pr.succ.succ.succ 0 1)))))))))

theorem toGlued_freeClosed {m : Nat} (w X Q pr b : Fin m) :
    (toGlued w X Q pr b).FreeClosed := by
  simp -implicitDefEqProofs [toGlued,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed]

theorem toGlued_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w X Q pr b : Fin m) :
    Project.Formula.satisfies env (toGlued w X Q pr b) ↔
      ToGlued (env.bound w) (env.bound X) (env.bound Q) (env.bound pr) (env.bound b) := by
  simp only [toGlued,ToGlued,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_iff_iff,Project.Formula.satisfies_mem_iff,Project.Formula.satisfies_exists_iff,Project.Term.eval_bound,GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_code,KuratowskiZF.source_edge,ForcingSupportSize.mapsTo_semantics (M := M)]
  rfl

theorem exists_component (hM : FirstOrder.Theory.Models M nativeZF)
    {D I mul q objects maps root A : M.Carrier .set}
    (hA : ForcingComponentMatches.Carrier D I mul q objects maps A) :
    ∃ P, Component D I mul q objects maps root P := by
  let schema : Project.UnarySchema 7 := { body := componentPoint 1 2 3 4 5 6 7 0, freeClosed := componentPoint_freeClosed _ _ _ _ _ _ _ _ }
  let env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) 7 := {
    bound := Fin.cases D (Fin.cases I (Fin.cases mul (Fin.cases q (Fin.cases objects (Fin.cases maps (fun _ => root)))))), free := fun _ => A }
  have he p : schema.denote env p ↔ ComponentPoint D I mul q objects maps root p := componentPoint_semantics hM (env.push p) 1 2 3 4 5 6 7 0
  obtain ⟨P,hP⟩ := ZF.separation_exists_d (ModelTransfer.project_models_iff.mp hM) schema env A
  exact ⟨P,fun p => ⟨fun hp => (he p).mp ((hP p).mp hp).2,
    fun hp => (hP p).mpr ⟨(hA p).mpr hp.1,(he p).mpr hp⟩⟩⟩

theorem exists_class (hM : FirstOrder.Theory.Models M nativeZF)
    (D I mul q objects maps P p : M.Carrier .set) : ∃ C, Class D I mul q objects maps P p C := by
  let schema : Project.UnarySchema 7 := {
    body := ForcingComponentMatches.matching 1 2 3 4 5 6 7 0
    freeClosed := ForcingComponentMatches.matching_freeClosed _ _ _ _ _ _ _ _ }
  let env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) 7 := {
    bound := Fin.cases D (Fin.cases I (Fin.cases mul (Fin.cases q (Fin.cases objects (Fin.cases maps (fun _ => p)))))), free := fun _ => P }
  have he r : schema.denote env r ↔ Matches D I mul q objects maps p r := ForcingComponentMatches.matching_semantics hM (env.push r) 1 2 3 4 5 6 7 0
  obtain ⟨C,hC⟩ := ZF.separation_exists_d (ModelTransfer.project_models_iff.mp hM) schema env P
  exact ⟨C,fun r => (hC r).trans (and_congr Iff.rfl (he r))⟩

theorem exists_quotient (hM : FirstOrder.Theory.Models M nativeZF)
    (D I mul q objects maps P : M.Carrier .set) :
    ∃ Q pr, MapsTo P Q pr ∧ Classes D I mul q objects maps P Q ∧ Projection D I mul q objects maps P pr := by
  let schema : Project.BinarySchema 7 := { body := eqClass 2 3 4 5 6 7 8 1 0, freeClosed := eqClass_freeClosed _ _ _ _ _ _ _ _ _ }
  let env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) 7 := {
    bound := Fin.cases D (Fin.cases I (Fin.cases mul (Fin.cases q (Fin.cases objects (Fin.cases maps (fun _ => P)))))), free := fun _ => P }
  have he p C : schema.denote env p C ↔ Class D I mul q objects maps P p C := eqClass_semantics hM ((env.push p).push C) 2 3 4 5 6 7 8 1 0
  have ht : ∀ p, (Project.FirstOrderSemantics.reduct M).mem p P → ∃ C, schema.denote env p C := by
    intro p _
    obtain ⟨C,hC⟩ := exists_class hM D I mul q objects maps P p
    exact ⟨C,(he p C).mpr hC⟩
  have hu : ∀ p C E, schema.denote env p C → schema.denote env p E → C = E :=
    fun p C E hC hE => class_unique hM ((he p C).mp hC) ((he p E).mp hE)
  obtain ⟨Q,hQ⟩ := ZF.exists_functionalImage (ModelTransfer.project_models_iff.mp hM) schema env P ht hu
  obtain ⟨pr,hpr,hEdge⟩ := ZF.exists_setFunctionFromTo_of_denote (ModelTransfer.project_models_iff.mp hM)
    (KuratowskiZF.interpretation hM) schema env ht (fun p _ C E hC hE => hu p C E hC hE)
    (fun p C hp hC => (hQ C).mpr ⟨p,hp,hC⟩)
  refine ⟨Q,pr,(ForcingSupportSize.native_mapsTo hM P Q pr).mpr hpr,?_,?_⟩
  · intro C
    exact (hQ C).trans ⟨fun ⟨p,hp,hC⟩ => ⟨p,hp,(he p C).mp hC⟩,
      fun ⟨p,hp,hC⟩ => ⟨p,hp,(he p C).mpr hC⟩⟩
  · exact fun p C => (hEdge p C).trans (and_congr Iff.rfl (he p C))

theorem point_mem {D I mul q objects maps root P w X x p : M.Carrier .set}
    (hP : Component D I mul q objects maps root P) (hw : EncodedCommon D I mul q root w)
    (hX : VertexFiber D mul objects maps w X) (hx : (Project.FirstOrderSemantics.reduct M).mem x X)
    (hp : PureKuratowski.Code M p w x) : (Project.FirstOrderSemantics.reduct M).mem p P := by
  have hCommon := hw
  obtain ⟨r,a,U,s,b,V,_,hwCode,_,hwV,_⟩ := hw
  exact (hP p).mpr ⟨⟨w,X,x,hp,⟨s,b,V,hwCode,hwV⟩,hX,hx⟩,w,x,hp,hCommon⟩

theorem exists_toGlued (hM : FirstOrder.Theory.Models M nativeZF)
    {D I mul q objects maps root P Q pr w X : M.Carrier .set}
    (hP : Component D I mul q objects maps root P) (hpr : MapsTo P Q pr)
    (hw : EncodedCommon D I mul q root w) (hX : VertexFiber D mul objects maps w X) :
    ∃ b, ToGlued w X Q pr b := by
  let schema : Project.BinarySchema 2 := {
    body := .existsE (.conj (ProjectSyntax.encode id (PairSyntax.ordered 0 3 2))
      (ProjectSyntax.encode id (Source.SetLanguage.edge 4 0 1)))
    freeClosed := by simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed] }
  let env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) 2 := { bound := Fin.cases w (fun _ => pr), free := fun _ => P }
  have he x C : schema.denote env x C ↔ ∃ p, PureKuratowski.Code M p w x ∧ PureKuratowski.PairMember M p C pr := by
    simp only [schema,env,Project.BinarySchema.denote,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,
      GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_code,KuratowskiZF.source_edge]
    rfl
  have ht : ∀ x, (Project.FirstOrderSemantics.reduct M).mem x X → ∃ C, schema.denote env x C := by
    intro x hx
    obtain ⟨p,hp⟩ := KuratowskiZF.exists_code hM w x
    obtain ⟨C,hC,_⟩ := hpr.1.2 p (point_mem hP hw hX hx hp)
    exact ⟨C,(he x C).mpr ⟨p,hp,hC⟩⟩
  have hu : ∀ x C E, schema.denote env x C → schema.denote env x E → C = E := by
    intro x C E hC hE
    obtain ⟨p,hp,hC⟩ := (he x C).mp hC
    obtain ⟨r,hr,hE⟩ := (he x E).mp hE
    have e := KuratowskiZF.code_unique hM hp hr
    subst r
    exact ForcingConditionGraphs.function_unique hpr.1 hC hE
  obtain ⟨b,hb,hEdge⟩ := ZF.exists_setFunctionFromTo_of_denote (ModelTransfer.project_models_iff.mp hM)
    (KuratowskiZF.interpretation hM) schema env ht (fun x _ C E hC hE => hu x C E hC hE)
    (fun x C _ hC => by obtain ⟨p,_,hp⟩ := (he x C).mp hC; exact hpr.2 p C hp)
  exact ⟨b,(ForcingSupportSize.native_mapsTo hM X Q b).mpr hb,
    fun x C => (hEdge x C).trans (and_congr Iff.rfl (he x C))⟩

theorem toGlued_bijective (hM : FirstOrder.Theory.Models M nativeZF)
    {D I mul e q diagrams objImage objects S mapImage maps root P Q pr w X b : M.Carrier .set}
    (hm : ForcingDiagramPoset.LeftCancelMonoid D mul e)
    (hJ : ConstructionProbeSharedIntersections.ConditionalJoins D mul)
    (hDiagrams : ForcingDiagramCarrier.Carrier D I diagrams) (hObj : MapsTo diagrams objImage objects)
    (hS : ForcingEligibleMapFamily.Arrows D mul diagrams S) (hMaps : MapsTo S mapImage maps)
    (hSys : ForcingEligibleSystem.System D objects maps)
    (hP : Component D I mul q objects maps root P) (hpr : MapsTo P Q pr)
    (hQ : Classes D I mul q objects maps P Q) (hProjection : Projection D I mul q objects maps P pr)
    (hw : EncodedCommon D I mul q root w) (hX : VertexFiber D mul objects maps w X)
    (hb : ToGlued w X Q pr b) : Injection X Q b ∧
      ∀ C, (Project.FirstOrderSemantics.reduct M).mem C Q →
        ∃ x, (Project.FirstOrderSemantics.reduct M).mem x X ∧ PureKuratowski.PairMember M x C b := by
  have hL := ForcingComponentMatches.laws_of_system hM hm hJ hDiagrams hObj hS hMaps hSys (q := q)
  have hCoh := ForcingComponentFibers.coherent_of_system hM hm hJ hDiagrams hObj hS hMaps hSys (q := q)
  constructor
  · refine ⟨hb.1,?_⟩
    intro x y C hx hy
    obtain ⟨hx,p,hp,hpC⟩ := (hb.2 x C).mp hx
    obtain ⟨_,r,hr,hrC⟩ := (hb.2 y C).mp hy
    obtain ⟨_,hCp⟩ := (hProjection p C).mp hpC
    obtain ⟨hrP,hCr⟩ := (hProjection r C).mp hrC
    have hMatch := (class_eq_iff hM hL hP hrP hCp hCr).mp rfl
    obtain ⟨_,_,_,s,c,V,_,hwCode,_,hwV,_⟩ := hw
    exact (hL.2.2.2.1 w X x y p r ⟨s,c,V,hwCode,hwV⟩ hX hx hp hr).mp hMatch
  · intro C hCQ
    obtain ⟨p,hpP,hCp⟩ := (hQ C).mp hCQ
    obtain ⟨⟨v,Y,y,hp,hv,hY,hy⟩,v',y',hp',hRoot⟩ := (hP p).mp hpP
    obtain ⟨rfl,rfl⟩ := PureKuratowski.code_injective hp hp'
    obtain ⟨x,hx,hRelated⟩ := ForcingComponentMatches.related_onto_common hM hDiagrams hObj hCoh
      (common_between hM hm hJ hw hRoot) hX hY hy
    obtain ⟨r,hr⟩ := KuratowskiZF.exists_code hM w x
    have hrP := point_mem hP hw hX hx hr
    obtain ⟨E,hrE,_⟩ := hpr.1.2 r hrP
    have hEq : E = C := (class_eq_iff hM hL hP hpP ((hProjection r E).mp hrE).2 hCp).mpr
      ⟨w,X,x,v,Y,y,hr,hp,hX,hY,hRelated⟩
    subst E
    exact ⟨x,hx,(hb.2 x C).mpr ⟨hx,r,hr,hrE⟩⟩

theorem toGlued_arrow (hM : FirstOrder.Theory.Models M nativeZF)
    {D I mul e q diagrams objImage objects S mapImage maps root P Q pr v w X Y n b f g x y C E : M.Carrier .set}
    (hm : ForcingDiagramPoset.LeftCancelMonoid D mul e)
    (hJ : ConstructionProbeSharedIntersections.ConditionalJoins D mul)
    (hDiagrams : ForcingDiagramCarrier.Carrier D I diagrams) (hObj : MapsTo diagrams objImage objects)
    (hS : ForcingEligibleMapFamily.Arrows D mul diagrams S) (hMaps : MapsTo S mapImage maps)
    (hSys : ForcingEligibleSystem.System D objects maps)
    (hP : Component D I mul q objects maps root P) (hProjection : Projection D I mul q objects maps P pr)
    (hX : VertexFiber D mul objects maps v X) (hY : VertexFiber D mul objects maps w Y)
    (hArrow : EncodedArrow D I mul q v w n) (hb : ArrowMap maps v w X Y b)
    (hf : ToGlued v X Q pr f) (hg : ToGlued w Y Q pr g)
    (hyx : PureKuratowski.PairMember M y x b) (hxC : PureKuratowski.PairMember M x C f)
    (hyE : PureKuratowski.PairMember M y E g) : C = E := by
  have hL := ForcingComponentMatches.laws_of_system hM hm hJ hDiagrams hObj hS hMaps hSys (q := q)
  have hCoh := ForcingComponentFibers.coherent_of_system hM hm hJ hDiagrams hObj hS hMaps hSys (q := q)
  obtain ⟨_,p,hp,hpC⟩ := (hf.2 x C).mp hxC
  obtain ⟨hy,r,hr,hrE⟩ := (hg.2 y E).mp hyE
  have hid := ForcingComponentMatches.arrow_id hm (ForcingComponentMatches.arrow_target hArrow)
  obtain ⟨i,hi⟩ := hCoh.1 w w e Y Y hid hY hY
  have hiy := ((hCoh.2.1 w Y i hY hi) y y).mpr ⟨hy,rfl⟩
  have hRelated : Related D I mul q objects maps v X x w Y y :=
    ⟨w,Y,n,e,b,i,y,hArrow,hid,hY,hb,hi,hy,hyx,hiy⟩
  exact (class_eq_iff hM hL hP ((hProjection r E).mp hrE).1
    ((hProjection p C).mp hpC).2 ((hProjection r E).mp hrE).2).mpr
    ⟨v,X,x,w,Y,y,hp,hr,hX,hY,hRelated⟩

def AllFiberMaps (D I mul q objects maps root Q pr : M.Carrier .set) : Prop :=
  ∀ w X, EncodedCommon D I mul q root w → VertexFiber D mul objects maps w X →
    ∃ b, ToGlued w X Q pr b ∧ Injection X Q b ∧
      ∀ C, (Project.FirstOrderSemantics.reduct M).mem C Q →
        ∃ x, (Project.FirstOrderSemantics.reduct M).mem x X ∧ PureKuratowski.PairMember M x C b

def Commuting (D I mul q objects maps Q pr : M.Carrier .set) : Prop :=
  ∀ v w X Y n b f g x y C E,
    VertexFiber D mul objects maps v X → VertexFiber D mul objects maps w Y →
    EncodedArrow D I mul q v w n → ArrowMap maps v w X Y b →
    ToGlued v X Q pr f → ToGlued w Y Q pr g →
    PureKuratowski.PairMember M y x b → PureKuratowski.PairMember M x C f →
    PureKuratowski.PairMember M y E g → C = E

theorem gluing_laws (hM : FirstOrder.Theory.Models M nativeZF)
    {D I mul e q diagrams objImage objects S mapImage maps root P Q pr : M.Carrier .set}
    (hm : ForcingDiagramPoset.LeftCancelMonoid D mul e)
    (hJ : ConstructionProbeSharedIntersections.ConditionalJoins D mul)
    (hDiagrams : ForcingDiagramCarrier.Carrier D I diagrams) (hObj : MapsTo diagrams objImage objects)
    (hS : ForcingEligibleMapFamily.Arrows D mul diagrams S) (hMaps : MapsTo S mapImage maps)
    (hSys : ForcingEligibleSystem.System D objects maps)
    (hP : Component D I mul q objects maps root P) (hpr : MapsTo P Q pr)
    (hQ : Classes D I mul q objects maps P Q) (hProjection : Projection D I mul q objects maps P pr) :
    AllFiberMaps D I mul q objects maps root Q pr ∧ Commuting D I mul q objects maps Q pr := by
  constructor
  · intro w X hw hX
    obtain ⟨b,hb⟩ := exists_toGlued hM hP hpr hw hX
    exact ⟨b,hb,toGlued_bijective hM hm hJ hDiagrams hObj hS hMaps hSys hP hpr hQ hProjection hw hX hb⟩
  · intro v w X Y n b f g x y C E hX hY hArrow hb hf hg hyx hxC hyE
    exact toGlued_arrow hM hm hJ hDiagrams hObj hS hMaps hSys hP hProjection hX hY hArrow hb hf hg hyx hxC hyE

def allFiberMaps {m : Nat} (D I mul q objects maps root Q pr : Fin m) : Project.Formula 1 m :=
  (.forallE (.forallE (.imp (ConstructionComponentCofinal.encodedCommon D.succ.succ I.succ.succ mul.succ.succ q.succ.succ root.succ.succ 1) (.imp (ForcingComponentFibers.vertexFiber D.succ.succ mul.succ.succ objects.succ.succ maps.succ.succ 1 0) (.existsE (.conj (toGlued 2 1 Q.succ.succ.succ pr.succ.succ.succ 0) (.conj (ProjectSyntax.encode id (Source.SetLanguage.injection 0 1 Q.succ.succ.succ)) (.forallE (.imp (.mem (.bound 0) (.bound Q.succ.succ.succ.succ)) (.existsE (.conj (.mem (.bound 0) (.bound 3)) (ProjectSyntax.encode id (Source.SetLanguage.edge 2 0 1)))))))))))))

theorem allFiberMaps_freeClosed {m : Nat} (D I mul q objects maps root Q pr : Fin m) :
    (allFiberMaps D I mul q objects maps root Q pr).FreeClosed := by
  simp -implicitDefEqProofs [allFiberMaps,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
    ConstructionComponentCofinal.encodedCommon_freeClosed,ForcingComponentFibers.vertexFiber_freeClosed,toGlued_freeClosed]

theorem allFiberMaps_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (D I mul q objects maps root Q pr : Fin m) :
    Project.Formula.satisfies env (allFiberMaps D I mul q objects maps root Q pr) ↔
      AllFiberMaps (env.bound D) (env.bound I) (env.bound mul) (env.bound q) (env.bound objects) (env.bound maps) (env.bound root) (env.bound Q) (env.bound pr) := by
  simp only [allFiberMaps,AllFiberMaps,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_imp_iff,
    Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    ConstructionComponentCofinal.encodedCommon_semantics hM,ForcingComponentFibers.vertexFiber_semantics hM,toGlued_semantics hM,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),ForcingSupportSize.injection_semantics (M := M),KuratowskiZF.source_edge]
  rfl

def commuting {m : Nat} (D I mul q objects maps Q pr : Fin m) : Project.Formula 1 m :=
  (.forallE (.forallE (.forallE (.forallE (.forallE (.forallE (.forallE (.forallE (.forallE (.forallE (.forallE (.forallE (.imp (ForcingComponentFibers.vertexFiber D.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ mul.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ objects.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ maps.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ 11 9) (.imp (ForcingComponentFibers.vertexFiber D.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ mul.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ objects.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ maps.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ 10 8) (.imp (ConstructionComponentCofinal.encodedArrow D.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ I.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ mul.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ q.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ 11 10 7) (.imp (ForcingComponentFibers.arrowMap maps.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ 11 10 9 8 6) (.imp (toGlued 11 9 Q.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ pr.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ 5) (.imp (toGlued 10 8 Q.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ pr.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ 4) (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge 6 2 3)) (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge 5 3 1)) (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge 4 2 0)) (Project.Formula.extensionalEq (.bound 1) (.bound 0)))))))))))))))))))))))

theorem commuting_freeClosed {m : Nat} (D I mul q objects maps Q pr : Fin m) :
    (commuting D I mul q objects maps Q pr).FreeClosed := by
  simp -implicitDefEqProofs [commuting,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
    ConstructionComponentCofinal.encodedArrow_freeClosed,ForcingComponentFibers.vertexFiber_freeClosed,
    ForcingComponentFibers.arrowMap_freeClosed,toGlued_freeClosed]

theorem commuting_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (D I mul q objects maps Q pr : Fin m) :
    Project.Formula.satisfies env (commuting D I mul q objects maps Q pr) ↔
      Commuting (env.bound D) (env.bound I) (env.bound mul) (env.bound q) (env.bound objects) (env.bound maps) (env.bound Q) (env.bound pr) := by
  simp only [commuting,Commuting,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_imp_iff,
    Project.Formula.satisfies_extensionalEq_iff_eq (ModelTransfer.extensionality hM),Project.Term.eval_bound,
    ConstructionComponentCofinal.encodedArrow_semantics hM,ForcingComponentFibers.vertexFiber_semantics hM,
    ForcingComponentFibers.arrowMap_semantics hM,toGlued_semantics hM,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge]
  rfl

def constructionSentence {k : Nat} (D I mul e q diagrams objImage objects S mapImage maps root : Fin k) : Project.Sentence where
  formula := Project.Formula.forallClosure k (.imp (ProjectSyntax.encode id (ForcingDiagramPoset.leftCancelMonoid D mul e)) (.imp (ConstructionProbeSharedIntersections.conditionalJoins D mul) (.imp (ProjectSyntax.encode id (ForcingDiagramCarrier.carrier D I diagrams)) (.imp (ProjectSyntax.encode id (Source.SetLanguage.mapsTo objects diagrams objImage)) (.imp (ProjectSyntax.encode id (ForcingEligibleMapFamily.arrows D mul diagrams S)) (.imp (ProjectSyntax.encode id (Source.SetLanguage.mapsTo maps S mapImage)) (.imp (ForcingEligibleSystem.system D objects maps) (.existsE (.existsE (.existsE (.conj (component D.succ.succ.succ I.succ.succ.succ mul.succ.succ.succ q.succ.succ.succ objects.succ.succ.succ maps.succ.succ.succ root.succ.succ.succ 2) (.conj (ProjectSyntax.encode id (Source.SetLanguage.mapsTo 0 2 1)) (.conj (classes D.succ.succ.succ I.succ.succ.succ mul.succ.succ.succ q.succ.succ.succ objects.succ.succ.succ maps.succ.succ.succ 2 1) (.conj (projection D.succ.succ.succ I.succ.succ.succ mul.succ.succ.succ q.succ.succ.succ objects.succ.succ.succ maps.succ.succ.succ 2 0) (.conj (allFiberMaps D.succ.succ.succ I.succ.succ.succ mul.succ.succ.succ q.succ.succ.succ objects.succ.succ.succ maps.succ.succ.succ root.succ.succ.succ 1 0) (commuting D.succ.succ.succ I.succ.succ.succ mul.succ.succ.succ q.succ.succ.succ objects.succ.succ.succ maps.succ.succ.succ 1 0))))))))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
      ConstructionProbeSharedIntersections.conditionalJoins_freeClosed,ForcingEligibleSystem.system_freeClosed,
      component_freeClosed,classes_freeClosed,projection_freeClosed,allFiberMaps_freeClosed,commuting_freeClosed]

theorem construction_models {k : Nat} (D I mul e q diagrams objImage objects S mapImage maps root : Fin k)
    (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence (constructionSentence D I mul e q diagrams objImage objects S mapImage maps root)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM)
    (constructionSentence D I mul e q diagrams objImage objects S mapImage maps root)]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingDiagramPoset.leftCancelMonoid_semantics (M := M),ConstructionProbeSharedIntersections.conditionalJoins_semantics hM,
    ForcingDiagramCarrier.carrier_semantics (M := M),ForcingSupportSize.mapsTo_semantics (M := M),
    ForcingEligibleMapFamily.arrows_semantics (M := M),ForcingEligibleSystem.system_semantics hM,
    component_semantics hM,classes_semantics hM,projection_semantics hM,allFiberMaps_semantics hM,commuting_semantics hM]
  intro hm hJ hDiagrams hObj hS hMaps hSys
  obtain ⟨vertices,hVertices⟩ := ConstructionComponentCarrier.exists_carrier hM (bound D) (bound I) (bound mul) (bound q)
  obtain ⟨image,fibers,hFibers,hFamily⟩ := ForcingComponentFibers.exists_family hM hDiagrams hObj hVertices
  obtain ⟨A,hA⟩ := ForcingComponentMatches.exists_carrier hM hVertices hFibers hFamily
  obtain ⟨P,hP⟩ := exists_component hM hA (root := bound root)
  obtain ⟨Q,pr,hpr,hQ,hProjection⟩ := exists_quotient hM (bound D) (bound I) (bound mul) (bound q) (bound objects) (bound maps) P
  exact ⟨P,Q,pr,hP,hpr,hQ,hProjection,gluing_laws hM hm hJ hDiagrams hObj hS hMaps hSys hP hpr hQ hProjection⟩

theorem construction_kernel_certificate {k : Nat} (D I mul e q diagrams objImage objects S mapImage maps root : Fin k) :
    FirstOrder.Derives nativeZF []
      (Project.fo_sentence (constructionSentence D I mul e q diagrams objImage objects S mapImage maps root)) :=
  ModelTransfer.derives (fun _ hM => construction_models D I mul e q diagrams objImage objects S mapImage maps root hM)

end PPAC.Migration.ForcingComponentGluing
