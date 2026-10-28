/- Pinned ComponentGluing.Point/Matches/refl/symm/trans/same/common:301-347.
The comparison uses actual common contractions and the SAME literal restriction
maps. Consumer: gluingSetoid/Glued/toGlued; no independently chosen bijections. -/
import PPAC.Migration.ForcingComponentFibers

namespace PPAC.Migration.ForcingComponentMatches
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ForcingSupportSize (MapsTo Injection)
open ConstructionComponentCarrier (Code EncodedVertex)
open ConstructionComponentCofinal (EncodedArrow EncodedCommon)
open ForcingComponentFibers (VertexFiber ArrowMap Coherent)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
set_option maxHeartbeats 1600000
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

theorem arrow_target {D I mul q v w n : M.Carrier .set}
    (h : EncodedArrow D I mul q v w n) : EncodedVertex D I mul q w := by
  obtain ⟨r,a,U,s,b,V,_,hw,_,hs,_⟩ := h
  exact ⟨s,b,V,hw,hs⟩

theorem arrow_id {D I mul e q v : M.Carrier .set}
    (hm : ForcingDiagramPoset.LeftCancelMonoid D mul e) (hv : EncodedVertex D I mul q v) :
    EncodedArrow D I mul q v v e := by
  obtain ⟨r,a,U,hv,hr⟩ := hv
  exact ⟨r,a,U,r,a,U,hv,hv,hr,hr,ConstructionComponentVertices.identity hm hr⟩

theorem arrow_comp {D I mul e q v w t n m : M.Carrier .set}
    (hm : ForcingDiagramPoset.LeftCancelMonoid D mul e)
    (hf : EncodedArrow D I mul q v w n) (hg : EncodedArrow D I mul q w t m) :
    ∃ nm, EncodedArrow D I mul q v t nm := by
  obtain ⟨r,a,U,s,b,V,hv,hw,hr,hs,hf⟩ := hf
  obtain ⟨s',b',V',t,c,W,hw',ht,_,htV,hg⟩ := hg
  obtain ⟨rfl,rfl,rfl⟩ := ConstructionComponentCarrier.code_injective hw hw'
  obtain ⟨nm,_,hp⟩ := (hm.2.1 n (hr.2.2.1 n hf.1)).1 m (hs.2.2.1 m hg.1)
  exact ⟨nm,r,a,U,t,c,W,hv,ht,hr,htV,ConstructionComponentVertices.compose hm hr hs hf hg hp⟩

theorem arrow_directed (hM : FirstOrder.Theory.Models M nativeZF)
    {D I mul e q v w t n m : M.Carrier .set}
    (hm : ForcingDiagramPoset.LeftCancelMonoid D mul e)
    (hJ : ConstructionProbeSharedIntersections.ConditionalJoins D mul)
    (hf : EncodedArrow D I mul q v w n) (hg : EncodedArrow D I mul q v t m) :
    ∃ z i j, EncodedArrow D I mul q w z i ∧ EncodedArrow D I mul q t z j := by
  obtain ⟨r,a,U,s,b,V,hv,hw,hr,hs,hf⟩ := hf
  obtain ⟨r',a',U',t,c,W,hv',ht,_,htV,hg⟩ := hg
  obtain ⟨rfl,rfl,rfl⟩ := ConstructionComponentCarrier.code_injective hv hv'
  obtain ⟨z,d,Z,i,j,hz,hi,hj⟩ := ConstructionComponentVertices.successors_directed hM hm hJ hr hs htV hf hg
  obtain ⟨vZ,hCode⟩ := ConstructionComponentCarrier.code_total hM z d Z
  exact ⟨vZ,i,j,⟨s,b,V,z,d,Z,hw,hCode,hs,hz,hi⟩,⟨t,c,W,z,d,Z,ht,hCode,htV,hz,hj⟩⟩

theorem arrow_common {D I mul q v w t n m : M.Carrier .set}
    (hf : EncodedArrow D I mul q v t n) (hg : EncodedArrow D I mul q w t m) :
    EncodedCommon D I mul q v w := by
  obtain ⟨r,a,U,s,b,V,hv,ht,hr,hs,hf⟩ := hf
  obtain ⟨w,c,W,s',b',V',hw,ht',hwV,_,hg⟩ := hg
  obtain ⟨rfl,rfl,rfl⟩ := ConstructionComponentCarrier.code_injective ht ht'
  exact ⟨r,a,U,w,c,W,hv,hw,hr,hwV,s,b,V,n,m,hs,hf,hg⟩

theorem map_bijective {maps v w X Y b : M.Carrier .set}
    (h : ArrowMap maps v w X Y b) : Injection Y X b ∧
      ∀ x, (Project.FirstOrderSemantics.reduct M).mem x X →
        ∃ y, (Project.FirstOrderSemantics.reduct M).mem y Y ∧ PureKuratowski.PairMember M y x b := by
  obtain ⟨_,_,_,_,_,_,_,_,_,_,_,_,_,hb,hOnto⟩ := h
  exact ⟨hb,hOnto⟩

def Related (D I mul q objects maps v X x w Y y : M.Carrier .set) : Prop :=
  ∃ t Z n m b c z, EncodedArrow D I mul q v t n ∧ EncodedArrow D I mul q w t m ∧
    VertexFiber D mul objects maps t Z ∧ ArrowMap maps v t X Z b ∧ ArrowMap maps w t Y Z c ∧
    (Project.FirstOrderSemantics.reduct M).mem z Z ∧
    PureKuratowski.PairMember M z x b ∧ PureKuratowski.PairMember M z y c

theorem related_refl {D I mul e q objects maps v X x : M.Carrier .set}
    (hm : ForcingDiagramPoset.LeftCancelMonoid D mul e) (hC : Coherent D I mul q objects maps)
    (hv : EncodedVertex D I mul q v) (hX : VertexFiber D mul objects maps v X)
    (hx : (Project.FirstOrderSemantics.reduct M).mem x X) : Related D I mul q objects maps v X x v X x := by
  have hid := arrow_id hm hv
  obtain ⟨b,hb⟩ := hC.1 v v e X X hid hX hX
  have he := ((hC.2.1 v X b hX hb) x x).mpr ⟨hx,rfl⟩
  exact ⟨v,X,e,e,b,b,x,hid,hid,hX,hb,hb,hx,he,he⟩

theorem related_symm {D I mul q objects maps v X x w Y y : M.Carrier .set}
    (h : Related D I mul q objects maps v X x w Y y) : Related D I mul q objects maps w Y y v X x := by
  obtain ⟨t,Z,n,m,b,c,z,hn,hm,hZ,hb,hc,hz,hx,hy⟩ := h
  exact ⟨t,Z,m,n,c,b,z,hm,hn,hZ,hc,hb,hz,hy,hx⟩

theorem related_trans (hM : FirstOrder.Theory.Models M nativeZF)
    {D I mul e q diagrams objImage objects S mapImage maps v X x w Y y t Z z : M.Carrier .set}
    (hm : ForcingDiagramPoset.LeftCancelMonoid D mul e)
    (hJ : ConstructionProbeSharedIntersections.ConditionalJoins D mul)
    (hDiagrams : ForcingDiagramCarrier.Carrier D I diagrams) (hObj : MapsTo diagrams objImage objects)
    (hMaps : MapsTo S mapImage maps) (hC : Coherent D I mul q objects maps)
    (hX : VertexFiber D mul objects maps v X) (hY : VertexFiber D mul objects maps w Y)
    (hZ : VertexFiber D mul objects maps t Z)
    (hxy : Related D I mul q objects maps v X x w Y y)
    (hyz : Related D I mul q objects maps w Y y t Z z) : Related D I mul q objects maps v X x t Z z := by
  obtain ⟨a,A,n,m,f,g,xa,hva,hwa,hA,hf,hg,hxa,hfx,hgy⟩ := hxy
  obtain ⟨b,B,i,j,h,k,xb,hwb,htb,hB,hh,hk,hxb,hhy,hkz⟩ := hyz
  obtain ⟨c,l,o,hac,hbc⟩ := arrow_directed hM hm hJ hwa hwb
  obtain ⟨C,hCfiber⟩ := ForcingComponentFibers.exists_vertexFiber hM hDiagrams hObj (arrow_target hac)
  obtain ⟨lf,hlf⟩ := hC.1 a c l A C hac hA hCfiber
  obtain ⟨of,hoff⟩ := hC.1 b c o B C hbc hB hCfiber
  obtain ⟨xc,hxc,hlxa⟩ := (map_bijective hlf).2 xa hxa
  obtain ⟨gl,hgl⟩ := arrow_comp hm hwa hac
  obtain ⟨ho,hho⟩ := arrow_comp hm hwb hbc
  obtain ⟨gf,hgf⟩ := hC.1 w c gl Y C hgl hY hCfiber
  obtain ⟨hf,hhf⟩ := hC.1 w c ho Y C hho hY hCfiber
  have eqmaps := ForcingComponentFibers.arrowMap_unique hM hMaps hgf hhf
  subst hf
  have hgy' := ((hC.2.2 w a c Y A C g lf gf hY hA hCfiber hg hlf hgf) xc y).mpr
    ⟨hxc,xa,hlxa,hgy⟩
  obtain ⟨_,xb',hox,hhy'⟩ := ((hC.2.2 w b c Y B C h of gf hY hB hCfiber hh hoff hhf) xc y).mp hgy'
  have he := (map_bijective hh).1.2 xb' xb y hhy' hhy
  subst xb'
  obtain ⟨fl,hfl⟩ := arrow_comp hm hva hac
  obtain ⟨ko,hko⟩ := arrow_comp hm htb hbc
  obtain ⟨ff,hff⟩ := hC.1 v c fl X C hfl hX hCfiber
  obtain ⟨kf,hkf⟩ := hC.1 t c ko Z C hko hZ hCfiber
  exact ⟨c,C,fl,ko,ff,kf,xc,hfl,hko,hCfiber,hff,hkf,hxc,
    ((hC.2.2 v a c X A C f lf ff hX hA hCfiber hf hlf hff) xc x).mpr ⟨hxc,xa,hlxa,hfx⟩,
    ((hC.2.2 t b c Z B C k of kf hZ hB hCfiber hk hoff hkf) xc z).mpr ⟨hxc,xb,hox,hkz⟩⟩

theorem related_same (hM : FirstOrder.Theory.Models M nativeZF)
    {D I mul e q objects maps S mapImage v X x y : M.Carrier .set}
    (hm : ForcingDiagramPoset.LeftCancelMonoid D mul e) (hMaps : MapsTo S mapImage maps)
    (hC : Coherent D I mul q objects maps) (hv : EncodedVertex D I mul q v)
    (hX : VertexFiber D mul objects maps v X) (hx : (Project.FirstOrderSemantics.reduct M).mem x X) :
    Related D I mul q objects maps v X x v X y ↔ x = y := by
  constructor
  · rintro ⟨t,Z,n,m,b,c,z,_,_,_,hb,hc,_,hx,hy⟩
    have he := ForcingComponentFibers.arrowMap_unique hM hMaps hb hc
    subst c
    exact ForcingConditionGraphs.function_unique (map_bijective hb).1.1.1 hx hy
  · rintro rfl
    exact related_refl hm hC hv hX hx

theorem related_common {D I mul q objects maps v X x w Y y : M.Carrier .set}
    (h : Related D I mul q objects maps v X x w Y y) : EncodedCommon D I mul q v w := by
  obtain ⟨_,_,_,_,_,_,_,hf,hg,_⟩ := h
  exact arrow_common hf hg

/-- An actual point of the disjoint union, encoded by the existing Kuratowski pair. -/
def Point (D I mul q objects maps p : M.Carrier .set) : Prop :=
  ∃ v X x, PureKuratowski.Code M p v x ∧ EncodedVertex D I mul q v ∧
    VertexFiber D mul objects maps v X ∧ (Project.FirstOrderSemantics.reduct M).mem x X

def Matches (D I mul q objects maps p r : M.Carrier .set) : Prop :=
  ∃ v X x w Y y, PureKuratowski.Code M p v x ∧ PureKuratowski.Code M r w y ∧
    VertexFiber D mul objects maps v X ∧ VertexFiber D mul objects maps w Y ∧
    Related D I mul q objects maps v X x w Y y

theorem matches_refl {D I mul e q objects maps p : M.Carrier .set}
    (hm : ForcingDiagramPoset.LeftCancelMonoid D mul e) (hC : Coherent D I mul q objects maps)
    (hp : Point D I mul q objects maps p) : Matches D I mul q objects maps p p := by
  obtain ⟨v,X,x,hp,hv,hX,hx⟩ := hp
  exact ⟨v,X,x,v,X,x,hp,hp,hX,hX,related_refl hm hC hv hX hx⟩

theorem matches_symm {D I mul q objects maps p r : M.Carrier .set}
    (h : Matches D I mul q objects maps p r) : Matches D I mul q objects maps r p := by
  obtain ⟨v,X,x,w,Y,y,hp,hr,hX,hY,h⟩ := h
  exact ⟨w,Y,y,v,X,x,hr,hp,hY,hX,related_symm h⟩

theorem matches_trans (hM : FirstOrder.Theory.Models M nativeZF)
    {D I mul e q diagrams objImage objects S mapImage maps p r s : M.Carrier .set}
    (hm : ForcingDiagramPoset.LeftCancelMonoid D mul e)
    (hJ : ConstructionProbeSharedIntersections.ConditionalJoins D mul)
    (hDiagrams : ForcingDiagramCarrier.Carrier D I diagrams) (hObj : MapsTo diagrams objImage objects)
    (hMaps : MapsTo S mapImage maps) (hC : Coherent D I mul q objects maps)
    (hpr : Matches D I mul q objects maps p r) (hrs : Matches D I mul q objects maps r s) :
    Matches D I mul q objects maps p s := by
  obtain ⟨v,X,x,w,Y,y,hp,hr,hX,hY,hpr⟩ := hpr
  obtain ⟨w',Y',y',t,Z,z,hr',hs,hY',hZ,hrs⟩ := hrs
  obtain ⟨rfl,rfl⟩ := PureKuratowski.code_injective hr hr'
  have he := ForcingComponentFibers.vertexFiber_unique hM hObj hY hY'
  subst Y'
  exact ⟨v,X,x,t,Z,z,hp,hs,hX,hZ,related_trans hM hm hJ hDiagrams hObj hMaps hC hX hY hZ hpr hrs⟩

theorem matches_same (hM : FirstOrder.Theory.Models M nativeZF)
    {D I mul e q diagrams objImage objects maps S mapImage v X x y p r : M.Carrier .set}
    (hm : ForcingDiagramPoset.LeftCancelMonoid D mul e) (hObj : MapsTo diagrams objImage objects)
    (hMaps : MapsTo S mapImage maps) (hC : Coherent D I mul q objects maps)
    (hv : EncodedVertex D I mul q v) (hX : VertexFiber D mul objects maps v X)
    (hx : (Project.FirstOrderSemantics.reduct M).mem x X)
    (hp : PureKuratowski.Code M p v x) (hr : PureKuratowski.Code M r v y) :
    Matches D I mul q objects maps p r ↔ x = y := by
  constructor
  · rintro ⟨v',X',x',w',Y',y',hp',hr',hX',hY',hR⟩
    obtain ⟨rfl,rfl⟩ := PureKuratowski.code_injective hp hp'
    obtain ⟨rfl,rfl⟩ := PureKuratowski.code_injective hr hr'
    have eX := ForcingComponentFibers.vertexFiber_unique hM hObj hX hX'
    have eY := ForcingComponentFibers.vertexFiber_unique hM hObj hX hY'
    subst X'; subst Y'
    exact (related_same hM hm hMaps hC hv hX hx).mp hR
  · rintro rfl
    have he := KuratowskiZF.code_unique hM hp hr
    subst r
    exact matches_refl hm hC ⟨v,X,x,hp,hv,hX,hx⟩

theorem matches_common {D I mul q objects maps p r v x w y : M.Carrier .set}
    (hp : PureKuratowski.Code M p v x) (hr : PureKuratowski.Code M r w y)
    (h : Matches D I mul q objects maps p r) : EncodedCommon D I mul q v w := by
  obtain ⟨v',X,x',w',Y,y',hp',hr',_,_,h⟩ := h
  obtain ⟨rfl,rfl⟩ := PureKuratowski.code_injective hp hp'
  obtain ⟨rfl,rfl⟩ := PureKuratowski.code_injective hr hr'
  exact related_common h

/-- The source surjectivity argument at a specified fiber of the same component. -/
theorem related_onto_common (hM : FirstOrder.Theory.Models M nativeZF)
    {D I mul q diagrams objImage objects maps v X w Y y : M.Carrier .set}
    (hDiagrams : ForcingDiagramCarrier.Carrier D I diagrams) (hObj : MapsTo diagrams objImage objects)
    (hC : Coherent D I mul q objects maps) (hCommon : EncodedCommon D I mul q v w)
    (hX : VertexFiber D mul objects maps v X) (hY : VertexFiber D mul objects maps w Y)
    (hy : (Project.FirstOrderSemantics.reduct M).mem y Y) :
    ∃ x, (Project.FirstOrderSemantics.reduct M).mem x X ∧ Related D I mul q objects maps v X x w Y y := by
  obtain ⟨r,a,U,s,b,V,hv,hw,hr,hs,t,c,W,n,m,ht,hn,hm⟩ := hCommon
  obtain ⟨z,hz⟩ := ConstructionComponentCarrier.code_total hM t c W
  have hZvertex : EncodedVertex D I mul q z := ⟨t,c,W,hz,ht⟩
  obtain ⟨Z,hZ⟩ := ForcingComponentFibers.exists_vertexFiber hM hDiagrams hObj hZvertex
  have hA : EncodedArrow D I mul q v z n := ⟨r,a,U,t,c,W,hv,hz,hr,ht,hn⟩
  have hB : EncodedArrow D I mul q w z m := ⟨s,b,V,t,c,W,hw,hz,hs,ht,hm⟩
  obtain ⟨f,hf⟩ := hC.1 v z n X Z hA hX hZ
  obtain ⟨g,hg⟩ := hC.1 w z m Y Z hB hY hZ
  obtain ⟨zv,hzv,hzy⟩ := (map_bijective hg).2 y hy
  obtain ⟨x,hzx,_⟩ := (map_bijective hf).1.1.1.2 zv hzv
  exact ⟨x,(map_bijective hf).1.1.2 zv x hzx,z,Z,n,m,f,g,zv,hA,hB,hZ,hf,hg,hzv,hzx,hzy⟩

def related {m : Nat} (D I mul q objects maps v X x w Y y : Fin m) : Project.Formula 1 m :=
  (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.conj (ConstructionComponentCofinal.encodedArrow D.succ.succ.succ.succ.succ.succ.succ I.succ.succ.succ.succ.succ.succ.succ mul.succ.succ.succ.succ.succ.succ.succ q.succ.succ.succ.succ.succ.succ.succ v.succ.succ.succ.succ.succ.succ.succ 6 4) (.conj (ConstructionComponentCofinal.encodedArrow D.succ.succ.succ.succ.succ.succ.succ I.succ.succ.succ.succ.succ.succ.succ mul.succ.succ.succ.succ.succ.succ.succ q.succ.succ.succ.succ.succ.succ.succ w.succ.succ.succ.succ.succ.succ.succ 6 3) (.conj (ForcingComponentFibers.vertexFiber D.succ.succ.succ.succ.succ.succ.succ mul.succ.succ.succ.succ.succ.succ.succ objects.succ.succ.succ.succ.succ.succ.succ maps.succ.succ.succ.succ.succ.succ.succ 6 5) (.conj (ForcingComponentFibers.arrowMap maps.succ.succ.succ.succ.succ.succ.succ v.succ.succ.succ.succ.succ.succ.succ 6 X.succ.succ.succ.succ.succ.succ.succ 5 2) (.conj (ForcingComponentFibers.arrowMap maps.succ.succ.succ.succ.succ.succ.succ w.succ.succ.succ.succ.succ.succ.succ 6 Y.succ.succ.succ.succ.succ.succ.succ 5 1) (.conj (.mem (.bound 0) (.bound 5)) (.conj (ProjectSyntax.encode id (Source.SetLanguage.edge 2 0 x.succ.succ.succ.succ.succ.succ.succ)) (ProjectSyntax.encode id (Source.SetLanguage.edge 1 0 y.succ.succ.succ.succ.succ.succ.succ))))))))))))))))

theorem related_freeClosed {m : Nat} (D I mul q objects maps v X x w Y y : Fin m) :
    (related D I mul q objects maps v X x w Y y).FreeClosed := by
  simp -implicitDefEqProofs [related,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,ConstructionComponentCofinal.encodedArrow_freeClosed, ForcingComponentFibers.vertexFiber_freeClosed, ForcingComponentFibers.arrowMap_freeClosed]

theorem related_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (D I mul q objects maps v X x w Y y : Fin m) :
    Project.Formula.satisfies env (related D I mul q objects maps v X x w Y y) ↔
      Related (env.bound D) (env.bound I) (env.bound mul) (env.bound q) (env.bound objects) (env.bound maps) (env.bound v) (env.bound X) (env.bound x) (env.bound w) (env.bound Y) (env.bound y) := by
  simp only [related,Related,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,
    ConstructionComponentCofinal.encodedArrow_semantics hM, ForcingComponentFibers.vertexFiber_semantics hM, ForcingComponentFibers.arrowMap_semantics hM]
  rfl

def point {m : Nat} (D I mul q objects maps p : Fin m) : Project.Formula 1 m :=
  (.existsE (.existsE (.existsE (.conj (ProjectSyntax.encode id (PairSyntax.ordered p.succ.succ.succ 2 0)) (.conj (ConstructionComponentCarrier.encodedVertex D.succ.succ.succ I.succ.succ.succ mul.succ.succ.succ q.succ.succ.succ 2) (.conj (ForcingComponentFibers.vertexFiber D.succ.succ.succ mul.succ.succ.succ objects.succ.succ.succ maps.succ.succ.succ 2 1) (.mem (.bound 0) (.bound 1))))))))

theorem point_freeClosed {m : Nat} (D I mul q objects maps p : Fin m) :
    (point D I mul q objects maps p).FreeClosed := by
  simp -implicitDefEqProofs [point,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,ConstructionComponentCarrier.encodedVertex_freeClosed, ForcingComponentFibers.vertexFiber_freeClosed]

theorem point_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (D I mul q objects maps p : Fin m) :
    Project.Formula.satisfies env (point D I mul q objects maps p) ↔
      Point (env.bound D) (env.bound I) (env.bound mul) (env.bound q) (env.bound objects) (env.bound maps) (env.bound p) := by
  simp only [point,Point,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_code,
    ConstructionComponentCarrier.encodedVertex_semantics hM, ForcingComponentFibers.vertexFiber_semantics hM]
  rfl

def matching {m : Nat} (D I mul q objects maps p r : Fin m) : Project.Formula 1 m :=
  (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.conj (ProjectSyntax.encode id (PairSyntax.ordered p.succ.succ.succ.succ.succ.succ 5 3)) (.conj (ProjectSyntax.encode id (PairSyntax.ordered r.succ.succ.succ.succ.succ.succ 2 0)) (.conj (ForcingComponentFibers.vertexFiber D.succ.succ.succ.succ.succ.succ mul.succ.succ.succ.succ.succ.succ objects.succ.succ.succ.succ.succ.succ maps.succ.succ.succ.succ.succ.succ 5 4) (.conj (ForcingComponentFibers.vertexFiber D.succ.succ.succ.succ.succ.succ mul.succ.succ.succ.succ.succ.succ objects.succ.succ.succ.succ.succ.succ maps.succ.succ.succ.succ.succ.succ 2 1) (related D.succ.succ.succ.succ.succ.succ I.succ.succ.succ.succ.succ.succ mul.succ.succ.succ.succ.succ.succ q.succ.succ.succ.succ.succ.succ objects.succ.succ.succ.succ.succ.succ maps.succ.succ.succ.succ.succ.succ 5 4 3 2 1 0)))))))))))

theorem matching_freeClosed {m : Nat} (D I mul q objects maps p r : Fin m) :
    (matching D I mul q objects maps p r).FreeClosed := by
  simp -implicitDefEqProofs [matching,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,ForcingComponentFibers.vertexFiber_freeClosed, related_freeClosed]

theorem matching_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (D I mul q objects maps p r : Fin m) :
    Project.Formula.satisfies env (matching D I mul q objects maps p r) ↔
      Matches (env.bound D) (env.bound I) (env.bound mul) (env.bound q) (env.bound objects) (env.bound maps) (env.bound p) (env.bound r) := by
  simp only [matching,Matches,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_code,
    ForcingComponentFibers.vertexFiber_semantics hM, related_semantics hM]
  rfl

def Carrier (D I mul q objects maps P : M.Carrier .set) : Prop := ∀ p,
  (Project.FirstOrderSemantics.reduct M).mem p P ↔ Point D I mul q objects maps p

def carrier {m : Nat} (D I mul q objects maps P : Fin m) : Project.Formula 1 m :=
  .forallE (.iff (.mem (.bound 0) (.bound P.succ)) (point D.succ I.succ mul.succ q.succ objects.succ maps.succ 0))

theorem carrier_freeClosed {m : Nat} (D I mul q objects maps P : Fin m) :
    (carrier D I mul q objects maps P).FreeClosed := by
  simp -implicitDefEqProofs [carrier,Definitional.Formula.FreeClosed,point_freeClosed]

theorem carrier_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (D I mul q objects maps P : Fin m) :
    Project.Formula.satisfies env (carrier D I mul q objects maps P) ↔
      Carrier (env.bound D) (env.bound I) (env.bound mul) (env.bound q) (env.bound objects) (env.bound maps) (env.bound P) := by
  simp only [carrier,Carrier,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_iff_iff,
    Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,point_semantics hM]
  rfl

theorem exists_carrier (hM : FirstOrder.Theory.Models M nativeZF)
    {D I mul q objects maps vertices image fibers : M.Carrier .set}
    (hVertices : ConstructionComponentCarrier.Carrier D I mul q vertices)
    (hFibers : MapsTo vertices image fibers) (hFamily : ForcingComponentFibers.Family D mul objects maps vertices fibers) :
    ∃ P, Carrier D I mul q objects maps P := by
  have hZF := ModelTransfer.project_models_iff.mp hM
  obtain ⟨U,hU⟩ := KP.exists_union (ZF.modelsKP hZF) image
  obtain ⟨A,hA⟩ := ZF.exists_cartesianProduct hZF (KuratowskiZF.interpretation hM) vertices U
  let schema : Project.UnarySchema 6 := { body := point 1 2 3 4 5 6 0, freeClosed := point_freeClosed _ _ _ _ _ _ _ }
  let env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) 6 := {
    bound := Fin.cases D (Fin.cases I (Fin.cases mul (Fin.cases q (Fin.cases objects (fun _ => maps))))), free := fun _ => vertices }
  have he p : schema.denote env p ↔ Point D I mul q objects maps p := point_semantics hM (env.push p) 1 2 3 4 5 6 0
  have bound p (hp : Point D I mul q objects maps p) : (Project.FirstOrderSemantics.reduct M).mem p A := by
    obtain ⟨v,X,x,hp,hv,hX,hx⟩ := hp
    have hvV := (hVertices v).mpr hv
    have hf := (hFamily v X).mpr ⟨hvV,hX⟩
    have hXI := hFibers.2 v X hf
    exact (hA p).mpr ⟨v,hvV,x,(hU x).mpr ⟨X,hXI,hx⟩,hp⟩
  obtain ⟨P,hP⟩ := ZF.separation_exists_d hZF schema env A
  exact ⟨P,fun p => ⟨fun hp => (he p).mp ((hP p).mp hp).2,
    fun hp => (hP p).mpr ⟨bound p hp,(he p).mpr hp⟩⟩⟩

def Laws (D I mul q objects maps : M.Carrier .set) : Prop :=
  (∀ p, Point D I mul q objects maps p → Matches D I mul q objects maps p p) ∧
  (∀ p r, Matches D I mul q objects maps p r → Matches D I mul q objects maps r p) ∧
  (∀ p r s, Matches D I mul q objects maps p r → Matches D I mul q objects maps r s → Matches D I mul q objects maps p s) ∧
  (∀ v X x y p r, EncodedVertex D I mul q v → VertexFiber D mul objects maps v X →
    (Project.FirstOrderSemantics.reduct M).mem x X → PureKuratowski.Code M p v x → PureKuratowski.Code M r v y →
    (Matches D I mul q objects maps p r ↔ x = y)) ∧
  (∀ p r v x w y, PureKuratowski.Code M p v x → PureKuratowski.Code M r w y →
    Matches D I mul q objects maps p r → EncodedCommon D I mul q v w)

theorem laws_of_system (hM : FirstOrder.Theory.Models M nativeZF)
    {D I mul e q diagrams objImage objects S mapImage maps : M.Carrier .set}
    (hm : ForcingDiagramPoset.LeftCancelMonoid D mul e)
    (hJ : ConstructionProbeSharedIntersections.ConditionalJoins D mul)
    (hDiagrams : ForcingDiagramCarrier.Carrier D I diagrams) (hObj : MapsTo diagrams objImage objects)
    (hS : ForcingEligibleMapFamily.Arrows D mul diagrams S) (hMaps : MapsTo S mapImage maps)
    (hSys : ForcingEligibleSystem.System D objects maps) : Laws D I mul q objects maps := by
  have hC := ForcingComponentFibers.coherent_of_system hM hm hJ hDiagrams hObj hS hMaps hSys (q := q)
  exact ⟨fun _ hp => matches_refl hm hC hp,fun _ _ h => matches_symm h,
    fun _ _ _ h1 h2 => matches_trans hM hm hJ hDiagrams hObj hMaps hC h1 h2,
    fun _ _ _ _ _ _ hv hX hx hp hr => matches_same hM hm hObj hMaps hC hv hX hx hp hr,
    fun _ _ _ _ _ _ hp hr h => matches_common hp hr h⟩

def laws {m : Nat} (D I mul q objects maps : Fin m) : Project.Formula 1 m :=
  (.conj (.forallE (.imp (point D.succ I.succ mul.succ q.succ objects.succ maps.succ 0) (matching D.succ I.succ mul.succ q.succ objects.succ maps.succ 0 0))) (.conj (.forallE (.forallE (.imp (matching D.succ.succ I.succ.succ mul.succ.succ q.succ.succ objects.succ.succ maps.succ.succ 1 0) (matching D.succ.succ I.succ.succ mul.succ.succ q.succ.succ objects.succ.succ maps.succ.succ 0 1)))) (.conj (.forallE (.forallE (.forallE (.imp (matching D.succ.succ.succ I.succ.succ.succ mul.succ.succ.succ q.succ.succ.succ objects.succ.succ.succ maps.succ.succ.succ 2 1) (.imp (matching D.succ.succ.succ I.succ.succ.succ mul.succ.succ.succ q.succ.succ.succ objects.succ.succ.succ maps.succ.succ.succ 1 0) (matching D.succ.succ.succ I.succ.succ.succ mul.succ.succ.succ q.succ.succ.succ objects.succ.succ.succ maps.succ.succ.succ 2 0)))))) (.conj (.forallE (.forallE (.forallE (.forallE (.forallE (.forallE (.imp (ConstructionComponentCarrier.encodedVertex D.succ.succ.succ.succ.succ.succ I.succ.succ.succ.succ.succ.succ mul.succ.succ.succ.succ.succ.succ q.succ.succ.succ.succ.succ.succ 5) (.imp (ForcingComponentFibers.vertexFiber D.succ.succ.succ.succ.succ.succ mul.succ.succ.succ.succ.succ.succ objects.succ.succ.succ.succ.succ.succ maps.succ.succ.succ.succ.succ.succ 5 4) (.imp (.mem (.bound 3) (.bound 4)) (.imp (ProjectSyntax.encode id (PairSyntax.ordered 1 5 3)) (.imp (ProjectSyntax.encode id (PairSyntax.ordered 0 5 2)) (.iff (matching D.succ.succ.succ.succ.succ.succ I.succ.succ.succ.succ.succ.succ mul.succ.succ.succ.succ.succ.succ q.succ.succ.succ.succ.succ.succ objects.succ.succ.succ.succ.succ.succ maps.succ.succ.succ.succ.succ.succ 1 0) (Project.Formula.extensionalEq (.bound 3) (.bound 2)))))))))))))) (.forallE (.forallE (.forallE (.forallE (.forallE (.forallE (.imp (ProjectSyntax.encode id (PairSyntax.ordered 5 3 2)) (.imp (ProjectSyntax.encode id (PairSyntax.ordered 4 1 0)) (.imp (matching D.succ.succ.succ.succ.succ.succ I.succ.succ.succ.succ.succ.succ mul.succ.succ.succ.succ.succ.succ q.succ.succ.succ.succ.succ.succ objects.succ.succ.succ.succ.succ.succ maps.succ.succ.succ.succ.succ.succ 5 4) (ConstructionComponentCofinal.encodedCommon D.succ.succ.succ.succ.succ.succ I.succ.succ.succ.succ.succ.succ mul.succ.succ.succ.succ.succ.succ q.succ.succ.succ.succ.succ.succ 3 1))))))))))))))

theorem laws_freeClosed {m : Nat} (D I mul q objects maps : Fin m) :
    (laws D I mul q objects maps).FreeClosed := by
  simp -implicitDefEqProofs [laws,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
    point_freeClosed,matching_freeClosed,ConstructionComponentCarrier.encodedVertex_freeClosed,
    ForcingComponentFibers.vertexFiber_freeClosed,ConstructionComponentCofinal.encodedCommon_freeClosed]

theorem laws_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (D I mul q objects maps : Fin m) :
    Project.Formula.satisfies env (laws D I mul q objects maps) ↔
      Laws (env.bound D) (env.bound I) (env.bound mul) (env.bound q) (env.bound objects) (env.bound maps) := by
  simp only [laws,Laws,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_imp_iff,
    Project.Formula.satisfies_iff_iff,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_mem_iff,
    Project.Formula.satisfies_extensionalEq_iff_eq (ModelTransfer.extensionality hM),Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_code,
    point_semantics hM,matching_semantics hM,ConstructionComponentCarrier.encodedVertex_semantics hM,
    ForcingComponentFibers.vertexFiber_semantics hM,ConstructionComponentCofinal.encodedCommon_semantics hM]
  rfl

def constructionSentence {k : Nat} (D I mul e q diagrams objImage objects S mapImage maps : Fin k) : Project.Sentence where
  formula := Project.Formula.forallClosure k
    (.imp (ProjectSyntax.encode id (ForcingDiagramPoset.leftCancelMonoid D mul e))
    (.imp (ConstructionProbeSharedIntersections.conditionalJoins D mul)
    (.imp (ProjectSyntax.encode id (ForcingDiagramCarrier.carrier D I diagrams))
    (.imp (ProjectSyntax.encode id (Source.SetLanguage.mapsTo objects diagrams objImage))
    (.imp (ProjectSyntax.encode id (ForcingEligibleMapFamily.arrows D mul diagrams S))
    (.imp (ProjectSyntax.encode id (Source.SetLanguage.mapsTo maps S mapImage))
    (.imp (ForcingEligibleSystem.system D objects maps)
      (.existsE (.conj (carrier D.succ I.succ mul.succ q.succ objects.succ maps.succ 0)
        (laws D.succ I.succ mul.succ q.succ objects.succ maps.succ))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
      ConstructionProbeSharedIntersections.conditionalJoins_freeClosed,ForcingEligibleSystem.system_freeClosed,
      carrier_freeClosed,laws_freeClosed]

theorem construction_models {k : Nat} (D I mul e q diagrams objImage objects S mapImage maps : Fin k)
    (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence (constructionSentence D I mul e q diagrams objImage objects S mapImage maps)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM)
    (constructionSentence D I mul e q diagrams objImage objects S mapImage maps)]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingDiagramPoset.leftCancelMonoid_semantics (M := M),ConstructionProbeSharedIntersections.conditionalJoins_semantics hM,
    ForcingDiagramCarrier.carrier_semantics (M := M),ForcingSupportSize.mapsTo_semantics (M := M),
    ForcingEligibleMapFamily.arrows_semantics (M := M),ForcingEligibleSystem.system_semantics hM,
    carrier_semantics hM,laws_semantics hM]
  intro hm hJ hDiagrams hObj hS hMaps hSys
  obtain ⟨vertices,hVertices⟩ := ConstructionComponentCarrier.exists_carrier hM (bound D) (bound I) (bound mul) (bound q)
  obtain ⟨image,fibers,hFibers,hFamily⟩ := ForcingComponentFibers.exists_family hM hDiagrams hObj hVertices
  obtain ⟨P,hP⟩ := exists_carrier hM hVertices hFibers hFamily
  exact ⟨P,hP,laws_of_system hM hm hJ hDiagrams hObj hS hMaps hSys⟩

theorem construction_kernel_certificate {k : Nat} (D I mul e q diagrams objImage objects S mapImage maps : Fin k) :
    FirstOrder.Derives nativeZF []
      (Project.fo_sentence (constructionSentence D I mul e q diagrams objImage objects S mapImage maps)) :=
  ModelTransfer.derives (fun _ hM => construction_models D I mul e q diagrams objImage objects S mapImage maps hM)

end PPAC.Migration.ForcingComponentMatches
