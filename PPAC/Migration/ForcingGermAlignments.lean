/- Pinned GermSelectors.Chain.fromRoot/index/Alignments and alignment lemmas
   (218-299), consumed by ConcreteQuotients.countable_quotient_of_cells.
   All indices are internal naturals and all arrows use the existing vertex
   carrier. No external sequence, chosen representative or new geometry. -/
import PPAC.Migration.ForcingTailGroup

namespace PPAC.Migration.ForcingGermAlignments
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ConstructionComponentCarrier (Code EncodedVertex Carrier)
open ConstructionComponentCofinal (Chain EncodedArrow EncodedCommon)
open ForcingComponentMove (Move)
open ForcingConditionGraphs (Permutation CompositionGraph InverseGraph)
open ForcingDiagramPoset (LeftCancelMonoid)
open ForcingDiagramOrder (Product)
open ConstructionFractionOrder (NatLe)
open ConstructionBaseMonoid (Divides)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

def Index (D I mul q root chain i n : M.Carrier .set) : Prop :=
  ∃ v, PureKuratowski.PairMember M i v chain ∧ EncodedArrow D I mul q root v n

def Alignment (D I mul q root chain pi i n : M.Carrier .set) : Prop :=
  ∃ v V, PureKuratowski.PairMember M i v chain ∧ Move D I mul q pi v V ∧
    EncodedArrow D I mul q root V n

theorem arrow_index_unique {D I mul e q v t n m : M.Carrier .set}
    (hm : LeftCancelMonoid D mul e) (hf : EncodedArrow D I mul q v t n)
    (hg : EncodedArrow D I mul q v t m) : n = m := by
  obtain ⟨r,a,U,s,b,V,hv,ht,hr,_,hf⟩ := hf
  obtain ⟨r',a',U',s',b',V',hv',ht',_,_,hg⟩ := hg
  obtain ⟨rfl,rfl,rfl⟩ := ConstructionComponentCarrier.code_injective hv hv'
  obtain ⟨rfl,rfl,rfl⟩ := ConstructionComponentCarrier.code_injective ht ht'
  exact ConstructionComponentVertices.arrow_index_unique hm hr hf hg

theorem arrow_index_mem {D I mul q v t n : M.Carrier .set}
    (h : EncodedArrow D I mul q v t n) :
    (Project.FirstOrderSemantics.reduct M).mem n D := by
  obtain ⟨_,_,_,_,_,_,_,_,hr,_,h⟩ := h
  exact hr.2.2.1 n h.1

theorem arrow_comp_product {D I mul e q v t z n m nm : M.Carrier .set}
    (hm : LeftCancelMonoid D mul e) (hf : EncodedArrow D I mul q v t n)
    (hg : EncodedArrow D I mul q t z m) (hp : Product mul n m nm) :
    EncodedArrow D I mul q v z nm := by
  obtain ⟨r,a,U,s,b,V,hv,ht,hr,hs,hf⟩ := hf
  obtain ⟨s',b',V',t,c,W,ht',hz,_,htV,hg⟩ := hg
  obtain ⟨rfl,rfl,rfl⟩ := ConstructionComponentCarrier.code_injective ht ht'
  exact ⟨r,a,U,t,c,W,hv,hz,hr,htV,ConstructionComponentVertices.compose hm hr hs hf hg hp⟩

theorem index_exists (hM : FirstOrder.Theory.Models M nativeZF)
    {w D I mul q zero root vertices chain i : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ x, ¬ (Project.FirstOrderSemantics.reduct M).mem x zero)
    (hC : Chain w D I mul q zero root vertices chain)
    (hi : (Project.FirstOrderSemantics.reduct M).mem i w) : ∃ n, Index D I mul q root chain i n := by
  have hzero := ForcingConditionGraphs.function_input hC.1.1 hC.2.1
  have hle : NatLe zero i := by
    rcases ConstructionFractionOrder.nat_compare hM hw hzero hi with he | hlt | hgt
    · exact Or.inl he
    · exact Or.inr hlt
    · exact (hz i hgt).elim
  obtain ⟨v,hv,_⟩ := hC.1.1.2 i hi
  obtain ⟨n,hn⟩ := hC.2.2.1 zero i root v hle hC.2.1 hv
  exact ⟨n,v,hv,hn⟩

theorem index_unique {w D I mul e q zero root vertices chain i n m : M.Carrier .set}
    (hm : LeftCancelMonoid D mul e) (hC : Chain w D I mul q zero root vertices chain)
    (hn : Index D I mul q root chain i n) (hm' : Index D I mul q root chain i m) : n = m := by
  obtain ⟨v,hv,hn⟩ := hn
  obtain ⟨v',hv',hm'⟩ := hm'
  have he := ForcingConditionGraphs.function_unique hC.1.1 hv hv'
  subst v'
  exact arrow_index_unique hm hn hm'

theorem index_transition {w D I mul e q zero root vertices chain i j v t n m d : M.Carrier .set}
    (hm : LeftCancelMonoid D mul e) (hC : Chain w D I mul q zero root vertices chain)
    (hi : Index D I mul q root chain i n) (hj : Index D I mul q root chain j m)
    (hiv : PureKuratowski.PairMember M i v chain) (hjt : PureKuratowski.PairMember M j t chain)
    (ha : EncodedArrow D I mul q v t d) : Product mul n d m := by
  obtain ⟨v',hv',hn⟩ := hi
  obtain ⟨t',ht',hm'⟩ := hj
  have he := ForcingConditionGraphs.function_unique hC.1.1 hiv hv'
  subst v'
  have he := ForcingConditionGraphs.function_unique hC.1.1 hjt ht'
  subst t'
  obtain ⟨p,_,hp⟩ := (hm.2.1 n (arrow_index_mem hn)).1 d (arrow_index_mem ha)
  exact arrow_index_unique hm (arrow_comp_product hm hn ha hp) hm' ▸ hp

theorem alignment_nonempty (hM : FirstOrder.Theory.Models M nativeZF)
    {w D I mul q zero root vertices chain pi rootT : M.Carrier .set}
    (hX : Carrier D I mul q vertices) (hC : Chain w D I mul q zero root vertices chain)
    (hq : ForcingSupportSize.Injection D I q)
    (hp : Permutation I pi) (hFix : CompositionGraph D pi q q)
    (hMove : Move D I mul q pi root rootT) (hCommon : EncodedCommon D I mul q root rootT) :
    ∃ i n, Alignment D I mul q root chain pi i n := by
  obtain ⟨inv,hInv,hi⟩ := ForcingConditionGraphs.exists_inverse hM hp
  have hFixInv := ForcingDiagramCarrier.reverse hp hq hi hFix
  obtain ⟨v,hv⟩ := ForcingComponentMove.exists_move hM hInv hFixInv (ForcingComponentMove.source_vertex hMove)
  have hvr : Move D I mul q pi v root := ForcingComponentMove.move_inverse hInv (fun x y => (hi y x).symm) hv
  have hcr := ForcingComponentRebase.common_symm
    (ForcingComponentMove.move_common hM hInv hFixInv hv (ForcingComponentMove.move_inverse hp hi hMove) hCommon)
  obtain ⟨i,t,n,_,hit,ha⟩ := hC.2.2.2.2 v ((hX v).mpr (ForcingComponentMove.target_vertex hv)) hcr
  obtain ⟨T,hT⟩ := ForcingComponentMove.exists_move hM hp hFix (ForcingComponentMatches.arrow_target ha)
  exact ⟨i,n,t,T,hit,hT,ForcingComponentMove.move_arrow hvr hT ha⟩

theorem alignment_bounded
    {w D I mul e q zero root vertices chain pi i a : M.Carrier .set}
    (hm : LeftCancelMonoid D mul e) (hX : Carrier D I mul q vertices)
    (hC : Chain w D I mul q zero root vertices chain)
    (h : Alignment D I mul q root chain pi i a) :
    ∃ N n, Index D I mul q root chain N n ∧ Divides D mul a n := by
  obtain ⟨v,V,_,hMove,ha⟩ := h
  have hV := ForcingComponentMove.target_vertex hMove
  have hc := ForcingComponentMatches.arrow_common ha (ForcingComponentMatches.arrow_id hm hV)
  obtain ⟨N,t,d,_,hNt,hd⟩ := hC.2.2.2.2 V ((hX V).mpr hV) hc
  obtain ⟨n,_,hn⟩ := (hm.2.1 a (arrow_index_mem ha)).1 d (arrow_index_mem hd)
  exact ⟨N,n,⟨t,hNt,arrow_comp_product hm ha hd hn⟩,d,arrow_index_mem hd,hn⟩

theorem alignment_replacement (hM : FirstOrder.Theory.Models M nativeZF)
    {w D I mul e q zero root vertices chain pi rootT i a N ni nN : M.Carrier .set}
    (hm : LeftCancelMonoid D mul e)
    (hJ : ConstructionProbeSharedIntersections.ConditionalJoins D mul)
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ x, ¬ (Project.FirstOrderSemantics.reduct M).mem x zero)
    (hX : Carrier D I mul q vertices) (hC : Chain w D I mul q zero root vertices chain)
    (hq : ForcingSupportSize.Injection D I q)
    (hp : Permutation I pi) (hFix : CompositionGraph D pi q q)
    (hMove : Move D I mul q pi root rootT) (hCommon : EncodedCommon D I mul q root rootT)
    (ha : Alignment D I mul q root chain pi i a)
    (hi : Index D I mul q root chain i ni) (hN : Index D I mul q root chain N nN) :
    ∃ j d b nj, Alignment D I mul q root chain pi j b ∧ NatLe i j ∧
      Product mul a d b ∧ Product mul ni d nj ∧ Index D I mul q root chain j nj ∧
        Divides D mul nN b := by
  obtain ⟨v,V,hiv,hv,hav⟩ := ha
  obtain ⟨vN,hNv,hNarrow⟩ := hN
  obtain ⟨inv,hInv,hInverse⟩ := ForcingConditionGraphs.exists_inverse hM hp
  have hFixInv := ForcingDiagramCarrier.reverse hp hq hInverse hFix
  obtain ⟨z,hzMove⟩ := ForcingComponentMove.exists_move hM hInv hFixInv
    (ForcingComponentMatches.arrow_target hNarrow)
  have hTCommon := (ForcingComponentRebase.common_iff hM hm hJ hCommon).mp
    (hC.2.2.2.1 N vN hNv)
  have hZCommon := ForcingComponentMove.move_common hM hInv hFixInv
    (ForcingComponentMove.move_inverse hp hInverse hMove) hzMove hTCommon
  obtain ⟨k,u,g,hk,hku,hg⟩ := hC.2.2.2.2 z
    ((hX z).mpr (ForcingComponentMove.target_vertex hzMove)) hZCommon
  have hiw := ForcingConditionGraphs.function_input hC.1.1 hiv
  obtain ⟨j,t,hjt,hij,hkj⟩ : ∃ j t, PureKuratowski.PairMember M j t chain ∧ NatLe i j ∧ NatLe k j := by
    rcases ConstructionFractionOrder.nat_compare hM hw hiw hk with he | hik | hki
    · exact ⟨k,u,hku,Or.inl he,Or.inl rfl⟩
    · exact ⟨k,u,hku,Or.inr hik,Or.inl rfl⟩
    · exact ⟨i,v,hiv,Or.inl rfl,Or.inr hki⟩
  obtain ⟨d,hd⟩ := hC.2.2.1 i j v t hij hiv hjt
  obtain ⟨f,hf⟩ := hC.2.2.1 k j u t hkj hku hjt
  obtain ⟨T,hT⟩ := ForcingComponentMove.exists_move hM hp hFix (ForcingComponentMatches.arrow_target hd)
  obtain ⟨gf,hgf⟩ := ForcingComponentMatches.arrow_comp hm hg hf
  have hzBack := ForcingComponentMove.move_inverse hInv (fun x y => (hInverse y x).symm) hzMove
  have hNtoT := ForcingComponentMove.move_arrow hzBack hT hgf
  obtain ⟨b,_,hb⟩ := (hm.2.1 a (arrow_index_mem hav)).1 d (arrow_index_mem hd)
  have hRootT := arrow_comp_product hm hav (ForcingComponentMove.move_arrow hv hT hd) hb
  obtain ⟨b',_,hb'⟩ := (hm.2.1 nN (arrow_index_mem hNarrow)).1 gf (arrow_index_mem hNtoT)
  have he := arrow_index_unique hm (arrow_comp_product hm hNarrow hNtoT hb') hRootT
  obtain ⟨nj,hnj⟩ := index_exists hM hw hz hC (ForcingConditionGraphs.function_input hC.1.1 hjt)
  exact ⟨j,d,b,nj,⟨t,T,hjt,hT,hRootT⟩,hij,hb,index_transition hm hC hi hnj hiv hjt hd,
    hnj,gf,arrow_index_mem hNtoT,he ▸ hb'⟩

/-- Source coset_eq_of_alignment, in the original equivalence relation:
    inverse(pi) * sigma fixes an actual tail of the same internal chain. -/
theorem same_alignment_tail (hM : FirstOrder.Theory.Models M nativeZF)
    {w D I mul q zero root vertices chain pi sigma inv diff i n : M.Carrier .set}
    (hC : Chain w D I mul q zero root vertices chain)
    (hp : Permutation I pi) (hi : InverseGraph pi inv)
    (hc : CompositionGraph I inv sigma diff)
    (hpi : Alignment D I mul q root chain pi i n)
    (hsigma : Alignment D I mul q root chain sigma i n) :
    ForcingTailCovariance.TailFixes w D diff chain := by
  obtain ⟨v,V,hiv,hv,hA⟩ := hpi
  obtain ⟨v',W,hiv',hw,hB⟩ := hsigma
  have he := ForcingConditionGraphs.function_unique hC.1.1 hiv hiv'
  subst v'
  obtain ⟨r,a,U,R,hvCode,hVCode,hr,hR,hPi⟩ := hv
  obtain ⟨r',a',U',S,hvCode',hWCode,_,hS,hSigma⟩ := hw
  obtain ⟨rfl,rfl,rfl⟩ := ConstructionComponentCarrier.code_injective hvCode hvCode'
  obtain ⟨r0,a0,U0,R',aR,UR,hRoot,hVCode',hr0,_,hA⟩ := hA
  obtain ⟨r0',a0',U0',S',aS,US,hRoot',hWCode',_,_,hB⟩ := hB
  obtain ⟨rfl,rfl,rfl⟩ := ConstructionComponentCarrier.code_injective hRoot hRoot'
  obtain ⟨rfl,rfl,rfl⟩ := ConstructionComponentCarrier.code_injective hVCode hVCode'
  obtain ⟨rfl,rfl,rfl⟩ := ConstructionComponentCarrier.code_injective hWCode hWCode'
  have hRS := ConstructionComponentVertices.sub_eq hM hR.1 hS.1 hA.2.1 hB.2.1
  subst S
  have hNative := (ForcingSupportSize.native_injection hM D I r).mp hr.1
  obtain ⟨A,hA⟩ := ZF.exists_range_of_setFunction (ModelTransfer.project_models_iff.mp hM)
    (KuratowskiZF.interpretation hM) hNative.1.1 hNative.1.2.1
  have hRange : ForcingSupportedNames.Range D r A := fun x => ⟨fun hx => by
      obtain ⟨k,hkx⟩ := (hA x).mp hx
      exact ⟨k,hNative.1.input_mem_of_pairMember hkx,hkx⟩,
    fun ⟨k,_,hkx⟩ => (hA x).mpr ⟨k,hkx⟩⟩
  refine ⟨i,v,r,a,U,A,ForcingConditionGraphs.function_input hC.1.1 hiv,hiv,hvCode,hRange,?_⟩
  intro x hx
  obtain ⟨k,hk,hkx⟩ := (hRange x).mp hx
  obtain ⟨y,hxy,_⟩ := hp.1.1.2 x (hr.1.1.2 k x hkx)
  have hky := (hPi k y).mpr ⟨hk,x,hkx,hxy⟩
  obtain ⟨_,x',hkx',hxy'⟩ := (hSigma k y).mp hky
  have he := ForcingConditionGraphs.function_unique hr.1.1.1 hkx' hkx
  subst x'
  exact (hc x x).mpr ⟨hr.1.1.2 k x hkx,y,hxy',(hi x y).mp hxy⟩

def Indices (w D I mul q root chain graph : M.Carrier .set) : Prop :=
  ForcingSupportSize.MapsTo w D graph ∧ ∀ i n,
    PureKuratowski.PairMember M i n graph ↔ Index D I mul q root chain i n

def index {m : Nat} (D I mul q root chain i n : Fin m) : Project.Formula 1 m :=
  (.existsE (.conj (ProjectSyntax.encode id (Source.SetLanguage.edge chain.succ i.succ 0)) (ConstructionComponentCofinal.encodedArrow D.succ I.succ mul.succ q.succ root.succ 0 n.succ)))

theorem index_freeClosed {m : Nat} (D I mul q root chain i n : Fin m) :
    (index D I mul q root chain i n).FreeClosed := by
  simp -implicitDefEqProofs [index,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,ConstructionComponentCofinal.encodedArrow_freeClosed]

theorem index_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (D I mul q root chain i n : Fin m) :
    Project.Formula.satisfies env (index D I mul q root chain i n) ↔ Index (env.bound D) (env.bound I) (env.bound mul) (env.bound q) (env.bound root) (env.bound chain) (env.bound i) (env.bound n) := by
  simp only [index,Index,Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_conj_iff,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,
    ConstructionComponentCofinal.encodedArrow_semantics hM]
  rfl

def alignment {m : Nat} (D I mul q root chain pi i n : Fin m) : Project.Formula 1 m :=
  (.existsE (.existsE (.conj (ProjectSyntax.encode id (Source.SetLanguage.edge chain.succ.succ i.succ.succ 1)) (.conj (ForcingComponentMove.move D.succ.succ I.succ.succ mul.succ.succ q.succ.succ pi.succ.succ 1 0) (ConstructionComponentCofinal.encodedArrow D.succ.succ I.succ.succ mul.succ.succ q.succ.succ root.succ.succ 0 n.succ.succ)))))

theorem alignment_freeClosed {m : Nat} (D I mul q root chain pi i n : Fin m) :
    (alignment D I mul q root chain pi i n).FreeClosed := by
  simp -implicitDefEqProofs [alignment,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,ForcingComponentMove.move_freeClosed,ConstructionComponentCofinal.encodedArrow_freeClosed]

theorem alignment_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (D I mul q root chain pi i n : Fin m) :
    Project.Formula.satisfies env (alignment D I mul q root chain pi i n) ↔ Alignment (env.bound D) (env.bound I) (env.bound mul) (env.bound q) (env.bound root) (env.bound chain) (env.bound pi) (env.bound i) (env.bound n) := by
  simp only [alignment,Alignment,Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_conj_iff,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,
    ForcingComponentMove.move_semantics hM,ConstructionComponentCofinal.encodedArrow_semantics hM]
  rfl

def indices {m : Nat} (w D I mul q root chain graph : Fin m) : Project.Formula 1 m :=
  (.conj (ProjectSyntax.encode id (Source.SetLanguage.mapsTo graph w D)) (.forallE (.forallE (.iff (ProjectSyntax.encode id (Source.SetLanguage.edge graph.succ.succ 1 0)) (index D.succ.succ I.succ.succ mul.succ.succ q.succ.succ root.succ.succ chain.succ.succ 1 0)))))

theorem indices_freeClosed {m : Nat} (w D I mul q root chain graph : Fin m) :
    (indices w D I mul q root chain graph).FreeClosed := by
  simp -implicitDefEqProofs [indices,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,index_freeClosed]

theorem indices_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w D I mul q root chain graph : Fin m) :
    Project.Formula.satisfies env (indices w D I mul q root chain graph) ↔ Indices (env.bound w) (env.bound D) (env.bound I) (env.bound mul) (env.bound q) (env.bound root) (env.bound chain) (env.bound graph) := by
  simp only [indices,Indices,Project.Formula.satisfies_forall_iff,
    Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_iff_iff,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,
    ForcingSupportSize.mapsTo_semantics (M := M),index_semantics hM]
  rfl

theorem exists_indices (hM : FirstOrder.Theory.Models M nativeZF)
    {w D I mul e q zero root vertices chain : M.Carrier .set}
    (hm : LeftCancelMonoid D mul e)
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ x, ¬ (Project.FirstOrderSemantics.reduct M).mem x zero)
    (hC : Chain w D I mul q zero root vertices chain) :
    ∃ graph, Indices w D I mul q root chain graph := by
  let schema : Project.BinarySchema 6 := {
    body := index 2 3 4 5 6 7 1 0
    freeClosed := index_freeClosed _ _ _ _ _ _ _ _ }
  let env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) 6 := {
    bound := Fin.cases D (Fin.cases I (Fin.cases mul (Fin.cases q (Fin.cases root (fun _ => chain))))),
    free := fun _ => D }
  have he i n : schema.denote env i n ↔ Index D I mul q root chain i n :=
    index_semantics hM ((env.push i).push n) 2 3 4 5 6 7 1 0
  obtain ⟨graph,hGraph,hEquation⟩ := ZF.exists_setFunctionFromTo_of_denote
    (ModelTransfer.project_models_iff.mp hM) (KuratowskiZF.interpretation hM) schema env
    (source := w) (target := D) (by
      intro i hi
      obtain ⟨n,hn⟩ := index_exists hM hw hz hC hi
      exact ⟨n,(he i n).mpr hn⟩) (by
      intro i _ n m hn hm'
      exact index_unique hm hC ((he i n).mp hn) ((he i m).mp hm')) (by
      intro i n _ hn
      obtain ⟨v,_,ha⟩ := (he i n).mp hn
      exact arrow_index_mem ha)
  refine ⟨graph,(ForcingSupportSize.native_mapsTo hM w D graph).mpr hGraph,?_⟩
  intro i n
  constructor
  · intro h
    exact (he i n).mp ((hEquation i n).mp h).2
  · intro h
    have hi : (Project.FirstOrderSemantics.reduct M).mem i w := by
      obtain ⟨v,hiv,_⟩ := h
      exact ForcingConditionGraphs.function_input hC.1.1 hiv
    exact (hEquation i n).mpr ⟨hi,(he i n).mpr h⟩

def Laws (w D I mul q root chain pi : M.Carrier .set) : Prop :=
  (∃ i n, Alignment D I mul q root chain pi i n) ∧
  (∀ i a, Alignment D I mul q root chain pi i a →
    ∃ N n, Index D I mul q root chain N n ∧ Divides D mul a n) ∧
  (∀ i a N ni nN, Alignment D I mul q root chain pi i a →
    Index D I mul q root chain i ni → Index D I mul q root chain N nN →
    ∃ j d b nj, Alignment D I mul q root chain pi j b ∧ NatLe i j ∧
      Product mul a d b ∧ Product mul ni d nj ∧ Index D I mul q root chain j nj ∧
        Divides D mul nN b) ∧
  (∀ sigma inv diff i n, InverseGraph pi inv → CompositionGraph I inv sigma diff →
    Alignment D I mul q root chain pi i n → Alignment D I mul q root chain sigma i n →
      ForcingTailCovariance.TailFixes w D diff chain)

def laws {m : Nat} (w D I mul q root chain pi : Fin m) : Project.Formula 1 m :=
  (.conj (.existsE (.existsE (alignment D.succ.succ I.succ.succ mul.succ.succ q.succ.succ root.succ.succ chain.succ.succ pi.succ.succ 1 0))) (.conj (.forallE (.forallE (.imp (alignment D.succ.succ I.succ.succ mul.succ.succ q.succ.succ root.succ.succ chain.succ.succ pi.succ.succ 1 0) (.existsE (.existsE (.conj (index D.succ.succ.succ.succ I.succ.succ.succ.succ mul.succ.succ.succ.succ q.succ.succ.succ.succ root.succ.succ.succ.succ chain.succ.succ.succ.succ 1 0) (ProjectSyntax.encode id (ConstructionBaseMonoid.divides D.succ.succ.succ.succ mul.succ.succ.succ.succ 2 0)))))))) (.conj (.forallE (.forallE (.forallE (.forallE (.forallE (.imp (alignment D.succ.succ.succ.succ.succ I.succ.succ.succ.succ.succ mul.succ.succ.succ.succ.succ q.succ.succ.succ.succ.succ root.succ.succ.succ.succ.succ chain.succ.succ.succ.succ.succ pi.succ.succ.succ.succ.succ 4 3) (.imp (index D.succ.succ.succ.succ.succ I.succ.succ.succ.succ.succ mul.succ.succ.succ.succ.succ q.succ.succ.succ.succ.succ root.succ.succ.succ.succ.succ chain.succ.succ.succ.succ.succ 4 1) (.imp (index D.succ.succ.succ.succ.succ I.succ.succ.succ.succ.succ mul.succ.succ.succ.succ.succ q.succ.succ.succ.succ.succ root.succ.succ.succ.succ.succ chain.succ.succ.succ.succ.succ 2 0) (.existsE (.existsE (.existsE (.existsE (.conj (alignment D.succ.succ.succ.succ.succ.succ.succ.succ.succ I.succ.succ.succ.succ.succ.succ.succ.succ.succ mul.succ.succ.succ.succ.succ.succ.succ.succ.succ q.succ.succ.succ.succ.succ.succ.succ.succ.succ root.succ.succ.succ.succ.succ.succ.succ.succ.succ chain.succ.succ.succ.succ.succ.succ.succ.succ.succ pi.succ.succ.succ.succ.succ.succ.succ.succ.succ 3 1) (.conj (.disj (Project.Formula.extensionalEq (.bound 8) (.bound 3)) (.mem (.bound 8) (.bound 3))) (.conj (ProjectSyntax.encode id (ForcingDiagramOrder.product mul.succ.succ.succ.succ.succ.succ.succ.succ.succ 7 2 1)) (.conj (ProjectSyntax.encode id (ForcingDiagramOrder.product mul.succ.succ.succ.succ.succ.succ.succ.succ.succ 5 2 0)) (.conj (index D.succ.succ.succ.succ.succ.succ.succ.succ.succ I.succ.succ.succ.succ.succ.succ.succ.succ.succ mul.succ.succ.succ.succ.succ.succ.succ.succ.succ q.succ.succ.succ.succ.succ.succ.succ.succ.succ root.succ.succ.succ.succ.succ.succ.succ.succ.succ chain.succ.succ.succ.succ.succ.succ.succ.succ.succ 3 0) (ProjectSyntax.encode id (ConstructionBaseMonoid.divides D.succ.succ.succ.succ.succ.succ.succ.succ.succ mul.succ.succ.succ.succ.succ.succ.succ.succ.succ 4 1))))))))))))))))))) (.forallE (.forallE (.forallE (.forallE (.forallE (.imp (ProjectSyntax.encode id (ForcingConditionGraphs.inverseGraph pi.succ.succ.succ.succ.succ 3)) (.imp (ProjectSyntax.encode id (ForcingConditionGraphs.compositionGraph I.succ.succ.succ.succ.succ 3 4 2)) (.imp (alignment D.succ.succ.succ.succ.succ I.succ.succ.succ.succ.succ mul.succ.succ.succ.succ.succ q.succ.succ.succ.succ.succ root.succ.succ.succ.succ.succ chain.succ.succ.succ.succ.succ pi.succ.succ.succ.succ.succ 1 0) (.imp (alignment D.succ.succ.succ.succ.succ I.succ.succ.succ.succ.succ mul.succ.succ.succ.succ.succ q.succ.succ.succ.succ.succ root.succ.succ.succ.succ.succ chain.succ.succ.succ.succ.succ 4 1 0) (ForcingTailCovariance.tailFixes w.succ.succ.succ.succ.succ D.succ.succ.succ.succ.succ 2 chain.succ.succ.succ.succ.succ)))))))))))))

theorem laws_freeClosed {m : Nat} (w D I mul q root chain pi : Fin m) :
    (laws w D I mul q root chain pi).FreeClosed := by
  simp -implicitDefEqProofs [laws,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
    Project.Formula.extensionalEq,index_freeClosed,alignment_freeClosed,ForcingTailCovariance.tailFixes_freeClosed]

theorem laws_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w D I mul q root chain pi : Fin m) :
    Project.Formula.satisfies env (laws w D I mul q root chain pi) ↔
      Laws (env.bound w) (env.bound D) (env.bound I) (env.bound mul) (env.bound q) (env.bound root) (env.bound chain) (env.bound pi) := by
  simp only [laws,Laws,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_disj_iff,
    Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    Project.Formula.satisfies_extensionalEq_iff_eq (ModelTransfer.extensionality hM),
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    index_semantics hM,alignment_semantics hM,ConstructionBaseMonoid.divides_semantics (M := M),
    ForcingDiagramOrder.product_semantics (M := M),ForcingConditionGraphs.inverseGraph_semantics (M := M),
    ForcingConditionGraphs.compositionGraph_semantics (M := M),ForcingTailCovariance.tailFixes_semantics hM]
  rfl

theorem source_construct (hM : FirstOrder.Theory.Models M nativeZF)
    {w D I mul e q zero root vertices chain pi rootT : M.Carrier .set}
    (hm : LeftCancelMonoid D mul e)
    (hJ : ConstructionProbeSharedIntersections.ConditionalJoins D mul)
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ x, ¬ (Project.FirstOrderSemantics.reduct M).mem x zero)
    (hX : Carrier D I mul q vertices) (hC : Chain w D I mul q zero root vertices chain)
    (hq : ForcingSupportSize.Injection D I q)
    (hp : Permutation I pi) (hFix : CompositionGraph D pi q q)
    (hMove : Move D I mul q pi root rootT) (hCommon : EncodedCommon D I mul q root rootT) :
    ∃ graph, Indices w D I mul q root chain graph ∧ PureKuratowski.PairMember M zero e graph ∧
      Laws w D I mul q root chain pi := by
  obtain ⟨graph,hGraph⟩ := exists_indices hM hm hw hz hC
  have hzero : Index D I mul q root chain zero e :=
    ⟨root,hC.2.1,ForcingComponentMatches.arrow_id hm (ForcingComponentMove.source_vertex hMove)⟩
  refine ⟨graph,hGraph,(hGraph.2 zero e).mpr hzero,?_,?_,?_,?_⟩
  · exact alignment_nonempty hM hX hC hq hp hFix hMove hCommon
  · intro i a ha
    exact alignment_bounded hm hX hC ha
  · intro i a N ni nN ha hi hN
    exact alignment_replacement hM hm hJ hw hz hX hC hq hp hFix hMove hCommon ha hi hN
  · intro sigma inv diff i n hi hc hpi hsigma
    exact same_alignment_tail hM hC hp hi hc hpi hsigma

def sourceSentence {m : Nat} (w D I mul e q zero root vertices chain pi rootT : Fin m) : Project.Sentence where
  formula := Project.Formula.forallClosure m (.imp (ProjectSyntax.encode id (ForcingDiagramPoset.leftCancelMonoid D mul e)) (.imp (ConstructionProbeSharedIntersections.conditionalJoins D mul) (.imp (Project.Formula.isOmega (.bound w)) (.imp (ProjectSyntax.encode id (ForcingWithTopCarrier.empty zero)) (.imp (ConstructionComponentCarrier.carrier D I mul q vertices) (.imp (ConstructionComponentCofinal.chain w D I mul q zero root vertices chain) (.imp (ProjectSyntax.encode id (Source.SetLanguage.injection q D I)) (.imp (ProjectSyntax.encode id (ForcingConditionGraphs.permutation I pi)) (.imp (ProjectSyntax.encode id (ForcingConditionGraphs.compositionGraph D pi q q)) (.imp (ForcingComponentMove.move D I mul q pi root rootT) (.imp (ConstructionComponentCofinal.encodedCommon D I mul q root rootT) (.existsE (.conj (indices w.succ D.succ I.succ mul.succ q.succ root.succ chain.succ 0) (.conj (ProjectSyntax.encode id (Source.SetLanguage.edge 0 zero.succ e.succ)) (laws w.succ D.succ I.succ mul.succ q.succ root.succ chain.succ pi.succ)))))))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,Project.Formula.isOmega,
      ConstructionProbeSharedIntersections.conditionalJoins_freeClosed,ConstructionComponentCarrier.carrier_freeClosed,
      ConstructionComponentCofinal.chain_freeClosed,ForcingComponentMove.move_freeClosed,
      ConstructionComponentCofinal.encodedCommon_freeClosed,indices_freeClosed,laws_freeClosed]

theorem source_models {m : Nat} (w D I mul e q zero root vertices chain pi rootT : Fin m) (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence (sourceSentence w D I mul e q zero root vertices chain pi rootT)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM)
    (sourceSentence w D I mul e q zero root vertices chain pi rootT)]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_isOmega_iff,Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,
    ForcingDiagramPoset.leftCancelMonoid_semantics (M := M),ConstructionProbeSharedIntersections.conditionalJoins_semantics hM,
    ForcingWithTopCarrier.empty_semantics (M := M),ConstructionComponentCarrier.carrier_semantics hM,
    ConstructionComponentCofinal.chain_semantics hM,ForcingSupportSize.injection_semantics (M := M),
    ForcingConditionGraphs.permutation_semantics (M := M),ForcingConditionGraphs.compositionGraph_semantics (M := M),
    ForcingComponentMove.move_semantics hM,ConstructionComponentCofinal.encodedCommon_semantics hM,
    indices_semantics hM,laws_semantics hM]
  exact source_construct hM

theorem source_kernel_certificate {m : Nat} (w D I mul e q zero root vertices chain pi rootT : Fin m) :
    FirstOrder.Derives nativeZF [] (Project.fo_sentence (sourceSentence w D I mul e q zero root vertices chain pi rootT)) :=
  ModelTransfer.derives (fun _ hM => source_models w D I mul e q zero root vertices chain pi rootT hM)

end PPAC.Migration.ForcingGermAlignments
