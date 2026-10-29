/- Pinned TailGraphs.ChainCode/At/Represents:21-88.
Use literal local normalized names, the actual internal omega-chain, and the
existing local/glued projections. No host List, Quotient or representative
choice replaces the object relation. Consumers: PersistentCodes and CodeLinks. -/
import PPAC.Migration.ForcingEligibleReindex
import YesMetaZFC.SetTheory.FunctionSpaceConstruction

namespace PPAC.Migration.ForcingTailCodes
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open Source (Formula)
open ForcingSupportSize (MapsTo)
open ConstructionComponentCofinal (EncodedCommon)
open ConstructionComponentCarrier (Code)
open ForcingEligibleFamily (Data)
open ConstructionFractionOrder (NatLe)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 6000000
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

def Entry (v : Fin 7 → M.Carrier .set) (G F bound vertex sigma : M.Carrier .set) : Prop :=
  ∃ r a U A H, Code vertex r a U ∧ ForcingSupportedNames.Range (v 0) r A ∧
    ForcingLabelPermutations.Fixing G A H ∧ ForcingLocalNames.LocalName v G F bound H sigma

def entry {m : Nat} (rho : Fin 7 → Fin m) (G F bound vertex sigma : Fin m) : Project.Formula 1 m :=
  (.existsE ((.existsE ((.existsE ((.existsE ((.existsE ((.conj (ConstructionComponentCarrier.code (vertex).succ.succ.succ.succ.succ 4 3 2) (.conj (ProjectSyntax.encode id (ForcingSupportedNames.range (rho 0).succ.succ.succ.succ.succ 4 1)) (.conj (ProjectSyntax.encode id (ForcingLabelPermutations.fixing (G).succ.succ.succ.succ.succ 1 0)) (ProjectSyntax.encode id (ForcingLocalNames.localName (fun j => (rho j).succ.succ.succ.succ.succ) (G).succ.succ.succ.succ.succ (F).succ.succ.succ.succ.succ (bound).succ.succ.succ.succ.succ 0 (sigma).succ.succ.succ.succ.succ)))))))))))))))

theorem entry_freeClosed {m : Nat} (rho : Fin 7 → Fin m) (G F bound vertex sigma : Fin m) :
    (entry rho G F bound vertex sigma).FreeClosed := by
  simp -implicitDefEqProofs [entry,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,ConstructionComponentCarrier.code_freeClosed]

theorem entry_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (rho : Fin 7 → Fin m) (G F bound vertex sigma : Fin m) :
    Project.Formula.satisfies env (entry rho G F bound vertex sigma) ↔
      Entry (fun j => env.bound (rho j)) (env.bound G) (env.bound F) (env.bound bound) (env.bound vertex) (env.bound sigma) := by
  simp only [entry,Entry,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,
    ConstructionComponentCarrier.code_semantics hM,GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingSupportedNames.range_semantics (M := M),ForcingLabelPermutations.fixing_semantics (M := M),ForcingLocalNames.localName_semantics (M := M)]
  rfl

def ChainCode (v : Fin 7 → M.Carrier .set) (G F bound w names chain a : M.Carrier .set) : Prop :=
  MapsTo w names a ∧ ∀ i sigma, PureKuratowski.PairMember M i sigma a →
    ∃ vertex, PureKuratowski.PairMember M i vertex chain ∧ Entry v G F bound vertex sigma

def chainCode {m : Nat} (rho : Fin 7 → Fin m) (G F bound w names chain a : Fin m) : Project.Formula 1 m :=
  .conj (ProjectSyntax.encode id (Source.SetLanguage.mapsTo a w names)) (.forallE ((.forallE ((.imp (ProjectSyntax.encode id (Source.SetLanguage.edge (a).succ.succ 1 0)) (.existsE ((.conj (ProjectSyntax.encode id (Source.SetLanguage.edge (chain).succ.succ.succ 2 0)) (entry (fun j => (rho j).succ.succ.succ) (G).succ.succ.succ (F).succ.succ.succ (bound).succ.succ.succ 0 1)))))))))

theorem chainCode_freeClosed {m : Nat} (rho : Fin 7 → Fin m) (G F bound w names chain a : Fin m) :
    (chainCode rho G F bound w names chain a).FreeClosed := by
  simp -implicitDefEqProofs [chainCode,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,entry_freeClosed]

theorem chainCode_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (rho : Fin 7 → Fin m) (G F bound w names chain a : Fin m) :
    Project.Formula.satisfies env (chainCode rho G F bound w names chain a) ↔
      ChainCode (fun j => env.bound (rho j)) (env.bound G) (env.bound F) (env.bound bound) (env.bound w) (env.bound names) (env.bound chain) (env.bound a) := by
  simp only [chainCode,ChainCode,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_imp_iff,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),ForcingSupportSize.mapsTo_semantics (M := M),KuratowskiZF.source_edge,entry_semantics hM]
  rfl

def Carrier (v : Fin 7 → M.Carrier .set) (G F bound w names chain codes : M.Carrier .set) : Prop :=
  ∀ a, (Project.FirstOrderSemantics.reduct M).mem a codes ↔ ChainCode v G F bound w names chain a

def carrier {m : Nat} (rho : Fin 7 → Fin m) (G F bound w names chain codes : Fin m) : Project.Formula 1 m :=
  .forallE (.iff (.mem (.bound 0) (.bound codes.succ))
    (chainCode (fun j => (rho j).succ) G.succ F.succ bound.succ w.succ names.succ chain.succ 0))

theorem carrier_freeClosed {m : Nat} (rho : Fin 7 → Fin m) (G F bound w names chain codes : Fin m) :
    (carrier rho G F bound w names chain codes).FreeClosed := by
  simp -implicitDefEqProofs [carrier,Definitional.Formula.FreeClosed,chainCode_freeClosed]

theorem carrier_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (rho : Fin 7 → Fin m) (G F bound w names chain codes : Fin m) :
    Project.Formula.satisfies env (carrier rho G F bound w names chain codes) ↔
      Carrier (fun j => env.bound (rho j)) (env.bound G) (env.bound F) (env.bound bound) (env.bound w) (env.bound names) (env.bound chain) (env.bound codes) := by
  simp only [carrier,Carrier,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_iff_iff,
    Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,chainCode_semantics hM]
  rfl

theorem exists_carrier (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k) (G F bound w names chain : Fin k) :
    ∃ codes, Carrier (fun j => env (rho j)) (env G) (env F) (env bound) (env w) (env names) (env chain) codes := by
  obtain ⟨space,hSpace⟩ := ZF.exists_functionSpace (ModelTransfer.project_models_iff.mp hM)
    (KuratowskiZF.interpretation hM) (env w) (env names)
  let schema : Project.UnarySchema k := {
    body := chainCode (fun j => (rho j).succ) G.succ F.succ bound.succ w.succ names.succ chain.succ 0
    freeClosed := chainCode_freeClosed _ _ _ _ _ _ _ _ }
  let penv : SetTheory.Env (Project.FirstOrderSemantics.reduct M) k := { bound := env, free := fun _ => env w }
  have he a : schema.denote penv a ↔ ChainCode (fun j => env (rho j)) (env G) (env F) (env bound) (env w) (env names) (env chain) a :=
    chainCode_semantics hM (penv.push a) _ _ _ _ _ _ _ _
  obtain ⟨codes,hCodes⟩ := ZF.separation_exists_d (ModelTransfer.project_models_iff.mp hM) schema penv space
  refine ⟨codes,fun a => ?_⟩
  constructor
  · intro ha
    exact (he a).mp ((hCodes a).mp ha).2
  · intro ha
    exact (hCodes a).mpr ⟨(hSpace a).mpr ((ForcingSupportSize.native_mapsTo hM _ _ _).mp ha.1),(he a).mpr ha⟩


def At {k : Nat} (R : Formula (k+2)) (Hdom : Formula (k+1))
    (env : Fin k → M.Carrier .set) (v : Fin 7 → M.Carrier .set)
    (I G F mul g q bound labels E objects maps root gluePr vertex sigma b : M.Carrier .set) : Prop :=
  ∃ r index U A H X Q pr O V x p,
    EncodedCommon (v 0) I mul q root vertex ∧ Code vertex r index U ∧
    Data R Hdom env v G F mul g q bound labels E r A H X Q pr O ∧
    PureKuratowski.PairMember M r O objects ∧ ForcingSystemFibers.Fiber (v 0) mul objects maps r O index U V ∧
    (Project.FirstOrderSemantics.reduct M).mem x V ∧ PureKuratowski.PairMember M sigma x pr ∧
    PureKuratowski.Code M p vertex x ∧ PureKuratowski.PairMember M p b gluePr

theorem at_unique (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    {R : Formula (k+2)} {Hdom : Formula (k+1)} {env : Fin k → M.Carrier .set} {v : Fin 7 → M.Carrier .set}
    {I G F mul g q bound labels E objects maps root gluePr vertex sigma b c P Q : M.Carrier .set}
    (hGlue : MapsTo P Q gluePr)
    (hb : At R Hdom env v I G F mul g q bound labels E objects maps root gluePr vertex sigma b)
    (hc : At R Hdom env v I G F mul g q bound labels E objects maps root gluePr vertex sigma c) : b = c := by
  obtain ⟨r,index,U,A,H,X,T,pr,O,V,x,p,_,hv,hD,_,_,_,hs,hp,hb⟩ := hb
  obtain ⟨r',index',U',A',H',X',T',pr',O',V',y,p',_,hv',hD',_,_,_,ht,hp',hc⟩ := hc
  obtain ⟨rfl,rfl,rfl⟩ := ConstructionComponentCarrier.code_injective hv hv'
  obtain ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩ := ForcingEligibleFamily.data_unique hM hD hD'
  have hxy := ForcingConditionGraphs.function_unique hD.2.2.2.1.1 hs ht
  subst y
  have he := KuratowskiZF.code_unique hM hp hp'
  subst p'
  exact ForcingConditionGraphs.function_unique hGlue.1 hb hc

theorem at_entry {k : Nat}
    {R : Formula (k+2)} {Hdom : Formula (k+1)} {env : Fin k → M.Carrier .set} {v : Fin 7 → M.Carrier .set}
    {I G F mul g q bound labels E objects maps root gluePr vertex sigma b : M.Carrier .set}
    (h : At R Hdom env v I G F mul g q bound labels E objects maps root gluePr vertex sigma b) :
    Entry v G F bound vertex sigma := by
  obtain ⟨r,index,U,A,H,X,Q,pr,O,V,x,p,_,hv,hD,_,_,_,hs,_,_⟩ := h
  exact ⟨r,index,U,A,H,hv,hD.1,hD.2.1,(hD.2.2.1 sigma).mp (ForcingConditionGraphs.function_input hD.2.2.2.1.1 hs)⟩

theorem at_total (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    {R : Formula (k+2)} {Hdom : Formula (k+1)} {env : Fin k → M.Carrier .set} {v : Fin 7 → M.Carrier .set}
    {I G F mul g q bound labels E objects maps root gluePr vertex b objImage Q : M.Carrier .set}
    (hDiagrams : ForcingDiagramCarrier.Carrier (v 0) I (v 4)) (hObjMap : MapsTo (v 4) objImage objects)
    (hObj : ForcingEligibleFamily.Family R Hdom env v G F mul g q bound labels E (v 4) objects)
    (hAll : ForcingComponentGluing.AllFiberMaps (v 0) I mul q objects maps root Q gluePr)
    (hv : EncodedCommon (v 0) I mul q root vertex) (hb : (Project.FirstOrderSemantics.reduct M).mem b Q) :
    ∃ sigma, At R Hdom env v I G F mul g q bound labels E objects maps root gluePr vertex sigma b := by
  have hCommon := hv
  obtain ⟨_,_,_,r,index,U,_,hCode,_,hVertex,_⟩ := hv
  obtain ⟨O,hr,_⟩ := hObjMap.1.2 r ((hDiagrams r).mpr hVertex.1)
  obtain ⟨A,H,X,T,pr,hD⟩ := ((hObj r O).mp hr).2
  obtain ⟨V,hV⟩ := ForcingSystemFibers.exists_fiber hM (v 0) mul objects maps r O index U
  obtain ⟨f,hf,_,hOnto⟩ := hAll vertex V hCommon ⟨r,index,U,O,hCode,hr,hV⟩
  obtain ⟨x,hx,hxb⟩ := hOnto b hb
  have hxT := ((hD.2.2.2.2.2.2 x).mp ((hV x).mp hx).1).1
  obtain ⟨sigma,_,hs⟩ := ForcingLocalQuotient.projection_onto hD.2.2.2.2.1 hD.2.2.2.2.2.1 hxT
  obtain ⟨_,p,hp,hpb⟩ := (hf.2 x b).mp hxb
  exact ⟨sigma,r,index,U,A,H,X,T,pr,O,V,x,p,hCommon,hCode,hD,hr,hV,hx,hs,hp,hpb⟩

def atName {k m : Nat} (R : Formula (k+2)) (Hdom : Formula (k+1)) (base : Fin k → Fin m) (rho : Fin 7 → Fin m)
    (I G F mul g q bound labels E objects maps root gluePr vertex sigma b : Fin m) : Project.Formula 1 m :=
  (.existsE ((.existsE ((.existsE ((.existsE ((.existsE ((.existsE ((.existsE ((.existsE ((.existsE ((.existsE ((.existsE ((.existsE ((.conj (ConstructionComponentCofinal.encodedCommon (rho 0).succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (I).succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (mul).succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (q).succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (root).succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (vertex).succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ) (.conj (ConstructionComponentCarrier.code (vertex).succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ 11 10 9) (.conj (ProjectSyntax.encode id (ForcingEligibleFamily.data R Hdom (fun j => (base j).succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ) (fun j => (rho j).succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ) (G).succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (F).succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (mul).succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (g).succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (q).succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (bound).succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (labels).succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (E).succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ 11 8 7 6 5 4 3)) (.conj (ProjectSyntax.encode id (Source.SetLanguage.edge (objects).succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ 11 3)) (.conj (ProjectSyntax.encode id (ForcingSystemFibers.fiber (rho 0).succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (mul).succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (objects).succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ (maps).succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ 11 3 10 9 2)) (.conj (.mem (.bound 1) (.bound 2)) (.conj (ProjectSyntax.encode id (Source.SetLanguage.edge 4 (sigma).succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ 1)) (.conj (ProjectSyntax.encode id (PairSyntax.ordered 0 (vertex).succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ 1)) (ProjectSyntax.encode id (Source.SetLanguage.edge (gluePr).succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ 0 (b).succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ.succ))))))))))))))))))))))))))))))))))

theorem atName_freeClosed {k m : Nat} (R : Formula (k+2)) (Hdom : Formula (k+1)) (base : Fin k → Fin m) (rho : Fin 7 → Fin m)
    (I G F mul g q bound labels E objects maps root gluePr vertex sigma b : Fin m) : (atName R Hdom base rho I G F mul g q bound labels E objects maps root gluePr vertex sigma b).FreeClosed := by
  simp -implicitDefEqProofs [atName,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
    ConstructionComponentCofinal.encodedCommon_freeClosed,ConstructionComponentCarrier.code_freeClosed]

theorem atName_semantics (hM : FirstOrder.Theory.Models M nativeZF) {k m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (R : Formula (k+2)) (Hdom : Formula (k+1))
    (base : Fin k → Fin m) (rho : Fin 7 → Fin m) (I G F mul g q bound labels E objects maps root gluePr vertex sigma b : Fin m) :
    Project.Formula.satisfies env (atName R Hdom base rho I G F mul g q bound labels E objects maps root gluePr vertex sigma b) ↔
      At R Hdom (fun j => env.bound (base j)) (fun j => env.bound (rho j)) (env.bound I) (env.bound G) (env.bound F) (env.bound mul) (env.bound g) (env.bound q) (env.bound bound) (env.bound labels) (env.bound E) (env.bound objects) (env.bound maps) (env.bound root) (env.bound gluePr) (env.bound vertex) (env.bound sigma) (env.bound b) := by
  simp only [atName,At,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    ConstructionComponentCofinal.encodedCommon_semantics hM,ConstructionComponentCarrier.code_semantics hM,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),ForcingEligibleFamily.data_semantics (M := M),
    ForcingSystemFibers.fiber_semantics (M := M),KuratowskiZF.source_edge,KuratowskiZF.source_code]
  rfl


def Represents {k : Nat} (R : Formula (k+2)) (Hdom : Formula (k+1))
    (env : Fin k → M.Carrier .set) (v : Fin 7 → M.Carrier .set)
    (I G F mul g q bound labels E objects maps root gluePr w chain a b : M.Carrier .set) : Prop :=
  ∃ N, (Project.FirstOrderSemantics.reduct M).mem N w ∧ ∀ i,
    (Project.FirstOrderSemantics.reduct M).mem i w → NatLe N i →
    ∃ vertex sigma, PureKuratowski.PairMember M i vertex chain ∧ PureKuratowski.PairMember M i sigma a ∧
      At R Hdom env v I G F mul g q bound labels E objects maps root gluePr vertex sigma b

theorem represents_unique (hM : FirstOrder.Theory.Models M nativeZF) {k : Nat}
    {R : Formula (k+2)} {Hdom : Formula (k+1)} {env : Fin k → M.Carrier .set} {v : Fin 7 → M.Carrier .set}
    {I G F mul g q bound labels E objects maps root gluePr w chain a b c P Q vertices names : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hChain : MapsTo w vertices chain) (hCode : MapsTo w names a) (hGlue : MapsTo P Q gluePr)
    (hb : Represents R Hdom env v I G F mul g q bound labels E objects maps root gluePr w chain a b)
    (hc : Represents R Hdom env v I G F mul g q bound labels E objects maps root gluePr w chain a c) : b = c := by
  obtain ⟨N,hN,hb⟩ := hb
  obtain ⟨L,hL,hc⟩ := hc
  have hZF := ModelTransfer.project_models_iff.mp hM
  have ord := hw.members_areOrdinals hZF
  have hCommon : ∃ i, (Project.FirstOrderSemantics.reduct M).mem i w ∧ NatLe N i ∧ NatLe L i := by
    rcases Structure.IsOrdinal.trichotomy hZF.1 (ord N hN) (ord L hL)
      (KP.difference_exists_d (ZF.modelsKP hZF)) (KP.intersection_exists_d (ZF.modelsKP hZF) N L) with he | hn | hl
    · exact ⟨L,hL,Or.inl (hZF.1.eq_of_same_members N L he),Or.inl rfl⟩
    · exact ⟨L,hL,Or.inr hn,Or.inl rfl⟩
    · exact ⟨N,hN,Or.inl rfl,Or.inr hl⟩
  obtain ⟨i,hi,hNi,hLi⟩ := hCommon
  obtain ⟨vertex,sigma,hv,hs,hb⟩ := hb i hi hNi
  obtain ⟨vertex',sigma',hv',hs',hc⟩ := hc i hi hLi
  have hvv := ForcingConditionGraphs.function_unique hChain.1 hv hv'
  have hss := ForcingConditionGraphs.function_unique hCode.1 hs hs'
  subst vertex'; subst sigma'
  exact at_unique hM hGlue hb hc


def represents {k m : Nat} (R : Formula (k+2)) (Hdom : Formula (k+1)) (base : Fin k → Fin m) (rho : Fin 7 → Fin m)
    (I G F mul g q bound labels E objects maps root gluePr w chain a b : Fin m) : Project.Formula 1 m :=
  .existsE (.conj (.mem (.bound 0) (.bound w.succ)) (.forallE (.imp (.mem (.bound 0) (.bound (w).succ.succ)) (.imp (.disj (Project.Formula.extensionalEq (.bound 1) (.bound 0)) (.mem (.bound 1) (.bound 0))) (.existsE ((.existsE ((.conj (ProjectSyntax.encode id (Source.SetLanguage.edge (chain).succ.succ.succ.succ 2 1)) (.conj (ProjectSyntax.encode id (Source.SetLanguage.edge (a).succ.succ.succ.succ 2 0)) (atName R Hdom (fun j => (base j).succ.succ.succ.succ) (fun j => (rho j).succ.succ.succ.succ) (I).succ.succ.succ.succ (G).succ.succ.succ.succ (F).succ.succ.succ.succ (mul).succ.succ.succ.succ (g).succ.succ.succ.succ (q).succ.succ.succ.succ (bound).succ.succ.succ.succ (labels).succ.succ.succ.succ (E).succ.succ.succ.succ (objects).succ.succ.succ.succ (maps).succ.succ.succ.succ (root).succ.succ.succ.succ (gluePr).succ.succ.succ.succ 1 0 (b).succ.succ.succ.succ)))))))))))

theorem represents_freeClosed {k m : Nat} (R : Formula (k+2)) (Hdom : Formula (k+1)) (base : Fin k → Fin m) (rho : Fin 7 → Fin m)
    (I G F mul g q bound labels E objects maps root gluePr w chain a b : Fin m) : (represents R Hdom base rho I G F mul g q bound labels E objects maps root gluePr w chain a b).FreeClosed := by
  simp -implicitDefEqProofs [represents,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,atName_freeClosed]

theorem represents_semantics (hM : FirstOrder.Theory.Models M nativeZF) {k m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (R : Formula (k+2)) (Hdom : Formula (k+1))
    (base : Fin k → Fin m) (rho : Fin 7 → Fin m) (I G F mul g q bound labels E objects maps root gluePr w chain a b : Fin m) :
    Project.Formula.satisfies env (represents R Hdom base rho I G F mul g q bound labels E objects maps root gluePr w chain a b) ↔
      Represents R Hdom (fun j => env.bound (base j)) (fun j => env.bound (rho j)) (env.bound I) (env.bound G) (env.bound F) (env.bound mul) (env.bound g) (env.bound q) (env.bound bound) (env.bound labels) (env.bound E) (env.bound objects) (env.bound maps) (env.bound root) (env.bound gluePr) (env.bound w) (env.bound chain) (env.bound a) (env.bound b) := by
  simp only [represents,Represents,NatLe,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_disj_iff,
    Project.Formula.satisfies_extensionalEq_iff_eq (ModelTransfer.extensionality hM),Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,atName_semantics hM]
  rfl


/-- The existing representing-code construction with an arbitrary environment embedding.
This lets its callers supply actual internally constructed families without changing R/Hdom. -/
theorem exists_representing_code_over (hM : FirstOrder.Theory.Models M nativeZF)
    (hChoice : ConstructionDirectedCardinality.Choice (M := M)) {k m : Nat}
    (R : Formula (k+2)) (Hdom : Formula (k+1)) (env : Fin m → M.Carrier .set) (base : Fin k → Fin m) (rho : Fin 7 → Fin m)
    (I G F mul g q bound labels E objects maps root gluePr w names chain b : Fin m)
    {vertices objImage Q : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega (env w))
    (hNames : ForcingPowerName.Candidates (fun j => env (rho j)) (env G) (env F) (env bound) (env names))
    (hChain : MapsTo (env w) vertices (env chain))
    (hCommon : ∀ i vertex, PureKuratowski.PairMember M i vertex (env chain) →
      EncodedCommon (env (rho 0)) (env I) (env mul) (env q) (env root) vertex)
    (hDiagrams : ForcingDiagramCarrier.Carrier (env (rho 0)) (env I) (env (rho 4)))
    (hObjMap : MapsTo (env (rho 4)) objImage (env objects))
    (hObj : ForcingEligibleFamily.Family R Hdom (fun j => env (base j)) (fun j => env (rho j)) (env G) (env F) (env mul) (env g)
      (env q) (env bound) (env labels) (env E) (env (rho 4)) (env objects))
    (hAll : ForcingComponentGluing.AllFiberMaps (env (rho 0)) (env I) (env mul) (env q) (env objects) (env maps) (env root) Q (env gluePr))
    (hb : (Project.FirstOrderSemantics.reduct M).mem (env b) Q) :
    ∃ a, ChainCode (fun j => env (rho j)) (env G) (env F) (env bound) (env w) (env names) (env chain) a ∧
      Represents R Hdom (fun j => env (base j)) (fun j => env (rho j)) (env I) (env G) (env F) (env mul) (env g) (env q) (env bound)
        (env labels) (env E) (env objects) (env maps) (env root) (env gluePr) (env w) (env chain) a (env b) := by
  let schema : Project.BinarySchema m := {
    body := .existsE (.conj (ProjectSyntax.encode id (Source.SetLanguage.edge chain.succ.succ.succ 2 0))
      (atName R Hdom (fun j => (base j).succ.succ.succ) (fun j => (rho j).succ.succ.succ)
        I.succ.succ.succ G.succ.succ.succ F.succ.succ.succ mul.succ.succ.succ g.succ.succ.succ q.succ.succ.succ
        bound.succ.succ.succ labels.succ.succ.succ E.succ.succ.succ objects.succ.succ.succ maps.succ.succ.succ
        root.succ.succ.succ gluePr.succ.succ.succ 0 1 b.succ.succ.succ))
    freeClosed := by simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,atName_freeClosed] }
  let penv : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m := { bound := env, free := fun _ => env w }
  have he i sigma : schema.denote penv i sigma ↔ ∃ vertex, PureKuratowski.PairMember M i vertex (env chain) ∧
      At R Hdom (fun j => env (base j)) (fun j => env (rho j)) (env I) (env G) (env F) (env mul) (env g) (env q) (env bound)
        (env labels) (env E) (env objects) (env maps) (env root) (env gluePr) vertex sigma (env b) := by
    simp only [schema,Project.BinarySchema.denote,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,
      GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,atName_semantics hM]
    rfl
  obtain ⟨a,ha,hSelect⟩ := ExistingSmallUnion.uniformize_formula_l (KuratowskiZF.interpretation hM)
    (ConstructionDirectedCardinality.models_zfc hM hChoice) schema penv (X := env w) (Y := env names) (by
      intro i hi
      obtain ⟨vertex,hv,_⟩ := hChain.1.2 i hi
      obtain ⟨sigma,hs⟩ := at_total hM hDiagrams hObjMap hObj hAll (hCommon i vertex hv) hb
      obtain ⟨_,_,_,_,_,_,_,_,hLocal⟩ := at_entry hs
      exact ⟨sigma,(hNames sigma).mpr hLocal.1,(he i sigma).mpr ⟨vertex,hv,hs⟩⟩)
  have hMap := (ForcingSupportSize.native_mapsTo hM _ _ _).mpr ha
  refine ⟨a,⟨hMap,?_⟩,?_⟩
  · intro i sigma his
    obtain ⟨vertex,hv,hs⟩ := (he i sigma).mp (hSelect i sigma his)
    exact ⟨vertex,hv,at_entry hs⟩
  · obtain ⟨zero,_,hz⟩ := hw.1.1
    refine ⟨zero,hz,fun i hi _ => ?_⟩
    obtain ⟨sigma,his,_⟩ := hMap.1.2 i hi
    obtain ⟨vertex,hv,hs⟩ := (he i sigma).mp (hSelect i sigma his)
    exact ⟨vertex,sigma,hv,his,hs⟩


theorem exists_representing_code (hM : FirstOrder.Theory.Models M nativeZF)
    (hChoice : ConstructionDirectedCardinality.Choice (M := M)) {k : Nat}
    (R : Formula (k+2)) (Hdom : Formula (k+1)) (env : Fin k → M.Carrier .set) (rho : Fin 7 → Fin k)
    (I G F mul g q bound labels E objects maps root gluePr w names chain b : Fin k)
    {vertices objImage Q : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega (env w))
    (hNames : ForcingPowerName.Candidates (fun j => env (rho j)) (env G) (env F) (env bound) (env names))
    (hChain : MapsTo (env w) vertices (env chain))
    (hCommon : ∀ i vertex, PureKuratowski.PairMember M i vertex (env chain) →
      EncodedCommon (env (rho 0)) (env I) (env mul) (env q) (env root) vertex)
    (hDiagrams : ForcingDiagramCarrier.Carrier (env (rho 0)) (env I) (env (rho 4)))
    (hObjMap : MapsTo (env (rho 4)) objImage (env objects))
    (hObj : ForcingEligibleFamily.Family R Hdom env (fun j => env (rho j)) (env G) (env F) (env mul) (env g)
      (env q) (env bound) (env labels) (env E) (env (rho 4)) (env objects))
    (hAll : ForcingComponentGluing.AllFiberMaps (env (rho 0)) (env I) (env mul) (env q) (env objects) (env maps) (env root) Q (env gluePr))
    (hb : (Project.FirstOrderSemantics.reduct M).mem (env b) Q) :
    ∃ a, ChainCode (fun j => env (rho j)) (env G) (env F) (env bound) (env w) (env names) (env chain) a ∧
      Represents R Hdom env (fun j => env (rho j)) (env I) (env G) (env F) (env mul) (env g) (env q) (env bound)
        (env labels) (env E) (env objects) (env maps) (env root) (env gluePr) (env w) (env chain) a (env b) := by
  exact exists_representing_code_over hM hChoice R Hdom env id rho
    I G F mul g q bound labels E objects maps root gluePr w names chain b hw hNames hChain hCommon hDiagrams hObjMap hObj hAll hb


def candidates {m : Nat} (rho : Fin 7 → Fin m) (G F bound names : Fin m) : Project.Formula 1 m :=
  .forallE (.iff (.mem (.bound 0) (.bound names.succ)) (ProjectSyntax.encode id
    (ForcingPowerName.candidate (fun j => (rho j).succ) G.succ F.succ bound.succ 0)))

theorem candidates_freeClosed {m : Nat} (rho : Fin 7 → Fin m) (G F bound names : Fin m) :
    (candidates rho G F bound names).FreeClosed := by
  simp -implicitDefEqProofs [candidates,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed]

theorem candidates_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (rho : Fin 7 → Fin m) (G F bound names : Fin m) :
    Project.Formula.satisfies env (candidates rho G F bound names) ↔
      ForcingPowerName.Candidates (fun j => env.bound (rho j)) (env.bound G) (env.bound F) (env.bound bound) (env.bound names) := by
  simp only [candidates,ForcingPowerName.Candidates,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_iff_iff,
    Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),ForcingPowerName.candidate_semantics (M := M)]
  rfl

def constructionSentence {k : Nat} (rho : Fin 7 → Fin k) (I G F mul g q bound labels E objects maps root gluePr w names chain objImage Q P vertices zero b : Fin k) : Project.Sentence where
  formula := Project.Formula.forallClosure k
    (.imp (Project.Formula.isOmega (.bound w))
      (.imp (candidates rho G F bound names)
      (.imp (ConstructionComponentCofinal.chain w (rho 0) I mul q zero root vertices chain)
      (.imp (ProjectSyntax.encode id (ForcingDiagramCarrier.carrier (rho 0) I (rho 4)))
      (.imp (ProjectSyntax.encode id (Source.SetLanguage.mapsTo objects (rho 4) objImage))
      (.imp (ProjectSyntax.encode id (ForcingEligibleFamily.family (ForcingProductSymmetry.orderFormula (rho 0) mul) (ForcingPairUnion.domain rho G F) id rho G F mul g q bound labels E (rho 4) objects))
      (.imp (ForcingComponentGluing.allFiberMaps (rho 0) I mul q objects maps root Q gluePr)
      (.imp (ProjectSyntax.encode id (Source.SetLanguage.mapsTo gluePr P Q))
      (.imp (.mem (.bound b) (.bound Q))
      (.existsE (.existsE (.conj (carrier (fun j => (rho j).succ.succ) (G).succ.succ (F).succ.succ (bound).succ.succ (w).succ.succ (names).succ.succ (chain).succ.succ 1) (.conj (.mem (.bound 0) (.bound 1)) (.conj (represents (ForcingProductSymmetry.orderFormula (rho 0) mul) (ForcingPairUnion.domain rho G F) (fun j => (j).succ.succ) (fun j => (rho j).succ.succ) (I).succ.succ (G).succ.succ (F).succ.succ (mul).succ.succ (g).succ.succ (q).succ.succ (bound).succ.succ (labels).succ.succ (E).succ.succ (objects).succ.succ (maps).succ.succ (root).succ.succ (gluePr).succ.succ (w).succ.succ (chain).succ.succ 0 (b).succ.succ) (.forallE (.imp (represents (ForcingProductSymmetry.orderFormula (rho 0) mul) (ForcingPairUnion.domain rho G F) (fun j => (j).succ.succ.succ) (fun j => (rho j).succ.succ.succ) (I).succ.succ.succ (G).succ.succ.succ (F).succ.succ.succ (mul).succ.succ.succ (g).succ.succ.succ (q).succ.succ.succ (bound).succ.succ.succ (labels).succ.succ.succ (E).succ.succ.succ (objects).succ.succ.succ (maps).succ.succ.succ (root).succ.succ.succ (gluePr).succ.succ.succ (w).succ.succ.succ (chain).succ.succ.succ 1 0) (Project.Formula.extensionalEq (.bound 0) (.bound (b).succ.succ.succ))))))))))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,Project.Formula.isOmega,ProjectSyntax.freeClosed,
      candidates_freeClosed,ConstructionComponentCofinal.chain_freeClosed,ForcingComponentGluing.allFiberMaps_freeClosed,
      carrier_freeClosed,represents_freeClosed]

theorem construction_models {k : Nat} (rho : Fin 7 → Fin k) (I G F mul g q bound labels E objects maps root gluePr w names chain objImage Q P vertices zero b : Fin k)
    (hM : FirstOrder.Theory.Models M nativeZF) (hChoice : ConstructionDirectedCardinality.Choice (M := M)) :
    (Project.fo_sentence (constructionSentence rho I G F mul g q bound labels E objects maps root gluePr w names chain objImage Q P vertices zero b)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) (constructionSentence rho I G F mul g q bound labels E objects maps root gluePr w names chain objImage Q P vertices zero b)]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro env
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_isOmega_iff,Project.Formula.satisfies_mem_iff,
    Project.Formula.satisfies_extensionalEq_iff_eq (ModelTransfer.extensionality hM),Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    candidates_semantics hM,ConstructionComponentCofinal.chain_semantics hM,
    ForcingDiagramCarrier.carrier_semantics (M := M),ForcingSupportSize.mapsTo_semantics (M := M),
    ForcingEligibleFamily.family_semantics (M := M),ForcingComponentGluing.allFiberMaps_semantics hM,
    carrier_semantics hM,represents_semantics hM]
  intro hw hNames hChain hDiagrams hObjMap hObj hAll hGlue hb
  obtain ⟨codes,hCodes⟩ := exists_carrier hM env rho G F bound w names chain
  obtain ⟨a,ha,hRep⟩ := exists_representing_code hM hChoice (ForcingProductSymmetry.orderFormula (rho 0) mul) (ForcingPairUnion.domain rho G F) env rho
    I G F mul g q bound labels E objects maps root gluePr w names chain b hw hNames hChain.1 hChain.2.2.2.1
    hDiagrams hObjMap hObj hAll hb
  exact ⟨codes,a,hCodes,(hCodes a).mpr ha,hRep,fun c hc => represents_unique hM hw hChain.1 ha.1 hGlue hc hRep⟩

theorem construction_kernel_certificate {k : Nat} (rho : Fin 7 → Fin k) (I G F mul g q bound labels E objects maps root gluePr w names chain objImage Q P vertices zero b : Fin k) :
    FirstOrder.Derives nativeZF []
      (Project.fo_sentence (ConstructibleGround.relative (constructionSentence rho I G F mul g q bound labels E objects maps root gluePr w names chain objImage Q P vertices zero b))) := by
  apply ModelTransfer.derives
  intro M hM
  have hL := ConstructibleSource.model_zf hM
  have hRawChoice := (Project.FirstOrderSemantics.sentence_correct
    (ModelTransfer.extensionality hL) Axioms.choice).mp (ConstructibleSource.model_choice hM)
  let inhabitant := Classical.choice ((ConstructibleSource.model hM).nonempty .set)
  let env : SetTheory.Env (Project.FirstOrderSemantics.reduct (ConstructibleSource.model hM)) 0 :=
    { bound := Fin.elim0, free := fun _ => inhabitant }
  have hSat : Project.Formula.satisfies env (ConstructionDirectedCardinality.choice (m := 0)) := by
    change Project.Formula.satisfies env (Axioms.choice.formula.rename Fin.elim0)
    rw [Project.Formula.satisfies_rename]
    exact hRawChoice env.free
  have hChoice := (ConstructionDirectedCardinality.choice_semantics hL env).mp hSat
  apply ConstructibleGround.relative_models hM (constructionSentence rho I G F mul g q bound labels E objects maps root gluePr w names chain objImage Q P vertices zero b)
  exact (Project.FirstOrderSemantics.sentence_correct
    (ModelTransfer.extensionality hL) (constructionSentence rho I G F mul g q bound labels E objects maps root gluePr w names chain objImage Q P vertices zero b)).mp
      (construction_models rho I G F mul g q bound labels E objects maps root gluePr w names chain objImage Q P vertices zero b hL hChoice)

end PPAC.Migration.ForcingTailCodes
