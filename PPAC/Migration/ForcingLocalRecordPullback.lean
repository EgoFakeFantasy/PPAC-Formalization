/- Pinned LocalRecords.Condition.pullback/mem_pullback:19-31 and
permute_eq_of_pullback_eq:35-58. Actual consumer: LocalWitness.equal_of_record_eq,
then CodeCardinals.ordinalType_cardinal_le.single. Reuse native definable
functions, Separation, existing coordinate graphs and Entry/Moved/extensionality. -/
import PPAC.Migration.ForcingCohenCounting

namespace PPAC.Migration.ForcingLocalRecordPullback
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ForcingConditionGraphs (FunctionOn function_input function_unique CompositionGraph Permutation)
open ForcingCohenCoordinates (Cartesian Graph Lifted)
open ForcingCohenConditions (Condition)
open ForcingSupportSize (MapsTo Injection)
open ConstructionCohenCompatibility (Entry Moved)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
universe u
set_option maxRecDepth 16384
set_option maxHeartbeats 2000000
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

/-- Extend the existing coordinate graph to an injection between different carriers. -/
theorem lift_injection (hM : FirstOrder.Theory.Models M nativeZF) {A I B S T r : M.Carrier .set}
    (hS : Cartesian A B S) (hT : Cartesian I B T) (hr : Injection A I r) :
    ∃ f, Injection S T f ∧ Graph S r f := by
  have hZF := ModelTransfer.project_models_iff.mp hM
  let pair := KuratowskiZF.interpretation hM
  let params : Fin 1 → M.Carrier .set := fun _ => r
  let query := ForcingCohenCoordinates.lifted (0 : Fin 1).castSucc.castSucc (Fin.last 1).castSucc (Fin.last 2)
  let env : Env (Project.FirstOrderSemantics.reduct M) 1 := ⟨fun j => params j.rev,fun _ => S⟩
  have hRel z v : (ProjectSyntax.binary query).denote env z v ↔ Lifted r z v := by
    rw [ForcingMapConditions.binary_semantics hM query params S z v]
    simp only [ForcingMapConditions.MapRel,query,ForcingCohenCoordinates.lifted_semantics (M := M),params,
      Fin.lastCases_last,Fin.lastCases_castSucc]
  obtain ⟨f,hf,he⟩ := ZF.exists_setFunctionFromTo_of_denote hZF pair (ProjectSyntax.binary query) env
    (source := S) (target := T)
    (by
      intro z hz
      obtain ⟨a,ha,b,_,hz⟩ := (hS z).mp hz
      obtain ⟨i,hai,_⟩ := hr.1.1.2 a ha
      obtain ⟨v,hv⟩ := pair.total i b
      exact ⟨v,(hRel z v).mpr ⟨a,b,i,hz,hai,hv⟩⟩)
    (by
      intro z _ v t hv ht
      obtain ⟨a,b,i,hz,hai,hv⟩ := (hRel z v).mp hv
      obtain ⟨a',b',j,hz',haj,ht⟩ := (hRel z t).mp ht
      obtain ⟨rfl,rfl⟩ := PureKuratowski.code_injective hz hz'
      exact pair.unique hv (function_unique hr.1.1 hai haj ▸ ht))
    (by
      intro z v hz hv
      obtain ⟨a,_,b,hb,hz⟩ := (hS z).mp hz
      obtain ⟨a',b',i,hz',hai,hv⟩ := (hRel z v).mp hv
      obtain ⟨rfl,rfl⟩ := PureKuratowski.code_injective hz hz'
      exact (hT v).mpr ⟨i,hr.1.2 a i hai,b,hb,hv⟩)
  have hgraph : Graph S r f := fun z v => (he z v).trans (and_congr Iff.rfl (hRel z v))
  refine ⟨f,⟨(ForcingSupportSize.native_mapsTo hM S T f).mpr hf,?_⟩,hgraph⟩
  intro z t v hz ht
  obtain ⟨_,a,b,i,hz,hai,hv⟩ := (hgraph z v).mp hz
  obtain ⟨_,a',b',i',ht,ha'i',hv'⟩ := (hgraph t v).mp ht
  obtain ⟨rfl,rfl⟩ := PureKuratowski.code_injective hv hv'
  exact pair.unique hz (hr.2 a a' i hai ha'i' ▸ ht)

/-- Exact inverse image of the condition graph under the actual coordinate injection. -/
def Preimage (S g p q : M.Carrier .set) : Prop :=
  ∀ z, (Project.FirstOrderSemantics.reduct M).mem z q ↔
    (Project.FirstOrderSemantics.reduct M).mem z S ∧
      ∃ v, PureKuratowski.PairMember M z v g ∧ (Project.FirstOrderSemantics.reduct M).mem v p

theorem exists_preimage (hM : FirstOrder.Theory.Models M nativeZF) (S g p : M.Carrier .set) :
    ∃ q, Preimage S g p q := by
  let env : Env (Project.FirstOrderSemantics.reduct M) 2 := (⟨fun _ => g,fun _ => p⟩ : Env _ 1).push p
  let schema : Project.UnarySchema 2 := {body := .existsE (.conj
    (Project.Formula.orderedPairMem PureKuratowskiProject.convention (.bound 1) .newest (.bound 3))
    (.mem .newest (.bound 2)))}
  obtain ⟨q,hq⟩ := ZF.separation_exists_d (ModelTransfer.project_models_iff.mp hM) schema env S
  refine ⟨q,fun z => ?_⟩
  rw [hq z]
  simp only [schema,Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_mem_iff,
    Project.Formula.satisfies_orderedPairMem_iff (KuratowskiZF.interpretation hM)]
  rfl

theorem preimage_condition (hM : FirstOrder.Theory.Models M nativeZF) {C D S T w f g p q : M.Carrier .set}
    (hf : MapsTo C D f) (hg : Injection S T g)
    (hgraph : Graph S f g) (hp : Condition T w p) (hq : Preimage S g p q) : Condition S w q := by
  have hZF := ModelTransfer.project_models_iff.mp hM
  let pair := KuratowskiZF.interpretation hM
  have hsub : (Project.FirstOrderSemantics.reduct M).MemberSubset q S := fun z hz => ((hq z).mp hz).1
  have hfunctional : ForcingCohenConditions.Functional q := by
    intro a b c hab hac
    obtain ⟨z,hz,hzq⟩ := hab
    obtain ⟨t,ht,htq⟩ := hac
    obtain ⟨_,v,hzv,hvp⟩ := (hq z).mp hzq
    obtain ⟨_,u,htu,hup⟩ := (hq t).mp htq
    obtain ⟨_,a',b',j,hz',haj,hv⟩ := (hgraph z v).mp hzv
    obtain ⟨rfl,rfl⟩ := PureKuratowski.code_injective hz hz'
    obtain ⟨_,a'',c',j',ht',haj',hu⟩ := (hgraph t u).mp htu
    obtain ⟨rfl,rfl⟩ := PureKuratowski.code_injective ht ht'
    have hj := function_unique hf.1 haj haj'
    exact hp.2.1 j b c ⟨v,hv,hvp⟩ (hj.symm ▸ (show PureKuratowski.PairMember M j' c p from ⟨u,hu,hup⟩))
  let env : Env (Project.FirstOrderSemantics.reduct M) 1 := ⟨fun _ => g,fun _ => g⟩
  let schema : Project.BinarySchema 1 := {body := Project.Formula.orderedPairMem PureKuratowskiProject.convention (.bound 1) .newest (.bound 2)}
  have hvalue x y : schema.denote env x y ↔ PureKuratowski.PairMember M x y g := by
    simp only [schema,Project.BinarySchema.denote,Project.Formula.satisfies_orderedPairMem_iff pair]
    rfl
  obtain ⟨J,hJ⟩ := ZF.exists_setInjectionFromTo_of_denote hZF pair schema env (source := q) (target := p)
    (by intro z hz; obtain ⟨_,v,hzv,_⟩ := (hq z).mp hz; exact ⟨v,(hvalue z v).mpr hzv⟩)
    (fun _ _ _ _ hx hy => function_unique hg.1.1 ((hvalue _ _).mp hx) ((hvalue _ _).mp hy))
    (by
      intro z v hz hzv
      obtain ⟨_,u,hzu,hup⟩ := (hq z).mp hz
      exact function_unique hg.1.1 hzu ((hvalue z v).mp hzv) ▸ hup)
    (fun x y z _ _ hx hy => hg.2 x y z ((hvalue x z).mp hx) ((hvalue y z).mp hy))
  obtain ⟨K,hK⟩ := (ForcingSupportSize.native_small hM p w).mp hp.2.2
  exact ⟨hsub,hfunctional,(ForcingSupportSize.native_small hM q w).mpr (ZF.exists_compositionInjection hZF pair hJ hK)⟩

/-- Literal source pullback, exposing labels, levels and bits instead of auxiliary graphs. -/
def Pullback (A r p q : M.Carrier .set) : Prop :=
  ∀ a k b, Entry q a k b ↔ (Project.FirstOrderSemantics.reduct M).mem a A ∧
    ∃ i, PureKuratowski.PairMember M a i r ∧ Entry p i k b

def pullback {m : Nat} (A r p q : Fin m) : Project.Formula 1 m :=
  .forallE (.forallE (.forallE (.iff
    (ConstructionCohenCompatibility.entry q.succ.succ.succ 2 1 0)
    (.conj (.mem (.bound 2) (.bound A.succ.succ.succ))
      (.existsE (.conj (Project.Formula.orderedPairMem PureKuratowskiProject.convention (.bound 3) .newest (.bound r.succ.succ.succ.succ))
        (ConstructionCohenCompatibility.entry p.succ.succ.succ.succ 0 2 1)))))))

theorem pullback_freeClosed {m : Nat} (A r p q : Fin m) : (pullback A r p q).FreeClosed := by
  simp -implicitDefEqProofs [pullback,Definitional.Formula.FreeClosed,ConstructionCohenCompatibility.entry_freeClosed]

theorem pullback_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : Env (Project.FirstOrderSemantics.reduct M) m) (A r p q : Fin m) :
    Project.Formula.satisfies env (pullback A r p q) ↔ Pullback (env.bound A) (env.bound r) (env.bound p) (env.bound q) := by
  simp only [pullback,Pullback,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_iff_iff,
    Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_mem_iff,Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_orderedPairMem_iff (KuratowskiZF.interpretation hM),ConstructionCohenCompatibility.entry_semantics hM]
  rfl

theorem preimage_pullback (hM : FirstOrder.Theory.Models M nativeZF) {A I K B C S D T w r f g p q : M.Carrier .set}
    (hC : Cartesian A K C) (hS : Cartesian C B S) (hD : Cartesian I K D) (hT : Cartesian D B T)
    (hf : Graph C r f) (hg : Graph S f g) (hp : Condition T w p) (hq : Preimage S g p q) : Pullback A r p q := by
  intro a k b
  constructor
  · rintro ⟨c,hc,z,hz,hzq⟩
    obtain ⟨hzS,v,hzv,hvp⟩ := (hq z).mp hzq
    obtain ⟨c',hcC,b',_,hz'⟩ := (hS z).mp hzS
    obtain ⟨rfl,rfl⟩ := PureKuratowski.code_injective hz hz'
    obtain ⟨a',ha,k',_,hc'⟩ := (hC c).mp hcC
    obtain ⟨rfl,rfl⟩ := PureKuratowski.code_injective hc hc'
    obtain ⟨_,c'',b'',d,hz'',hcd,hv⟩ := (hg z v).mp hzv
    obtain ⟨rfl,rfl⟩ := PureKuratowski.code_injective hz hz''
    obtain ⟨_,a'',k'',i,hc'',hai,hd⟩ := (hf c d).mp hcd
    obtain ⟨rfl,rfl⟩ := PureKuratowski.code_injective hc hc''
    exact ⟨ha,i,hai,d,hd,v,hv,hvp⟩
  · rintro ⟨ha,i,hai,he⟩
    have ht := ConstructionCohenCompatibility.entry_typed hD hT hp he
    obtain ⟨d,hd,v,hv,hvp⟩ := he
    obtain ⟨c,hc⟩ := KuratowskiZF.exists_code hM a k
    obtain ⟨z,hz⟩ := KuratowskiZF.exists_code hM c b
    have hcC := (hC c).mpr ⟨a,ha,k,ht.2.1,hc⟩
    have hzS := (hS z).mpr ⟨c,hcC,b,ht.2.2,hz⟩
    have hcd := (hf c d).mpr ⟨hcC,a,k,i,hc,hai,hd⟩
    exact ⟨c,hc,z,hz,(hq z).mpr ⟨hzS,v,(hg z v).mpr ⟨hzS,c,b,d,hz,hcd,hv⟩,hvp⟩⟩

theorem exists_pullback (hM : FirstOrder.Theory.Models M nativeZF) {A I K B C S D T w r p : M.Carrier .set}
    (hC : Cartesian A K C) (hS : Cartesian C B S) (hD : Cartesian I K D) (hT : Cartesian D B T)
    (hr : Injection A I r) (hp : Condition T w p) : ∃ q, Condition S w q ∧ Pullback A r p q := by
  obtain ⟨f,hf,hfg⟩ := lift_injection hM hC hD hr
  obtain ⟨g,hg,hgg⟩ := lift_injection hM hS hT hf
  obtain ⟨q,hq⟩ := exists_preimage hM S g p
  exact ⟨q,preimage_condition hM hf.1 hg hgg hp hq,preimage_pullback hM hC hS hD hT hfg hgg hp hq⟩


/-- The source condition support is contained in the range of the diagram. -/
def Supported (A r p : M.Carrier .set) : Prop :=
  ∀ i k b, Entry p i k b → ∃ a, (Project.FirstOrderSemantics.reduct M).mem a A ∧ PureKuratowski.PairMember M a i r

def supported {m : Nat} (A r p : Fin m) : Project.Formula 1 m :=
  .forallE (.forallE (.forallE (.imp (ConstructionCohenCompatibility.entry p.succ.succ.succ 2 1 0)
    (.existsE (.conj (.mem .newest (.bound A.succ.succ.succ.succ))
      (Project.Formula.orderedPairMem PureKuratowskiProject.convention .newest (.bound 3) (.bound r.succ.succ.succ.succ)))))))

theorem supported_freeClosed {m : Nat} (A r p : Fin m) : (supported A r p).FreeClosed := by
  simp -implicitDefEqProofs [supported,Definitional.Formula.FreeClosed,ConstructionCohenCompatibility.entry_freeClosed]

theorem supported_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : Env (Project.FirstOrderSemantics.reduct M) m) (A r p : Fin m) :
    Project.Formula.satisfies env (supported A r p) ↔ Supported (env.bound A) (env.bound r) (env.bound p) := by
  simp only [supported,Supported,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_imp_iff,
    Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_mem_iff,Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_orderedPairMem_iff (KuratowskiZF.interpretation hM),ConstructionCohenCompatibility.entry_semantics hM]
  rfl

theorem supported_iff {A r p H : M.Carrier .set} (hH : ConstructionCohenCompatibility.Support p H) :
    Supported A r p ↔ ∀ i, (Project.FirstOrderSemantics.reduct M).mem i H →
      ∃ a, (Project.FirstOrderSemantics.reduct M).mem a A ∧ PureKuratowski.PairMember M a i r := by
  constructor
  · intro h i hi; obtain ⟨k,b,he⟩ := (hH i).mp hi; exact h i k b he
  · intro h i k b he; exact h i ((hH i).mpr ⟨k,b,he⟩)

theorem pullback_unique (hM : FirstOrder.Theory.Models M nativeZF) {A K C B S w r p q t : M.Carrier .set}
    (hC : Cartesian A K C) (hS : Cartesian C B S) (hq : Condition S w q) (ht : Condition S w t)
    (hqpb : Pullback A r p q) (htpb : Pullback A r p t) : q = t :=
  ConstructionCohenCompatibility.entries_ext hM hC hS hq ht (fun a k b => (hqpb a k b).trans (htpb a k b).symm)

/-- Exact source record comparison before applying the existing coordinate action. -/
theorem moved_of_equal_pullbacks {A r s pi p q pb : M.Carrier .set}
    (hr : FunctionOn A r) (hs : FunctionOn A s) (hmatch : CompositionGraph A pi r s)
    (hp : Supported A r p) (hq : Supported A s q)
    (hpr : Pullback A r p pb) (hqs : Pullback A s q pb) : Moved pi p q := by
  intro j k b
  constructor
  · intro he
    obtain ⟨a,ha,haj⟩ := hq j k b he
    have hpb := (hqs a k b).mpr ⟨ha,j,haj,he⟩
    obtain ⟨_,i,hai,hpi⟩ := (hmatch a j).mp haj
    obtain ⟨_,i',hai',he'⟩ := (hpr a k b).mp hpb
    exact ⟨i,hpi,function_unique hr hai hai' ▸ he'⟩
  · rintro ⟨i,hij,he⟩
    obtain ⟨a,ha,hai⟩ := hp i k b he
    have haj := (hmatch a j).mpr ⟨ha,i,hai,hij⟩
    have hpb := (hpr a k b).mpr ⟨ha,i,hai,he⟩
    obtain ⟨_,j',haj',he'⟩ := (hqs a k b).mp hpb
    exact function_unique hs haj haj' ▸ he'

/-- The SAME internal coordinate permutation sends p to q; no quotient equality is assumed. -/
theorem transport (hM : FirstOrder.Theory.Models M nativeZF) {A I K B C S w r s pi p q pb : M.Carrier .set}
    (hC : Cartesian I K C) (hS : Cartesian C B S) (hr : Injection A I r) (hs : Injection A I s)
    (hpi : Permutation I pi) (hmatch : CompositionGraph A pi r s)
    (hp : Condition S w p) (hq : Condition S w q) (hpS : Supported A r p) (hqS : Supported A s q)
    (hpr : Pullback A r p pb) (hqs : Pullback A s q pb) :
    ∃ f g, Permutation C f ∧ Graph C pi f ∧ Permutation S g ∧ Graph S f g ∧
      ForcingStabilizerTransport.Image g p q ∧ Moved pi p q := by
  have hm := moved_of_equal_pullbacks hr.1.1 hs.1.1 hmatch hpS hqS hpr hqs
  obtain ⟨f,g,t,hf,hfg,hg,hgg,ht,him,hmt⟩ := ConstructionCohenCompatibility.exists_moved hM hC hS hpi hp
  have he : t = q := ConstructionCohenCompatibility.entries_ext hM hC hS ht hq
    (fun i k b => (hmt i k b).trans (hm i k b).symm)
  exact ⟨f,g,hf,hfg,hg,hgg,he ▸ him,hm⟩

def constructionSentence : Project.Sentence where
  formula := Project.Formula.forallClosure 11 (.imp (ProjectSyntax.encode id (ForcingCohenCoordinates.cartesian (0 : Fin 11) 2 4))
    (.imp (ProjectSyntax.encode id (ForcingCohenCoordinates.cartesian (4 : Fin 11) 3 5))
    (.imp (ProjectSyntax.encode id (ForcingCohenCoordinates.cartesian (1 : Fin 11) 2 6))
    (.imp (ProjectSyntax.encode id (ForcingCohenCoordinates.cartesian (6 : Fin 11) 3 7))
    (.imp (ProjectSyntax.encode id (Source.SetLanguage.injection (9 : Fin 11) 0 1))
    (.imp (ProjectSyntax.encode id (ForcingCohenConditions.condition (7 : Fin 11) 8 10))
    (.existsE (.conj (ProjectSyntax.encode id (ForcingCohenConditions.condition (6 : Fin 12) 9 0)) (pullback (1 : Fin 12) 10 11 0)))))))))
  freeClosed := by simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,pullback_freeClosed]

theorem construction_models (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.FirstOrderSemantics.reduct M).SatisfiesSentence constructionSentence := by
  apply (Structure.satisfiesSentence_iff _ _).mpr
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingCohenCoordinates.cartesian_semantics (M := M),ForcingSupportSize.injection_semantics (M := M),
    ForcingCohenConditions.condition_semantics (M := M),Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,
    pullback_semantics hM]
  exact fun hC hS hD hT hr hp => exists_pullback hM hC hS hD hT hr hp

theorem construction_kernel_certificate : FirstOrder.Derives nativeZF [] (Project.fo_sentence constructionSentence) := by
  apply ModelTransfer.derives
  intro N hN
  exact (Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hN) constructionSentence).mpr (construction_models hN)

def transportSentence : Project.Sentence where
  formula := Project.Formula.forallClosure 13 (.imp (ProjectSyntax.encode id (ForcingCohenCoordinates.cartesian (1 : Fin 13) 2 4))
    (.imp (ProjectSyntax.encode id (ForcingCohenCoordinates.cartesian (4 : Fin 13) 3 5))
    (.imp (ProjectSyntax.encode id (Source.SetLanguage.injection (7 : Fin 13) 0 1))
    (.imp (ProjectSyntax.encode id (Source.SetLanguage.injection (8 : Fin 13) 0 1))
    (.imp (ProjectSyntax.encode id (ForcingConditionGraphs.permutation (1 : Fin 13) 9))
    (.imp (ProjectSyntax.encode id (ForcingConditionGraphs.compositionGraph (0 : Fin 13) 9 7 8))
    (.imp (ProjectSyntax.encode id (ForcingCohenConditions.condition (5 : Fin 13) 6 10))
    (.imp (ProjectSyntax.encode id (ForcingCohenConditions.condition (5 : Fin 13) 6 11))
    (.imp (supported (0 : Fin 13) 7 10)
    (.imp (supported (0 : Fin 13) 8 11)
    (.imp (pullback (0 : Fin 13) 7 10 12)
    (.imp (pullback (0 : Fin 13) 8 11 12)
    (.existsE (.existsE (.conj (ProjectSyntax.encode id (ForcingConditionGraphs.permutation (6 : Fin 15) 1))
      (.conj (ProjectSyntax.encode id (ForcingCohenCoordinates.graph (6 : Fin 15) 11 1))
      (.conj (ProjectSyntax.encode id (ForcingConditionGraphs.permutation (7 : Fin 15) 0))
      (.conj (ProjectSyntax.encode id (ForcingCohenCoordinates.graph (7 : Fin 15) 1 0))
      (.conj (ProjectSyntax.encode id (ForcingStabilizerTransport.image (0 : Fin 15) 12 13))
      (ConstructionCohenCompatibility.moved (11 : Fin 15) 12 13))))))))))))))))))))
  freeClosed := by simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,pullback_freeClosed,supported_freeClosed,ConstructionCohenCompatibility.moved_freeClosed]

theorem transport_models (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.FirstOrderSemantics.reduct M).SatisfiesSentence transportSentence := by
  apply (Structure.satisfiesSentence_iff _ _).mpr
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingCohenCoordinates.cartesian_semantics (M := M),ForcingSupportSize.injection_semantics (M := M),
    ForcingConditionGraphs.permutation_semantics (M := M),ForcingConditionGraphs.compositionGraph_semantics (M := M),
    ForcingCohenConditions.condition_semantics (M := M),supported_semantics hM,pullback_semantics hM,
    Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,ForcingCohenCoordinates.graph_semantics (M := M),
    ForcingStabilizerTransport.image_semantics (M := M),ConstructionCohenCompatibility.moved_semantics hM]
  exact fun hC hS hr hs hpi hm hp hq hps hqs hpr hqr => transport hM hC hS hr hs hpi hm hp hq hps hqs hpr hqr

theorem transport_kernel_certificate : FirstOrder.Derives nativeZF [] (Project.fo_sentence transportSentence) := by
  apply ModelTransfer.derives
  intro N hN
  exact (Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hN) transportSentence).mpr (transport_models hN)

end PPAC.Migration.ForcingLocalRecordPullback
