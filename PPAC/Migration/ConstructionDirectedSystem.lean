/- Pinned DirectLimits.ConservativeLimit: underlying source DirectedSystem.
ALL internal set-indexed directed PREORDERS, varying stage carriers and real
transition FUNCTION GRAPHS. Exact common-future equality; not transitive
closure or a fixed-carrier/omega specialization. Consumer: actual limit
carrier/projection, of_map/of_injective and common-stage multiplication. -/
import PPAC.Migration.ForcingDiagramOrder
import PPAC.Migration.ForcingMapConditions

namespace PPAC.Migration.ConstructionDirectedSystem
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ForcingDiagramOrder (Product)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

/-- x is in the ACTUAL carrier displayed at stage i by Domains. -/
def At (J Domains i x : M.Carrier .set) : Prop :=
  (Project.FirstOrderSemantics.reduct M).mem i J ∧ ∃ D,
    PureKuratowski.PairMember M i D Domains ∧ (Project.FirstOrderSemantics.reduct M).mem x D

/-- F(i,j) is the actual graph of the transition, not a chosen value oracle. -/
def Transition (J Domains F i j x y : M.Carrier .set) : Prop :=
  At J Domains i x ∧ At J Domains j y ∧
    ∃ f, Product F i j f ∧ PureKuratowski.PairMember M x y f

def IndexLaws (J E : M.Carrier .set) : Prop :=
  (∀ i, (Project.FirstOrderSemantics.reduct M).mem i J → PureKuratowski.PairMember M i i E) ∧
  (∀ i j k, (Project.FirstOrderSemantics.reduct M).mem i J →
    (Project.FirstOrderSemantics.reduct M).mem j J → (Project.FirstOrderSemantics.reduct M).mem k J →
    PureKuratowski.PairMember M i j E → PureKuratowski.PairMember M j k E → PureKuratowski.PairMember M i k E) ∧
  ∀ i j, (Project.FirstOrderSemantics.reduct M).mem i J → (Project.FirstOrderSemantics.reduct M).mem j J →
    ∃ k, (Project.FirstOrderSemantics.reduct M).mem k J ∧ PureKuratowski.PairMember M i k E ∧ PureKuratowski.PairMember M j k E

/-- Exactly totality/functionality, identity and composition from the source
family of transition maps. Injectivity is deliberately NOT a premise. -/
def TransitionLaws (J E Domains F : M.Carrier .set) : Prop :=
  (∀ i j x, At J Domains i x → (Project.FirstOrderSemantics.reduct M).mem j J →
    PureKuratowski.PairMember M i j E → ∃ y, Transition J Domains F i j x y) ∧
  (∀ i j x y z, PureKuratowski.PairMember M i j E →
    Transition J Domains F i j x y → Transition J Domains F i j x z → y = z) ∧
  (∀ i x, At J Domains i x → Transition J Domains F i i x x) ∧
  ∀ i j k x y z, PureKuratowski.PairMember M i j E → PureKuratowski.PairMember M j k E →
    Transition J Domains F i j x y → Transition J Domains F j k y z → Transition J Domains F i k x z

def Meets (J E Domains F i x j y : M.Carrier .set) : Prop :=
  At J Domains i x ∧ At J Domains j y ∧ ∃ k z,
    (Project.FirstOrderSemantics.reduct M).mem k J ∧ PureKuratowski.PairMember M i k E ∧
    PureKuratowski.PairMember M j k E ∧ Transition J Domains F i k x z ∧ Transition J Domains F j k y z

def InjectiveTransitions (J E Domains F : M.Carrier .set) : Prop :=
  ∀ i j x y z, PureKuratowski.PairMember M i j E →
    Transition J Domains F i j x z → Transition J Domains F i j y z → x = y

theorem meets_refl {J E Domains F i x : M.Carrier .set}
    (hE : IndexLaws J E) (hT : TransitionLaws J E Domains F) (hx : At J Domains i x) :
    Meets J E Domains F i x i x :=
  ⟨hx,hx,i,x,hx.1,hE.1 i hx.1,hE.1 i hx.1,hT.2.2.1 i x hx,hT.2.2.1 i x hx⟩

theorem meets_symm {J E Domains F i x j y : M.Carrier .set}
    (h : Meets J E Domains F i x j y) : Meets J E Domains F j y i x := by
  obtain ⟨hx,hy,k,z,hk,hik,hjk,hi,hj⟩ := h
  exact ⟨hy,hx,k,z,hk,hjk,hik,hj,hi⟩

theorem meets_trans {J E Domains F i x j y k z : M.Carrier .set}
    (hE : IndexLaws J E) (hT : TransitionLaws J E Domains F)
    (hxy : Meets J E Domains F i x j y) (hyz : Meets J E Domains F j y k z) :
    Meets J E Domains F i x k z := by
  obtain ⟨hx,hy,a,v,ha,hia,hja,hxv,hyv⟩ := hxy
  obtain ⟨_,hz,b,t,hb,hjb,hkb,hyt,hzt⟩ := hyz
  obtain ⟨c,hc,hac,hbc⟩ := hE.2.2 a b ha hb
  obtain ⟨v',hvv⟩ := hT.1 a c v hxv.2.1 hc hac
  obtain ⟨t',htt⟩ := hT.1 b c t hyt.2.1 hc hbc
  have hjc := hE.2.1 j a c hy.1 ha hc hja hac
  have hvv' := hT.2.2.2 j a c y v v' hja hac hyv hvv
  have htt' := hT.2.2.2 j b c y t t' hjb hbc hyt htt
  have he := hT.2.1 j c y v' t' hjc hvv' htt'
  subst t'
  exact ⟨hx,hz,c,v',hc,hE.2.1 i a c hx.1 ha hc hia hac,hE.2.1 k b c hz.1 hb hc hkb hbc,
    hT.2.2.2 i a c x v v' hia hac hxv hvv,hT.2.2.2 k b c z t v' hkb hbc hzt htt⟩

theorem transition_meets {J E Domains F i x j y : M.Carrier .set}
    (hE : IndexLaws J E) (hT : TransitionLaws J E Domains F)
    (hij : PureKuratowski.PairMember M i j E) (hxy : Transition J Domains F i j x y) :
    Meets J E Domains F i x j y :=
  ⟨hxy.1,hxy.2.1,j,y,hxy.2.1.1,hij,hE.1 j hxy.2.1.1,hxy,hT.2.2.1 j y hxy.2.1⟩

/-- Source same-stage equality reflection uses precisely injective transitions. -/
theorem meets_same_iff {J E Domains F i x y : M.Carrier .set}
    (hE : IndexLaws J E) (hT : TransitionLaws J E Domains F)
    (hI : InjectiveTransitions J E Domains F) (hx : At J Domains i x) :
    Meets J E Domains F i x i y ↔ x = y := by
  constructor
  · rintro ⟨_,_,k,z,_,hik,_,hxz,hyz⟩
    exact hI i k x y z hik hxz hyz
  · intro he
    subst y
    exact meets_refl hE hT hx

def atStage {m : Nat} (J Domains i x : Fin m) : Project.Formula 1 m :=
  (.conj (.mem (.bound i) (.bound J)) (.existsE (.conj (ProjectSyntax.encode id (Source.SetLanguage.edge
  (Domains).succ (i).succ (0 : Fin (m+1)))) (.mem (.bound (x).succ) (.bound (0 : Fin (m+1)))))))

theorem atStage_freeClosed {m : Nat} (J Domains i x : Fin m) : (atStage J Domains i x).FreeClosed := by
  simp -implicitDefEqProofs [atStage,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed]

theorem atStage_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (J Domains i x : Fin m) :
    Project.Formula.satisfies env (atStage J Domains i x) ↔ At (env.bound J) (env.bound Domains) (env.bound i) (env.bound x) := by
  simp only [atStage,At,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge]
  rfl

def transition {m : Nat} (J Domains F i j x y : Fin m) : Project.Formula 1 m :=
  (.conj (atStage J Domains i x) (.conj (atStage J Domains j y) (.existsE (.conj (ProjectSyntax.encode id
  (ForcingDiagramOrder.product (F).succ (i).succ (j).succ (0 : Fin (m+1)))) (ProjectSyntax.encode id
  (Source.SetLanguage.edge (0 : Fin (m+1)) (x).succ (y).succ))))))

theorem transition_freeClosed {m : Nat} (J Domains F i j x y : Fin m) : (transition J Domains F i j x y).FreeClosed := by
  simp -implicitDefEqProofs [transition,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,atStage_freeClosed]

theorem transition_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (J Domains F i j x y : Fin m) :
    Project.Formula.satisfies env (transition J Domains F i j x y) ↔ Transition (env.bound J) (env.bound Domains) (env.bound F) (env.bound i) (env.bound j) (env.bound x) (env.bound y) := by
  simp only [transition,Transition,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,ForcingDiagramOrder.product_semantics (M := M),atStage_semantics hM]
  rfl

def indexLaws {m : Nat} (J E : Fin m) : Project.Formula 1 m :=
  (.conj (.forallE (.imp (.mem (.bound (0 : Fin (m+1))) (.bound (J).succ)) (ProjectSyntax.encode id
  (Source.SetLanguage.edge (E).succ (0 : Fin (m+1)) (0 : Fin (m+1)))))) (.conj (.forallE (.forallE
  (.forallE (.imp (.mem (.bound (((0 : Fin (m+1))).succ).succ) (.bound (((J).succ).succ).succ)) (.imp
  (.mem (.bound ((0 : Fin (m+2))).succ) (.bound (((J).succ).succ).succ)) (.imp (.mem (.bound (0 : Fin
  (m+3))) (.bound (((J).succ).succ).succ)) (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge
  (((E).succ).succ).succ (((0 : Fin (m+1))).succ).succ ((0 : Fin (m+2))).succ)) (.imp
  (ProjectSyntax.encode id (Source.SetLanguage.edge (((E).succ).succ).succ ((0 : Fin (m+2))).succ (0 :
  Fin (m+3)))) (ProjectSyntax.encode id (Source.SetLanguage.edge (((E).succ).succ).succ (((0 : Fin
  (m+1))).succ).succ (0 : Fin (m+3)))))))))))) (.forallE (.forallE (.imp (.mem (.bound ((0 : Fin
  (m+1))).succ) (.bound ((J).succ).succ)) (.imp (.mem (.bound (0 : Fin (m+2))) (.bound ((J).succ).succ))
  (.existsE (.conj (.mem (.bound (0 : Fin (m+3))) (.bound (((J).succ).succ).succ)) (.conj
  (ProjectSyntax.encode id (Source.SetLanguage.edge (((E).succ).succ).succ (((0 : Fin (m+1))).succ).succ
  (0 : Fin (m+3)))) (ProjectSyntax.encode id (Source.SetLanguage.edge (((E).succ).succ).succ ((0 : Fin
  (m+2))).succ (0 : Fin (m+3)))))))))))))

theorem indexLaws_freeClosed {m : Nat} (J E : Fin m) : (indexLaws J E).FreeClosed := by
  simp -implicitDefEqProofs [indexLaws,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed]

theorem indexLaws_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (J E : Fin m) :
    Project.Formula.satisfies env (indexLaws J E) ↔ IndexLaws (env.bound J) (env.bound E) := by
  simp only [indexLaws,IndexLaws,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge]
  rfl

def transitionLaws {m : Nat} (J E Domains F : Fin m) : Project.Formula 1 m :=
  (.conj (.forallE (.forallE (.forallE (.imp (atStage (((J).succ).succ).succ (((Domains).succ).succ).succ (((0 :
  Fin (m+1))).succ).succ (0 : Fin (m+3))) (.imp (.mem (.bound ((0 : Fin (m+2))).succ) (.bound
  (((J).succ).succ).succ)) (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge (((E).succ).succ).succ
  (((0 : Fin (m+1))).succ).succ ((0 : Fin (m+2))).succ)) (.existsE (transition
  ((((J).succ).succ).succ).succ ((((Domains).succ).succ).succ).succ ((((F).succ).succ).succ).succ ((((0 :
  Fin (m+1))).succ).succ).succ (((0 : Fin (m+2))).succ).succ ((0 : Fin (m+3))).succ (0 : Fin
  (m+4)))))))))) (.conj (.forallE (.forallE (.forallE (.forallE (.forallE (.imp (ProjectSyntax.encode id
  (Source.SetLanguage.edge (((((E).succ).succ).succ).succ).succ (((((0 : Fin
  (m+1))).succ).succ).succ).succ ((((0 : Fin (m+2))).succ).succ).succ)) (.imp (transition
  (((((J).succ).succ).succ).succ).succ (((((Domains).succ).succ).succ).succ).succ
  (((((F).succ).succ).succ).succ).succ (((((0 : Fin (m+1))).succ).succ).succ).succ ((((0 : Fin
  (m+2))).succ).succ).succ (((0 : Fin (m+3))).succ).succ ((0 : Fin (m+4))).succ) (.imp (transition
  (((((J).succ).succ).succ).succ).succ (((((Domains).succ).succ).succ).succ).succ
  (((((F).succ).succ).succ).succ).succ (((((0 : Fin (m+1))).succ).succ).succ).succ ((((0 : Fin
  (m+2))).succ).succ).succ (((0 : Fin (m+3))).succ).succ (0 : Fin (m+5))) (Project.Formula.extensionalEq
  (.bound ((0 : Fin (m+4))).succ) (.bound (0 : Fin (m+5)))))))))))) (.conj (.forallE (.forallE (.imp (atStage
  ((J).succ).succ ((Domains).succ).succ ((0 : Fin (m+1))).succ (0 : Fin (m+2))) (transition
  ((J).succ).succ ((Domains).succ).succ ((F).succ).succ ((0 : Fin (m+1))).succ ((0 : Fin (m+1))).succ (0
  : Fin (m+2)) (0 : Fin (m+2)))))) (.forallE (.forallE (.forallE (.forallE (.forallE (.forallE (.imp
  (ProjectSyntax.encode id (Source.SetLanguage.edge ((((((E).succ).succ).succ).succ).succ).succ ((((((0 :
  Fin (m+1))).succ).succ).succ).succ).succ (((((0 : Fin (m+2))).succ).succ).succ).succ)) (.imp
  (ProjectSyntax.encode id (Source.SetLanguage.edge ((((((E).succ).succ).succ).succ).succ).succ (((((0 :
  Fin (m+2))).succ).succ).succ).succ ((((0 : Fin (m+3))).succ).succ).succ)) (.imp (transition
  ((((((J).succ).succ).succ).succ).succ).succ ((((((Domains).succ).succ).succ).succ).succ).succ
  ((((((F).succ).succ).succ).succ).succ).succ ((((((0 : Fin (m+1))).succ).succ).succ).succ).succ (((((0 :
  Fin (m+2))).succ).succ).succ).succ (((0 : Fin (m+4))).succ).succ ((0 : Fin (m+5))).succ) (.imp
  (transition ((((((J).succ).succ).succ).succ).succ).succ
  ((((((Domains).succ).succ).succ).succ).succ).succ ((((((F).succ).succ).succ).succ).succ).succ (((((0 :
  Fin (m+2))).succ).succ).succ).succ ((((0 : Fin (m+3))).succ).succ).succ ((0 : Fin (m+5))).succ (0 : Fin
  (m+6))) (transition ((((((J).succ).succ).succ).succ).succ).succ
  ((((((Domains).succ).succ).succ).succ).succ).succ ((((((F).succ).succ).succ).succ).succ).succ ((((((0 :
  Fin (m+1))).succ).succ).succ).succ).succ ((((0 : Fin (m+3))).succ).succ).succ (((0 : Fin
  (m+4))).succ).succ (0 : Fin (m+6))))))))))))))))

theorem transitionLaws_freeClosed {m : Nat} (J E Domains F : Fin m) : (transitionLaws J E Domains F).FreeClosed := by
  simp -implicitDefEqProofs [transitionLaws,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,Project.Formula.extensionalEq,atStage_freeClosed,transition_freeClosed]

theorem transitionLaws_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (J E Domains F : Fin m) :
    Project.Formula.satisfies env (transitionLaws J E Domains F) ↔ TransitionLaws (env.bound J) (env.bound E) (env.bound Domains) (env.bound F) := by
  simp only [transitionLaws,TransitionLaws,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,Project.Formula.satisfies_extensionalEq_iff_eq (ModelTransfer.extensionality hM),atStage_semantics hM,transition_semantics hM]
  rfl

def meets {m : Nat} (J E Domains F i x j y : Fin m) : Project.Formula 1 m :=
  (.conj (atStage J Domains i x) (.conj (atStage J Domains j y) (.existsE (.existsE (.conj (.mem (.bound ((0 : Fin
  (m+1))).succ) (.bound ((J).succ).succ)) (.conj (ProjectSyntax.encode id (Source.SetLanguage.edge
  ((E).succ).succ ((i).succ).succ ((0 : Fin (m+1))).succ)) (.conj (ProjectSyntax.encode id
  (Source.SetLanguage.edge ((E).succ).succ ((j).succ).succ ((0 : Fin (m+1))).succ)) (.conj (transition
  ((J).succ).succ ((Domains).succ).succ ((F).succ).succ ((i).succ).succ ((0 : Fin (m+1))).succ
  ((x).succ).succ (0 : Fin (m+2))) (transition ((J).succ).succ ((Domains).succ).succ ((F).succ).succ
  ((j).succ).succ ((0 : Fin (m+1))).succ ((y).succ).succ (0 : Fin (m+2)))))))))))

theorem meets_freeClosed {m : Nat} (J E Domains F i x j y : Fin m) : (meets J E Domains F i x j y).FreeClosed := by
  simp -implicitDefEqProofs [meets,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,atStage_freeClosed,transition_freeClosed]

theorem meets_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (J E Domains F i x j y : Fin m) :
    Project.Formula.satisfies env (meets J E Domains F i x j y) ↔ Meets (env.bound J) (env.bound E) (env.bound Domains) (env.bound F) (env.bound i) (env.bound x) (env.bound j) (env.bound y) := by
  simp only [meets,Meets,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,atStage_semantics hM,transition_semantics hM]
  rfl

def injectiveTransitions {m : Nat} (J E Domains F : Fin m) : Project.Formula 1 m :=
  (.forallE (.forallE (.forallE (.forallE (.forallE (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge
  (((((E).succ).succ).succ).succ).succ (((((0 : Fin (m+1))).succ).succ).succ).succ ((((0 : Fin
  (m+2))).succ).succ).succ)) (.imp (transition (((((J).succ).succ).succ).succ).succ
  (((((Domains).succ).succ).succ).succ).succ (((((F).succ).succ).succ).succ).succ (((((0 : Fin
  (m+1))).succ).succ).succ).succ ((((0 : Fin (m+2))).succ).succ).succ (((0 : Fin (m+3))).succ).succ (0 :
  Fin (m+5))) (.imp (transition (((((J).succ).succ).succ).succ).succ
  (((((Domains).succ).succ).succ).succ).succ (((((F).succ).succ).succ).succ).succ (((((0 : Fin
  (m+1))).succ).succ).succ).succ ((((0 : Fin (m+2))).succ).succ).succ ((0 : Fin (m+4))).succ (0 : Fin
  (m+5))) (Project.Formula.extensionalEq (.bound (((0 : Fin (m+3))).succ).succ) (.bound ((0 : Fin
  (m+4))).succ))))))))))

theorem injectiveTransitions_freeClosed {m : Nat} (J E Domains F : Fin m) : (injectiveTransitions J E Domains F).FreeClosed := by
  simp -implicitDefEqProofs [injectiveTransitions,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,Project.Formula.extensionalEq,transition_freeClosed]

theorem injectiveTransitions_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (J E Domains F : Fin m) :
    Project.Formula.satisfies env (injectiveTransitions J E Domains F) ↔ InjectiveTransitions (env.bound J) (env.bound E) (env.bound Domains) (env.bound F) := by
  simp only [injectiveTransitions,InjectiveTransitions,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_imp_iff,Project.Term.eval_bound,GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge,Project.Formula.satisfies_extensionalEq_iff_eq (ModelTransfer.extensionality hM),transition_semantics hM]
  rfl

end PPAC.Migration.ConstructionDirectedSystem
