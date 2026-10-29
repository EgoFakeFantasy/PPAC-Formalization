/- Pinned Algebra/PlacementExtensions.probeDenseSet_dense:59 and its actual
CodeCardinals.ordinalType_lower_count.hits consumer:201-212.
All indices, copy graphs, supports and conditions are internal sets. Reuse
existing fresh rows, countable supports, restriction and Cohen union. -/
import PPAC.Migration.ConstructionCohenCompatibility
import PPAC.Migration.ConstructionCompatiblePlacement
import PPAC.Migration.ConstructibleSource

namespace PPAC.Migration.ForcingProbeDensity
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ForcingCohenCoordinates (Cartesian)
open ForcingCohenConditions (Condition)
open ForcingConditionGraphs (FunctionOn)
open ForcingSupportSize (Small)
open ConstructionCohenCompatibility (Entry Restricted Compatible)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 8192
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

def OffSupport (p J i : M.Carrier .set) : Prop :=
  (∃ k b, Entry p i k b) ∧ ¬ (Project.FirstOrderSemantics.reduct M).mem i J

def offSupport {n : Nat} (p J i : Fin n) : Project.Formula 1 n :=
  .conj (.existsE (.existsE (ConstructionCohenCompatibility.entry p.succ.succ i.succ.succ 1 0)))
    (.neg (.mem (.bound i) (.bound J)))

theorem offSupport_freeClosed {n : Nat} (p J i : Fin n) : (offSupport p J i).FreeClosed := by
  simp -implicitDefEqProofs [offSupport,Definitional.Formula.FreeClosed,ConstructionCohenCompatibility.entry_freeClosed]

theorem offSupport_semantics (hM : FirstOrder.Theory.Models M nativeZF) {n : Nat}
    (env : Env (Project.FirstOrderSemantics.reduct M) n) (p J i : Fin n) :
    Project.Formula.satisfies env (offSupport p J i) ↔ OffSupport (env.bound p) (env.bound J) (env.bound i) := by
  simp only [offSupport,OffSupport,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_neg_iff,Project.Formula.satisfies_mem_iff,ConstructionCohenCompatibility.entry_semantics hM,Project.Term.eval_bound]
  rfl

def Copies (A F S w J root : M.Carrier .set) : Prop :=
  FunctionOn A F ∧ ∀ a p, PureKuratowski.PairMember M a p F → Condition S w p ∧ Restricted J p root

def DisjointOff (A F J : M.Carrier .set) : Prop :=
  ∀ a b p q i, (Project.FirstOrderSemantics.reduct M).mem a A → (Project.FirstOrderSemantics.reduct M).mem b A →
    PureKuratowski.PairMember M a p F → PureKuratowski.PairMember M b q F →
    OffSupport p J i → OffSupport q J i → a = b

def OffRows (A F J R : M.Carrier .set) : Prop :=
  ∀ a i, PureKuratowski.PairMember M a i R ↔ (Project.FirstOrderSemantics.reduct M).mem a A ∧
    ∃ p, PureKuratowski.PairMember M a p F ∧ OffSupport p J i

theorem exists_offRows (hM : FirstOrder.Theory.Models M nativeZF)
    {A F I K C B S w J root : M.Carrier .set}
    (hC : Cartesian I K C) (hS : Cartesian C B S) (hF : Copies A F S w J root) :
    ∃ R, OffRows A F J R := by
  have hZF := ModelTransfer.project_models_iff.mp hM
  let pair := KuratowskiZF.interpretation hM
  obtain ⟨W,hW⟩ := KP.exists_unionOfTwo (ZF.modelsKP hZF) A I
  let env : Env (Project.FirstOrderSemantics.reduct M) 3 := ⟨Fin.cases A (Fin.cases F (fun _ => J)),fun _ => A⟩
  let schema : Project.BinarySchema 3 := {
    body := .conj (.mem (.bound 1) (.bound 2))
      (.existsE (.conj (Project.Formula.orderedPairMem PureKuratowskiProject.convention (.bound 2) (.bound 0) (.bound 4))
        (offSupport 0 5 1)))
    freeClosed := by simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,Project.Formula.orderedPairMem_freeClosed,offSupport_freeClosed] }
  have hs a i : schema.denote env a i ↔ (Project.FirstOrderSemantics.reduct M).mem a A ∧
      ∃ p, PureKuratowski.PairMember M a p F ∧ OffSupport p J i := by
    simp only [Project.BinarySchema.denote,schema,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_mem_iff,
      Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_orderedPairMem_iff pair,offSupport_semantics hM]
    rfl
  obtain ⟨R,_,hR⟩ := ZF.exists_setRelationOn_of_denote hZF pair schema env W
  refine ⟨R,fun a i => ⟨fun h => (hs a i).mp ((hR a i).mp h).2.2,?_⟩⟩
  intro h
  have input := h
  obtain ⟨ha,p,hap,⟨⟨k,b,he⟩,_⟩⟩ := h
  have hi := (ConstructionCohenCompatibility.entry_typed hC hS (hF.2 a p hap).1 he).1
  exact (hR a i).mpr ⟨(hW a).mpr (Or.inl ha),(hW i).mpr (Or.inr hi),(hs a i).mpr input⟩

/-- The fresh copy is chosen from the same internal index set, not a host family. -/
theorem compatible_copy (hM : FirstOrder.Theory.Models M nativeZF)
    (hChoice : ConstructionDirectedCardinality.Choice (M := M))
    {A F I K C B S w J root c : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hC : Cartesian I K C) (hS : Cartesian C B S) (hF : Copies A F S w J root)
    (hDisj : DisjointOff A F J) (hA : ¬ Small A w) (hc : Condition S w c) (hRoot : Compatible c root) :
    ∃ a p, (Project.FirstOrderSemantics.reduct M).mem a A ∧ PureKuratowski.PairMember M a p F ∧ Compatible c p := by
  obtain ⟨H,hH,_,hSmall⟩ := ConstructionCohenCompatibility.exists_support hM hw hC hS hc
  obtain ⟨R,hR⟩ := exists_offRows hM hC hS hF
  have hRows : ConstructionPlacementFreshness.DisjointRows A R := by
    intro a b i ha hb hai hbi
    obtain ⟨_,p,hap,hp⟩ := (hR a i).mp hai
    obtain ⟨_,q,hbq,hq⟩ := (hR b i).mp hbi
    exact hDisj a b p q i ha hb hap hbq hp hq
  obtain ⟨a,ha,hFresh⟩ := ConstructionPlacementFreshness.exists_fresh hM hChoice hRows hSmall hA
  obtain ⟨p,hap,_⟩ := hF.1.2 a ha
  refine ⟨a,p,ha,hap,ConstructionCohenCompatibility.compatible_of_entries hC hS hc ?_⟩
  intro i k b v hb hv
  have hi : (Project.FirstOrderSemantics.reduct M).mem i J := by
    apply Classical.byContradiction
    intro hn
    exact hFresh i ((hH i).mpr ⟨k,b,hb⟩) ((hR a i).mpr ⟨ha,p,hap,⟨k,v,hv⟩,hn⟩)
  have hr := (ConstructionCohenCompatibility.restricted_entry (hF.2 a p hap).2).mpr ⟨hv,hi⟩
  obtain ⟨x,hx,hb⟩ := hb
  obtain ⟨x',hx',hr⟩ := hr
  have eq := KuratowskiZF.code_unique hM hx' hx
  subst x'
  exact hRoot x b v hb hr

theorem probeDenseSet_dense (hM : FirstOrder.Theory.Models M nativeZF)
    (hChoice : ConstructionDirectedCardinality.Choice (M := M))
    {A F I K C B S w J root c : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hC : Cartesian I K C) (hS : Cartesian C B S) (hF : Copies A F S w J root)
    (hDisj : DisjointOff A F J) (hA : ¬ Small A w) (hc : Condition S w c) :
    ∃ f, Condition S w f ∧ (Project.FirstOrderSemantics.reduct M).MemberSubset c f ∧
      (¬ Compatible f root ∨ ∃ a p, (Project.FirstOrderSemantics.reduct M).mem a A ∧
        PureKuratowski.PairMember M a p F ∧ (Project.FirstOrderSemantics.reduct M).MemberSubset p f) := by
  classical
  by_cases hRoot : Compatible c root
  · obtain ⟨a,p,ha,hap,hcp⟩ := compatible_copy hM hChoice hw hC hS hF hDisj hA hc hRoot
    obtain ⟨f,hf,_,hcf,hpf⟩ := ConstructionCohenCompatibility.exists_union hM hw hc (hF.2 a p hap).1 hcp
    exact ⟨f,hf,hcf,Or.inr ⟨a,p,ha,hap,hpf⟩⟩
  · exact ⟨c,hc,fun _ h => h,Or.inl hRoot⟩

/-- Source CodeCardinals.hits: a condition extending the common root can
actually be strengthened to one of the independent copies. -/
theorem hits (hM : FirstOrder.Theory.Models M nativeZF)
    (hChoice : ConstructionDirectedCardinality.Choice (M := M))
    {A F I K C B S w J root c : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hC : Cartesian I K C) (hS : Cartesian C B S) (hF : Copies A F S w J root)
    (hDisj : DisjointOff A F J) (hA : ¬ Small A w) (hc : Condition S w c)
    (hRoot : (Project.FirstOrderSemantics.reduct M).MemberSubset root c) :
    ∃ f a p, Condition S w f ∧ (Project.FirstOrderSemantics.reduct M).MemberSubset c f ∧
      (Project.FirstOrderSemantics.reduct M).mem a A ∧ PureKuratowski.PairMember M a p F ∧
      (Project.FirstOrderSemantics.reduct M).MemberSubset p f := by
  obtain ⟨f,hf,hcf,hn | ⟨a,p,ha,hap,hpf⟩⟩ := probeDenseSet_dense hM hChoice hw hC hS hF hDisj hA hc
  · exfalso
    apply hn
    intro x b v hb hv
    obtain ⟨z,hz,hzr⟩ := hv
    exact hf.2.1 x b v hb ⟨z,hz,hcf z (hRoot z hzr)⟩
  · exact ⟨f,a,p,hf,hcf,ha,hap,hpf⟩


def copies {n : Nat} (A F S w J root : Fin n) : Project.Formula 1 n :=
  .conj (ProjectSyntax.encode id (Source.SetLanguage.functionOn F A))
    (.forallE (.forallE (.imp (Project.Formula.orderedPairMem PureKuratowskiProject.convention
      (.bound 1) (.bound 0) (.bound F.succ.succ))
      (.conj (ProjectSyntax.encode id (ForcingCohenConditions.condition S.succ.succ w.succ.succ 0))
        (ConstructionCohenCompatibility.restricted J.succ.succ 0 root.succ.succ)))))

theorem copies_freeClosed {n : Nat} (A F S w J root : Fin n) : (copies A F S w J root).FreeClosed := by
  simp -implicitDefEqProofs [copies,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
    Project.Formula.orderedPairMem_freeClosed,ConstructionCohenCompatibility.restricted_freeClosed]

theorem copies_semantics (hM : FirstOrder.Theory.Models M nativeZF) {n : Nat}
    (env : Env (Project.FirstOrderSemantics.reduct M) n) (A F S w J root : Fin n) :
    Project.Formula.satisfies env (copies A F S w J root) ↔
      Copies (env.bound A) (env.bound F) (env.bound S) (env.bound w) (env.bound J) (env.bound root) := by
  simp only [copies,Copies,Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_forall_iff,
    Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_orderedPairMem_iff (KuratowskiZF.interpretation hM),
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),ForcingConditionGraphs.functionOn_semantics (M := M),
    ForcingCohenConditions.condition_semantics (M := M),ConstructionCohenCompatibility.restricted_semantics hM,Project.Term.eval_bound]
  rfl

def disjointOff {n : Nat} (A F J : Fin n) : Project.Formula 1 n :=
  let up : Fin n → Fin (n+5) := fun i => i.succ.succ.succ.succ.succ
  let body : Project.Formula 1 (n+5) :=
    .imp (.mem (.bound 4) (.bound (up A))) (.imp (.mem (.bound 3) (.bound (up A)))
      (.imp (Project.Formula.orderedPairMem PureKuratowskiProject.convention (.bound 4) (.bound 2) (.bound (up F)))
      (.imp (Project.Formula.orderedPairMem PureKuratowskiProject.convention (.bound 3) (.bound 1) (.bound (up F)))
      (.imp (offSupport 2 (up J) 0) (.imp (offSupport 1 (up J) 0)
        (Project.Formula.extensionalEq (.bound 4) (.bound 3)))))))
  .forallE (.forallE (.forallE (.forallE (.forallE body))))

theorem disjointOff_freeClosed {n : Nat} (A F J : Fin n) : (disjointOff A F J).FreeClosed := by
  simp -implicitDefEqProofs [disjointOff,Definitional.Formula.FreeClosed,offSupport_freeClosed,
    Project.Formula.orderedPairMem_freeClosed,Project.Formula.extensionalEq]

theorem disjointOff_semantics (hM : FirstOrder.Theory.Models M nativeZF) {n : Nat}
    (env : Env (Project.FirstOrderSemantics.reduct M) n) (A F J : Fin n) :
    Project.Formula.satisfies env (disjointOff A F J) ↔ DisjointOff (env.bound A) (env.bound F) (env.bound J) := by
  simp only [disjointOff,DisjointOff,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_imp_iff,
    Project.Formula.satisfies_mem_iff,Project.Formula.satisfies_orderedPairMem_iff (KuratowskiZF.interpretation hM),
    offSupport_semantics hM,Project.Formula.satisfies_extensionalEq_iff_eq (ModelTransfer.extensionality hM),Project.Term.eval_bound]
  rfl

def denseResult {n : Nat} (A F S w root c : Fin n) : Project.Formula 1 n :=
  .existsE (.conj (ProjectSyntax.encode id (ForcingCohenConditions.condition S.succ w.succ 0))
    (.conj (ProjectSyntax.encode id (Source.SetLanguage.subset c.succ 0))
      (.disj (.neg (ConstructionCompatiblePlacement.compatible 0 root.succ))
        (.existsE (.existsE (.conj (.mem (.bound 1) (.bound A.succ.succ.succ))
          (.conj (Project.Formula.orderedPairMem PureKuratowskiProject.convention
            (.bound 1) (.bound 0) (.bound F.succ.succ.succ))
            (ProjectSyntax.encode id (Source.SetLanguage.subset 0 2)))))))))

def hitsResult {n : Nat} (A F S w c : Fin n) : Project.Formula 1 n :=
  .existsE (.existsE (.existsE
    (.conj (ProjectSyntax.encode id (ForcingCohenConditions.condition S.succ.succ.succ w.succ.succ.succ 2))
      (.conj (ProjectSyntax.encode id (Source.SetLanguage.subset c.succ.succ.succ 2))
        (.conj (.mem (.bound 1) (.bound A.succ.succ.succ))
          (.conj (Project.Formula.orderedPairMem PureKuratowskiProject.convention
            (.bound 1) (.bound 0) (.bound F.succ.succ.succ))
            (ProjectSyntax.encode id (Source.SetLanguage.subset 0 2))))))))

/-- A,F,I,K,C,B,S,w,J,root,c are all universally quantified internal sets. -/
def densitySentence : Project.Sentence where
  formula := Project.Formula.forallClosure 11
    (.imp (Project.Formula.isOmega (.bound 7))
    (.imp (ProjectSyntax.encode id (ForcingCohenCoordinates.cartesian 2 3 4))
    (.imp (ProjectSyntax.encode id (ForcingCohenCoordinates.cartesian 4 5 6))
    (.imp (copies 0 1 6 7 8 9)
    (.imp (disjointOff 0 1 8)
    (.imp (.neg (ProjectSyntax.encode id (ForcingSupportSize.small 0 7)))
    (.imp (ProjectSyntax.encode id (ForcingCohenConditions.condition 6 7 10))
      (.conj (denseResult 0 1 6 7 9 10)
        (.imp (ProjectSyntax.encode id (Source.SetLanguage.subset 9 10)) (hitsResult 0 1 6 7 10))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,copies_freeClosed,
      disjointOff_freeClosed,denseResult,hitsResult,Project.Formula.orderedPairMem_freeClosed,
      ConstructionCompatiblePlacement.compatible_freeClosed]

theorem density_models (hM : FirstOrder.Theory.Models M nativeZF)
    (hChoice : ConstructionDirectedCardinality.Choice (M := M)) :
    (Project.fo_sentence densitySentence).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM),SetTheory.Structure.satisfiesSentence_iff]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro env
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_isOmega_iff,
    Project.Formula.satisfies_neg_iff,Project.Formula.satisfies_conj_iff,Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingCohenCoordinates.cartesian_semantics (M := M),copies_semantics hM,disjointOff_semantics hM,
    ForcingSupportSize.small_semantics (M := M),ForcingCohenConditions.condition_semantics (M := M),
    ForcingLabelPermutations.subset_semantics (M := M)]
  intro hw hC hS hF hDisj hA hc
  simp only [denseResult,hitsResult,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_disj_iff,Project.Formula.satisfies_neg_iff,Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),ForcingCohenConditions.condition_semantics (M := M),
    ForcingLabelPermutations.subset_semantics (M := M),ConstructionCompatiblePlacement.compatible_semantics hM,
    Project.Formula.satisfies_orderedPairMem_iff (KuratowskiZF.interpretation hM)]
  exact ⟨probeDenseSet_dense hM hChoice hw hC hS hF hDisj hA hc,
    fun hr => hits hM hChoice hw hC hS hF hDisj hA hc hr⟩

theorem density_kernel_certificate : FirstOrder.Derives nativeZF []
    (Project.fo_sentence (ConstructibleGround.relative densitySentence)) := by
  apply ModelTransfer.derives
  intro N hN
  have hL := ConstructibleSource.model_zf hN
  have hRawChoice := (Project.FirstOrderSemantics.sentence_correct
    (ModelTransfer.extensionality hL) Axioms.choice).mp (ConstructibleSource.model_choice hN)
  let inhabitant := Classical.choice ((ConstructibleSource.model hN).nonempty .set)
  let env : Env (Project.FirstOrderSemantics.reduct (ConstructibleSource.model hN)) 0 := ⟨Fin.elim0,fun _ => inhabitant⟩
  have hSat : Project.Formula.satisfies env (ConstructionDirectedCardinality.choice (m := 0)) := by
    change Project.Formula.satisfies env (Axioms.choice.formula.rename Fin.elim0)
    rw [Project.Formula.satisfies_rename]
    exact hRawChoice env.free
  have hChoice := (ConstructionDirectedCardinality.choice_semantics hL env).mp hSat
  apply ConstructibleGround.relative_models hN
  exact (Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hL) _).mp (density_models hL hChoice)

end PPAC.Migration.ForcingProbeDensity
