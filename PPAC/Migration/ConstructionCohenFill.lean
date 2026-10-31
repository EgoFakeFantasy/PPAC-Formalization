/- Pinned StableSelectors.Condition.fill/fill_le/subset_dom_fill:46-68.
Only previously undefined coordinates in the prescribed internal countable
set are assigned the fixed bit. Reuse native functional images, Separation,
ordinal image bounds and the existing compatible-condition union. -/
import PPAC.Migration.ConstructionCohenCompatibility

namespace PPAC.Migration.ConstructionCohenFill
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ForcingCohenCoordinates (Cartesian)
open ForcingCohenConditions (Condition)
open ForcingSupportSize (Small)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

def Fill (A p bit r : M.Carrier .set) : Prop := ∀ z,
  (Project.FirstOrderSemantics.reduct M).mem z r ↔
    (Project.FirstOrderSemantics.reduct M).mem z p ∨ ∃ a,
      (Project.FirstOrderSemantics.reduct M).mem a A ∧ PureKuratowski.Code M z a bit ∧
        ¬ ∃ b, PureKuratowski.PairMember M a b p

theorem fill_edge (hM : FirstOrder.Theory.Models M nativeZF)
    {A p bit r a b : M.Carrier .set} (h : Fill A p bit r) :
    PureKuratowski.PairMember M a b r ↔ PureKuratowski.PairMember M a b p ∨
      ((Project.FirstOrderSemantics.reduct M).mem a A ∧ (¬ ∃ c, PureKuratowski.PairMember M a c p) ∧ b = bit) := by
  constructor
  · rintro ⟨z,hz,hzr⟩
    rcases (h z).mp hzr with hzp | ⟨a',ha,hz',hn⟩
    · exact Or.inl ⟨z,hz,hzp⟩
    · obtain ⟨rfl,rfl⟩ := PureKuratowski.code_injective hz hz'
      exact Or.inr ⟨ha,hn,rfl⟩
  · rintro (⟨z,hz,hzp⟩ | ⟨ha,hn,rfl⟩)
    · exact ⟨z,hz,(h z).mpr (Or.inl hzp)⟩
    · obtain ⟨z,hz⟩ := KuratowskiZF.exists_code hM a b
      exact ⟨z,hz,(h z).mpr (Or.inr ⟨a,ha,hz,hn⟩)⟩

theorem fill_le {A p bit r : M.Carrier .set} (h : Fill A p bit r) :
    (Project.FirstOrderSemantics.reduct M).MemberSubset p r := fun z hz => (h z).mpr (Or.inl hz)

theorem subset_dom_fill (hM : FirstOrder.Theory.Models M nativeZF)
    {A p bit r : M.Carrier .set} (h : Fill A p bit r) : ∀ a,
    (Project.FirstOrderSemantics.reduct M).mem a A → ∃ b, PureKuratowski.PairMember M a b r := by
  intro a ha
  classical
  by_cases hp : ∃ b, PureKuratowski.PairMember M a b p
  · obtain ⟨b,hb⟩ := hp
    exact ⟨b,(fill_edge hM h).mpr (Or.inl hb)⟩
  · exact ⟨bit,(fill_edge hM h).mpr (Or.inr ⟨ha,hp,rfl⟩)⟩

theorem exists_fill (hM : FirstOrder.Theory.Models M nativeZF)
    {w C B S A p bit : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hS : Cartesian C B S) (hA : (Project.FirstOrderSemantics.reduct M).MemberSubset A C)
    (hSmall : Small A w) (hb : (Project.FirstOrderSemantics.reduct M).mem bit B)
    (hp : Condition S w p) : ∃ r, Condition S w r ∧ Fill A p bit r := by
  have hZF := ModelTransfer.project_models_iff.mp hM
  let P := KuratowskiZF.interpretation hM
  let schema : Project.BinarySchema 1 := {
    body := PureKuratowskiProject.code (.bound 0) (.bound 1) (.bound 2)
    freeClosed := by simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,PureKuratowskiProject.code,Project.Formula.isSingleton,Project.Formula.isUnorderedPair,Project.Formula.extensionalEq] }
  let env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) 1 := { bound := fun _ => bit, free := fun _ => p }
  have he a z : schema.denote env a z ↔ PureKuratowski.Code M z a bit := by
    simp only [Project.BinarySchema.denote,schema,KuratowskiZF.code_correct hM,Project.Term.eval_bound]
    rfl
  have ht : ∀ a, (Project.FirstOrderSemantics.reduct M).mem a A → ∃ z, schema.denote env a z := by
    intro a _
    obtain ⟨z,hz⟩ := KuratowskiZF.exists_code hM a bit
    exact ⟨z,(he a z).mpr hz⟩
  have hu : ∀ a, (Project.FirstOrderSemantics.reduct M).mem a A → ∀ y z,
      schema.denote env a y → schema.denote env a z → y = z :=
    fun a _ y z hy hz => KuratowskiZF.code_unique hM ((he a y).mp hy) ((he a z).mp hz)
  obtain ⟨E,hE⟩ := ZF.exists_functionalImageOn hZF schema env A ht hu
  obtain ⟨f,hf,hEdge⟩ := ZF.exists_setFunctionFromTo_of_denote hZF P schema env ht hu
    (fun a z ha hz => (hE z).mpr ⟨a,ha,hz⟩)
  have hESmall := ExistingOrdinalImage.ordinal_image_bound_l P hZF
    (ExistingCardinalBounds.omega_cardinal_l P hZF hw).1
    ((ForcingSupportSize.native_small hM A w).mp hSmall) hf (by
      intro z hz
      obtain ⟨a,ha,haz⟩ := (hE z).mp hz
      exact ⟨a,ha,(hEdge a z).mpr ⟨ha,haz⟩⟩)
  let fresh : Project.UnarySchema 2 := {
    body := .existsE (.conj (PureKuratowskiProject.code (.bound 1) (.bound 0) (.bound 2))
      (.neg (.existsE (ProjectSyntax.encode id (Source.SetLanguage.edge 4 1 0)))))
    freeClosed := by simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,PureKuratowskiProject.code,ProjectSyntax.freeClosed] }
  let rho : SetTheory.Env (Project.FirstOrderSemantics.reduct M) 2 := {
    bound := Fin.cases bit (fun _ => p), free := fun _ => p }
  have hFresh z : fresh.denote rho z ↔ ∃ a, PureKuratowski.Code M z a bit ∧ ¬ ∃ b, PureKuratowski.PairMember M a b p := by
    simp only [Project.UnarySchema.denote,fresh,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,
      Project.Formula.satisfies_neg_iff,KuratowskiZF.code_correct hM,Project.Term.eval_bound,
      GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge]
    rfl
  obtain ⟨F,hF⟩ := ZF.separation_exists_d hZF fresh rho E
  have hFmem z : (Project.FirstOrderSemantics.reduct M).mem z F ↔ ∃ a,
      (Project.FirstOrderSemantics.reduct M).mem a A ∧ PureKuratowski.Code M z a bit ∧ ¬ ∃ b, PureKuratowski.PairMember M a b p := by
    constructor
    · intro hz
      obtain ⟨hzE,hzF⟩ := (hF z).mp hz
      obtain ⟨a,ha,haz⟩ := (hE z).mp hzE
      obtain ⟨a',ha',hn⟩ := (hFresh z).mp hzF
      obtain ⟨rfl,_⟩ := PureKuratowski.code_injective ((he a z).mp haz) ha'
      exact ⟨a,ha,(he a z).mp haz,hn⟩
    · rintro ⟨a,ha,haz,hn⟩
      exact (hF z).mpr ⟨(hE z).mpr ⟨a,ha,(he a z).mpr haz⟩,(hFresh z).mpr ⟨a,haz,hn⟩⟩
  have hFedge a b (hab : PureKuratowski.PairMember M a b F) :
      (Project.FirstOrderSemantics.reduct M).mem a A ∧ b = bit ∧ ¬ ∃ c, PureKuratowski.PairMember M a c p := by
    obtain ⟨z,hz,hzF⟩ := hab
    obtain ⟨a',ha',hz',hn⟩ := (hFmem z).mp hzF
    obtain ⟨rfl,rfl⟩ := PureKuratowski.code_injective hz hz'
    exact ⟨ha',rfl,hn⟩
  have hFC : Condition S w F := ⟨(by
      intro z hz
      obtain ⟨a,ha,haz,_⟩ := (hFmem z).mp hz
      exact (hS z).mpr ⟨a,hA a ha,bit,hb,haz⟩),
    (fun a b c hab hac => (hFedge a b hab).2.1.trans (hFedge a c hac).2.1.symm),
    ForcingSupportSize.small_subset hM (fun z hz => ((hF z).mp hz).1)
      ((ForcingSupportSize.native_small hM E w).mpr hESmall)⟩
  obtain ⟨r,hr,hUnion,_,_⟩ := ConstructionCohenCompatibility.exists_union hM hw hp hFC (by
    intro a b c hab hac
    exact False.elim ((hFedge a c hac).2.2 ⟨b,hab⟩))
  exact ⟨r,hr,fun z => (hUnion z).trans (or_congr Iff.rfl (hFmem z))⟩

def fill {m : Nat} (A p bit r : Fin m) : Project.Formula 1 m :=
  (.forallE (.iff (.mem (.bound 0) (.bound r.succ)) (.disj (.mem (.bound 0) (.bound p.succ)) (.existsE (.conj (.mem (.bound 0) (.bound A.succ.succ)) (.conj (PureKuratowskiProject.code (.bound 1) (.bound 0) (.bound bit.succ.succ)) (.neg (.existsE (ProjectSyntax.encode id (Source.SetLanguage.edge p.succ.succ.succ 1 0))))))))))

theorem fill_freeClosed {m : Nat} (A p bit r : Fin m) : (fill A p bit r).FreeClosed := by
  simp -implicitDefEqProofs [fill,Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,PureKuratowskiProject.code]

theorem fill_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (A p bit r : Fin m) :
    Project.Formula.satisfies env (fill A p bit r) ↔ Fill (env.bound A) (env.bound p) (env.bound bit) (env.bound r) := by
  simp only [fill,Fill,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_iff_iff,
    Project.Formula.satisfies_disj_iff,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_neg_iff,Project.Formula.satisfies_mem_iff,Project.Term.eval_bound,
    KuratowskiZF.code_correct hM,GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),KuratowskiZF.source_edge]
  rfl

def constructionSentence {m : Nat} (w C B S A p bit : Fin m) : Project.Sentence where
  formula := Project.Formula.forallClosure m (.imp (Project.Formula.isOmega (.bound w)) (.imp (ProjectSyntax.encode id (ForcingCohenCoordinates.cartesian C B S)) (.imp (Project.Formula.subset (.bound A) (.bound C)) (.imp (ProjectSyntax.encode id (ForcingSupportSize.small A w)) (.imp (.mem (.bound bit) (.bound B)) (.imp (ProjectSyntax.encode id (ForcingCohenConditions.condition S w p)) (.existsE (.conj (ProjectSyntax.encode id (ForcingCohenConditions.condition S.succ w.succ 0)) (fill A.succ p.succ bit.succ 0)))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,Project.Formula.isOmega,Project.Formula.subset,fill_freeClosed]

theorem construction_models {m : Nat} (w C B S A p bit : Fin m) (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence (constructionSentence w C B S A p bit)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) (constructionSentence w C B S A p bit)]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_mem_iff,Project.Formula.satisfies_isOmega_iff,Project.Formula.satisfies_subset_iff,
    Project.Term.eval_bound,GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingCohenCoordinates.cartesian_semantics (M := M),ForcingCohenConditions.condition_semantics (M := M),
    ForcingSupportSize.small_semantics (M := M),fill_semantics hM]
  exact exists_fill hM

theorem construction_kernel_certificate {m : Nat} (w C B S A p bit : Fin m) :
    FirstOrder.Derives nativeZF [] (Project.fo_sentence (constructionSentence w C B S A p bit)) :=
  ModelTransfer.derives (fun _ hM => construction_models w C B S A p bit hM)

end PPAC.Migration.ConstructionCohenFill
