/- Pinned CohenForcing.Condition.insert:229, fresh_level:245,
separate_labels:256. Reuse singleton fill and the existing ordinal-image bound;
no new insertion, choice, or cardinal backend. -/
import PPAC.Migration.ConstructionCohenFusion
import PPAC.Migration.ForcingLabelNames

namespace PPAC.Migration.ConstructionCohenSeparation
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ForcingCohenCoordinates (Cartesian)
open ForcingCohenConditions (Condition)
open ConstructionCohenCompatibility (Entry)
open ForcingSupportSize (Small)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

def Level (z k : M.Carrier .set) : Prop :=
  ∃ a i b, PureKuratowski.Code M z a b ∧ PureKuratowski.Code M a i k

theorem level_unique {z k l : M.Carrier .set} (hk : Level z k) (hl : Level z l) : k = l := by
  obtain ⟨a,i,b,hz,ha⟩ := hk
  obtain ⟨a',i',b',hz',ha'⟩ := hl
  obtain ⟨rfl,_⟩ := PureKuratowski.code_injective hz hz'
  exact (PureKuratowski.code_injective ha ha').2

def level {m : Nat} (z k : Fin m) : Project.Formula 1 m :=
  .existsE (.existsE (.existsE (.conj
    (PureKuratowskiProject.code (.bound z.succ.succ.succ) (.bound 2) (.bound 0))
    (PureKuratowskiProject.code (.bound 2) (.bound 1) (.bound k.succ.succ.succ)))))

theorem level_freeClosed {m : Nat} (z k : Fin m) : (level z k).FreeClosed := by
  simp -implicitDefEqProofs [level,Definitional.Formula.FreeClosed,PureKuratowskiProject.code]

theorem level_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (z k : Fin m) :
    Project.Formula.satisfies env (level z k) ↔ Level (env.bound z) (env.bound k) := by
  simp only [level,Level,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,
    KuratowskiZF.code_correct hM,Project.Term.eval_bound]
  rfl

theorem exists_levels (hM : FirstOrder.Theory.Models M nativeZF)
    {w I K C B S p : M.Carrier .set} (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hC : Cartesian I K C) (hS : Cartesian C B S) (hp : Condition S w p) :
    ∃ L, Small L w ∧ ∀ k, (Project.FirstOrderSemantics.reduct M).mem k L ↔ ∃ i b, Entry p i k b := by
  have hZF := ModelTransfer.project_models_iff.mp hM
  let P := KuratowskiZF.interpretation hM
  let schema : Project.BinarySchema 0 := { body := level 1 0, freeClosed := level_freeClosed _ _ }
  let env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) 0 := { bound := Fin.elim0, free := fun _ => p }
  have he z k : schema.denote env z k ↔ Level z k := level_semantics hM ((env.push z).push k) 1 0
  have ht : ∀ z, (Project.FirstOrderSemantics.reduct M).mem z p → ∃ k, schema.denote env z k := by
    intro z hz
    obtain ⟨a,ha,b,_,hzab⟩ := (hS z).mp (hp.1 z hz)
    obtain ⟨i,_,k,_,haik⟩ := (hC a).mp ha
    exact ⟨k,(he z k).mpr ⟨a,i,b,hzab,haik⟩⟩
  have hu : ∀ z, (Project.FirstOrderSemantics.reduct M).mem z p → ∀ k l,
      schema.denote env z k → schema.denote env z l → k = l :=
    fun z _ k l hk hl => level_unique ((he z k).mp hk) ((he z l).mp hl)
  obtain ⟨L,hL⟩ := ZF.exists_functionalImageOn hZF schema env p ht hu
  obtain ⟨f,hf,hEdge⟩ := ZF.exists_setFunctionFromTo_of_denote hZF P schema env ht hu
    (fun z k hz hk => (hL k).mpr ⟨z,hz,hk⟩)
  have hSmall := ExistingOrdinalImage.ordinal_image_bound_l P hZF
    (ExistingCardinalBounds.omega_cardinal_l P hZF hw).1
    ((ForcingSupportSize.native_small hM p w).mp hp.2.2) hf (by
      intro k hk
      obtain ⟨z,hz,hzk⟩ := (hL k).mp hk
      exact ⟨z,hz,(hEdge z k).mpr ⟨hz,hzk⟩⟩)
  refine ⟨L,(ForcingSupportSize.native_small hM L w).mpr hSmall,?_⟩
  intro k
  constructor
  · intro hk
    obtain ⟨z,hz,hzk⟩ := (hL k).mp hk
    obtain ⟨a,i,b,hzab,haik⟩ := (he z k).mp hzk
    exact ⟨i,b,a,haik,z,hzab,hz⟩
  · rintro ⟨i,b,a,haik,z,hzab,hz⟩
    exact (hL k).mpr ⟨z,hz,(he z k).mpr ⟨a,i,b,hzab,haik⟩⟩

theorem fresh_level (hM : FirstOrder.Theory.Models M nativeZF)
    {w I K C B S p : M.Carrier .set} (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hC : Cartesian I K C) (hS : Cartesian C B S) (hp : Condition S w p) (hK : ¬ Small K w) :
    ∃ k, (Project.FirstOrderSemantics.reduct M).mem k K ∧ ∀ i b, ¬ Entry p i k b := by
  classical
  obtain ⟨L,hSmall,hL⟩ := exists_levels hM hw hC hS hp
  have hfresh : ∃ k, (Project.FirstOrderSemantics.reduct M).mem k K ∧ ¬ (Project.FirstOrderSemantics.reduct M).mem k L := by
    apply Classical.byContradiction
    intro hn
    apply hK
    apply ForcingSupportSize.small_subset hM (B := L) ?_ hSmall
    intro k hk
    apply Classical.byContradiction
    exact fun hnot => hn ⟨k,hk,hnot⟩
  obtain ⟨k,hk,hn⟩ := hfresh
  exact ⟨k,hk,fun i b h => hn ((hL k).mpr ⟨i,b,h⟩)⟩

def Insert (p a bit r : M.Carrier .set) : Prop := ∀ z,
  (Project.FirstOrderSemantics.reduct M).mem z r ↔
    (Project.FirstOrderSemantics.reduct M).mem z p ∨ PureKuratowski.Code M z a bit

theorem insert_le {p a bit r : M.Carrier .set} (h : Insert p a bit r) :
    (Project.FirstOrderSemantics.reduct M).MemberSubset p r := fun z hz => (h z).mpr (Or.inl hz)

theorem insert_edge (hM : FirstOrder.Theory.Models M nativeZF)
    {p a bit r x b : M.Carrier .set} (h : Insert p a bit r) :
    PureKuratowski.PairMember M x b r ↔ PureKuratowski.PairMember M x b p ∨ (x = a ∧ b = bit) := by
  constructor
  · rintro ⟨z,hz,hzr⟩
    rcases (h z).mp hzr with hzp | hz'
    · exact Or.inl ⟨z,hz,hzp⟩
    · exact Or.inr (PureKuratowski.code_injective hz hz')
  · rintro (⟨z,hz,hzp⟩ | ⟨rfl,rfl⟩)
    · exact ⟨z,hz,(h z).mpr (Or.inl hzp)⟩
    · obtain ⟨z,hz⟩ := KuratowskiZF.exists_code hM x b
      exact ⟨z,hz,(h z).mpr (Or.inr hz)⟩

theorem exists_insert (hM : FirstOrder.Theory.Models M nativeZF)
    {w C B S p a bit : M.Carrier .set} (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hS : Cartesian C B S) (hp : Condition S w p)
    (ha : (Project.FirstOrderSemantics.reduct M).mem a C) (hb : (Project.FirstOrderSemantics.reduct M).mem bit B)
    (hFresh : ¬ ∃ b, PureKuratowski.PairMember M a b p) : ∃ r, Condition S w r ∧ Insert p a bit r := by
  obtain ⟨A,hA⟩ := ForcingWithTopCarrier.exists_single hM a
  obtain ⟨id,hId,_⟩ := ForcingConditionGraphs.exists_identity hM w
  have hSmall := ForcingLabelNames.singleton_small hM hw ⟨id,hId.1,hId.2.1⟩ hA
  obtain ⟨r,hr,hFill⟩ := ConstructionCohenFill.exists_fill hM hw hS
    (fun x hx => ((hA x).mp hx).symm ▸ ha) hSmall hb hp
  refine ⟨r,hr,?_⟩
  intro z
  refine (hFill z).trans (or_congr Iff.rfl ?_)
  constructor
  · rintro ⟨x,hx,hzx,_⟩
    exact (hA x).mp hx ▸ hzx
  · intro hza
    exact ⟨a,(hA a).mpr rfl,hza,hFresh⟩

theorem separate_labels (hM : FirstOrder.Theory.Models M nativeZF)
    {w I K C B S p j k lo hi : M.Carrier .set} (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hC : Cartesian I K C) (hS : Cartesian C B S) (hp : Condition S w p) (hK : ¬ Small K w)
    (hj : (Project.FirstOrderSemantics.reduct M).mem j I) (hk : (Project.FirstOrderSemantics.reduct M).mem k I)
    (hne : j ≠ k) (hlo : (Project.FirstOrderSemantics.reduct M).mem lo B) (hhi : (Project.FirstOrderSemantics.reduct M).mem hi B) :
    ∃ r a, Condition S w r ∧ (Project.FirstOrderSemantics.reduct M).MemberSubset p r ∧
      (Project.FirstOrderSemantics.reduct M).mem a K ∧ Entry r j a lo ∧ Entry r k a hi := by
  obtain ⟨a,ha,hFresh⟩ := fresh_level hM hw hC hS hp hK
  obtain ⟨x,hx⟩ := KuratowskiZF.exists_code hM j a
  obtain ⟨y,hy⟩ := KuratowskiZF.exists_code hM k a
  obtain ⟨r,hr,hIns⟩ := exists_insert hM hw hS hp ((hC x).mpr ⟨j,hj,a,ha,hx⟩) hlo
    (fun ⟨b,hb⟩ => hFresh j b ⟨x,hx,hb⟩)
  have hFreshY : ¬ ∃ b, PureKuratowski.PairMember M y b r := by
    rintro ⟨b,hb⟩
    rcases (insert_edge hM hIns).mp hb with hb | ⟨he,_⟩
    · exact hFresh k b ⟨y,hy,hb⟩
    · exact hne (PureKuratowski.code_injective hx (he ▸ hy)).1
  obtain ⟨s,hs,hIns'⟩ := exists_insert hM hw hS hr ((hC y).mpr ⟨k,hk,a,ha,hy⟩) hhi hFreshY
  have hLo : PureKuratowski.PairMember M x lo r := (insert_edge hM hIns).mpr (Or.inr ⟨rfl,rfl⟩)
  obtain ⟨z,hz,hzr⟩ := hLo
  exact ⟨s,a,hs,fun z hz => insert_le hIns' z (insert_le hIns z hz),ha,
    ⟨x,hx,z,hz,insert_le hIns' z hzr⟩,⟨y,hy,(insert_edge hM hIns').mpr (Or.inr ⟨rfl,rfl⟩)⟩⟩

def constructionSentence {m : Nat} (w I K C B S p j k lo hi : Fin m) : Project.Sentence where
  formula := Project.Formula.forallClosure m (.imp (Project.Formula.isOmega (.bound w)) (.imp (ProjectSyntax.encode id (ForcingCohenCoordinates.cartesian I K C)) (.imp (ProjectSyntax.encode id (ForcingCohenCoordinates.cartesian C B S)) (.imp (ProjectSyntax.encode id (ForcingCohenConditions.condition S w p)) (.imp (.neg (ProjectSyntax.encode id (ForcingSupportSize.small K w))) (.imp (.mem (.bound j) (.bound I)) (.imp (.mem (.bound k) (.bound I)) (.imp (.neg (Project.Formula.extensionalEq (.bound j) (.bound k))) (.imp (.mem (.bound lo) (.bound B)) (.imp (.mem (.bound hi) (.bound B)) (.existsE (.existsE (.conj (ProjectSyntax.encode id (ForcingCohenConditions.condition S.succ.succ w.succ.succ 1)) (.conj (Project.Formula.subset (.bound p.succ.succ) (.bound 1)) (.conj (.mem (.bound 0) (.bound K.succ.succ)) (.conj (ConstructionCohenCompatibility.entry 1 j.succ.succ 0 lo.succ.succ) (ConstructionCohenCompatibility.entry 1 k.succ.succ 0 hi.succ.succ)))))))))))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,Project.Formula.isOmega,
      Project.Formula.subset,Project.Formula.extensionalEq,ConstructionCohenCompatibility.entry_freeClosed]

theorem construction_models {m : Nat} (w I K C B S p j k lo hi : Fin m) (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence (constructionSentence w I K C B S p j k lo hi)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) (constructionSentence w I K C B S p j k lo hi)]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_mem_iff,Project.Formula.satisfies_neg_iff,Project.Formula.satisfies_isOmega_iff,
    Project.Formula.satisfies_subset_iff,Project.Term.eval_bound,
    Project.Formula.satisfies_extensionalEq_iff_eq (ModelTransfer.extensionality hM),
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingCohenCoordinates.cartesian_semantics (M := M),ForcingCohenConditions.condition_semantics (M := M),
    ForcingSupportSize.small_semantics (M := M),ConstructionCohenCompatibility.entry_semantics hM]
  exact separate_labels hM

theorem construction_kernel_certificate {m : Nat} (w I K C B S p j k lo hi : Fin m) :
    FirstOrder.Derives nativeZF [] (Project.fo_sentence (constructionSentence w I K C B S p j k lo hi)) :=
  ModelTransfer.derives (fun _ hM => construction_models w I K C B S p j k lo hi hM)

end PPAC.Migration.ConstructionCohenSeparation
