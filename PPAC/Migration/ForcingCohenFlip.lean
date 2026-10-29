/- Pinned AssignedGraphs.Condition.flip:390-392 and hbits:414-421.
Actual internal Option(C x 2) function, using the existing empty/singleton
representation and von Neumann zero/one/two. No host Bool or standard omega. -/
import PPAC.Migration.ForcingCohenRestriction

namespace PPAC.Migration.ForcingCohenFlip
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ForcingWithTopCarrier (Empty Single)
open ForcingSupportSize (MapsTo)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
universe u
set_option maxRecDepth 8192
set_option maxHeartbeats 2000000
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

def SomePair (a b x : M.Carrier .set) : Prop := ∃ z, PureKuratowski.Code M z a b ∧ Single x z

def somePair {m} (a b x : Fin m) : Project.Formula 1 m := .existsE (.conj
  (PureKuratowskiProject.code .newest (.bound a.succ) (.bound b.succ))
  (Project.Formula.isSingleton (.bound x.succ) .newest))
theorem somePair_freeClosed {m} (a b x : Fin m) : (somePair a b x).FreeClosed := by
  simp -implicitDefEqProofs [somePair,Definitional.Formula.FreeClosed,PureKuratowskiProject.code]

theorem somePair_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m}
    (ρ : Env (Project.FirstOrderSemantics.reduct M) m) (a b x : Fin m) :
    Project.Formula.satisfies ρ (somePair a b x) ↔ SomePair (ρ.bound a) (ρ.bound b) (ρ.bound x) := by
  simp only [somePair,SomePair,Project.Formula.satisfies_exists_iff,Project.Formula.satisfies_conj_iff,
    KuratowskiZF.code_correct hM,Project.Formula.satisfies_isSingleton_iff (ModelTransfer.extensionality hM)]
  rfl

theorem somePair_exists (hM : FirstOrder.Theory.Models M nativeZF) (a b : M.Carrier .set) :
    ∃ x, SomePair a b x := by
  obtain ⟨z,hz⟩ := KuratowskiZF.exists_code hM a b
  obtain ⟨x,hx⟩ := ForcingWithTopCarrier.exists_single hM z
  exact ⟨x,z,hz,hx⟩

theorem somePair_injective {a b c d x : M.Carrier .set} (h : SomePair a b x) (k : SomePair c d x) :
    a = c ∧ b = d := by
  obtain ⟨z,hz,hx⟩ := h
  obtain ⟨v,hv,kx⟩ := k
  have e := ForcingWithTopCarrier.single_injective hx kx
  exact PureKuratowski.code_injective hz (e.symm ▸ hv)

theorem somePair_unique (hM : FirstOrder.Theory.Models M nativeZF) {a b x y : M.Carrier .set}
    (hx : SomePair a b x) (hy : SomePair a b y) : x = y := by
  obtain ⟨z,hz,hx⟩ := hx
  obtain ⟨v,hv,hy⟩ := hy
  exact ForcingWithTopCarrier.single_unique hM hx (KuratowskiZF.code_unique hM hv hz ▸ hy)

def Toggle (zero one b c : M.Carrier .set) : Prop := (b = zero ∧ c = one) ∨ (b = one ∧ c = zero)

def toggle {m} (zero one b c : Fin m) : Project.Formula 1 m := .disj
  (.conj (Project.Formula.extensionalEq (.bound b) (.bound zero)) (Project.Formula.extensionalEq (.bound c) (.bound one)))
  (.conj (Project.Formula.extensionalEq (.bound b) (.bound one)) (Project.Formula.extensionalEq (.bound c) (.bound zero)))
derive_free_closed toggle

theorem toggle_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m} (ρ : Env (Project.FirstOrderSemantics.reduct M) m) (z o b c : Fin m) :
    Project.Formula.satisfies ρ (toggle z o b c) ↔ Toggle (ρ.bound z) (ρ.bound o) (ρ.bound b) (ρ.bound c) := by
  simp only [toggle,Toggle,Project.Formula.satisfies_disj_iff,Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_extensionalEq_iff_eq (ModelTransfer.extensionality hM)]
  rfl

theorem toggle_unique {z o b c d : M.Carrier .set} (hc : Toggle z o b c) (hd : Toggle z o b d) : c = d := by
  rcases hc with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> rcases hd with ⟨h,rfl⟩ | ⟨h,rfl⟩
  · rfl
  · exact h.symm
  · exact h.symm
  · rfl

theorem two_cases (hM : FirstOrder.Theory.Models M nativeZF) {z o B b : M.Carrier .set}
    (hz : Empty z) (ho : (Project.FirstOrderSemantics.reduct M).SuccessorOf o z)
    (hB : (Project.FirstOrderSemantics.reduct M).SuccessorOf B o)
    (hb : (Project.FirstOrderSemantics.reduct M).mem b B) : b = z ∨ b = o := by
  rcases (hB b).mp hb with hb | hb
  · rcases (ho b).mp hb with hb | hb
    · exact (hz b hb).elim
    · exact Or.inl ((ModelTransfer.extensionality hM).eq_of_same_members b z hb)
  · exact Or.inr ((ModelTransfer.extensionality hM).eq_of_same_members b o hb)

def Flip (z o x y : M.Carrier .set) : Prop := (Empty x ∧ Empty y) ∨
  ∃ a b c, SomePair a b x ∧ Toggle z o b c ∧ SomePair a c y

def flip {m} (z o x y : Fin m) : Project.Formula 1 m := .disj
  (.conj (Project.Formula.isEmpty (.bound x)) (Project.Formula.isEmpty (.bound y)))
  (.existsE (.existsE (.existsE (.conj (somePair (2 : Fin (m+3)) 1 x.succ.succ.succ)
    (.conj (toggle z.succ.succ.succ o.succ.succ.succ 1 0) (somePair 2 0 y.succ.succ.succ))))))
theorem flip_freeClosed {m} (z o x y : Fin m) : (flip z o x y).FreeClosed := by
  simp -implicitDefEqProofs [flip,Definitional.Formula.FreeClosed,somePair_freeClosed,toggle_freeClosed]

theorem flip_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m}
    (ρ : Env (Project.FirstOrderSemantics.reduct M) m) (z o x y : Fin m) :
    Project.Formula.satisfies ρ (flip z o x y) ↔ Flip (ρ.bound z) (ρ.bound o) (ρ.bound x) (ρ.bound y) := by
  simp only [flip,Flip,Project.Formula.satisfies_disj_iff,Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_isEmpty_iff,Project.Formula.satisfies_exists_iff,
    somePair_semantics hM,toggle_semantics hM]
  rfl

theorem flip_unique (hM : FirstOrder.Theory.Models M nativeZF) {z o x y v : M.Carrier .set}
    (hy : Flip z o x y) (hv : Flip z o x v) : y = v := by
  rcases hy with ⟨hx,hy⟩ | ⟨a,b,c,hx,ht,hy⟩ <;>
    rcases hv with ⟨kx,hv⟩ | ⟨a',b',c',kx,kt,hv⟩
  · exact ForcingWithTopCarrier.empty_unique hM hy hv
  · obtain ⟨_,_,hs⟩ := kx; exact (ForcingWithTopCarrier.single_nonempty hs hx).elim
  · obtain ⟨_,_,hs⟩ := hx; exact (ForcingWithTopCarrier.single_nonempty hs kx).elim
  · obtain ⟨rfl,rfl⟩ := somePair_injective hx kx
    exact somePair_unique hM hy (toggle_unique ht kt ▸ hv)

theorem flip_exists (hM : FirstOrder.Theory.Models M nativeZF) {z o B C S W x : M.Carrier .set}
    (hz : Empty z) (ho : (Project.FirstOrderSemantics.reduct M).SuccessorOf o z)
    (hB : (Project.FirstOrderSemantics.reduct M).SuccessorOf B o)
    (hS : ForcingCohenCoordinates.Cartesian C B S) (hW : ForcingWithTopCarrier.Carrier S W)
    (hx : (Project.FirstOrderSemantics.reduct M).mem x W) :
    ∃ y, (Project.FirstOrderSemantics.reduct M).mem y W ∧ Flip z o x y := by
  rcases (hW x).mp hx with he | ⟨v,hv,hxv⟩
  · exact ⟨x,hx,Or.inl ⟨he,he⟩⟩
  · obtain ⟨a,ha,b,hb,hv⟩ := (hS v).mp hv
    have hc : ∃ c, (Project.FirstOrderSemantics.reduct M).mem c B ∧ Toggle z o b c := by
      rcases two_cases hM hz ho hB hb with rfl | rfl
      · exact ⟨o,hB.predecessor_mem,Or.inl ⟨rfl,rfl⟩⟩
      · exact ⟨z,(hB z).mpr (Or.inl ho.predecessor_mem),Or.inr ⟨rfl,rfl⟩⟩
    obtain ⟨c,hc,ht⟩ := hc
    obtain ⟨y,t,htc,hyt⟩ := somePair_exists hM a c
    exact ⟨y,(hW y).mpr (Or.inr ⟨t,(hS t).mpr ⟨a,ha,c,hc,htc⟩,hyt⟩),
      Or.inr ⟨a,b,c,⟨v,hv,hxv⟩,ht,⟨t,htc,hyt⟩⟩⟩

def Graph (z o W F : M.Carrier .set) : Prop := MapsTo W W F ∧
  ∀ x y, PureKuratowski.PairMember M x y F → Flip z o x y

def graph {m} (z o W F : Fin m) : Project.Formula 1 m := .conj
  (Project.Formula.isFunctionFromTo PureKuratowskiProject.convention (.bound F) (.bound W) (.bound W))
  (.forallE (.forallE (.imp
    (Project.Formula.orderedPairMem PureKuratowskiProject.convention (.bound 1) .newest (.bound F.succ.succ))
    (flip z.succ.succ o.succ.succ 1 0))))
theorem graph_freeClosed {m} (z o W F : Fin m) : (graph z o W F).FreeClosed := by
  simp -implicitDefEqProofs [graph,Definitional.Formula.FreeClosed,flip_freeClosed]

theorem graph_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m}
    (ρ : Env (Project.FirstOrderSemantics.reduct M) m) (z o W F : Fin m) :
    Project.Formula.satisfies ρ (graph z o W F) ↔ Graph (ρ.bound z) (ρ.bound o) (ρ.bound W) (ρ.bound F) := by
  simp only [graph,Graph,Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_isFunctionFromTo_iff (KuratowskiZF.interpretation hM) (ModelTransfer.extensionality hM),
    Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_imp_iff,
    Project.Formula.satisfies_orderedPairMem_iff (KuratowskiZF.interpretation hM),flip_semantics hM]
  exact and_congr (ForcingSupportSize.native_mapsTo hM _ _ _).symm Iff.rfl

theorem exists_flip (hM : FirstOrder.Theory.Models M nativeZF) {z o B C S W : M.Carrier .set}
    (hz : Empty z) (ho : (Project.FirstOrderSemantics.reduct M).SuccessorOf o z)
    (hB : (Project.FirstOrderSemantics.reduct M).SuccessorOf B o)
    (hS : ForcingCohenCoordinates.Cartesian C B S) (hW : ForcingWithTopCarrier.Carrier S W) :
    ∃ F, Graph z o W F := by
  let ρ : Env (Project.FirstOrderSemantics.reduct M) 2 := (⟨fun _ => z,fun _ => z⟩ : Env _ 1).push o
  let φ : Project.BinarySchema 2 := {body := flip (3 : Fin 4) 2 1 0, freeClosed := flip_freeClosed _ _ _ _}
  have hφ x y : φ.denote ρ x y ↔ Flip z o x y := flip_semantics hM _ _ _ _ _
  have hZF := ModelTransfer.project_models_iff.mp hM
  obtain ⟨F,hF,he⟩ := ZF.exists_setFunctionFromTo_of_denote hZF (KuratowskiZF.interpretation hM) φ ρ
    (source := W) (target := W)
    (by intro x hx; obtain ⟨y,_,hy⟩ := flip_exists hM hz ho hB hS hW hx; exact ⟨y,(hφ x y).mpr hy⟩)
    (fun x _ y v hy hv => flip_unique hM ((hφ x y).mp hy) ((hφ x v).mp hv))
    (by
      intro x y hx hy
      obtain ⟨v,hv,hf⟩ := flip_exists hM hz ho hB hS hW hx
      exact flip_unique hM hf ((hφ x y).mp hy) ▸ hv)
  exact ⟨F,(ForcingSupportSize.native_mapsTo hM W W F).mpr hF,
    fun x y h => (hφ x y).mp ((he x y).mp h).2⟩

def Closed (F Y : M.Carrier .set) : Prop := ∀ x y,
  (Project.FirstOrderSemantics.reduct M).mem x Y → PureKuratowski.PairMember M x y F →
    (Project.FirstOrderSemantics.reduct M).mem y Y

def closed {m} (F Y : Fin m) : Project.Formula 1 m := .forallE (.forallE (.imp
  (.mem (.bound 1) (.bound Y.succ.succ)) (.imp
    (Project.Formula.orderedPairMem PureKuratowskiProject.convention (.bound 1) .newest (.bound F.succ.succ))
    (.mem .newest (.bound Y.succ.succ)))))
derive_free_closed closed

theorem closed_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m}
    (ρ : Env (Project.FirstOrderSemantics.reduct M) m) (F Y : Fin m) :
    Project.Formula.satisfies ρ (closed F Y) ↔ Closed (ρ.bound F) (ρ.bound Y) := by
  simp only [closed,Closed,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_imp_iff,
    Project.Formula.satisfies_mem_iff,Project.Formula.satisfies_orderedPairMem_iff (KuratowskiZF.interpretation hM)]
  rfl

def BitsClosed (B Y : M.Carrier .set) : Prop := ∀ a b c x y,
  (Project.FirstOrderSemantics.reduct M).mem b B → (Project.FirstOrderSemantics.reduct M).mem c B →
    SomePair a b x → SomePair a c y → (Project.FirstOrderSemantics.reduct M).mem x Y →
      (Project.FirstOrderSemantics.reduct M).mem y Y

def bitsClosed {m} (B Y : Fin m) : Project.Formula 1 m := .forallE (.forallE (.forallE (.forallE (.forallE
  (.imp (.mem (.bound 3) (.bound B.succ.succ.succ.succ.succ))
  (.imp (.mem (.bound 2) (.bound B.succ.succ.succ.succ.succ))
  (.imp (somePair (4 : Fin (m+5)) 3 1) (.imp (somePair 4 2 0)
  (.imp (.mem (.bound 1) (.bound Y.succ.succ.succ.succ.succ))
    (.mem .newest (.bound Y.succ.succ.succ.succ.succ)))))))))))
theorem bitsClosed_freeClosed {m} (B Y : Fin m) : (bitsClosed B Y).FreeClosed := by
  simp -implicitDefEqProofs [bitsClosed,Definitional.Formula.FreeClosed,somePair_freeClosed]

theorem bitsClosed_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m}
    (ρ : Env (Project.FirstOrderSemantics.reduct M) m) (B Y : Fin m) :
    Project.Formula.satisfies ρ (bitsClosed B Y) ↔ BitsClosed (ρ.bound B) (ρ.bound Y) := by
  simp only [bitsClosed,BitsClosed,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_imp_iff,
    Project.Formula.satisfies_mem_iff,somePair_semantics hM]
  rfl

theorem flip_bits (hM : FirstOrder.Theory.Models M nativeZF) {z o B W F Y : M.Carrier .set}
    (hz : Empty z) (ho : (Project.FirstOrderSemantics.reduct M).SuccessorOf o z)
    (hB : (Project.FirstOrderSemantics.reduct M).SuccessorOf B o) (hF : Graph z o W F)
    (hY : (Project.FirstOrderSemantics.reduct M).MemberSubset Y W) (hc : Closed F Y) : BitsClosed B Y := by
  intro a b c x y hb hcB hx hy hxY
  have hFlip (ht : Toggle z o b c) : (Project.FirstOrderSemantics.reduct M).mem y Y := by
    have hf := (ForcingSupportSize.native_mapsTo hM W W F).mp hF.1
    obtain ⟨v,_,hv⟩ := hf.2.2 x (hY x hxY)
    have e := flip_unique hM (hF.2 x v hv) (Or.inr ⟨a,b,c,hx,ht,hy⟩)
    exact e ▸ hc x v hxY hv
  rcases two_cases hM hz ho hB hb with rfl | rfl <;>
    rcases two_cases hM hz ho hB hcB with rfl | rfl
  · exact somePair_unique hM hx hy ▸ hxY
  · exact hFlip (Or.inl ⟨rfl,rfl⟩)
  · exact hFlip (Or.inr ⟨rfl,rfl⟩)
  · exact somePair_unique hM hx hy ▸ hxY

def flipSentence : Project.Sentence where
  formula := Project.Formula.forallClosure 6 (.imp (Project.Formula.isEmpty (.bound 0))
    (.imp (Project.Formula.isSuccessor (.bound 1) (.bound 0))
    (.imp (Project.Formula.isSuccessor (.bound 2) (.bound 1))
    (.imp (ProjectSyntax.encode id (ForcingCohenCoordinates.cartesian (3 : Fin 6) 2 4))
    (.imp (ProjectSyntax.encode id (ForcingWithTopCarrier.carrier (4 : Fin 6) 5))
    (.existsE (.conj (graph (1 : Fin 7) 2 6 0) (.forallE
      (.imp (Project.Formula.subset .newest (.bound 7))
        (.imp (closed (1 : Fin 8) 0) (bitsClosed (4 : Fin 8) 0)))))))))))
  freeClosed := by simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
    graph_freeClosed,closed_freeClosed,bitsClosed_freeClosed]

theorem flip_models (hM : FirstOrder.Theory.Models M nativeZF) : (Project.fo_sentence flipSentence).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) flipSentence]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,Project.Formula.satisfies_isEmpty_iff,
    Project.Formula.satisfies_isSuccessor_iff,Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_conj_iff,Project.Formula.satisfies_forall_iff,Project.Formula.satisfies_subset_iff,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingCohenCoordinates.cartesian_semantics (M := M),ForcingWithTopCarrier.carrier_semantics (M := M),
    graph_semantics hM,closed_semantics hM,bitsClosed_semantics hM]
  intro hz ho hB hS hW
  obtain ⟨F,hF⟩ := exists_flip hM hz ho hB hS hW
  exact ⟨F,hF,fun _ hY hc => flip_bits hM hz ho hB hF hY hc⟩

theorem flip_kernel_certificate : FirstOrder.Derives nativeZF [] (Project.fo_sentence flipSentence) :=
  ModelTransfer.derives (fun _ hM => flip_models hM)

/-- Source hbp: the SAME restricted graph and bit-closed range recover compatibility. -/
theorem compatible_of_bits (hM : FirstOrder.Theory.Models M nativeZF) {C B S w Y p d q : M.Carrier .set}
    (hS : ForcingCohenCoordinates.Cartesian C B S)
    (hp : ForcingCohenConditions.Condition S w p) (hq : ForcingCohenConditions.Condition S w q)
    (hd : ForcingCohenRestriction.Restricted Y p d) (hcover : ForcingCohenRestriction.Covered q Y)
    (hbits : BitsClosed B Y) (hcompat : ConstructionCohenCompatibility.Compatible d q) :
    ConstructionCohenCompatibility.Compatible p q := by
  intro a b c hab hac
  obtain ⟨z,hz,hzp⟩ := hab
  obtain ⟨t,ht,htq⟩ := hac
  have hb : (Project.FirstOrderSemantics.reduct M).mem b B := by
    obtain ⟨a',_,b',hb,hz'⟩ := (hS z).mp (hp.1 z hzp)
    exact (PureKuratowski.code_injective hz' hz).2 ▸ hb
  have hc : (Project.FirstOrderSemantics.reduct M).mem c B := by
    obtain ⟨a',_,c',hc,ht'⟩ := (hS t).mp (hq.1 t htq)
    exact (PureKuratowski.code_injective ht' ht).2 ▸ hc
  obtain ⟨x,hx,hxY⟩ := hcover t htq
  obtain ⟨y,hy⟩ := ForcingWithTopCarrier.exists_single hM z
  have hyY := hbits a c b x y hc hb ⟨t,ht,hx⟩ ⟨z,hz,hy⟩ hxY
  exact hcompat a b c ⟨z,hz,(hd z).mpr ⟨hzp,y,hy,hyY⟩⟩ ⟨t,ht,htq⟩

def compatibilitySentence : Project.Sentence where
  formula := Project.Formula.forallClosure 8
    (.imp (ProjectSyntax.encode id (ForcingCohenCoordinates.cartesian (0 : Fin 8) 1 2))
    (.imp (ProjectSyntax.encode id (ForcingCohenConditions.condition (2 : Fin 8) 3 5))
    (.imp (ProjectSyntax.encode id (ForcingCohenConditions.condition (2 : Fin 8) 3 7))
    (.imp (ForcingCohenRestriction.restricted (4 : Fin 8) 5 6)
    (.imp (ForcingCohenRestriction.covered (7 : Fin 8) 4)
    (.imp (bitsClosed (1 : Fin 8) 4)
    (.imp (ConstructionCompatiblePlacement.compatible (6 : Fin 8) 7)
      (ConstructionCompatiblePlacement.compatible (5 : Fin 8) 7))))))))
  freeClosed := by simp -implicitDefEqProofs [Definitional.Formula.FreeClosed,ProjectSyntax.freeClosed,
    ForcingCohenRestriction.restricted_freeClosed,ForcingCohenRestriction.covered_freeClosed,
    bitsClosed_freeClosed,ConstructionCompatiblePlacement.compatible_freeClosed]

theorem compatibility_models (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence compatibilitySentence).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM) compatibilitySentence]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff,GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingCohenCoordinates.cartesian_semantics (M := M),ForcingCohenConditions.condition_semantics (M := M),
    ForcingCohenRestriction.restricted_semantics hM,ForcingCohenRestriction.covered_semantics hM,
    bitsClosed_semantics hM,ConstructionCompatiblePlacement.compatible_semantics hM]
  exact fun hS hp hq hd hc hb he => compatible_of_bits hM hS hp hq hd hc hb he

theorem compatibility_kernel_certificate : FirstOrder.Derives nativeZF []
    (Project.fo_sentence compatibilitySentence) := ModelTransfer.derives (fun _ hM => compatibility_models hM)

end PPAC.Migration.ForcingCohenFlip
