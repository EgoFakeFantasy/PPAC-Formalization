/- Internal graphs for the actual permutations in pinned
ForcingNames.ConditionAction. Reuses the original functionOn formula and
YesMetaZFC's identity-schema, inverse and composition graph constructions. -/
import PPAC.Migration.ForcingEvaluationCovariance
import YesMetaZFC.SetTheory.FunctionConstruction

namespace PPAC.Migration.ForcingConditionGraphs
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open Source (Formula)
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
attribute [local implicit_reducible] SetTheory.signature Definitional.Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 4096
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

def FunctionOn (P r : M.Carrier .set) : Prop :=
  (∀ z, (Definitional.Project.FirstOrderSemantics.reduct M).mem z r →
    ∃ x y, (Definitional.Project.FirstOrderSemantics.reduct M).mem x P ∧ PureKuratowski.Code M z x y) ∧
  ∀ x, (Definitional.Project.FirstOrderSemantics.reduct M).mem x P →
    ∃ y, PureKuratowski.PairMember M x y r ∧ ∀ z, PureKuratowski.PairMember M x z r → z = y

theorem functionOn_semantics {m : Nat} (v : Fin m → M.Carrier .set) (P r : Fin m) :
    Formula.Realize (Definitional.Project.FirstOrderSemantics.reduct M).mem v (Source.SetLanguage.functionOn r P) ↔
      FunctionOn (v P) (v r) := by
  rw [GraphSyntax.functionOn_original]
  simp only [GraphSyntax.functionOn, GraphSyntax.entriesOn, GraphSyntax.entryOn, GraphSyntax.totalOn,
    GraphSyntax.valueExists, GraphSyntax.valueAt, ← GraphSyntax.edge_original, Formula.Realize,
    KuratowskiZF.source_code, KuratowskiZF.source_edge, Fin.lastCases_last, Fin.lastCases_castSucc, FunctionOn]
  rfl

def endomap {m : Nat} (P r : Fin m) : Formula m :=
  (Source.SetLanguage.functionOn r P).conj (.all (.all
    ((Source.SetLanguage.edge r.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))).imp
      (.mem (Fin.last (m+1)) P.castSucc.castSucc))))

def Endomap (P r : M.Carrier .set) : Prop :=
  FunctionOn P r ∧ ∀ x y, PureKuratowski.PairMember M x y r →
    (Definitional.Project.FirstOrderSemantics.reduct M).mem y P

theorem endomap_semantics {m : Nat} (v : Fin m → M.Carrier .set) (P r : Fin m) :
    Formula.Realize (Definitional.Project.FirstOrderSemantics.reduct M).mem v (endomap P r) ↔ Endomap (v P) (v r) := by
  simp only [endomap, Formula.Realize, functionOn_semantics (M := M), KuratowskiZF.source_edge,
    Fin.lastCases_last, Fin.lastCases_castSucc, Endomap]
  rfl

def permutation {m : Nat} (P r : Fin m) : Formula m :=
  (endomap P r).conj ((Formula.all (.all (.all
    ((Source.SetLanguage.edge r.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc (Fin.last (m+2))).imp
      ((Source.SetLanguage.edge r.castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc (Fin.last (m+2))).imp
        (.equal (Fin.last m).castSucc.castSucc (Fin.last (m+1)).castSucc)))))).conj
    (.all ((Formula.mem (Fin.last m) P.castSucc).imp (.ex
      ((Formula.mem (Fin.last (m+1)) P.castSucc.castSucc).conj
        (Source.SetLanguage.edge r.castSucc.castSucc (Fin.last (m+1)) (Fin.last m).castSucc))))))

def Permutation (P r : M.Carrier .set) : Prop :=
  Endomap P r ∧ (∀ x y z, PureKuratowski.PairMember M x z r → PureKuratowski.PairMember M y z r → x = y) ∧
    ∀ y, (Definitional.Project.FirstOrderSemantics.reduct M).mem y P →
      ∃ x, (Definitional.Project.FirstOrderSemantics.reduct M).mem x P ∧ PureKuratowski.PairMember M x y r

theorem permutation_semantics {m : Nat} (v : Fin m → M.Carrier .set) (P r : Fin m) :
    Formula.Realize (Definitional.Project.FirstOrderSemantics.reduct M).mem v (permutation P r) ↔ Permutation (v P) (v r) := by
  simp only [permutation, Formula.Realize, endomap_semantics (M := M), KuratowskiZF.source_edge,
    Fin.lastCases_last, Fin.lastCases_castSucc, Permutation]
  rfl

theorem function_input {P r x y : M.Carrier .set} (h : FunctionOn P r) (he : PureKuratowski.PairMember M x y r) :
    (Definitional.Project.FirstOrderSemantics.reduct M).mem x P := by
  obtain ⟨code, hCode, hMem⟩ := he
  obtain ⟨x', y', hx, hCode'⟩ := h.1 code hMem
  obtain ⟨hx', _⟩ := PureKuratowski.code_injective hCode hCode'
  exact hx'.symm ▸ hx

theorem function_unique {P r x y z : M.Carrier .set} (h : FunctionOn P r)
    (hy : PureKuratowski.PairMember M x y r) (hz : PureKuratowski.PairMember M x z r) : y = z := by
  obtain ⟨value, _, hu⟩ := h.2 x (function_input h hy)
  exact (hu y hy).trans (hu z hz).symm

/-- Exact interface to the completed donor function constructors. -/
theorem native_endomap (hM : FirstOrder.Theory.Models M nativeZF) (P r : M.Carrier .set) :
    Endomap P r ↔ (Definitional.Project.FirstOrderSemantics.reduct M).IsSetFunctionFromTo
      (KuratowskiZF.interpretation hM) r P P := by
  constructor
  · intro h
    refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
    · intro z hz
      obtain ⟨x, y, _, hCode⟩ := h.1.1 z hz
      exact ⟨x, y, hCode⟩
    · intro x y z hy hz
      exact function_unique h.1 hy hz
    · intro x
      constructor
      · intro hx
        obtain ⟨y, hy, _⟩ := h.1.2 x hx
        exact ⟨y, hy⟩
      · rintro ⟨y, hy⟩
        exact function_input h.1 hy
    · intro x hx
      obtain ⟨y, hy, _⟩ := h.1.2 x hx
      exact ⟨y, h.2 x y hy, hy⟩
  · intro h
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · intro z hz
      obtain ⟨x, y, hCode⟩ := h.1.1 z hz
      exact ⟨x, y, h.input_mem_of_pairMember ⟨z, hCode, hz⟩, hCode⟩
    · intro x hx
      obtain ⟨y, _, hy⟩ := h.2.2 x hx
      exact ⟨y, hy, fun z hz => h.1.2 x z y hz hy⟩
    · intro x y he
      exact h.output_mem_of_pairMember he

theorem native_permutation (hM : FirstOrder.Theory.Models M nativeZF) (P r : M.Carrier .set) :
    Permutation P r ↔ (Definitional.Project.FirstOrderSemantics.reduct M).IsSetBijectionFromTo
      (KuratowskiZF.interpretation hM) r P P := by
  constructor
  · intro h
    exact ⟨⟨(native_endomap hM P r).mp h.1, h.2.1⟩, h.2.2⟩
  · intro h
    exact ⟨(native_endomap hM P r).mpr h.1.1, h.1.2, h.2⟩

def identityGraph {m : Nat} (P r : Fin m) : Formula m :=
  .all (.all ((Source.SetLanguage.edge r.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))).iff
    ((Formula.mem (Fin.last m).castSucc P.castSucc.castSucc).conj (.equal (Fin.last m).castSucc (Fin.last (m+1))))))

def IdentityGraph (P r : M.Carrier .set) : Prop :=
  ∀ x y, PureKuratowski.PairMember M x y r ↔ (Definitional.Project.FirstOrderSemantics.reduct M).mem x P ∧ x = y

theorem identityGraph_semantics {m : Nat} (v : Fin m → M.Carrier .set) (P r : Fin m) :
    Formula.Realize (Definitional.Project.FirstOrderSemantics.reduct M).mem v (identityGraph P r) ↔ IdentityGraph (v P) (v r) := by
  simp only [identityGraph, Source.Formula.iff, Formula.Realize, KuratowskiZF.source_edge,
    Fin.lastCases_last, Fin.lastCases_castSucc, IdentityGraph]
  exact forall_congr' (fun _ => forall_congr' (fun _ => ⟨fun h => ⟨h.1, h.2⟩, fun h => ⟨h.mp, h.mpr⟩⟩))

def inverseGraph {m : Nat} (r s : Fin m) : Formula m :=
  .all (.all ((Source.SetLanguage.edge r.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))).iff
    (Source.SetLanguage.edge s.castSucc.castSucc (Fin.last (m+1)) (Fin.last m).castSucc)))

def InverseGraph (r s : M.Carrier .set) : Prop :=
  ∀ x y, PureKuratowski.PairMember M x y r ↔ PureKuratowski.PairMember M y x s

theorem inverseGraph_semantics {m : Nat} (v : Fin m → M.Carrier .set) (r s : Fin m) :
    Formula.Realize (Definitional.Project.FirstOrderSemantics.reduct M).mem v (inverseGraph r s) ↔ InverseGraph (v r) (v s) := by
  simp only [inverseGraph, Source.Formula.iff, Formula.Realize, KuratowskiZF.source_edge,
    Fin.lastCases_last, Fin.lastCases_castSucc, InverseGraph]
  exact forall_congr' (fun _ => forall_congr' (fun _ => ⟨fun h => ⟨h.1, h.2⟩, fun h => ⟨h.mp, h.mpr⟩⟩))

def compositionGraph {m : Nat} (P r s t : Fin m) : Formula m :=
  .all (.all ((Source.SetLanguage.edge t.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))).iff
    ((Formula.mem (Fin.last m).castSucc P.castSucc.castSucc).conj (.ex
      ((Source.SetLanguage.edge s.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc (Fin.last (m+2))).conj
        (Source.SetLanguage.edge r.castSucc.castSucc.castSucc (Fin.last (m+2)) (Fin.last (m+1)).castSucc))))))

def CompositionGraph (P r s t : M.Carrier .set) : Prop :=
  ∀ x z, PureKuratowski.PairMember M x z t ↔ (Definitional.Project.FirstOrderSemantics.reduct M).mem x P ∧
    ∃ y, PureKuratowski.PairMember M x y s ∧ PureKuratowski.PairMember M y z r

theorem compositionGraph_semantics {m : Nat} (v : Fin m → M.Carrier .set) (P r s t : Fin m) :
    Formula.Realize (Definitional.Project.FirstOrderSemantics.reduct M).mem v (compositionGraph P r s t) ↔
      CompositionGraph (v P) (v r) (v s) (v t) := by
  simp only [compositionGraph, Source.Formula.iff, Formula.Realize, KuratowskiZF.source_edge,
    Fin.lastCases_last, Fin.lastCases_castSucc, CompositionGraph]
  exact forall_congr' (fun _ => forall_congr' (fun _ => ⟨fun h => ⟨h.1, h.2⟩, fun h => ⟨h.mp, h.mpr⟩⟩))

/-- The general donor function constructor retains exact pairs, unlike its
existence-only identity-bijection corollary. No new graph construction. -/
theorem exists_identity (hM : FirstOrder.Theory.Models M nativeZF) (P : M.Carrier .set) :
    ∃ r, Permutation P r ∧ IdentityGraph P r := by
  let env : SetTheory.Env (Definitional.Project.FirstOrderSemantics.reduct M) 0 := ⟨Fin.elim0, fun _ => P⟩
  have hv := Definitional.Project.Formula.denote_identityValue_iff (ModelTransfer.extensionality hM) env
  obtain ⟨r, hr, he⟩ := SetTheory.ZF.exists_setFunctionFromTo_of_denote
    (ModelTransfer.project_models_iff.mp hM) (KuratowskiZF.interpretation hM)
    Definitional.Project.BinarySchema.identityValue env (source := P) (target := P)
    (fun x _ => ⟨x, (hv x x).mpr rfl⟩)
    (fun x _ y z hy hz => ((hv x y).mp hy).symm.trans ((hv x z).mp hz))
    (fun x y hx hy => (hv x y).mp hy ▸ hx)
  have hi : IdentityGraph P r := by
    intro x y
    exact (he x y).trans (and_congr Iff.rfl (hv x y))
  refine ⟨r, ⟨(native_endomap hM P r).mpr hr, ?_, ?_⟩, hi⟩
  · intro x y z hx hy
    exact ((hi x z).mp hx).2.trans ((hi y z).mp hy).2.symm
  · intro y hy
    exact ⟨y, hy, (hi y y).mpr ⟨hy, rfl⟩⟩

theorem exists_inverse (hM : FirstOrder.Theory.Models M nativeZF) {P r : M.Carrier .set}
    (hr : Permutation P r) : ∃ s, Permutation P s ∧ InverseGraph r s := by
  obtain ⟨s, hs, he⟩ := SetTheory.ZF.exists_inverseBijectionWithPairs
    (ModelTransfer.project_models_iff.mp hM) (KuratowskiZF.interpretation hM) ((native_permutation hM P r).mp hr)
  exact ⟨s, (native_permutation hM P s).mpr hs, fun x y => (he y x).symm⟩

theorem exists_composition (hM : FirstOrder.Theory.Models M nativeZF) {P r s : M.Carrier .set}
    (hr : Permutation P r) (hs : Permutation P s) : ∃ t, Permutation P t ∧ CompositionGraph P r s t := by
  obtain ⟨t, ht, he⟩ := SetTheory.ZF.exists_compositionFunction
    (ModelTransfer.project_models_iff.mp hM) (KuratowskiZF.interpretation hM)
    ((native_endomap hM P s).mp hs.1) ((native_endomap hM P r).mp hr.1)
  refine ⟨t, ⟨(native_endomap hM P t).mpr ht, ?_, ?_⟩, he⟩
  · intro x y z hx hy
    obtain ⟨_, mx, hxm, hmx⟩ := (he x z).mp hx
    obtain ⟨_, my, hym, hmy⟩ := (he y z).mp hy
    have hm := hr.2.1 mx my z hmx hmy
    subst my
    exact hs.2.1 x y mx hxm hym
  · intro z hz
    obtain ⟨y, hy, hyr⟩ := hr.2.2 z hz
    obtain ⟨x, hx, hxs⟩ := hs.2.2 y hy
    exact ⟨x, hx, (he x z).mpr ⟨hx, y, hxs, hyr⟩⟩

def identitySentence : Source.Sentence :=
  (Formula.ex ((permutation (Fin.last 0).castSucc (Fin.last 1)).conj
    (identityGraph (Fin.last 0).castSucc (Fin.last 1)))).close

def inverseSentence : Source.Sentence :=
  ((permutation (Fin.last 0).castSucc (Fin.last 1)).imp (.ex
    ((permutation (Fin.last 0).castSucc.castSucc (Fin.last 2)).conj
      (inverseGraph (Fin.last 1).castSucc (Fin.last 2))))).close

def compositionSentence : Source.Sentence :=
  ((permutation (Fin.last 0).castSucc.castSucc (Fin.last 1).castSucc).imp
    ((permutation (Fin.last 0).castSucc.castSucc (Fin.last 2)).imp (.ex
      ((permutation (Fin.last 0).castSucc.castSucc.castSucc (Fin.last 3)).conj
        (compositionGraph (Fin.last 0).castSucc.castSucc.castSucc (Fin.last 1).castSucc.castSucc
          (Fin.last 2).castSucc (Fin.last 3)))))).close

theorem identity_models (hM : FirstOrder.Theory.Models M nativeZF) :
    (Translation.sentence identitySentence).TrueIn M := by
  apply (Translation.realizes_sentence M _).mpr
  apply (GodelDefOutput.close_semantics _ _).mpr
  intro v
  obtain ⟨r, hr, hi⟩ := exists_identity hM (v (Fin.last 0))
  refine ⟨r, ?_, ?_⟩
  · apply (permutation_semantics (Fin.lastCases r v) (Fin.last 0).castSucc (Fin.last 1)).mpr
    simpa only [Fin.lastCases_last, Fin.lastCases_castSucc] using hr
  · apply (identityGraph_semantics (Fin.lastCases r v) (Fin.last 0).castSucc (Fin.last 1)).mpr
    simpa only [Fin.lastCases_last, Fin.lastCases_castSucc] using hi

theorem inverse_models (hM : FirstOrder.Theory.Models M nativeZF) :
    (Translation.sentence inverseSentence).TrueIn M := by
  apply (Translation.realizes_sentence M _).mpr
  apply (GodelDefOutput.close_semantics _ _).mpr
  intro v hr
  obtain ⟨s, hs, hi⟩ := exists_inverse hM ((permutation_semantics v (Fin.last 0).castSucc (Fin.last 1)).mp hr)
  refine ⟨s, ?_, ?_⟩
  · apply (permutation_semantics (Fin.lastCases s v) (Fin.last 0).castSucc.castSucc (Fin.last 2)).mpr
    simpa only [Fin.lastCases_last, Fin.lastCases_castSucc] using hs
  · apply (inverseGraph_semantics (Fin.lastCases s v) (Fin.last 1).castSucc (Fin.last 2)).mpr
    simpa only [Fin.lastCases_last, Fin.lastCases_castSucc] using hi

theorem composition_models (hM : FirstOrder.Theory.Models M nativeZF) :
    (Translation.sentence compositionSentence).TrueIn M := by
  apply (Translation.realizes_sentence M _).mpr
  apply (GodelDefOutput.close_semantics _ _).mpr
  intro v hr hs
  obtain ⟨t, ht, hc⟩ := exists_composition hM
    ((permutation_semantics v (Fin.last 0).castSucc.castSucc (Fin.last 1).castSucc).mp hr)
    ((permutation_semantics v (Fin.last 0).castSucc.castSucc (Fin.last 2)).mp hs)
  refine ⟨t, ?_, ?_⟩
  · apply (permutation_semantics (Fin.lastCases t v) (Fin.last 0).castSucc.castSucc.castSucc (Fin.last 3)).mpr
    simpa only [Fin.lastCases_last, Fin.lastCases_castSucc] using ht
  · apply (compositionGraph_semantics (Fin.lastCases t v) (Fin.last 0).castSucc.castSucc.castSucc
      (Fin.last 1).castSucc.castSucc (Fin.last 2).castSucc (Fin.last 3)).mpr
    simpa only [Fin.lastCases_last, Fin.lastCases_castSucc] using hc

theorem identity_kernel_certificate : FirstOrder.Derives nativeZF [] (Translation.sentence identitySentence) :=
  ModelTransfer.derives (fun _ hM => identity_models hM)
theorem inverse_kernel_certificate : FirstOrder.Derives nativeZF [] (Translation.sentence inverseSentence) :=
  ModelTransfer.derives (fun _ hM => inverse_models hM)
theorem composition_kernel_certificate : FirstOrder.Derives nativeZF [] (Translation.sentence compositionSentence) :=
  ModelTransfer.derives (fun _ hM => composition_models hM)

end PPAC.Migration.ForcingConditionGraphs
