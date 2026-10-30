/- Pinned GateTowers.finite_descent:51-81 and ConcreteQuotients:99-125.
Actual consumer: ConcreteQuotients.Chain.countable_quotient_of_cells.
Paths are internal finite sequences, stored endpoint-to-start so that the
source single-step prefix is the existing native sequence append. -/
import PPAC.Migration.ConstructionCellDescent
import PPAC.Migration.ConstructionConservativeHull

namespace PPAC.Migration.ConstructionFiniteDescent
open YesMetaZFC YesMetaZFC.Logic YesMetaZFC.Logic.FirstOrder YesMetaZFC.SetTheory
open YesMetaZFC.Logic.FirstOrder.FormalSystem.ProofT.ZFC
open SetTheory.Definitional
open ForcingSupportSize (MapsTo)
open ForcingDiagramOrder (Product)
open ForcingDiagramPoset (LeftCancelMonoid)
open ConstructionBaseMonoid (Divides)
open ConstructionProbeRaw (native_sequence maps_of_sequence)
open ConstructionCellDescent (OldGateStep)
open ConstructionConservativeHull (FactorClosed)
attribute [local implicit_reducible] SetTheory.signature Project.FirstOrderSemantics.reduct
set_option autoImplicit false
set_option maxRecDepth 16384
set_option maxHeartbeats 4000000
universe u
variable {M : FirstOrder.Structure.{0,0,0,u} ℒ}

/-- Literal source replacement: one and the same right factor in both equations. -/
def Replaces (w D mul n A p q : M.Carrier .set) : Prop :=
  (Project.FirstOrderSemantics.reduct M).mem p A ∧
  (Project.FirstOrderSemantics.reduct M).mem q A ∧
  ∃ i j x y ni nj d,
    PureKuratowski.Code M p i x ∧ PureKuratowski.Code M q j y ∧
    (Project.FirstOrderSemantics.reduct M).mem i w ∧
    (Project.FirstOrderSemantics.reduct M).mem j w ∧
    (i = j ∨ (Project.FirstOrderSemantics.reduct M).mem i j) ∧
    (Project.FirstOrderSemantics.reduct M).mem d D ∧
    PureKuratowski.PairMember M i ni n ∧ PureKuratowski.PairMember M j nj n ∧
    Product mul ni d nj ∧ Product mul x d y

/-- An actual nonempty internal sequence, with replacements directed toward zero. -/
def Path (w zero D mul n A p q : M.Carrier .set) : Prop := ∃ k len f,
  (Project.FirstOrderSemantics.reduct M).mem k w ∧
  (Project.FirstOrderSemantics.reduct M).mem len w ∧
  (Project.FirstOrderSemantics.reduct M).SuccessorOf len k ∧ MapsTo len A f ∧
  PureKuratowski.PairMember M zero q f ∧ PureKuratowski.PairMember M k p f ∧
  ∀ i j x y, (Project.FirstOrderSemantics.reduct M).SuccessorOf j i →
    PureKuratowski.PairMember M i x f → PureKuratowski.PairMember M j y f →
    Replaces w D mul n A y x

def Result (w zero D mul n A base p : M.Carrier .set) : Prop := ∃ q j y,
  (Project.FirstOrderSemantics.reduct M).mem q A ∧ PureKuratowski.Code M q j y ∧
  (Project.FirstOrderSemantics.reduct M).mem y base ∧ Path w zero D mul n A p q

def At (w zero D mul n A base stages a : M.Carrier .set) : Prop := ∀ S p i x,
  PureKuratowski.PairMember M a S stages → (Project.FirstOrderSemantics.reduct M).mem p A →
  PureKuratowski.Code M p i x → (Project.FirstOrderSemantics.reduct M).mem x S →
  Result w zero D mul n A base p

/-- Exactly the tower fields used by finite descent. Actual tower construction
and countable reordering are separate producers, not assumed proved here. -/
def Tower (D mul zero base stages : M.Carrier .set) : Prop :=
  PureKuratowski.PairMember M zero base stages ∧
  (∀ a S, PureKuratowski.PairMember M a S stages →
    (Project.FirstOrderSemantics.reduct M).MemberSubset S D) ∧
  (∀ a S, PureKuratowski.PairMember M a S stages →
    (Project.FirstOrderSemantics.reduct M).MemberSubset base S) ∧
  (∀ a b R, PureKuratowski.PairMember M a R stages →
    (Project.FirstOrderSemantics.reduct M).SuccessorOf a b →
    ∃ S, PureKuratowski.PairMember M b S stages ∧ (S = R ∨ OldGateStep D mul S R)) ∧
  (∀ a S, PureKuratowski.PairMember M a S stages →
    (Project.FirstOrderSemantics.reduct M).IsLimitOrdinal a →
    ∀ x, (Project.FirstOrderSemantics.reduct M).mem x S →
    ∃ b R, (Project.FirstOrderSemantics.reduct M).mem b a ∧
      PureKuratowski.PairMember M b R stages ∧ (Project.FirstOrderSemantics.reduct M).mem x R) ∧
  (∀ a S R, PureKuratowski.PairMember M a S stages →
    PureKuratowski.PairMember M a R stages → S = R)

def Inputs (w D mul n A base : M.Carrier .set) : Prop :=
  MapsTo w base n ∧ FactorClosed base D mul ∧
  (∀ p i x, (Project.FirstOrderSemantics.reduct M).mem p A → PureKuratowski.Code M p i x →
    ∃ N nN, (Project.FirstOrderSemantics.reduct M).mem N w ∧
      PureKuratowski.PairMember M N nN n ∧ Divides D mul x nN) ∧
  (∀ p i x N nN, (Project.FirstOrderSemantics.reduct M).mem p A →
    PureKuratowski.Code M p i x → (Project.FirstOrderSemantics.reduct M).mem N w →
    PureKuratowski.PairMember M N nN n →
    ∃ q j y, PureKuratowski.Code M q j y ∧ Replaces w D mul n A p q ∧ Divides D mul nN y)

def replaces {m : Nat} (w D mul n A p q : Fin m) : Project.Formula 1 m :=
  (.conj (.mem (.bound p) (.bound A)) (.conj (.mem (.bound q) (.bound A)) (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.existsE (.conj (PureKuratowskiProject.code (.bound p.succ.succ.succ.succ.succ.succ.succ) (.bound 6) (.bound 4)) (.conj (PureKuratowskiProject.code (.bound q.succ.succ.succ.succ.succ.succ.succ) (.bound 5) (.bound 3)) (.conj (.mem (.bound 6) (.bound w.succ.succ.succ.succ.succ.succ.succ)) (.conj (.mem (.bound 5) (.bound w.succ.succ.succ.succ.succ.succ.succ)) (.conj (.disj (Project.Formula.extensionalEq (.bound 6) (.bound 5)) (.mem (.bound 6) (.bound 5))) (.conj (.mem (.bound 0) (.bound D.succ.succ.succ.succ.succ.succ.succ)) (.conj (ProjectSyntax.encode id (Source.SetLanguage.edge n.succ.succ.succ.succ.succ.succ.succ 6 2)) (.conj (ProjectSyntax.encode id (Source.SetLanguage.edge n.succ.succ.succ.succ.succ.succ.succ 5 1)) (.conj (ProjectSyntax.encode id (ForcingDiagramOrder.product mul.succ.succ.succ.succ.succ.succ.succ 2 0 1)) (ProjectSyntax.encode id (ForcingDiagramOrder.product mul.succ.succ.succ.succ.succ.succ.succ 4 0 3))))))))))))))))))))

theorem replaces_freeClosed {m : Nat} (w D mul n A p q : Fin m) : (replaces w D mul n A p q).FreeClosed := by
  simp -implicitDefEqProofs [replaces, Definitional.Formula.FreeClosed, ProjectSyntax.freeClosed, PureKuratowskiProject.code, Project.Formula.extensionalEq_freeClosed_iff]

theorem replaces_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w D mul n A p q : Fin m) :
    Project.Formula.satisfies env (replaces w D mul n A p q) ↔
      Replaces (env.bound w) (env.bound D) (env.bound mul) (env.bound n) (env.bound A) (env.bound p) (env.bound q) := by
  simp only [replaces, Replaces, Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_disj_iff, Project.Formula.satisfies_mem_iff,
    Project.Formula.satisfies_extensionalEq_iff_eq (ModelTransfer.extensionality hM),
    
    Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    KuratowskiZF.source_edge, KuratowskiZF.code_correct hM,
    
    ForcingDiagramOrder.product_semantics (M := M)]
  rfl

def path {m : Nat} (w zero D mul n A p q : Fin m) : Project.Formula 1 m :=
  (.existsE (.existsE (.existsE (.conj (.mem (.bound 2) (.bound w.succ.succ.succ)) (.conj (.mem (.bound 1) (.bound w.succ.succ.succ)) (.conj (Project.Formula.isSuccessor (.bound 1) (.bound 2)) (.conj (ProjectSyntax.encode id (Source.SetLanguage.mapsTo 0 1 A.succ.succ.succ)) (.conj (ProjectSyntax.encode id (Source.SetLanguage.edge 0 zero.succ.succ.succ q.succ.succ.succ)) (.conj (ProjectSyntax.encode id (Source.SetLanguage.edge 0 2 p.succ.succ.succ)) (.forallE (.forallE (.forallE (.forallE (.imp (Project.Formula.isSuccessor (.bound 2) (.bound 3)) (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge 4 3 1)) (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge 4 2 0)) (replaces w.succ.succ.succ.succ.succ.succ.succ D.succ.succ.succ.succ.succ.succ.succ mul.succ.succ.succ.succ.succ.succ.succ n.succ.succ.succ.succ.succ.succ.succ A.succ.succ.succ.succ.succ.succ.succ 0 1)))))))))))))))))

theorem path_freeClosed {m : Nat} (w zero D mul n A p q : Fin m) : (path w zero D mul n A p q).FreeClosed := by
  simp -implicitDefEqProofs [path, Definitional.Formula.FreeClosed, ProjectSyntax.freeClosed, Project.Formula.isSuccessor, Project.Formula.extensionalEq_freeClosed_iff, replaces_freeClosed]

theorem path_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w zero D mul n A p q : Fin m) :
    Project.Formula.satisfies env (path w zero D mul n A p q) ↔
      Path (env.bound w) (env.bound zero) (env.bound D) (env.bound mul) (env.bound n) (env.bound A) (env.bound p) (env.bound q) := by
  simp only [path, Path, Project.Formula.satisfies_forall_iff, Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_imp_iff, Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_mem_iff,
    
    Project.Formula.satisfies_isSuccessor_iff, 
    Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    KuratowskiZF.source_edge, 
    ForcingSupportSize.mapsTo_semantics (M := M),
    
    replaces_semantics hM]
  rfl

def result {m : Nat} (w zero D mul n A base p : Fin m) : Project.Formula 1 m :=
  (.existsE (.existsE (.existsE (.conj (.mem (.bound 2) (.bound A.succ.succ.succ)) (.conj (PureKuratowskiProject.code (.bound 2) (.bound 1) (.bound 0)) (.conj (.mem (.bound 0) (.bound base.succ.succ.succ)) (path w.succ.succ.succ zero.succ.succ.succ D.succ.succ.succ mul.succ.succ.succ n.succ.succ.succ A.succ.succ.succ p.succ.succ.succ 2)))))))

theorem result_freeClosed {m : Nat} (w zero D mul n A base p : Fin m) : (result w zero D mul n A base p).FreeClosed := by
  simp -implicitDefEqProofs [result, Definitional.Formula.FreeClosed, PureKuratowskiProject.code, path_freeClosed]

theorem result_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w zero D mul n A base p : Fin m) :
    Project.Formula.satisfies env (result w zero D mul n A base p) ↔
      Result (env.bound w) (env.bound zero) (env.bound D) (env.bound mul) (env.bound n) (env.bound A) (env.bound base) (env.bound p) := by
  simp only [result, Result, Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_mem_iff,
    
    
    Project.Term.eval_bound,
    
    KuratowskiZF.code_correct hM,
    
    
    path_semantics hM]
  rfl

def atStage {m : Nat} (w zero D mul n A base stages a : Fin m) : Project.Formula 1 m :=
  (.forallE (.forallE (.forallE (.forallE (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge stages.succ.succ.succ.succ a.succ.succ.succ.succ 3)) (.imp (.mem (.bound 2) (.bound A.succ.succ.succ.succ)) (.imp (PureKuratowskiProject.code (.bound 2) (.bound 1) (.bound 0)) (.imp (.mem (.bound 0) (.bound 3)) (result w.succ.succ.succ.succ zero.succ.succ.succ.succ D.succ.succ.succ.succ mul.succ.succ.succ.succ n.succ.succ.succ.succ A.succ.succ.succ.succ base.succ.succ.succ.succ 2)))))))))

theorem atStage_freeClosed {m : Nat} (w zero D mul n A base stages a : Fin m) : (atStage w zero D mul n A base stages a).FreeClosed := by
  simp -implicitDefEqProofs [atStage, Definitional.Formula.FreeClosed, ProjectSyntax.freeClosed, PureKuratowskiProject.code, result_freeClosed]

theorem atStage_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w zero D mul n A base stages a : Fin m) :
    Project.Formula.satisfies env (atStage w zero D mul n A base stages a) ↔
      At (env.bound w) (env.bound zero) (env.bound D) (env.bound mul) (env.bound n) (env.bound A) (env.bound base) (env.bound stages) (env.bound a) := by
  simp only [atStage, At, Project.Formula.satisfies_forall_iff, 
    Project.Formula.satisfies_imp_iff, 
    Project.Formula.satisfies_mem_iff,
    
    
    Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    KuratowskiZF.source_edge, KuratowskiZF.code_correct hM,
    
    
    result_semantics hM]
  rfl

def tower {m : Nat} (D mul zero base stages : Fin m) : Project.Formula 1 m :=
  (.conj (ProjectSyntax.encode id (Source.SetLanguage.edge stages zero base)) (.conj (.forallE (.forallE (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge stages.succ.succ 1 0)) (Project.Formula.subset (.bound 0) (.bound D.succ.succ))))) (.conj (.forallE (.forallE (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge stages.succ.succ 1 0)) (Project.Formula.subset (.bound base.succ.succ) (.bound 0))))) (.conj (.forallE (.forallE (.forallE (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge stages.succ.succ.succ 2 0)) (.imp (Project.Formula.isSuccessor (.bound 2) (.bound 1)) (.existsE (.conj (ProjectSyntax.encode id (Source.SetLanguage.edge stages.succ.succ.succ.succ 2 0)) (.disj (Project.Formula.extensionalEq (.bound 0) (.bound 1)) (ConstructionCellDescent.oldGateStep D.succ.succ.succ.succ mul.succ.succ.succ.succ 0 1))))))))) (.conj (.forallE (.forallE (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge stages.succ.succ 1 0)) (.imp (Project.Formula.isLimitOrdinal (.bound 1)) (.forallE (.imp (.mem (.bound 0) (.bound 1)) (.existsE (.existsE (.conj (.mem (.bound 1) (.bound 4)) (.conj (ProjectSyntax.encode id (Source.SetLanguage.edge stages.succ.succ.succ.succ.succ 1 0)) (.mem (.bound 2) (.bound 0)))))))))))) (.forallE (.forallE (.forallE (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge stages.succ.succ.succ 2 1)) (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge stages.succ.succ.succ 2 0)) (Project.Formula.extensionalEq (.bound 1) (.bound 0))))))))))))

theorem tower_freeClosed {m : Nat} (D mul zero base stages : Fin m) : (tower D mul zero base stages).FreeClosed := by
  simp -implicitDefEqProofs [tower, Definitional.Formula.FreeClosed, ProjectSyntax.freeClosed, Project.Formula.isSuccessor, Project.Formula.isOrdinal, Project.Formula.isLimitOrdinal, Project.Formula.subset, Project.Formula.extensionalEq_freeClosed_iff, ConstructionCellDescent.oldGateStep_freeClosed]

theorem tower_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (D mul zero base stages : Fin m) :
    Project.Formula.satisfies env (tower D mul zero base stages) ↔
      Tower (env.bound D) (env.bound mul) (env.bound zero) (env.bound base) (env.bound stages) := by
  simp only [tower, Tower, Project.Formula.satisfies_forall_iff, Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_imp_iff, Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_disj_iff, Project.Formula.satisfies_mem_iff,
    Project.Formula.satisfies_extensionalEq_iff_eq (ModelTransfer.extensionality hM),
    Project.Formula.satisfies_isSuccessor_iff, Project.Formula.satisfies_isLimitOrdinal_iff,
    Project.Formula.satisfies_subset_iff, Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    KuratowskiZF.source_edge, 
    
    
    ConstructionCellDescent.oldGateStep_semantics hM]
  rfl

def inputs {m : Nat} (w D mul n A base : Fin m) : Project.Formula 1 m :=
  (.conj (ProjectSyntax.encode id (Source.SetLanguage.mapsTo n w base)) (.conj (ConstructionConservativeHull.factorClosed base D mul) (.conj (.forallE (.forallE (.forallE (.imp (.mem (.bound 2) (.bound A.succ.succ.succ)) (.imp (PureKuratowskiProject.code (.bound 2) (.bound 1) (.bound 0)) (.existsE (.existsE (.conj (.mem (.bound 1) (.bound w.succ.succ.succ.succ.succ)) (.conj (ProjectSyntax.encode id (Source.SetLanguage.edge n.succ.succ.succ.succ.succ 1 0)) (ProjectSyntax.encode id (ConstructionBaseMonoid.divides D.succ.succ.succ.succ.succ mul.succ.succ.succ.succ.succ 2 0))))))))))) (.forallE (.forallE (.forallE (.forallE (.forallE (.imp (.mem (.bound 4) (.bound A.succ.succ.succ.succ.succ)) (.imp (PureKuratowskiProject.code (.bound 4) (.bound 3) (.bound 2)) (.imp (.mem (.bound 1) (.bound w.succ.succ.succ.succ.succ)) (.imp (ProjectSyntax.encode id (Source.SetLanguage.edge n.succ.succ.succ.succ.succ 1 0)) (.existsE (.existsE (.existsE (.conj (PureKuratowskiProject.code (.bound 2) (.bound 1) (.bound 0)) (.conj (replaces w.succ.succ.succ.succ.succ.succ.succ.succ D.succ.succ.succ.succ.succ.succ.succ.succ mul.succ.succ.succ.succ.succ.succ.succ.succ n.succ.succ.succ.succ.succ.succ.succ.succ A.succ.succ.succ.succ.succ.succ.succ.succ 7 2) (ProjectSyntax.encode id (ConstructionBaseMonoid.divides D.succ.succ.succ.succ.succ.succ.succ.succ mul.succ.succ.succ.succ.succ.succ.succ.succ 3 0)))))))))))))))))))

theorem inputs_freeClosed {m : Nat} (w D mul n A base : Fin m) : (inputs w D mul n A base).FreeClosed := by
  simp -implicitDefEqProofs [inputs, Definitional.Formula.FreeClosed, ProjectSyntax.freeClosed, PureKuratowskiProject.code, ConstructionConservativeHull.factorClosed_freeClosed, replaces_freeClosed]

theorem inputs_semantics (hM : FirstOrder.Theory.Models M nativeZF) {m : Nat}
    (env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) m) (w D mul n A base : Fin m) :
    Project.Formula.satisfies env (inputs w D mul n A base) ↔
      Inputs (env.bound w) (env.bound D) (env.bound mul) (env.bound n) (env.bound A) (env.bound base) := by
  simp only [inputs, Inputs, Project.Formula.satisfies_forall_iff, Project.Formula.satisfies_exists_iff,
    Project.Formula.satisfies_imp_iff, Project.Formula.satisfies_conj_iff,
    Project.Formula.satisfies_mem_iff,
    
    
    Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    KuratowskiZF.source_edge, KuratowskiZF.code_correct hM,
    ForcingSupportSize.mapsTo_semantics (M := M),
    ConstructionBaseMonoid.divides_semantics (M := M),
    ConstructionConservativeHull.factorClosed_semantics hM, replaces_semantics hM]
  rfl


/-- Zero replacements, represented by a genuine internal singleton sequence. -/
theorem path_refl (hM : FirstOrder.Theory.Models M nativeZF) {w zero D mul n A p : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ x, ¬ (Project.FirstOrderSemantics.reduct M).mem x zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hp : (Project.FirstOrderSemantics.reduct M).mem p A) : Path w zero D mul n A p p := by
  have hZF := ModelTransfer.project_models_iff.mp hM
  obtain ⟨one,hone,honw⟩ := hw.1.2 zero hzw
  obtain ⟨f,hf,hgraph⟩ := (SetTheory.Structure.IsSequenceOfLength.empty
    (KuratowskiZF.interpretation hM) hz).exists_append (ZF.modelsKP hZF)
    (KuratowskiZF.interpretation hM) (value := p) (hw.members_areOrdinals hZF one honw) hone
  have hEmpty (i x) : ¬ PureKuratowski.PairMember M i x zero := by
    rintro ⟨z,_,hz'⟩; exact hz z hz'
  have hMap : MapsTo one A f := maps_of_sequence hM hf (by
    intro i x hx
    rcases (hgraph i x).mp hx with he | ⟨_,rfl⟩
    · exact (hEmpty i x he).elim
    · exact hp)
  have hPoint := (hgraph zero p).mpr (Or.inr ⟨rfl,rfl⟩)
  refine ⟨zero,one,f,hzw,honw,hone,hMap,hPoint,hPoint,?_⟩
  intro i j x y hs hx hy
  obtain ⟨hi,hxEq⟩ := ((hgraph i x).mp hx).resolve_left (hEmpty i x)
  subst i; subst x
  obtain ⟨hj,hyEq⟩ := ((hgraph j y).mp hy).resolve_left (hEmpty j y)
  subst j; subst y
  exact (hz zero hs.predecessor_mem).elim

/-- Prepend one source replacement by appending to the reversed internal path. -/
theorem path_prepend (hM : FirstOrder.Theory.Models M nativeZF)
    {w zero D mul n A p r q : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hstep : Replaces w D mul n A p r) (hpath : Path w zero D mul n A r q) :
    Path w zero D mul n A p q := by
  have hZF := ModelTransfer.project_models_iff.mp hM
  obtain ⟨k,len,f,hkw,hlenw,hsk,hf,hq,hr,hsteps⟩ := hpath
  obtain ⟨len',hslen,hlen'w⟩ := hw.1.2 len hlenw
  have hlenOrd := hw.members_areOrdinals hZF len hlenw
  obtain ⟨g,hg,hgraph⟩ := (native_sequence hM hlenOrd hf).exists_append
    (ZF.modelsKP hZF) (KuratowskiZF.interpretation hM) (value := p)
    (hw.members_areOrdinals hZF len' hlen'w) hslen
  have hgMap : MapsTo len' A g := maps_of_sequence hM hg (by
    intro i x hx
    rcases (hgraph i x).mp hx with he | ⟨_,rfl⟩
    · exact hf.2 i x he
    · exact hstep.1)
  refine ⟨len,len',g,hlenw,hlen'w,hslen,hgMap,(hgraph zero q).mpr (Or.inl hq),
    (hgraph len p).mpr (Or.inr ⟨rfl,rfl⟩),?_⟩
  intro i j x y hs hx hy
  rcases (hgraph i x).mp hx with hx | ⟨hiEq,hxEq⟩
  · rcases (hgraph j y).mp hy with hy | ⟨hjEq,hyEq⟩
    · exact hsteps i j x y hs hx hy
    · subst j; subst y
      have hi : (Project.FirstOrderSemantics.reduct M).mem i len :=
        ((native_sequence hM hlenOrd hf).2.2 i).mpr ⟨x,hx⟩
      have he : i = k := SetTheory.Structure.SuccessorOf.predecessor_eq hZF.1
        (hw.members_areOrdinals hZF i ((hw.isOrdinal hZF).transitive len hlenw i hi)) hs hsk
      subst i
      have he := ForcingConditionGraphs.function_unique hf.1 hx hr
      subst x
      exact hstep
  · subst i; subst x
    rcases (hgraph j y).mp hy with hy | ⟨hjEq,hyEq⟩
    · have hj : (Project.FirstOrderSemantics.reduct M).mem j len :=
        ((native_sequence hM hlenOrd hf).2.2 j).mpr ⟨y,hy⟩
      have hh := hlenOrd.transitive j hj len hs.predecessor_mem
      exact (hlenOrd.wellOrder.linear.irrefl len hh hh).elim
    · subst j; subst y
      have hh := hs.predecessor_mem
      exact (hlenOrd.wellOrder.linear.irrefl len hh hh).elim

/-- Literal stage induction, with an internal finite path retained at every step. -/
theorem finite_descent (hM : FirstOrder.Theory.Models M nativeZF)
    {w zero D mul e n A base stages a : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ x, ¬ (Project.FirstOrderSemantics.reduct M).mem x zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hm : LeftCancelMonoid D mul e) (hT : Tower D mul zero base stages)
    (hI : Inputs w D mul n A base)
    (ha : (Project.FirstOrderSemantics.reduct M).IsOrdinal a) : At w zero D mul n A base stages a := by
  classical
  have hZF := ModelTransfer.project_models_iff.mp hM
  let env : SetTheory.Env (Project.FirstOrderSemantics.reduct M) 8 := {
    bound := Fin.cases w (Fin.cases zero (Fin.cases D (Fin.cases mul
      (Fin.cases n (Fin.cases A (Fin.cases base (fun _ => stages)))))))
    free := fun _ => zero }
  let schema : Project.UnarySchema 8 := {
    body := atStage 1 2 3 4 5 6 7 8 0
    freeClosed := atStage_freeClosed _ _ _ _ _ _ _ _ _ }
  have hMeaning (b : M.Carrier .set) : schema.denote env b ↔ At w zero D mul n A base stages b :=
    atStage_semantics hM (env.push b) 1 2 3 4 5 6 7 8 0
  apply ha.induction (At w zero D mul n A base stages)
  · obtain ⟨B,hB⟩ := ZF.separation_exists_d hZF schema.neg env a
    refine ⟨B,fun b => (hB b).trans (and_congr_right (fun _ => ?_))⟩
    change Project.Formula.satisfies (env.push b) (.neg schema.body) ↔ _
    rw [Project.Formula.satisfies_neg_iff]
    exact not_congr (hMeaning b)
  · intro b hb ih S p i x hS hp hpx hx
    rcases hb.classify hZF.1 with hb0 | ⟨c,hc,hbc⟩ | hlim
    · have he : b = zero := hZF.1.eq_of_same_members b zero
        (fun z => ⟨fun h => (hb0 z h).elim,fun h => (hz z h).elim⟩)
      subst b
      have he := hT.2.2.2.2.2 zero S base hS hT.1
      subst S
      exact ⟨p,i,x,hp,hpx,hx,path_refl hM hw hz hzw hp⟩
    · obtain ⟨R,hR,hstep⟩ := hT.2.2.2.1 b c S hS hbc
      by_cases hxR : (Project.FirstOrderSemantics.reduct M).mem x R
      · exact ih c hbc.predecessor_mem R p i x hR hp hpx hxR
      rcases hstep with he | hgate
      · exact (hxR (he.symm ▸ hx)).elim
      obtain ⟨N,nN,hNw,hN,hbound⟩ := hI.2.2.1 p i x hp hpx
      have hNbase := hI.1.2 N nN hN
      have hNR := hT.2.2.1 c R hR nN hNbase
      obtain ⟨g,hgR,_,hleast,hconsume⟩ := hgate x hx hxR ⟨nN,hNR,hbound⟩
      obtain ⟨q,j,y,hqy,hrep,hNy⟩ := hI.2.2.2 p i x N nN hp hpx hNw hN
      obtain ⟨i',j',x',y',ni,nj,d,hpc,hqc,_,_,_,hd,hni,hnj,hnd,hxd⟩ := hrep.2.2
      obtain ⟨hiEq,hxEq⟩ := PureKuratowski.code_injective hpc hpx
      subst i'; subst x'
      obtain ⟨hjEq,hyEq⟩ := PureKuratowski.code_injective hqc hqy
      subst j'; subst y'
      have hdBase := hI.2.1 ni nj d (hI.1.2 i ni hni) (hI.1.2 j nj hnj) hd hnd
      have hdR := hT.2.2.1 c R hR d hdBase
      have hgy := ConstructionProbeGates.divides_trans hm (hT.2.1 c R hR g hgR)
        (hleast nN hNR hbound) hNy
      have hyR := hconsume d y hdR hxd hgy
      obtain ⟨q',j',y',hq',hc',hy',hpath⟩ := ih c hbc.predecessor_mem R q j y hR hrep.2.1 hqy hyR
      exact ⟨q',j',y',hq',hc',hy',path_prepend hM hw hrep hpath⟩
    · obtain ⟨c,R,hcb,hR,hxR⟩ := hT.2.2.2.2.1 b S hS hlim x hx
      exact ih c hcb R p i x hR hp hpx hxR

/-- At a terminal stage equal to the whole monoid, every alignment descends. -/
theorem finite_descent_terminal (hM : FirstOrder.Theory.Models M nativeZF)
    {w zero D mul e n A base stages top p i x : M.Carrier .set}
    (hw : (Project.FirstOrderSemantics.reduct M).IsOmega w)
    (hz : ∀ x, ¬ (Project.FirstOrderSemantics.reduct M).mem x zero)
    (hzw : (Project.FirstOrderSemantics.reduct M).mem zero w)
    (hm : LeftCancelMonoid D mul e) (hT : Tower D mul zero base stages)
    (hI : Inputs w D mul n A base)
    (htop : (Project.FirstOrderSemantics.reduct M).IsOrdinal top)
    (hTerminal : PureKuratowski.PairMember M top D stages)
    (hp : (Project.FirstOrderSemantics.reduct M).mem p A) (hc : PureKuratowski.Code M p i x)
    (hx : (Project.FirstOrderSemantics.reduct M).mem x D) : Result w zero D mul n A base p :=
  finite_descent hM hw hz hzw hm hT hI htop D p i x hTerminal hp hc hx

def sourceSentence {m : Nat} (w zero D mul e n A base stages a : Fin m) : Project.Sentence where
  formula := Project.Formula.forallClosure m
    (.imp (Project.Formula.isOmega (.bound w))
      (.imp (Project.Formula.isEmpty (.bound zero))
        (.imp (.mem (.bound zero) (.bound w))
          (.imp (ProjectSyntax.encode id (ForcingDiagramPoset.leftCancelMonoid D mul e))
            (.imp (tower D mul zero base stages)
              (.imp (inputs w D mul n A base)
                (.imp (Project.Formula.isOrdinal (.bound a))
                  (atStage w zero D mul n A base stages a))))))))
  freeClosed := by
    simp -implicitDefEqProofs [Definitional.Formula.FreeClosed, Project.Formula.isOmega,
      Project.Formula.isEmpty, Project.Formula.isOrdinal, ProjectSyntax.freeClosed,
      tower_freeClosed, inputs_freeClosed, atStage_freeClosed]

theorem source_models {m : Nat} (w zero D mul e n A base stages a : Fin m)
    (hM : FirstOrder.Theory.Models M nativeZF) :
    (Project.fo_sentence (sourceSentence w zero D mul e n A base stages a)).TrueIn M := by
  rw [Project.FirstOrderSemantics.sentence_correct (ModelTransfer.extensionality hM)
    (sourceSentence w zero D mul e n A base stages a)]
  intro free
  apply (Project.Formula.satisfies_forallClosure_iff free _).mpr
  intro bound
  simp only [Project.Formula.satisfies_imp_iff, Project.Formula.satisfies_isOmega_iff,
    Project.Formula.satisfies_isEmpty_iff, Project.Formula.satisfies_mem_iff,
    Project.Formula.satisfies_isOrdinal_iff, Project.Term.eval_bound,
    GodelDefRecursion.encode_semantics (ModelTransfer.extensionality hM),
    ForcingDiagramPoset.leftCancelMonoid_semantics (M := M), tower_semantics hM,
    inputs_semantics hM, atStage_semantics hM]
  exact finite_descent hM

theorem source_kernel_certificate {m : Nat} (w zero D mul e n A base stages a : Fin m) :
    FirstOrder.Derives nativeZF []
      (Project.fo_sentence (sourceSentence w zero D mul e n A base stages a)) :=
  ModelTransfer.derives (fun _ hM => source_models w zero D mul e n A base stages a hM)

end PPAC.Migration.ConstructionFiniteDescent
