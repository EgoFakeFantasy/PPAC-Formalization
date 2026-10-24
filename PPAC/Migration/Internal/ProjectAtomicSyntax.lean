import PPAC.Migration.Internal.ProjectSubsetExistence

/-! Three original Project atomic source shapes and their actual pure-code outputs. -/
namespace PPAC.Migration.Internal.ProjectAtomicSyntax
open Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax
open SyntaxRenameQuerySyntax (of_eq)

def sourceTag (kind : Fin 3) : Nat := if kind.val=0 then 2 else if kind.val=1 then 3 else 11

def sourceAt {m} (kind : Fin 3) (w b x y n : Fin m) : Formula m :=
  (Formula.mem b w).conj ((SyntaxTermSyntax.branch true w b x).conj
    ((SyntaxTermSyntax.branch true w b y).conj
      (SyntaxNodeSyntax.constructor 2 (sourceTag kind) w (SyntaxAtomSyntax.two x y) n)))

def memberResult {m} (w x y q : Fin m) : Formula m := .ex
  ((SyntaxAtomSyntax.zeroScalar w.castSucc (Fin.last m)).conj
    (SyntaxAtomSyntax.memberCode w.castSucc (Fin.last m) x.castSucc y.castSucc q.castSucc))

def result {m} (kind : Fin 3) (w b z x y q : Fin m) : Formula m :=
  match kind.val with
  | 0 => memberResult w x y q
  | 1 => SyntaxAtomSyntax.equalCode w x y q
  | _ => ProjectSubsetSyntax.expanded w b z x y q

def compiled {m} (kind : Fin 3) (w b z x y n q : Fin m) : Formula m :=
  (sourceAt kind w b x y n).conj (result kind w b z x y q)

def existsResult {m} (kind : Fin 3) (w b z x y : Fin m) : Formula m := .ex
  ((Formula.mem (Fin.last m) w.castSucc).conj (result kind w.castSucc b.castSucc z.castSucc x.castSucc y.castSucc (Fin.last m)))

def uniqueOutput {m} (kind : Fin 3) (w b z x y n q : Fin m) : Formula m := .all
  ((compiled kind w.castSucc b.castSucc z.castSucc x.castSucc y.castSucc n.castSucc (Fin.last m)).imp (.equal (Fin.last m) q.castSucc))

def fiber {m} (kind : Fin 3) (w b z x y n : Fin m) : Formula m := .ex
  ((((Formula.mem (Fin.last m) w.castSucc).conj
    (compiled kind w.castSucc b.castSucc z.castSucc x.castSucc y.castSucc n.castSucc (Fin.last m))).conj
      (FormulaCodeSyntax.formulaCode w.castSucc (Fin.last m) b.castSucc z.castSucc)).conj
        (uniqueOutput kind w.castSucc b.castSucc z.castSucc x.castSucc y.castSucc n.castSucc (Fin.last m)))

theorem sourceAt_rename {m l} (kind : Fin 3) (w b x y n : Fin m) (ρ : Fin m → Fin l) :
    (sourceAt kind w b x y n).rename ρ = sourceAt kind (ρ w) (ρ b) (ρ x) (ρ y) (ρ n) := by
  simp only [sourceAt, Formula.rename, SyntaxTermSyntax.branch_rename, SyntaxNodeSyntax.constructor_rename, SyntaxAtomSyntax.two_map]

theorem memberResult_rename {m l} (w x y q : Fin m) (ρ : Fin m → Fin l) :
    (memberResult w x y q).rename ρ = memberResult (ρ w) (ρ x) (ρ y) (ρ q) := by
  simp only [memberResult, Formula.rename, SyntaxAtomSyntax.zeroScalar_rename, SyntaxAtomSyntax.memberCode_rename,
    Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem result_rename {m l} (kind : Fin 3) (w b z x y q : Fin m) (ρ : Fin m → Fin l) :
    (result kind w b z x y q).rename ρ = result kind (ρ w) (ρ b) (ρ z) (ρ x) (ρ y) (ρ q) := by
  rcases kind with ⟨k,hk⟩
  have h : k=0 ∨ k=1 ∨ k=2 := by omega
  rcases h with rfl | rfl | rfl
  · exact memberResult_rename w x y q ρ
  · exact SyntaxAtomSyntax.equalCode_rename w x y q ρ
  · exact ProjectSubsetSyntax.expanded_rename w b z x y q ρ

theorem compiled_rename {m l} (kind : Fin 3) (w b z x y n q : Fin m) (ρ : Fin m → Fin l) :
    (compiled kind w b z x y n q).rename ρ = compiled kind (ρ w) (ρ b) (ρ z) (ρ x) (ρ y) (ρ n) (ρ q) := by
  simp only [compiled, Formula.rename, sourceAt_rename, result_rename]

theorem existsResult_rename {m l} (kind : Fin 3) (w b z x y : Fin m) (ρ : Fin m → Fin l) :
    (existsResult kind w b z x y).rename ρ = existsResult kind (ρ w) (ρ b) (ρ z) (ρ x) (ρ y) := by
  simp only [existsResult, Formula.rename, result_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem uniqueOutput_rename {m l} (kind : Fin 3) (w b z x y n q : Fin m) (ρ : Fin m → Fin l) :
    (uniqueOutput kind w b z x y n q).rename ρ = uniqueOutput kind (ρ w) (ρ b) (ρ z) (ρ x) (ρ y) (ρ n) (ρ q) := by
  simp only [uniqueOutput, Formula.rename, compiled_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem fiber_rename {m l} (kind : Fin 3) (w b z x y n : Fin m) (ρ : Fin m → Fin l) :
    (fiber kind w b z x y n).rename ρ = fiber kind (ρ w) (ρ b) (ρ z) (ρ x) (ρ y) (ρ n) := by
  simp only [fiber, Formula.rename, compiled_rename, FormulaCodeSyntax.formulaCode_rename, uniqueOutput_rename,
    Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem intro_result {m} {Γ : Context m} (kind : Fin 3) (w b z x y q : Fin m) (hq : Derives Γ (.mem q w))
    (hr : Derives Γ (result kind w b z x y q)) : Derives Γ (existsResult kind w b z x y) := by
  apply Derives.exI q
  exact of_eq (by simp only [Formula.instantiate, Formula.rename, result_rename,
    Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) (.conjI hq hr)

end PPAC.Migration.Internal.ProjectAtomicSyntax
