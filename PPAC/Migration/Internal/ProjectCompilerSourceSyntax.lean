import PPAC.Migration.Internal.ObjectProjectCompilerUnique

/-! Object source-validity predicate for actual compiler inputs and complete member induction. -/
namespace PPAC.Migration.Internal.ProjectCompilerSourceSyntax
open Source SourceAlgebra SourceLogic HornBinderSyntax ProjectCompilerCaseSyntax ProjectSourceCodeSyntax
open SyntaxRenameQuerySyntax (of_eq)

def queryBody {k m} (P : Formula (k+3)) (ρ : Fin k → Fin m) (w n f : Fin m) : Formula (m+3) :=
  (queried P (fun i => old 3 (ρ i)) (old 3 n) (slot 3 0) (slot 3 1) (slot 3 2)).imp
    (sourceCode (old 3 w) (slot 3 0) (slot 3 1) (old 3 f))

def goodQueries {k m} (P : Formula (k+3)) (ρ : Fin k → Fin m) (w n f : Fin m) : Formula m :=
  OriginalUniversalBlock.allMany 3 (queryBody P ρ w n f)

theorem queryBody_lift {k m j} (P : Formula (k+3)) (ρ : Fin k → Fin m) (w n f : Fin m) (σ : Fin m → Fin j) :
    (queryBody P ρ w n f).rename (lift 3 σ) = queryBody P (fun i => σ (ρ i)) (σ w) (σ n) (σ f) := by
  simp only [queryBody, Formula.rename, queried_rename, sourceCode_rename, lift_old, lift_slot]

theorem goodQueries_rename {k m j} (P : Formula (k+3)) (ρ : Fin k → Fin m) (w n f : Fin m) (σ : Fin m → Fin j) :
    (goodQueries P ρ w n f).rename σ = goodQueries P (fun i => σ (ρ i)) (σ w) (σ n) (σ f) := by
  simp only [goodQueries, OriginalUniversalBlock.allMany_rename, queryBody_lift]

theorem query_source {k m} {Γ : Context m} (P : Formula (k+3)) (ρ : Fin k → Fin m) (w n f x b q : Fin m)
    (hg : Derives Γ (goodQueries P ρ w n f)) (hq : Derives Γ (queried P ρ n x b q)) :
    Derives Γ (sourceCode w x b f) := by
  have hi := OriginalUniversalBlock.at_many 3 (queryBody P ρ w n f) (SyntaxAtomSyntax.three x b q) hg
  have hr : Derives Γ ((queried P ρ n x b q).imp (sourceCode w x b f)) :=
    of_eq (by simp only [queryBody, Formula.rename, queried_rename, sourceCode_rename, assign_old, assign_slot]; rfl) hi
  exact .impE hr hq

def propertyBody {m} (w n : Fin m) : Formula (m+3) :=
  (Formula.mem (slot 3 2) (old 3 w)).imp
    ((ProjectCompilerCodeSyntax.compiled (old 3 w) (old 3 n) (slot 3 0) (slot 3 1)).imp
      (sourceCode (old 3 w) (old 3 n) (slot 3 0) (slot 3 2)))

def correct {m} (w n : Fin m) : Formula m := OriginalUniversalBlock.allMany 3 (propertyBody w n)

theorem propertyBody_lift {m j} (w n : Fin m) (σ : Fin m → Fin j) :
    (propertyBody w n).rename (lift 3 σ) = propertyBody (σ w) (σ n) := by
  simp only [propertyBody, Formula.rename, ProjectCompilerCodeSyntax.compiled_rename, sourceCode_rename, lift_old, lift_slot]

theorem correct_rename {m j} (w n : Fin m) (σ : Fin m → Fin j) :
    (correct w n).rename σ = correct (σ w) (σ n) := by
  simp only [correct, OriginalUniversalBlock.allMany_rename, propertyBody_lift]

theorem at_correct {m} {Γ : Context m} (w n b q f : Fin m) (hc : Derives Γ (correct w n))
    (hf : Derives Γ (.mem f w)) (hi : Derives Γ (ProjectCompilerCodeSyntax.compiled w n b q)) :
    Derives Γ (sourceCode w n b f) := by
  have ha := OriginalUniversalBlock.at_many 3 (propertyBody w n) (SyntaxAtomSyntax.three b q f) hc
  have hr : Derives Γ ((Formula.mem f w).imp ((ProjectCompilerCodeSyntax.compiled w n b q).imp (sourceCode w n b f))) :=
    of_eq (by simp only [propertyBody, Formula.rename, ProjectCompilerCodeSyntax.compiled_rename,
      sourceCode_rename, assign_old, assign_slot]; rfl) ha
  exact .impE (.impE hr hf) hi

def allIH {m} (w n : Fin m) : Formula m := .all
  ((Formula.mem (Fin.last m) n.castSucc).imp (correct w.castSucc (Fin.last m)))

theorem allIH_rename {m j} (w n : Fin m) (σ : Fin m → Fin j) :
    (allIH w n).rename σ = allIH (σ w) (σ n) := by
  simp only [allIH, Formula.rename, correct_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem below_correct {m} {Γ : Context m} (w n x : Fin m)
    (hI : Derives Γ (allIH w n)) (hx : Derives Γ (.mem x n)) : Derives Γ (correct w x) := by
  have ha := Derives.allE x hI
  have hr : Derives Γ ((Formula.mem x n).imp (correct w x)) :=
    of_eq (by simp only [Formula.instantiate, Formula.rename, correct_rename,
      Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) ha
  exact .impE hr hx

end PPAC.Migration.Internal.ProjectCompilerSourceSyntax
