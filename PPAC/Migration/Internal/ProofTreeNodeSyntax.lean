import PPAC.Migration.Internal.ProofTreeChildren

/-! 原六类载荷及各真实子Node的独立关系式；准确局部表在外层明确保留。 -/
namespace PPAC.Migration.Internal.ProofTreeNodeSyntax
open Source SourceAlgebra SourceLogic OmegaSyntax HornExprSyntax HornBinderSyntax
open SyntaxRenameQuerySyntax (of_eq)
open ProofTreeBranchConstruction (shape)

def matrix {m} (test : Formula 1) (kind : Fin 6) (w code : Fin m) (env : Fin ((shape kind).extra+2) → Fin m) : Formula m :=
  (environmentNat ((shape kind).extra+2) w env).conj
    ((SyntaxNodeSyntax.constructor ((shape kind).extra+2) (shape kind).tag w env code).conj
      (ProofTreeChildren.children test (shape kind).children w env))

def body {m} (test : Formula 1) (kind : Fin 6) (w code : Fin m) : Formula (m+((shape kind).extra+2)) :=
  matrix test kind (old ((shape kind).extra+2) w) (old ((shape kind).extra+2) code) (slot ((shape kind).extra+2))

def branch {m} (test : Formula 1) (kind : Fin 6) (w code : Fin m) : Formula m :=
  existsMany ((shape kind).extra+2) (body test kind w code)

def payloadCases {m} (test : Formula 1) (w code : Fin m) : Formula m :=
  LogicalAllPatterns.disjoin (ProofTreeRootSyntax.kinds.map (fun kind => branch test kind w code))

def normalized {m} (test : Formula 1) (w code : Fin m) : Formula m :=
  (ProofAllNodeSyntax.table test w code).conj (payloadCases test w code)

theorem matrix_rename {m l} (test : Formula 1) (kind : Fin 6) (w code : Fin m) (env : Fin ((shape kind).extra+2) → Fin m) (ρ : Fin m → Fin l) :
    (matrix test kind w code env).rename ρ = matrix test kind (ρ w) (ρ code) (fun i => ρ (env i)) := by
  simp only [matrix, Formula.rename, environmentNat_rename, SyntaxNodeSyntax.constructor_rename, ProofTreeChildren.children_rename]

theorem body_lift {m l} (test : Formula 1) (kind : Fin 6) (w code : Fin m) (ρ : Fin m → Fin l) :
    (body test kind w code).rename (lift ((shape kind).extra+2) ρ) = body test kind (ρ w) (ρ code) := by
  simp only [body, matrix_rename, lift_old, lift_slot]

theorem branch_rename {m l} (test : Formula 1) (kind : Fin 6) (w code : Fin m) (ρ : Fin m → Fin l) :
    (branch test kind w code).rename ρ = branch test kind (ρ w) (ρ code) := by
  simp only [branch, existsMany_rename, body_lift]

theorem payloadCases_rename {m l} (test : Formula 1) (w code : Fin m) (ρ : Fin m → Fin l) :
    (payloadCases test w code).rename ρ = payloadCases test (ρ w) (ρ code) := by
  unfold payloadCases
  rw [LogicalTableRenaming.disjoin_rename, List.map_map]
  congr 1
  apply List.map_congr_left
  intro kind _
  exact branch_rename test kind w code ρ

theorem normalized_rename {m l} (test : Formula 1) (w code : Fin m) (ρ : Fin m → Fin l) :
    (normalized test w code).rename ρ = normalized test (ρ w) (ρ code) := by
  simp only [normalized, Formula.rename, ProofAllTableRenaming.table_rename, payloadCases_rename]

theorem intro_cases {m} {Γ : Context m} (test : Formula 1) (kind : Fin 6) (w code : Fin m)
    (env : Fin ((shape kind).extra+2) → Fin m) (hm : Derives Γ (matrix test kind w code env)) :
    Derives Γ (payloadCases test w code) := by
  have hb : Derives Γ (branch test kind w code) := by
    apply HornBinderRules.intro_many ((shape kind).extra+2) (body test kind w code) env
    exact of_eq (by simp only [body, matrix_rename, assign_old, assign_slot]) hm
  exact ProofTreeRootSyntax.disjoin_intro _ _ (List.mem_map.mpr ⟨kind,ProofTreeRootSyntax.kind_mem kind,rfl⟩) hb

theorem payload_field_below {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (kind : Fin 6) (w code : Fin m)
    (env : Fin ((shape kind).extra+2) → Fin m) (i : Fin ((shape kind).extra+2)) (hw : Derives Γ (omega w))
    (hc : Derives Γ (SyntaxNodeSyntax.constructor ((shape kind).extra+2) (shape kind).tag w env code)) :
    Derives Γ (.mem (env i) code) := SyntaxConstructors.child_member hZ _ _ w env code i hw hc

end PPAC.Migration.Internal.ProofTreeNodeSyntax
