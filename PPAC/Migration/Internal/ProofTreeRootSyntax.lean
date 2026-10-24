import PPAC.Migration.Internal.ProofTreeEntryFacts

/-! 根关闭性与实际结论字段的独立纯关系规格；无头表达式、搜索界或宿主谓词。 -/
namespace PPAC.Migration.Internal.ProofTreeRootSyntax
open Source SourceAlgebra SourceLogic OmegaSyntax HornExprSyntax HornBinderSyntax
open SyntaxRenameQuerySyntax (of_eq)
open ProofTreeBranchConstruction (shape)

def matrix {m} (kind : Fin 6) (w code conclusion : Fin m) (env : Fin ((shape kind).extra+2) → Fin m) : Formula m :=
  (environmentNat ((shape kind).extra+2) w env).conj
    ((SyntaxNodeSyntax.constructor ((shape kind).extra+2) (shape kind).tag w env code).conj
      ((empty (env 0)).conj (.equal (env 1) conclusion)))

def body {m} (kind : Fin 6) (w code conclusion : Fin m) : Formula (m+((shape kind).extra+2)) :=
  matrix kind (old ((shape kind).extra+2) w) (old ((shape kind).extra+2) code) (old ((shape kind).extra+2) conclusion) (slot ((shape kind).extra+2))

def branch {m} (kind : Fin 6) (w code conclusion : Fin m) : Formula m :=
  existsMany ((shape kind).extra+2) (body kind w code conclusion)

def kinds : List (Fin 6) := [0,1,2,3,4,5]

def closedPayload {m} (w code conclusion : Fin m) : Formula m :=
  LogicalAllPatterns.disjoin (kinds.map (fun kind => branch kind w code conclusion))

def normalized {m} (test : Formula 1) (w code conclusion : Fin m) : Formula m :=
  (ProofTreeEntrySyntax.node test w code).conj (closedPayload w code conclusion)

theorem kind_mem (kind : Fin 6) : kind ∈ kinds := by
  rcases kind with ⟨k,hk⟩
  have hc : k=0 ∨ k=1 ∨ k=2 ∨ k=3 ∨ k=4 ∨ k=5 := by omega
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
  · change (0 : Fin 6) ∈ kinds
    decide
  · change (1 : Fin 6) ∈ kinds
    decide
  · change (2 : Fin 6) ∈ kinds
    decide
  · change (3 : Fin 6) ∈ kinds
    decide
  · change (4 : Fin 6) ∈ kinds
    decide
  · change (5 : Fin 6) ∈ kinds
    decide

theorem matrix_rename {m l} (kind : Fin 6) (w code conclusion : Fin m) (env : Fin ((shape kind).extra+2) → Fin m) (ρ : Fin m → Fin l) :
    (matrix kind w code conclusion env).rename ρ = matrix kind (ρ w) (ρ code) (ρ conclusion) (fun i => ρ (env i)) := by
  simp only [matrix, Formula.rename, environmentNat_rename, SyntaxNodeSyntax.constructor_rename, empty_rename]

theorem body_lift {m l} (kind : Fin 6) (w code conclusion : Fin m) (ρ : Fin m → Fin l) :
    (body kind w code conclusion).rename (lift ((shape kind).extra+2) ρ) = body kind (ρ w) (ρ code) (ρ conclusion) := by
  simp only [body, matrix_rename, lift_old, lift_slot]

theorem branch_rename {m l} (kind : Fin 6) (w code conclusion : Fin m) (ρ : Fin m → Fin l) :
    (branch kind w code conclusion).rename ρ = branch kind (ρ w) (ρ code) (ρ conclusion) := by
  simp only [branch, existsMany_rename, body_lift]

theorem closedPayload_rename {m l} (w code conclusion : Fin m) (ρ : Fin m → Fin l) :
    (closedPayload w code conclusion).rename ρ = closedPayload (ρ w) (ρ code) (ρ conclusion) := by
  unfold closedPayload
  rw [LogicalTableRenaming.disjoin_rename, List.map_map]
  congr 1
  apply List.map_congr_left
  intro kind _
  exact branch_rename kind w code conclusion ρ

theorem normalized_rename {m l} (test : Formula 1) (w code conclusion : Fin m) (ρ : Fin m → Fin l) :
    (normalized test w code conclusion).rename ρ = normalized test (ρ w) (ρ code) (ρ conclusion) := by
  simp only [normalized, Formula.rename, ProofTreeEntryFacts.node_rename, closedPayload_rename]

theorem disjoin_intro {m} {Γ : Context m} (ps : List (Formula m)) (p : Formula m) (hp : p ∈ ps) (h : Derives Γ p) :
    Derives Γ (LogicalAllPatterns.disjoin ps) := by
  induction ps with
  | nil => simp only [List.not_mem_nil] at hp
  | cons a ps ih =>
    rcases List.mem_cons.mp hp with rfl | hp
    · exact .disjL h
    · exact .disjR (ih hp)

theorem disjoin_elim {m} {Γ : Context m} (ps : List (Formula m)) (p : Formula m)
    (he : Derives Γ (LogicalAllPatterns.disjoin ps)) (hc : ∀ q, q ∈ ps → Derives Γ (q.imp p)) : Derives Γ p := by
  induction ps generalizing Γ with
  | nil => exact .botE he
  | cons q ps ih =>
    apply Derives.disjE he
    · exact .impE (add (hc q List.mem_cons_self) _) (.hyp (Or.inl rfl))
    · exact ih (.hyp (Or.inl rfl)) (fun a ha => add (hc a (List.mem_cons_of_mem q ha)) _)

theorem intro_closedPayload {m} {Γ : Context m} (kind : Fin 6) (w code conclusion : Fin m)
    (env : Fin ((shape kind).extra+2) → Fin m) (hm : Derives Γ (matrix kind w code conclusion env)) :
    Derives Γ (closedPayload w code conclusion) := by
  have hb : Derives Γ (branch kind w code conclusion) := by
    apply HornBinderRules.intro_many ((shape kind).extra+2) (body kind w code conclusion) env
    exact of_eq (by simp only [body, matrix_rename, assign_old, assign_slot]) hm
  exact disjoin_intro _ _ (List.mem_map.mpr ⟨kind,kind_mem kind,rfl⟩) hb

end PPAC.Migration.Internal.ProofTreeRootSyntax
