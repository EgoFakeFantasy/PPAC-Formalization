import PPAC.Migration.Internal.SchemaDoubleShiftGraph

/-! Three original schema embeddings; all parameter scopes and graph witnesses are objects. -/
namespace PPAC.Migration.Internal.SchemaIndexSyntax
open Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax
open SyntaxRenameQuerySyntax (of_eq)

def sourceScope (site : Fin 3) {α : Type} (scopes : Fin 4 → α) : α := if site.val = 0 then scopes 0 else scopes 1

def targetScope (site : Fin 3) {α : Type} (scopes : Fin 4 → α) : α := if site.val = 2 then scopes 3 else scopes 2

def chain {m} (n : Fin m) (scopes : Fin 4 → Fin m) : Formula m :=
  (successor (scopes 0) n).conj ((successor (scopes 1) (scopes 0)).conj
    ((successor (scopes 2) (scopes 1)).conj (successor (scopes 3) (scopes 2))))

def matrix {m} (site : Fin 3) (w n : Fin m) (scopes : Fin 4 → Fin m) (g : Fin m) (env : Fin 2 → Fin m) : Formula m :=
  match site.val with
  | 0 => (SchemaDoubleShiftSyntax.map w n (scopes 0) (scopes 1) (env 0)).conj
      ((Formula.equal (env 1) (env 0)).conj (SyntaxIndexLiftSyntax.lifted w (env 0) n (scopes 1) (scopes 0) (scopes 2) g))
  | 1 => (SyntaxFreeShiftSyntax.shiftMap w n (scopes 0) (env 0)).conj
      ((SyntaxIndexLiftSyntax.lifted w (env 0) n (scopes 0) (scopes 0) (scopes 1) (env 1)).conj
        (SyntaxIndexLiftSyntax.lifted w (env 1) (scopes 0) (scopes 1) (scopes 1) (scopes 2) g))
  | _ => (SchemaDoubleShiftSyntax.map w n (scopes 0) (scopes 1) (env 0)).conj
      ((SyntaxIndexLiftSyntax.lifted w (env 0) n (scopes 1) (scopes 0) (scopes 2) (env 1)).conj
        (SyntaxIndexLiftSyntax.lifted w (env 1) (scopes 0) (scopes 2) (scopes 1) (scopes 3) g))

def body {m} (site : Fin 3) (w n : Fin m) (scopes : Fin 4 → Fin m) (g : Fin m) : Formula (m+2) :=
  matrix site (old 2 w) (old 2 n) (fun i => old 2 (scopes i)) (old 2 g) (slot 2)

def graph {m} (site : Fin 3) (w n : Fin m) (scopes : Fin 4 → Fin m) (g : Fin m) : Formula m := existsMany 2 (body site w n scopes g)

def existsGraph {m} (site : Fin 3) (w n : Fin m) (scopes : Fin 4 → Fin m) : Formula m := .ex
  (graph site w.castSucc n.castSucc (fun i => (scopes i).castSucc) (Fin.last m))

def state {m} (site : Fin 3) (w n : Fin m) (scopes : Fin 4 → Fin m) (g : Fin m) : Formula m :=
  (chain n scopes).conj (graph site w n scopes g)

def stateBody {m} (site : Fin 3) (w n : Fin m) : Formula (m+5) :=
  state site (old 5 w) (old 5 n) (fun i => slot 5 i.castSucc) (slot 5 (Fin.last 4))

def existsState {m} (site : Fin 3) (w n : Fin m) : Formula m := existsMany 5 (stateBody site w n)

def codedState {m} (site : Fin 3) (w n : Fin m) (scopes : Fin 4 → Fin m) (g R : Fin m) : Formula m :=
  (state site w n scopes g).conj (SyntaxMapCodeSyntax.encoded w g (sourceScope site scopes) (targetScope site scopes) R)

def codedBody {m} (site : Fin 3) (w n : Fin m) : Formula (m+6) :=
  codedState site (old 6 w) (old 6 n) (fun i => slot 6 i.castSucc.castSucc) (slot 6 (Fin.last 4).castSucc) (slot 6 (Fin.last 5))

def existsCodedState {m} (site : Fin 3) (w n : Fin m) : Formula m := existsMany 6 (codedBody site w n)

theorem sourceScope_map {α β : Type} (site : Fin 3) (scopes : Fin 4 → α) (f : α → β) :
    sourceScope site (fun i => f (scopes i)) = f (sourceScope site scopes) := by simp only [sourceScope]; split <;> rfl

theorem targetScope_map {α β : Type} (site : Fin 3) (scopes : Fin 4 → α) (f : α → β) :
    targetScope site (fun i => f (scopes i)) = f (targetScope site scopes) := by simp only [targetScope]; split <;> rfl

theorem chain_rename {m l} (n : Fin m) (scopes : Fin 4 → Fin m) (ρ : Fin m → Fin l) :
    (chain n scopes).rename ρ = chain (ρ n) (fun i => ρ (scopes i)) := by simp only [chain, Formula.rename, successor_rename]

theorem matrix_rename {m l} (site : Fin 3) (w n : Fin m) (scopes : Fin 4 → Fin m) (g : Fin m) (env : Fin 2 → Fin m) (ρ : Fin m → Fin l) :
    (matrix site w n scopes g env).rename ρ = matrix site (ρ w) (ρ n) (fun i => ρ (scopes i)) (ρ g) (fun i => ρ (env i)) := by
  rcases site with ⟨k,hk⟩
  have h : k=0 ∨ k=1 ∨ k=2 := by omega
  rcases h with rfl | rfl | rfl <;> simp only [matrix, Formula.rename, SchemaDoubleShiftSyntax.map_rename,
    SyntaxFreeShiftSyntax.shiftMap_rename, SyntaxIndexLiftSyntax.lifted_rename]

theorem body_lift {m l} (site : Fin 3) (w n : Fin m) (scopes : Fin 4 → Fin m) (g : Fin m) (ρ : Fin m → Fin l) :
    (body site w n scopes g).rename (lift 2 ρ) = body site (ρ w) (ρ n) (fun i => ρ (scopes i)) (ρ g) := by
  simp only [body, matrix_rename, lift_old, lift_slot]

theorem graph_rename {m l} (site : Fin 3) (w n : Fin m) (scopes : Fin 4 → Fin m) (g : Fin m) (ρ : Fin m → Fin l) :
    (graph site w n scopes g).rename ρ = graph site (ρ w) (ρ n) (fun i => ρ (scopes i)) (ρ g) := by
  simp only [graph, existsMany_rename, body_lift]

theorem existsGraph_rename {m l} (site : Fin 3) (w n : Fin m) (scopes : Fin 4 → Fin m) (ρ : Fin m → Fin l) :
    (existsGraph site w n scopes).rename ρ = existsGraph site (ρ w) (ρ n) (fun i => ρ (scopes i)) := by
  simp only [existsGraph, Formula.rename, graph_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem state_rename {m l} (site : Fin 3) (w n : Fin m) (scopes : Fin 4 → Fin m) (g : Fin m) (ρ : Fin m → Fin l) :
    (state site w n scopes g).rename ρ = state site (ρ w) (ρ n) (fun i => ρ (scopes i)) (ρ g) := by
  simp only [state, Formula.rename, chain_rename, graph_rename]

theorem stateBody_lift {m l} (site : Fin 3) (w n : Fin m) (ρ : Fin m → Fin l) :
    (stateBody site w n).rename (lift 5 ρ) = stateBody site (ρ w) (ρ n) := by simp only [stateBody, state_rename, lift_old, lift_slot]

theorem existsState_rename {m l} (site : Fin 3) (w n : Fin m) (ρ : Fin m → Fin l) :
    (existsState site w n).rename ρ = existsState site (ρ w) (ρ n) := by simp only [existsState, existsMany_rename, stateBody_lift]

theorem codedState_rename {m l} (site : Fin 3) (w n : Fin m) (scopes : Fin 4 → Fin m) (g R : Fin m) (ρ : Fin m → Fin l) :
    (codedState site w n scopes g R).rename ρ = codedState site (ρ w) (ρ n) (fun i => ρ (scopes i)) (ρ g) (ρ R) := by
  simp only [codedState, Formula.rename, state_rename, SyntaxMapCodeSyntax.encoded_rename, sourceScope_map, targetScope_map]

theorem codedBody_lift {m l} (site : Fin 3) (w n : Fin m) (ρ : Fin m → Fin l) :
    (codedBody site w n).rename (lift 6 ρ) = codedBody site (ρ w) (ρ n) := by simp only [codedBody, codedState_rename, lift_old, lift_slot]

theorem existsCodedState_rename {m l} (site : Fin 3) (w n : Fin m) (ρ : Fin m → Fin l) :
    (existsCodedState site w n).rename ρ = existsCodedState site (ρ w) (ρ n) := by simp only [existsCodedState, existsMany_rename, codedBody_lift]

theorem intro_graph {m} {Γ : Context m} (site : Fin 3) (w n : Fin m) (scopes : Fin 4 → Fin m) (g r h : Fin m)
    (hm : Derives Γ (matrix site w n scopes g (Source.SetLanguage.args2 r h))) : Derives Γ (graph site w n scopes g) := by
  apply HornBinderRules.intro_many 2 (body site w n scopes g) (Source.SetLanguage.args2 r h)
  exact of_eq (by simp only [body, matrix_rename, assign_old, assign_slot]) hm

theorem intro_exists_graph {m} {Γ : Context m} (site : Fin 3) (w n : Fin m) (scopes : Fin 4 → Fin m) (g : Fin m)
    (hg : Derives Γ (graph site w n scopes g)) : Derives Γ (existsGraph site w n scopes) := by
  apply Derives.exI g
  exact of_eq (by simp only [Formula.instantiate, graph_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) hg

end PPAC.Migration.Internal.SchemaIndexSyntax
