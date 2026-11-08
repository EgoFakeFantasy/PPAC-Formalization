import PPAC.Migration.ForcingCodeStep
import PPAC.Migration.ObjectTransfiniteRecursion

/-! The actual fixed-source forcing-code table, built using the original ZF
Separation and original internal ordinal recursion. Its rows contain actual
scope/output states and the complete eleven-constructor dispatch, not an
abstract supplied transition relation. Table existence/uniqueness does not
prove that a legal input row is occupied or that its formula output is unique;
those require the remaining code induction. No new recursion backend. -/
namespace PPAC.Migration.ForcingCodeRecursion
open Internal Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax PairSyntax
open SyntaxRenameQuerySyntax (of_eq)
open ReplacementPredicates (paramsUp)
set_option maxRecDepth 16384
attribute [local irreducible] NaturalRecursionSyntax.matrix

private def params {m} (w z f j : Fin m) : Fin 4 → Fin m := Fin.cases w (Fin.cases z (SyntaxAtomSyntax.two f j))
private theorem params_map {m l} (w z f j : Fin m) (r : Fin m → Fin l) :
    (fun i => r (params w z f j i)) = params (r w) (r z) (r f) (r j) := by
  funext i
  exact Fin.cases rfl (fun i => Fin.cases rfl (fun i => Fin.cases rfl (fun i => Fin.cases rfl (fun b => Fin.elim0 b) i) i) i) i
private def rowParams {m} (w z f j n h : Fin m) : Fin 6 → Fin m := Fin.lastCases h (Fin.lastCases n (params w z f j))
private theorem rowParams_map {m l} (w z f j n h : Fin m) (r : Fin m → Fin l) :
    (fun i => r (rowParams w z f j n h i)) = rowParams (r w) (r z) (r f) (r j) (r n) (r h) := by
  funext i
  refine Fin.lastCases rfl (fun b => ?_) i
  refine Fin.lastCases rfl (fun a => ?_) b
  simpa only [rowParams, Fin.lastCases_castSucc] using congrFun (params_map w z f j r) a

private def rowData {k m} (R : Source.Formula (k+2)) (H : Source.Formula (k+1)) (w z f j n h t : Fin m) (v : Fin 5 → Fin m) : Formula m :=
  (ForcingCodeStep.state w (v 0) f (v 4) t).conj
    ((successor (v 1) (v 0)).conj ((successor (v 2) (v 1)).conj ((successor (v 3) (v 2)).conj
      (ForcingCodeStep.step R H w z f j (v 0) (v 1) (v 2) (v 3) h n (v 4)))))
private theorem rowData_rename {k m l} (R : Source.Formula (k+2)) (H : Source.Formula (k+1)) (w z f j n h t : Fin m)
    (v : Fin 5 → Fin m) (r : Fin m → Fin l) :
    (rowData R H w z f j n h t v).rename r = rowData R H (r w) (r z) (r f) (r j) (r n) (r h) (r t) (fun i => r (v i)) := by
  simp only [rowData, Formula.rename, ForcingCodeStep.state_rename, successor_rename, ForcingCodeStep.step_rename]
private def rowBody {k m} (R : Source.Formula (k+2)) (H : Source.Formula (k+1)) (w z f j n h t : Fin m) : Formula (m+5) :=
  rowData R H (old 5 w) (old 5 z) (old 5 f) (old 5 j) (old 5 n) (old 5 h) (old 5 t) (slot 5)
def row {k m} (R : Source.Formula (k+2)) (H : Source.Formula (k+1)) (w z f j n h t : Fin m) : Formula m :=
  existsMany 5 (rowBody R H w z f j n h t)
theorem row_rename {k m l} (R : Source.Formula (k+2)) (H : Source.Formula (k+1)) (w z f j n h t : Fin m) (r : Fin m → Fin l) :
    (row R H w z f j n h t).rename r = row R H (r w) (r z) (r f) (r j) (r n) (r h) (r t) := by
  simp only [row, existsMany_rename, rowBody, rowData_rename, lift_old, lift_slot]

private def selection {k} (R : Source.Formula (k+2)) (H : Source.Formula (k+1)) : Formula (6+1) :=
  row R H (0 : Fin 6).castSucc (1 : Fin 6).castSucc (2 : Fin 6).castSucc (3 : Fin 6).castSucc
    (4 : Fin 6).castSucc (5 : Fin 6).castSucc (Fin.last 6)
private theorem selection_at {k m} (R : Source.Formula (k+2)) (H : Source.Formula (k+1)) (w z f j n h t : Fin m) :
    MinimalPredicates.pred (selection R H) (rowParams w z f j n h) t = row R H w z f j n h t := by
  simp only [MinimalPredicates.pred, selection, row_rename, Fin.lastCases_last, Fin.lastCases_castSucc]
  rfl

def value {k m} (R : Source.Formula (k+2)) (H : Source.Formula (k+1)) (w z f j n h v : Fin m) : Formula m :=
  MinimalPredicates.separated (selection R H) (rowParams w z f j n h) w v
theorem value_rename {k m l} (R : Source.Formula (k+2)) (H : Source.Formula (k+1)) (w z f j n h v : Fin m) (r : Fin m → Fin l) :
    (value R H w z f j n h v).rename r = value R H (r w) (r z) (r f) (r j) (r n) (r h) (r v) := by
  simp only [value, MinimalPredicates.separated_rename, rowParams_map]
def existsValue {k m} (R : Source.Formula (k+2)) (H : Source.Formula (k+1)) (w z f j n h : Fin m) : Formula m := .ex
  (value R H w.castSucc z.castSucc f.castSucc j.castSucc n.castSucc h.castSucc (Fin.last m))
private theorem existsValue_rename {k m l} (R : Source.Formula (k+2)) (H : Source.Formula (k+1)) (w z f j n h : Fin m) (r : Fin m → Fin l) :
    (existsValue R H w z f j n h).rename r = existsValue R H (r w) (r z) (r f) (r j) (r n) (r h) := by
  simp only [existsValue, Formula.rename, value_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem value_at {k m} {Γ : Context m} (R : Source.Formula (k+2)) (H : Source.Formula (k+1)) (w z f j n h v t : Fin m)
    (hv : Derives Γ (value R H w z f j n h v)) : Derives Γ ((Formula.mem t v).iff ((Formula.mem t w).conj (row R H w z f j n h t))) := by
  exact of_eq (by simp only [MinimalPredicates.satisfying, selection_at])
    (MinimalPredicates.specialize_separated (selection R H) (rowParams w z f j n h) w v t hv)

theorem exists_value {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (R : Source.Formula (k+2)) (H : Source.Formula (k+1))
    (w z f j n h : Fin m) : Derives Γ (existsValue R H w z f j n h) := by
  have he := MinimalInstances.separation_instance (selection R H) (rowParams w z f j n h) w (ZFContext.separation hZ (selection R H))
  have hmap : paramsUp (rowParams w z f j n h) = rowParams w.castSucc z.castSucc f.castSucc j.castSucc n.castSucc h.castSucc := rowParams_map w z f j n h Fin.castSucc
  simpa only [MinimalPredicates.separationExists, existsValue, value, hmap] using he

theorem unique_value {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (R : Source.Formula (k+2)) (H : Source.Formula (k+1))
    (w z f j n h v u : Fin m) (hv : Derives Γ (value R H w z f j n h v)) (hu : Derives Γ (value R H w z f j n h u)) : Derives Γ (.equal v u) := by
  apply Derives.impE (extensionality_instance v u (ZFContext.arithmetic hZ).base.extensionality)
  apply Derives.allI
  have hv1 := of_eq (value_rename R H w z f j n h v Fin.castSucc) (Derives.rename Fin.castSucc hv)
  have hu1 := of_eq (value_rename R H w z f j n h u Fin.castSucc) (Derives.rename Fin.castSucc hu)
  have hvl := value_at R H w.castSucc z.castSucc f.castSucc j.castSucc n.castSucc h.castSucc v.castSucc (Fin.last m) hv1
  have hul := value_at R H w.castSucc z.castSucc f.castSucc j.castSucc n.castSucc h.castSucc u.castSucc (Fin.last m) hu1
  apply Derives.conjI
  · apply Derives.impI
    exact .impE (add (.conjR hul) _) (.impE (add (.conjL hvl) _) (.hyp (Or.inl rfl)))
  · apply Derives.impI
    exact .impE (add (.conjR hvl) _) (.impE (add (.conjL hul) _) (.hyp (Or.inl rfl)))

theorem intro_row {k m} {Γ : Context m} (R : Source.Formula (k+2)) (H : Source.Formula (k+1))
    (w z f j n h t a A B C Q : Fin m) (hs : Derives Γ (ForcingCodeStep.state w a f Q t))
    (hA : Derives Γ (successor A a)) (hB : Derives Γ (successor B A)) (hC : Derives Γ (successor C B))
    (hc : Derives Γ (ForcingCodeStep.step R H w z f j a A B C h n Q)) : Derives Γ (row R H w z f j n h t) := by
  let v : Fin 5 → Fin m := Fin.cases a (Fin.cases A (Fin.cases B (SyntaxAtomSyntax.two C Q)))
  apply HornBinderRules.intro_many 5 _ v
  exact of_eq (by simp only [rowBody, rowData_rename, assign_old, assign_slot]; rfl) (.conjI hs (.conjI hA (.conjI hB (.conjI hC hc))))

private def matrix {k} (R : Source.Formula (k+2)) (H : Source.Formula (k+1)) : Formula (4+3) :=
  value R H (0 : Fin 4).castSucc.castSucc.castSucc (1 : Fin 4).castSucc.castSucc.castSucc
    (2 : Fin 4).castSucc.castSucc.castSucc (3 : Fin 4).castSucc.castSucc.castSucc
    (Fin.last 4).castSucc.castSucc (Fin.last 5).castSucc (Fin.last 6)
private theorem matrix_operator {k m} (R : Source.Formula (k+2)) (H : Source.Formula (k+1)) (ρ : Fin 4 → Fin m) (n h v : Fin m) :
    OrdinalRecursionSyntax.operator (matrix R H) ρ n h v = value R H (ρ 0) (ρ 1) (ρ 2) (ρ 3) n h v := by
  simp only [OrdinalRecursionSyntax.operator, matrix, value_rename, Fin.lastCases_last, Fin.lastCases_castSucc]

private theorem operator_total {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (R : Source.Formula (k+2)) (H : Source.Formula (k+1)) (ρ : Fin 4 → Fin m) :
    Derives Γ (OrdinalRecursionTotal.total (matrix R H) ρ) := by
  simp only [OrdinalRecursionTotal.total, OrdinalRecursionTotal.hasValue, matrix_operator, paramsUp]
  apply Derives.allI
  apply Derives.allI
  apply Derives.impI
  let T := (OrdinalSyntax.ordinal (Fin.last m).castSucc).conj (GraphSyntax.functionOn (Fin.last (m+1)) (Fin.last m).castSucc)
  exact exists_value (ZFContext.under_two hZ T) R H (ρ 0).castSucc.castSucc (ρ 1).castSucc.castSucc
    (ρ 2).castSucc.castSucc (ρ 3).castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))
private theorem operator_deterministic {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ)
    (R : Source.Formula (k+2)) (H : Source.Formula (k+1)) (ρ : Fin 4 → Fin m) :
    Derives Γ (OrdinalRecursionDeterminism.deterministic (matrix R H) ρ) := by
  simp only [OrdinalRecursionDeterminism.deterministic, OrdinalRecursionDeterminism.functional, matrix_operator, paramsUp]
  apply Derives.allI
  apply Derives.allI
  apply Derives.impI
  let T := (OrdinalSyntax.ordinal (Fin.last m).castSucc).conj (GraphSyntax.functionOn (Fin.last (m+1)) (Fin.last m).castSucc)
  have hZ2 := ZFContext.under_two hZ T
  apply Derives.allI
  apply Derives.allI
  apply Derives.impI
  apply Derives.impI
  let Y := value R H (ρ 0).castSucc.castSucc.castSucc.castSucc (ρ 1).castSucc.castSucc.castSucc.castSucc
    (ρ 2).castSucc.castSucc.castSucc.castSucc (ρ 3).castSucc.castSucc.castSucc.castSucc
    (Fin.last m).castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc.castSucc (Fin.last (m+2)).castSucc
  let U := value R H (ρ 0).castSucc.castSucc.castSucc.castSucc (ρ 1).castSucc.castSucc.castSucc.castSucc
    (ρ 2).castSucc.castSucc.castSucc.castSucc (ρ 3).castSucc.castSucc.castSucc.castSucc
    (Fin.last m).castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc.castSucc (Fin.last (m+3))
  have hZ4 := ZFContext.add (ZFContext.add (ZFContext.rename (ZFContext.rename hZ2 Fin.castSucc) Fin.castSucc) Y) U
  exact unique_value hZ4 R H (ρ 0).castSucc.castSucc.castSucc.castSucc (ρ 1).castSucc.castSucc.castSucc.castSucc
    (ρ 2).castSucc.castSucc.castSucc.castSucc (ρ 3).castSucc.castSucc.castSucc.castSucc
    (Fin.last m).castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc.castSucc (Fin.last (m+2)).castSucc (Fin.last (m+3))
    (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

def recursors {k m} (R : Source.Formula (k+2)) (H : Source.Formula (k+1)) (w z f j : Fin m) : Formula m :=
  OrdinalRecursionExistenceSyntax.allUnique (matrix R H) (params w z f j)
def graph {k m} (R : Source.Formula (k+2)) (H : Source.Formula (k+1)) (w z f j g n : Fin m) : Formula m :=
  OrdinalRecursionSyntax.recursor (matrix R H) (params w z f j) g n
theorem graph_rename {k m l} (R : Source.Formula (k+2)) (H : Source.Formula (k+1)) (w z f j g n : Fin m) (r : Fin m → Fin l) :
    (graph R H w z f j g n).rename r = graph R H (r w) (r z) (r f) (r j) (r g) (r n) := by
  simp only [graph, OrdinalRecursionSyntax.recursor_rename, params_map]
def existsGraph {k m} (R : Source.Formula (k+2)) (H : Source.Formula (k+1)) (w z f j n : Fin m) : Formula m := .ex
  (graph R H w.castSucc z.castSucc f.castSucc j.castSucc (Fin.last m) n.castSucc)
private theorem existsGraph_rename {k m l} (R : Source.Formula (k+2)) (H : Source.Formula (k+1)) (w z f j n : Fin m) (r : Fin m → Fin l) :
    (existsGraph R H w z f j n).rename r = existsGraph R H (r w) (r z) (r f) (r j) (r n) := by
  simp only [existsGraph, Formula.rename, graph_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem all_unique {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (R : Source.Formula (k+2)) (H : Source.Formula (k+1))
    (w z f j : Fin m) : Derives Γ (recursors R H w z f j) := by
  have hc := ZFContext.closed hZ (ObjectTransfiniteRecursion.source_uniqueness (matrix R H))
  have hi := specialize_close
    ((OrdinalRecursionTotal.total (matrix R H) (id : Fin 4 → Fin 4)).imp
      ((OrdinalRecursionDeterminism.deterministic (matrix R H) id).imp (OrdinalRecursionExistenceSyntax.allUnique (matrix R H) id)))
    (params w z f j) hc
  have hh : Derives Γ ((OrdinalRecursionTotal.total (matrix R H) (params w z f j)).imp
      ((OrdinalRecursionDeterminism.deterministic (matrix R H) (params w z f j)).imp (recursors R H w z f j))) := by
    simpa only [Formula.rename, OrdinalRecursionTotal.total_rename, OrdinalRecursionDeterminism.deterministic_rename,
      OrdinalRecursionExistenceSyntax.allUnique_rename, id_eq, recursors] using hi
  exact .impE (.impE hh (operator_total hZ R H (params w z f j))) (operator_deterministic hZ R H (params w z f j))

theorem at_ordinal {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (R : Source.Formula (k+2)) (H : Source.Formula (k+1))
    (w z f j n : Fin m) (hn : Derives Γ (OrdinalSyntax.ordinal n)) :
    Derives Γ (OrdinalRecursionExistenceSyntax.fiber (matrix R H) (params w z f j) n) := by
  have hh : Derives Γ ((OrdinalSyntax.ordinal n).imp (OrdinalRecursionExistenceSyntax.fiber (matrix R H) (params w z f j) n)) := by
    simpa only [recursors, OrdinalRecursionExistenceSyntax.allUnique, Formula.instantiate, Formula.rename,
      OrdinalSyntax.ordinal_rename, OrdinalRecursionExistenceSyntax.fiber_rename, paramsUp,
      Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using Derives.allE n (all_unique hZ R H w z f j)
  exact .impE hh hn

theorem exists_graph {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (R : Source.Formula (k+2)) (H : Source.Formula (k+1))
    (w z f j n : Fin m) (hn : Derives Γ (OrdinalSyntax.ordinal n)) : Derives Γ (existsGraph R H w z f j n) := by
  let T := (graph R H w.castSucc z.castSucc f.castSucc j.castSucc (Fin.last m) n.castSucc).conj
    (OrdinalRecursionExistenceSyntax.uniqueAt (matrix R H) (params w.castSucc z.castSucc f.castSucc j.castSucc) n.castSucc (Fin.last m))
  let Δ := Context.add T (Context.image Formula.raise Γ)
  have he := at_ordinal hZ R H w z f j n hn
  have hmap : paramsUp (params w z f j) = params w.castSucc z.castSucc f.castSucc j.castSucc := params_map w z f j Fin.castSucc
  have heT : Derives Γ (.ex T) := by simpa only [T, OrdinalRecursionExistenceSyntax.fiber, graph, hmap] using he
  apply Derives.exE (p := T) heT
  have hT : Derives Δ T := .hyp (Or.inl rfl)
  have ho : Derives Δ (existsGraph R H w.castSucc z.castSucc f.castSucc j.castSucc n.castSucc) := by
    apply Derives.exI (Fin.last m)
    exact of_eq (by simp only [Formula.instantiate, graph_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) (.conjL hT)
  exact of_eq (existsGraph_rename R H w z f j n Fin.castSucc).symm ho

theorem graph_unique {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (R : Source.Formula (k+2)) (H : Source.Formula (k+1))
    (w z f j g t n : Fin m) (hn : Derives Γ (OrdinalSyntax.ordinal n))
    (hg : Derives Γ (graph R H w z f j g n)) (ht : Derives Γ (graph R H w z f j t n)) : Derives Γ (.equal g t) :=
  OrdinalRecursionCompatibility.unique_same_domain (matrix R H) (params w z f j) g t n
    (ZFContext.arithmetic hZ).base.extensionality (ZFContext.arithmetic hZ).base.foundation
    (ZFContext.separation hZ IterationSyntax.agreementMatrix.neg) (operator_deterministic hZ R H (params w z f j)) hn hg ht

def evaluation {k m} (R : Source.Formula (k+2)) (H : Source.Formula (k+1)) (w z f j n v : Fin m) : Formula m := .ex
  ((graph R H w.castSucc z.castSucc f.castSucc j.castSucc (Fin.last m) n.castSucc).conj
    (value R H w.castSucc z.castSucc f.castSucc j.castSucc n.castSucc (Fin.last m) v.castSucc))
theorem evaluation_rename {k m l} (R : Source.Formula (k+2)) (H : Source.Formula (k+1)) (w z f j n v : Fin m) (r : Fin m → Fin l) :
    (evaluation R H w z f j n v).rename r = evaluation R H (r w) (r z) (r f) (r j) (r n) (r v) := by
  simp only [evaluation, Formula.rename, graph_rename, value_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]
def existsEvaluation {k m} (R : Source.Formula (k+2)) (H : Source.Formula (k+1)) (w z f j n : Fin m) : Formula m := .ex
  (evaluation R H w.castSucc z.castSucc f.castSucc j.castSucc n.castSucc (Fin.last m))
private theorem existsEvaluation_rename {k m l} (R : Source.Formula (k+2)) (H : Source.Formula (k+1)) (w z f j n : Fin m) (r : Fin m → Fin l) :
    (existsEvaluation R H w z f j n).rename r = existsEvaluation R H (r w) (r z) (r f) (r j) (r n) := by
  simp only [existsEvaluation, Formula.rename, evaluation_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem intro_evaluation {k m} {Γ : Context m} (R : Source.Formula (k+2)) (H : Source.Formula (k+1)) (w z f j n h v : Fin m)
    (hg : Derives Γ (graph R H w z f j h n)) (hv : Derives Γ (value R H w z f j n h v)) : Derives Γ (evaluation R H w z f j n v) := by
  apply Derives.exI h
  exact of_eq (by simp only [Formula.instantiate, Formula.rename, graph_rename, value_rename,
    Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) (.conjI hg hv)

theorem evaluation_exists {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (R : Source.Formula (k+2)) (H : Source.Formula (k+1))
    (w z f j n : Fin m) (hn : Derives Γ (OrdinalSyntax.ordinal n)) : Derives Γ (existsEvaluation R H w z f j n) := by
  let G := graph R H w.castSucc z.castSucc f.castSucc j.castSucc (Fin.last m) n.castSucc
  let Δ := Context.add G (Context.image Formula.raise Γ)
  apply Derives.exE (p := G) (exists_graph hZ R H w z f j n hn)
  have hG : Derives Δ G := .hyp (Or.inl rfl)
  let V := value R H w.castSucc.castSucc z.castSucc.castSucc f.castSucc.castSucc j.castSucc.castSucc n.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))
  let Ξ := Context.add V (Context.image Formula.raise Δ)
  apply Derives.exE (p := V) (exists_value (ZFContext.under hZ G) R H w.castSucc z.castSucc f.castSucc j.castSucc n.castSucc (Fin.last m))
  have hV : Derives Ξ V := .hyp (Or.inl rfl)
  have hG2 := of_eq (graph_rename R H w.castSucc z.castSucc f.castSucc j.castSucc (Fin.last m) n.castSucc Fin.castSucc) (under hG V)
  have he := intro_evaluation R H w.castSucc.castSucc z.castSucc.castSucc f.castSucc.castSucc j.castSucc.castSucc n.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) hG2 hV
  have ho : Derives Ξ (existsEvaluation R H w.castSucc.castSucc z.castSucc.castSucc f.castSucc.castSucc j.castSucc.castSucc n.castSucc.castSucc) := by
    apply Derives.exI (Fin.last (m+1))
    exact of_eq (by simp only [Formula.instantiate, evaluation_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) he
  exact of_eq (by simp only [Formula.raise, existsEvaluation_rename]) ho

private theorem value_history_subst {k m} {Γ : Context m} (R : Source.Formula (k+2)) (H : Source.Formula (k+1)) (w z f j n h t v : Fin m)
    (he : Derives Γ (.equal h t)) (hv : Derives Γ (value R H w z f j n h v)) : Derives Γ (value R H w z f j n t v) := by
  let P := value R H w.castSucc z.castSucc f.castSucc j.castSucc n.castSucc (Fin.last m) v.castSucc
  exact of_eq (by simp only [P, Formula.instantiate, value_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq])
    (.eqSubst P he (of_eq (by simp only [P, Formula.instantiate, value_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) hv))

theorem evaluation_unique {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (R : Source.Formula (k+2)) (H : Source.Formula (k+1))
    (w z f j n v u : Fin m) (hn : Derives Γ (OrdinalSyntax.ordinal n))
    (hv : Derives Γ (evaluation R H w z f j n v)) (hu : Derives Γ (evaluation R H w z f j n u)) : Derives Γ (.equal v u) := by
  let G := (graph R H w.castSucc z.castSucc f.castSucc j.castSucc (Fin.last m) n.castSucc).conj (value R H w.castSucc z.castSucc f.castSucc j.castSucc n.castSucc (Fin.last m) v.castSucc)
  let Δ := Context.add G (Context.image Formula.raise Γ)
  apply Derives.exE (p := G) hv
  have hG : Derives Δ G := .hyp (Or.inl rfl)
  have hu1 := of_eq (evaluation_rename R H w z f j n u Fin.castSucc) (under hu G)
  let T := (graph R H w.castSucc.castSucc z.castSucc.castSucc f.castSucc.castSucc j.castSucc.castSucc (Fin.last (m+1)) n.castSucc.castSucc).conj
    (value R H w.castSucc.castSucc z.castSucc.castSucc f.castSucc.castSucc j.castSucc.castSucc n.castSucc.castSucc (Fin.last (m+1)) u.castSucc.castSucc)
  let Ξ := Context.add T (Context.image Formula.raise Δ)
  apply Derives.exE (p := T) hu1
  have hT : Derives Ξ T := .hyp (Or.inl rfl)
  have hG2 : Derives Ξ ((graph R H w.castSucc.castSucc z.castSucc.castSucc f.castSucc.castSucc j.castSucc.castSucc (Fin.last m).castSucc n.castSucc.castSucc).conj (value R H w.castSucc.castSucc z.castSucc.castSucc f.castSucc.castSucc j.castSucc.castSucc n.castSucc.castSucc (Fin.last m).castSucc v.castSucc.castSucc)) :=
    of_eq (by simp only [G, Formula.rename, graph_rename, value_rename]) (under hG T)
  have hn2 : Derives Ξ (OrdinalSyntax.ordinal n.castSucc.castSucc) := of_eq (by simp only [Formula.raise, OrdinalSyntax.ordinal_rename]) (under (under hn G) T)
  have he := graph_unique (ZFContext.under (ZFContext.under hZ G) T) R H w.castSucc.castSucc z.castSucc.castSucc f.castSucc.castSucc j.castSucc.castSucc
    (Fin.last m).castSucc (Fin.last (m+1)) n.castSucc.castSucc hn2 (.conjL hG2) (.conjL hT)
  have hv2 := value_history_subst R H w.castSucc.castSucc z.castSucc.castSucc f.castSucc.castSucc j.castSucc.castSucc n.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) v.castSucc.castSucc he (.conjR hG2)
  exact unique_value (ZFContext.under (ZFContext.under hZ G) T) R H w.castSucc.castSucc z.castSucc.castSucc f.castSucc.castSucc j.castSucc.castSucc
    n.castSucc.castSucc (Fin.last (m+1)) v.castSucc.castSucc u.castSucc.castSucc hv2 (.conjR hT)

/-- An actual edge of the parent recursive graph yields the independently
specified evaluation at the child's own index. -/
theorem edge_evaluation {k m} {Γ : Context m} (_hZ : ZFContext.Evidence Γ) (R : Source.Formula (k+2)) (H : Source.Formula (k+1))
    (w z f j g d n v : Fin m) (hd : Derives Γ (OrdinalSyntax.ordinal d)) (hn : Derives Γ (.mem n d))
    (hg : Derives Γ (graph R H w z f j g d)) (he : Derives Γ (GraphSyntax.edge g n v)) : Derives Γ (evaluation R H w z f j n v) := by
  have hno := OrdinalRestriction.member d n hd hn
  have hsub := OrdinalTransitivity.subset_of_member d n (.conjL hd) hn
  have hh := Derives.impE (Derives.impE (OrdinalRecursionSyntax.equations_at (matrix R H) (params w z f j) g d n v (.conjR hg)) hn) he
  let T := (RestrictionSyntax.restrict (Fin.last m) g.castSucc n.castSucc).conj
    (value R H w.castSucc z.castSucc f.castSucc j.castSucc n.castSucc (Fin.last m) v.castSucc)
  let Δ := Context.add T (Context.image Formula.raise Γ)
  have hhT : Derives Γ (.ex T) := by
    exact of_eq (by simp only [T, OrdinalRecursionSyntax.history, matrix_operator, paramsUp]; rfl) hh
  apply Derives.exE (p := T) hhT
  have hT : Derives Δ T := .hyp (Or.inl rfl)
  have hno1 := of_eq (OrdinalSyntax.ordinal_rename n Fin.castSucc) (under hno T)
  have hsub1 := of_eq (RestrictionSyntax.subset_rename n d Fin.castSucc) (under hsub T)
  have hg1 := of_eq (graph_rename R H w z f j g d Fin.castSucc) (under hg T)
  have hp := OrdinalRecursionRestriction.recursor_restrict (matrix R H) (params w.castSucc z.castSucc f.castSucc j.castSucc) (Fin.last m) g.castSucc n.castSucc d.castSucc
    (.conjL hno1) hsub1 (.conjL hT) hg1
  have ho := intro_evaluation R H w.castSucc z.castSucc f.castSucc j.castSucc n.castSucc (Fin.last m) v.castSucc hp (.conjR hT)
  exact of_eq (evaluation_rename R H w z f j n v Fin.castSucc).symm ho

theorem evaluation_edge {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (R : Source.Formula (k+2)) (H : Source.Formula (k+1))
    (w z f j g d n v : Fin m) (hd : Derives Γ (OrdinalSyntax.ordinal d)) (hn : Derives Γ (.mem n d))
    (hg : Derives Γ (graph R H w z f j g d)) (hv : Derives Γ (evaluation R H w z f j n v)) : Derives Γ (GraphSyntax.edge g n v) := by
  let T := GraphSyntax.edge g.castSucc n.castSucc (Fin.last m)
  let Δ := Context.add T (Context.image Formula.raise Γ)
  apply Derives.exE (p := T) (GraphProperties.output_exists g d n (.conjL hg) hn)
  have hT : Derives Δ T := .hyp (Or.inl rfl)
  have hd1 := of_eq (OrdinalSyntax.ordinal_rename d Fin.castSucc) (under hd T)
  have hg1 := of_eq (graph_rename R H w z f j g d Fin.castSucc) (under hg T)
  have hv1 := of_eq (evaluation_rename R H w z f j n v Fin.castSucc) (under hv T)
  have hn1 := under hn T
  have hy := edge_evaluation (ZFContext.under hZ T) R H w.castSucc z.castSucc f.castSucc j.castSucc g.castSucc d.castSucc n.castSucc (Fin.last m) hd1 hn1 hg1 hT
  have hno := OrdinalRestriction.member d.castSucc n.castSucc hd1 hn1
  have heq := evaluation_unique (ZFContext.under hZ T) R H w.castSucc z.castSucc f.castSucc j.castSucc n.castSucc (Fin.last m) v.castSucc hno hy hv1
  let P := GraphSyntax.edge g.castSucc.castSucc n.castSucc.castSucc (Fin.last (m+1))
  have ho : Derives Δ (GraphSyntax.edge g.castSucc n.castSucc v.castSucc) :=
    of_eq (by simp only [P, Formula.instantiate, GraphSyntax.edge_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq])
      (.eqSubst P heq (of_eq (by simp only [T, P, Formula.instantiate, GraphSyntax.edge_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]) hT))
  exact of_eq (by simp only [Formula.raise, GraphSyntax.edge_rename]) ho

def compiled {k m} (R : Source.Formula (k+2)) (H : Source.Formula (k+1)) (w z f j a n Q : Fin m) : Formula m := existsMany 2
  ((evaluation R H (old 2 w) (old 2 z) (old 2 f) (old 2 j) (old 2 n) (slot 2 0)).conj
    ((Formula.mem (slot 2 1) (slot 2 0)).conj (ForcingCodeStep.state (old 2 w) (old 2 a) (old 2 f) (old 2 Q) (slot 2 1))))
theorem compiled_rename {k m l} (R : Source.Formula (k+2)) (H : Source.Formula (k+1)) (w z f j a n Q : Fin m) (r : Fin m → Fin l) :
    (compiled R H w z f j a n Q).rename r = compiled R H (r w) (r z) (r f) (r j) (r a) (r n) (r Q) := by
  simp only [compiled, existsMany_rename, Formula.rename, evaluation_rename, ForcingCodeStep.state_rename, lift_old, lift_slot]
theorem intro_compiled {k m} {Γ : Context m} (R : Source.Formula (k+2)) (H : Source.Formula (k+1)) (w z f j a n Q v t : Fin m)
    (hv : Derives Γ (evaluation R H w z f j n v)) (ht : Derives Γ (.mem t v)) (hs : Derives Γ (ForcingCodeStep.state w a f Q t)) :
    Derives Γ (compiled R H w z f j a n Q) := by
  apply HornBinderRules.intro_many 2 _ (SyntaxAtomSyntax.two v t)
  exact of_eq (by simp only [Formula.rename, evaluation_rename, ForcingCodeStep.state_rename, assign_old, assign_slot]; rfl) (.conjI hv (.conjI ht hs))

theorem read_to_compiled {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (R : Source.Formula (k+2)) (H : Source.Formula (k+1))
    (w z f j g d a n Q : Fin m) (hd : Derives Γ (OrdinalSyntax.ordinal d)) (hn : Derives Γ (.mem n d))
    (hg : Derives Γ (graph R H w z f j g d)) (hc : Derives Γ (ForcingCodeStep.read w g n a f Q)) : Derives Γ (compiled R H w z f j a n Q) := by
  let T := (GraphSyntax.edge (old 2 g) (old 2 n) (slot 2 0)).conj
    ((Formula.mem (slot 2 1) (slot 2 0)).conj (ForcingCodeStep.state (old 2 w) (old 2 a) (old 2 f) (old 2 Q) (slot 2 1)))
  let Δ := Context.add T (raisedContext 2 Γ)
  apply HornBinderRules.eliminate_many 2 T _ hc
  have hT : Derives Δ T := .hyp (Or.inl rfl)
  have hd2 := of_eq (OrdinalSyntax.ordinal_rename d (old 2)) (HornBinderRules.under_body 2 hd T)
  have hn2 := HornBinderRules.under_body 2 hn T
  have hg2 := of_eq (graph_rename R H w z f j g d (old 2)) (HornBinderRules.under_body 2 hg T)
  have he := edge_evaluation (HornBinderRules.zf_body 2 hZ T) R H (old 2 w) (old 2 z) (old 2 f) (old 2 j)
    (old 2 g) (old 2 d) (old 2 n) (slot 2 0) hd2 hn2 hg2 (.conjL hT)
  have ho := intro_compiled R H (old 2 w) (old 2 z) (old 2 f) (old 2 j) (old 2 a) (old 2 n) (old 2 Q) (slot 2 0) (slot 2 1) he (.conjL (.conjR hT)) (.conjR (.conjR hT))
  exact of_eq (compiled_rename R H w z f j a n Q (old 2)).symm ho

theorem compiled_to_read {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (R : Source.Formula (k+2)) (H : Source.Formula (k+1))
    (w z f j g d a n Q : Fin m) (hd : Derives Γ (OrdinalSyntax.ordinal d)) (hn : Derives Γ (.mem n d))
    (hg : Derives Γ (graph R H w z f j g d)) (hc : Derives Γ (compiled R H w z f j a n Q)) : Derives Γ (ForcingCodeStep.read w g n a f Q) := by
  let T := (evaluation R H (old 2 w) (old 2 z) (old 2 f) (old 2 j) (old 2 n) (slot 2 0)).conj
    ((Formula.mem (slot 2 1) (slot 2 0)).conj (ForcingCodeStep.state (old 2 w) (old 2 a) (old 2 f) (old 2 Q) (slot 2 1)))
  let Δ := Context.add T (raisedContext 2 Γ)
  apply HornBinderRules.eliminate_many 2 T _ hc
  have hT : Derives Δ T := .hyp (Or.inl rfl)
  have hd2 := of_eq (OrdinalSyntax.ordinal_rename d (old 2)) (HornBinderRules.under_body 2 hd T)
  have hn2 := HornBinderRules.under_body 2 hn T
  have hg2 := of_eq (graph_rename R H w z f j g d (old 2)) (HornBinderRules.under_body 2 hg T)
  have he := evaluation_edge (HornBinderRules.zf_body 2 hZ T) R H (old 2 w) (old 2 z) (old 2 f) (old 2 j)
    (old 2 g) (old 2 d) (old 2 n) (slot 2 0) hd2 hn2 hg2 (.conjL hT)
  have ho := ForcingCodeStep.intro_read (old 2 w) (old 2 g) (old 2 n) (old 2 a) (old 2 f) (old 2 Q) (slot 2 0) (slot 2 1) he (.conjL (.conjR hT)) (.conjR (.conjR hT))
  exact of_eq (ForcingCodeStep.read_rename w g n a f Q (old 2)).symm ho

/-- The old arbitrary-history read is now identified with the actual
independently specified recursive interpretation, on every bounded index. -/
theorem bounded_read_iff {k m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (R : Source.Formula (k+2)) (H : Source.Formula (k+1))
    (w z f j g d a n Q : Fin m) (hd : Derives Γ (OrdinalSyntax.ordinal d)) (hn : Derives Γ (.mem n d))
    (hg : Derives Γ (graph R H w z f j g d)) : Derives Γ ((ForcingCodeStep.read w g n a f Q).iff (compiled R H w z f j a n Q)) := by
  apply Derives.conjI
  · apply Derives.impI
    exact read_to_compiled (ZFContext.add hZ _) R H w z f j g d a n Q (add hd _) (add hn _) (add hg _) (.hyp (Or.inl rfl))
  · apply Derives.impI
    exact compiled_to_read (ZFContext.add hZ _) R H w z f j g d a n Q (add hd _) (add hn _) (add hg _) (.hyp (Or.inl rfl))

theorem target_type {k m} {Γ : Context m} (R : Source.Formula (k+2)) (H : Source.Formula (k+1)) (w z f j a n Q : Fin m)
    (hc : Derives Γ (compiled R H w z f j a n Q)) : Derives Γ (FormulaCodeSyntax.formulaCode w Q a f) := by
  let T := (evaluation R H (old 2 w) (old 2 z) (old 2 f) (old 2 j) (old 2 n) (slot 2 0)).conj
    ((Formula.mem (slot 2 1) (slot 2 0)).conj (ForcingCodeStep.state (old 2 w) (old 2 a) (old 2 f) (old 2 Q) (slot 2 1)))
  let Δ := Context.add T (raisedContext 2 Γ)
  apply HornBinderRules.eliminate_many 2 T _ hc
  have hT : Derives Δ T := .hyp (Or.inl rfl)
  exact of_eq (FormulaCodeSyntax.formulaCode_rename w Q a f (old 2)).symm (.conjR (.conjR (.conjR hT)))

def recursionSentence {k m} (R : Source.Formula (k+2)) (H : Source.Formula (k+1)) (w z f j : Fin m) : Source.Sentence :=
  (recursors R H w z f j).close
theorem recursion_kernel_certificate {k m} (R : Source.Formula (k+2)) (H : Source.Formula (k+1)) (w z f j : Fin m) :
    YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence (recursionSentence R H w z f j)) := by
  apply ZFReplay.replay
  apply TheoryTransport.sentence
  apply close_derives
  exact all_unique (ZFContext.source_ZF m) R H w z f j

def evaluationSentence {k m} (R : Source.Formula (k+2)) (H : Source.Formula (k+1)) (w z f j n : Fin m) : Source.Sentence :=
  ((OrdinalSyntax.ordinal n).imp (existsEvaluation R H w z f j n)).close
theorem evaluation_kernel_certificate {k m} (R : Source.Formula (k+2)) (H : Source.Formula (k+1)) (w z f j n : Fin m) :
    YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence (evaluationSentence R H w z f j n)) := by
  apply ZFReplay.replay
  apply TheoryTransport.sentence
  apply close_derives
  apply Derives.impI
  exact evaluation_exists (ZFContext.add (ZFContext.source_ZF m) _) R H w z f j n (.hyp (Or.inl rfl))

def evaluationUniqueSentence {k m} (R : Source.Formula (k+2)) (H : Source.Formula (k+1)) (w z f j n v u : Fin m) : Source.Sentence :=
  ((OrdinalSyntax.ordinal n).imp ((evaluation R H w z f j n v).imp ((evaluation R H w z f j n u).imp (Formula.equal v u)))).close
theorem evaluationUnique_kernel_certificate {k m} (R : Source.Formula (k+2)) (H : Source.Formula (k+1)) (w z f j n v u : Fin m) :
    YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence (evaluationUniqueSentence R H w z f j n v u)) := by
  apply ZFReplay.replay
  apply TheoryTransport.sentence
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  exact evaluation_unique (ZFContext.add (ZFContext.add (ZFContext.add (ZFContext.source_ZF m) _) _) _) R H w z f j n v u (.hyp (Or.inr (Or.inr (Or.inl rfl)))) (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

def boundedReadSentence {k m} (R : Source.Formula (k+2)) (H : Source.Formula (k+1)) (w z f j g d a n Q : Fin m) : Source.Sentence :=
  ((OrdinalSyntax.ordinal d).imp ((Formula.mem n d).imp ((graph R H w z f j g d).imp ((ForcingCodeStep.read w g n a f Q).iff (compiled R H w z f j a n Q))))).close
theorem boundedRead_kernel_certificate {k m} (R : Source.Formula (k+2)) (H : Source.Formula (k+1)) (w z f j g d a n Q : Fin m) :
    YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence (boundedReadSentence R H w z f j g d a n Q)) := by
  apply ZFReplay.replay
  apply TheoryTransport.sentence
  apply close_derives
  apply Derives.impI
  apply Derives.impI
  apply Derives.impI
  exact bounded_read_iff (ZFContext.add (ZFContext.add (ZFContext.add (ZFContext.source_ZF m) _) _) _) R H w z f j g d a n Q (.hyp (Or.inr (Or.inr (Or.inl rfl)))) (.hyp (Or.inr (Or.inl rfl))) (.hyp (Or.inl rfl))

def targetTypeSentence {k m} (R : Source.Formula (k+2)) (H : Source.Formula (k+1)) (w z f j a n Q : Fin m) : Source.Sentence :=
  ((compiled R H w z f j a n Q).imp (FormulaCodeSyntax.formulaCode w Q a f)).close
theorem targetType_kernel_certificate {k m} (R : Source.Formula (k+2)) (H : Source.Formula (k+1)) (w z f j a n Q : Fin m) :
    YesMetaZFC.Logic.FirstOrder.Derives nativeZF [] (Translation.sentence (targetTypeSentence R H w z f j a n Q)) := by
  apply ZFReplay.replay
  apply TheoryTransport.sentence
  apply close_derives
  apply Derives.impI
  exact target_type R H w z f j a n Q (.hyp (Or.inl rfl))

end PPAC.Migration.ForcingCodeRecursion
