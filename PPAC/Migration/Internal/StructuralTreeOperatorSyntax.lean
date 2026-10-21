import PPAC.Migration.Internal.ObjectStructuralFieldBounds

/-! 原raw树节点及实际完整子字段图上的二值前段算子；只查询严格更小子码，不引用树有效性。 -/
namespace PPAC.Migration.Internal.StructuralTreeOperatorSyntax
open Source SourceAlgebra SourceLogic OmegaSyntax GraphSyntax StructuralNodeSyntax StructuralListFieldGraphSyntax
open StructuralListLengthSyntax (hasLength hasLength_rename)
open NaturalAdditionTransport (params3 params3_0 params3_1 params3_2)

def shape {m} (w n tag p l f : Fin m) : Formula m :=
  ((Formula.mem tag w).conj (raw w tag p n)).conj ((hasLength w p l).conj (fields w p l f))

def marks {m} (e f h : Fin m) : Formula m := .all (.all
  ((edge f.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))).imp
    (edge h.castSucc.castSucc (Fin.last (m+1)) e.castSucc.castSucc)))

def children {m} (e n f h : Fin m) : Formula m := .all (.all
  ((edge f.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))).imp
    ((Formula.mem (Fin.last (m+1)) n.castSucc.castSucc).conj (edge h.castSucc.castSucc (Fin.last (m+1)) e.castSucc.castSucc))))

def goodBody {m} (w e n h : Fin m) : Formula (m+4) :=
  (shape w.castSucc.castSucc.castSucc.castSucc n.castSucc.castSucc.castSucc.castSucc
    (Fin.last m).castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc.castSucc (Fin.last (m+2)).castSucc (Fin.last (m+3))).conj
    (children e.castSucc.castSucc.castSucc.castSucc n.castSucc.castSucc.castSucc.castSucc (Fin.last (m+3)) h.castSucc.castSucc.castSucc.castSucc)

def good {m} (w e n h : Fin m) : Formula m := .ex (.ex (.ex (.ex (goodBody w e n h))))

def step {m} (w z e n h y : Fin m) : Formula m :=
  ((good w e n h).conj (.equal y e)).disj ((good w e n h).neg.conj (.equal y z))

def matrix : Formula 6 := step 0 1 2 3 4 5

def recursors {m} (w z e : Fin m) : Formula m := OrdinalRecursionExistenceSyntax.allUnique matrix (params3 w z e)

def actualRecursors {m} (w : Fin m) : Formula m := .ex (.ex
  (((empty (Fin.last m).castSucc).conj (successor (Fin.last (m+1)) (Fin.last m).castSucc)).conj
    (recursors w.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)))))

theorem shape_rename {m k} (w n tag p l f : Fin m) (s : Fin m → Fin k) : (shape w n tag p l f).rename s = shape (s w) (s n) (s tag) (s p) (s l) (s f) := by
  simp only [shape, Formula.rename, raw_rename, hasLength_rename, fields_rename]

theorem marks_rename {m k} (e f h : Fin m) (s : Fin m → Fin k) : (marks e f h).rename s = marks (s e) (s f) (s h) := by
  simp only [marks, Formula.rename, edge_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem children_rename {m k} (e n f h : Fin m) (s : Fin m → Fin k) : (children e n f h).rename s = children (s e) (s n) (s f) (s h) := by
  simp only [children, Formula.rename, edge_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem good_rename {m k} (w e n h : Fin m) (s : Fin m → Fin k) : (good w e n h).rename s = good (s w) (s e) (s n) (s h) := by
  simp only [good, goodBody, Formula.rename, shape_rename, children_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem step_rename {m k} (w z e n h y : Fin m) (s : Fin m → Fin k) : (step w z e n h y).rename s = step (s w) (s z) (s e) (s n) (s h) (s y) := by
  simp only [step, Formula.rename, Formula.neg, good_rename]

theorem matrix_operator {m} (ρ : Fin 3 → Fin m) (n h y : Fin m) : OrdinalRecursionSyntax.operator matrix ρ n h y = step (ρ 0) (ρ 1) (ρ 2) n h y := by
  have h0 : Fin.lastCases y (Fin.lastCases h (Fin.lastCases n ρ)) (0 : Fin 6) = ρ 0 := by
    change Fin.lastCases y (Fin.lastCases h (Fin.lastCases n ρ)) (0 : Fin 3).castSucc.castSucc.castSucc = ρ 0
    simp only [Fin.lastCases_castSucc]
  have h1 : Fin.lastCases y (Fin.lastCases h (Fin.lastCases n ρ)) (1 : Fin 6) = ρ 1 := by
    change Fin.lastCases y (Fin.lastCases h (Fin.lastCases n ρ)) (1 : Fin 3).castSucc.castSucc.castSucc = ρ 1
    simp only [Fin.lastCases_castSucc]
  have h2 : Fin.lastCases y (Fin.lastCases h (Fin.lastCases n ρ)) (2 : Fin 6) = ρ 2 := by
    change Fin.lastCases y (Fin.lastCases h (Fin.lastCases n ρ)) (2 : Fin 3).castSucc.castSucc.castSucc = ρ 2
    simp only [Fin.lastCases_castSucc]
  have h3 : Fin.lastCases y (Fin.lastCases h (Fin.lastCases n ρ)) (3 : Fin 6) = n := by
    change Fin.lastCases y (Fin.lastCases h (Fin.lastCases n ρ)) (Fin.last 3).castSucc.castSucc = n
    simp only [Fin.lastCases_castSucc, Fin.lastCases_last]
  have h4 : Fin.lastCases y (Fin.lastCases h (Fin.lastCases n ρ)) (4 : Fin 6) = h := by
    change Fin.lastCases y (Fin.lastCases h (Fin.lastCases n ρ)) (Fin.last 4).castSucc = h
    simp only [Fin.lastCases_castSucc, Fin.lastCases_last]
  have h5 : Fin.lastCases y (Fin.lastCases h (Fin.lastCases n ρ)) (5 : Fin 6) = y := by
    change Fin.lastCases y (Fin.lastCases h (Fin.lastCases n ρ)) (Fin.last 5) = y
    exact Fin.lastCases_last
  simp only [OrdinalRecursionSyntax.operator, matrix, step_rename, h0, h1, h2, h3, h4, h5]

theorem params3_map {m k} (w z e : Fin m) (s : Fin m → Fin k) : (fun i => s (params3 w z e i)) = params3 (s w) (s z) (s e) := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp only [NaturalAdditionTransport.params3, Fin.lastCases_last]
  · simp only [NaturalAdditionTransport.params3, Fin.lastCases_castSucc]
    refine Fin.cases ?_ (fun k => ?_) j
    · rfl
    · refine Fin.cases ?_ (fun bad => Fin.elim0 bad) k
      rfl

theorem recursors_rename {m k} (w z e : Fin m) (s : Fin m → Fin k) : (recursors w z e).rename s = recursors (s w) (s z) (s e) := by
  simp only [recursors, OrdinalRecursionExistenceSyntax.allUnique_rename, params3_map]

theorem actualRecursors_rename {m k} (w : Fin m) (s : Fin m → Fin k) : (actualRecursors w).rename s = actualRecursors (s w) := by
  simp only [actualRecursors, Formula.rename, empty_rename, successor_rename, recursors_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem marks_at {m} {Γ : Context m} (e f h i y : Fin m) (hm : Derives Γ (marks e f h)) (he : Derives Γ (edge f i y)) : Derives Γ (edge h y e) := by
  have h : Derives Γ ((edge f i y).imp (edge h y e)) := by
    simpa only [marks, Formula.instantiate, Formula.rename, edge_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using Derives.allE y (Derives.allE i hm)
  exact .impE h he

theorem children_at {m} {Γ : Context m} (e n f h i y : Fin m) (hc : Derives Γ (children e n f h)) (he : Derives Γ (edge f i y)) : Derives Γ ((Formula.mem y n).conj (edge h y e)) := by
  have h : Derives Γ ((edge f i y).imp ((Formula.mem y n).conj (edge h y e))) := by
    simpa only [children, Formula.instantiate, Formula.rename, edge_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using Derives.allE y (Derives.allE i hc)
  exact .impE h he

theorem intro_good {m} {Γ : Context m} (w e n h tag p l f : Fin m) (hs : Derives Γ (shape w n tag p l f))
    (hc : Derives Γ (children e n f h)) : Derives Γ (good w e n h) := by
  apply Derives.exI tag
  apply Derives.exI p
  apply Derives.exI l
  apply Derives.exI f
  simp only [goodBody, Formula.instantiate, Formula.rename, shape_rename, children_rename,
    Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  exact .conjI hs hc

theorem eliminate_good {m} {Γ : Context m} (w e n h : Fin m) (q : Formula m) (hg : Derives Γ (good w e n h))
    (hc : Derives (Context.add (goodBody w e n h) (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise (Context.image Formula.raise Γ))))) q.raise.raise.raise.raise) : Derives Γ q := by
  change Derives Γ (.ex (.ex (.ex (.ex _)))) at hg
  apply Derives.exE hg
  apply Derives.exE (.hyp (Or.inl rfl))
  apply Derives.exE (.hyp (Or.inl rfl))
  apply Derives.exE (.hyp (Or.inl rfl))
  refine Derives.weaken ?_ hc
  rintro r (hr | ⟨s, ⟨t, ⟨u, hu, h1⟩, h2⟩, h3⟩)
  · exact Or.inl hr
  · exact Or.inr ⟨s, Or.inr ⟨t, Or.inr ⟨u, Or.inr hu, h1⟩, h2⟩, h3⟩
end PPAC.Migration.Internal.StructuralTreeOperatorSyntax
