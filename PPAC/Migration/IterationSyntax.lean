import PPAC.Migration.ObjectGraphPointwise
import PPAC.Migration.ObjectOmegaStructure

/-! 内部并集迭代轨迹；不是宿主数组，所有索引/图/值均为对象集合。 -/
namespace PPAC.Migration.IterationSyntax
open Source SourceAlgebra SourceLogic OmegaSyntax GraphSyntax InsertSyntax MinimalPredicates

def agreesAt {m} (f g x : Fin m) : Formula m := .all (.all
  ((edge f.castSucc.castSucc x.castSucc.castSucc (Fin.last m).castSucc).imp
    ((edge g.castSucc.castSucc x.castSucc.castSucc (Fin.last (m+1))).imp
      (.equal (Fin.last m).castSucc (Fin.last (m+1))))))

def commonAt {m} (f g d e x : Fin m) : Formula m :=
  (Formula.mem x d).imp ((Formula.mem x e).imp (agreesAt f g x))

def allCommon {m} (f g d e w : Fin m) : Formula m := .all
  ((Formula.mem (Fin.last m) w.castSucc).imp
    (commonAt f.castSucc g.castSucc d.castSucc e.castSucc (Fin.last m)))

def next {m} (f : Fin m) : Formula m := .all (.all (.all (.all
  ((successor (Fin.last (m+1)).castSucc.castSucc (Fin.last m).castSucc.castSucc.castSucc).imp
    ((edge f.castSucc.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc.castSucc (Fin.last (m+2)).castSucc).imp
      ((edge f.castSucc.castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc.castSucc (Fin.last (m+3))).imp
        (unionOf (Fin.last (m+3)) (Fin.last (m+2)).castSucc)))))))

def track {m} (f d z a : Fin m) : Formula m :=
  (functionOn f d).conj ((edge f z a).conj (next f))

def agreementMatrix : Formula 5 := commonAt 0 1 2 3 4

def args4 {m} (f g d e : Fin m) : Fin 4 → Fin m := Fin.cases f (Fin.cases g (Fin.cases d (fun _ => e)))

theorem args4_0 {m} (f g d e : Fin m) : args4 f g d e 0 = f := rfl

theorem args4_1 {m} (f g d e : Fin m) : args4 f g d e 1 = g := rfl

theorem args4_2 {m} (f g d e : Fin m) : args4 f g d e 2 = d := rfl

theorem args4_3 {m} (f g d e : Fin m) : args4 f g d e 3 = e := rfl

theorem agreesAt_rename {m k} (f g x : Fin m) (r : Fin m → Fin k) :
    (agreesAt f g x).rename r = agreesAt (r f) (r g) (r x) := by
  simp only [agreesAt, Formula.rename, edge_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem commonAt_rename {m k} (f g d e x : Fin m) (r : Fin m → Fin k) :
    (commonAt f g d e x).rename r = commonAt (r f) (r g) (r d) (r e) (r x) := by
  simp only [commonAt, Formula.rename, agreesAt_rename]

theorem allCommon_rename {m k} (f g d e w : Fin m) (r : Fin m → Fin k) :
    (allCommon f g d e w).rename r = allCommon (r f) (r g) (r d) (r e) (r w) := by
  simp only [allCommon, Formula.rename, commonAt_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem next_rename {m k} (f : Fin m) (r : Fin m → Fin k) :
    (next f).rename r = next (r f) := by
  simp only [next, Formula.rename, successor_rename, edge_rename, unionOf_rename,
    Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem track_rename {m k} (f d z a : Fin m) (r : Fin m → Fin k) :
    (track f d z a).rename r = track (r f) (r d) (r z) (r a) := by
  simp only [track, Formula.rename, functionOn_rename, edge_rename, next_rename]

theorem agreesAt_at {m} {Γ : Context m} (f g x u v : Fin m) (h : Derives Γ (agreesAt f g x)) :
    Derives Γ ((edge f x u).imp ((edge g x v).imp (.equal u v))) := by
  have hi := Derives.allE v (Derives.allE u h)
  simpa only [Formula.instantiate, Formula.rename, edge_rename, Formula.liftRen,
    Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hi

theorem next_at {m} {Γ : Context m} (f j k u v : Fin m) (h : Derives Γ (next f)) :
    Derives Γ ((successor k j).imp ((edge f j u).imp ((edge f k v).imp (unionOf v u)))) := by
  have hi := Derives.allE v (Derives.allE u (Derives.allE k (Derives.allE j h)))
  simpa only [Formula.instantiate, Formula.rename, successor_rename, edge_rename, unionOf_rename,
    Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hi

theorem agreement_pred {m} (ρ : Fin 4 → Fin m) (x : Fin m) :
    pred agreementMatrix ρ x = commonAt (ρ 0) (ρ 1) (ρ 2) (ρ 3) x := by
  have h0 : Fin.lastCases x ρ (0 : Fin 5) = ρ 0 := by
    change Fin.lastCases x ρ (0 : Fin 4).castSucc = ρ 0
    exact Fin.lastCases_castSucc _
  have h1 : Fin.lastCases x ρ (1 : Fin 5) = ρ 1 := by
    change Fin.lastCases x ρ (1 : Fin 4).castSucc = ρ 1
    exact Fin.lastCases_castSucc _
  have h2 : Fin.lastCases x ρ (2 : Fin 5) = ρ 2 := by
    change Fin.lastCases x ρ (2 : Fin 4).castSucc = ρ 2
    exact Fin.lastCases_castSucc _
  have h3 : Fin.lastCases x ρ (3 : Fin 5) = ρ 3 := by
    change Fin.lastCases x ρ (3 : Fin 4).castSucc = ρ 3
    exact Fin.lastCases_castSucc _
  have h4 : Fin.lastCases x ρ (4 : Fin 5) = x := by
    change Fin.lastCases x ρ (Fin.last 4) = x
    exact Fin.lastCases_last
  simp only [pred, agreementMatrix, commonAt_rename, h0, h1, h2, h3, h4]
end PPAC.Migration.IterationSyntax
