import PPAC.Migration.Internal.StructuralListPositionArithmetic

/-! 全原迹位置的纯对象对应：内部r+k=l，实际旧边给真实tail第r值。 -/
namespace PPAC.Migration.Internal.StructuralListPositionSyntax
open Source SourceAlgebra SourceLogic GraphSyntax NaturalAdditionSyntax StructuralListProjectionSyntax

def positions {m} (w l f n r : Fin m) : Formula m := .all (.all
  ((((Formula.mem (Fin.last m).castSucc w.castSucc.castSucc).conj
      (sum w.castSucc.castSucc r.castSucc.castSucc (Fin.last m).castSucc l.castSucc.castSucc)).conj
      (edge f.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)))).imp
    (iteration false w.castSucc.castSucc n.castSucc.castSucc r.castSucc.castSucc (Fin.last (m+1)))))

def matrix : Formula 5 := positions 0 1 2 3 4

theorem positions_rename {m k} (w l f n r : Fin m) (s : Fin m → Fin k) :
    (positions w l f n r).rename s = positions (s w) (s l) (s f) (s n) (s r) := by
  simp only [positions, Formula.rename, sum_rename, edge_rename, iteration_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem matrix_pred {m} (ρ : Fin 4 → Fin m) (x : Fin m) : MinimalPredicates.pred matrix ρ x = positions (ρ 0) (ρ 1) (ρ 2) (ρ 3) x := by
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
  simp only [MinimalPredicates.pred, matrix, positions_rename, h0, h1, h2, h3, h4]

theorem at_position {m} {Γ : Context m} (w l f n r k y : Fin m) (hp : Derives Γ (positions w l f n r))
    (hk : Derives Γ (.mem k w)) (hs : Derives Γ (sum w r k l)) (hy : Derives Γ (edge f k y)) : Derives Γ (iteration false w n r y) := by
  have h : Derives Γ ((((Formula.mem k w).conj (sum w r k l)).conj (edge f k y)).imp (iteration false w n r y)) := by
    simpa only [positions, Formula.instantiate, Formula.rename, sum_rename, edge_rename, iteration_rename,
      Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using Derives.allE y (Derives.allE k hp)
  exact .impE h (.conjI (.conjI hk hs) hy)

def params {m} (w l f n : Fin m) : Fin 4 → Fin m := Fin.lastCases n (Fin.lastCases f (Source.SetLanguage.args2 w l))

theorem params_first {m} (w l f n : Fin m) : params w l f n 0 = w := by
  change Fin.lastCases n (Fin.lastCases f (Source.SetLanguage.args2 w l)) (0 : Fin 2).castSucc.castSucc = w
  simp only [Fin.lastCases_castSucc, PairSyntax.args2_first]

theorem params_length {m} (w l f n : Fin m) : params w l f n 1 = l := by
  change Fin.lastCases n (Fin.lastCases f (Source.SetLanguage.args2 w l)) (1 : Fin 2).castSucc.castSucc = l
  simp only [Fin.lastCases_castSucc, PairSyntax.args2_second]

theorem params_graph {m} (w l f n : Fin m) : params w l f n 2 = f := by
  change Fin.lastCases n (Fin.lastCases f (Source.SetLanguage.args2 w l)) (Fin.last 2).castSucc = f
  simp only [Fin.lastCases_castSucc, Fin.lastCases_last]

theorem params_code {m} (w l f n : Fin m) : params w l f n 3 = n := by
  change Fin.lastCases n (Fin.lastCases f (Source.SetLanguage.args2 w l)) (Fin.last 3) = n
  exact Fin.lastCases_last

def reversedAt {m} (w l f n k r : Fin m) : Formula m :=
  ((Formula.mem r w).conj (sum w r k l)).conj (.all
    ((edge f.castSucc k.castSucc (Fin.last m)).iff (iteration false w.castSucc n.castSucc r.castSucc (Fin.last m))))

def reverseExists {m} (w l f n k : Fin m) : Formula m := .ex (reversedAt w.castSucc l.castSucc f.castSucc n.castSucc k.castSucc (Fin.last m))

theorem reversedAt_rename {m k} (w l f n i r : Fin m) (s : Fin m → Fin k) :
    (reversedAt w l f n i r).rename s = reversedAt (s w) (s l) (s f) (s n) (s i) (s r) := by
  simp only [reversedAt, Formula.rename, Formula.iff, sum_rename, edge_rename, iteration_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem reverseExists_rename {m k} (w l f n i : Fin m) (s : Fin m → Fin k) :
    (reverseExists w l f n i).rename s = reverseExists (s w) (s l) (s f) (s n) (s i) := by
  simp only [reverseExists, Formula.rename, reversedAt_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem intro_reverse {m} {Γ : Context m} (w l f n k r : Fin m) (hr : Derives Γ (.mem r w)) (hs : Derives Γ (sum w r k l))
    (he : Derives Γ (.all ((edge f.castSucc k.castSucc (Fin.last m)).iff (iteration false w.castSucc n.castSucc r.castSucc (Fin.last m))))) :
    Derives Γ (reverseExists w l f n k) := by
  apply Derives.exI r
  simp only [Formula.instantiate, reversedAt_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  exact .conjI (.conjI hr hs) he
end PPAC.Migration.Internal.StructuralListPositionSyntax
