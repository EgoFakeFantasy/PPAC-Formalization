import PPAC.Migration.Internal.StructuralListLengthConstruct

/-! 固定源序列的内部后缀编码不变量；长度r及全部偏移k都保留对象量词。 -/
namespace PPAC.Migration.Internal.StructuralListSuffixSyntax
open Source SourceAlgebra SourceLogic GraphSyntax NaturalAdditionSyntax StructuralListLengthSyntax StructuralListFieldSyntax

def aligned {m} (w f k r n : Fin m) : Formula m := .all (.all (.all
  (((Formula.mem (Fin.last m).castSucc.castSucc r.castSucc.castSucc.castSucc).conj
    (sum w.castSucc.castSucc.castSucc k.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc (Fin.last (m+1)).castSucc)).imp
      ((field w.castSucc.castSucc.castSucc n.castSucc.castSucc.castSucc (Fin.last m).castSucc.castSucc (Fin.last (m+2))).iff
        (edge f.castSucc.castSucc.castSucc (Fin.last (m+1)).castSucc (Fin.last (m+2)))))))

def coded {m} (w f k r n : Fin m) : Formula m := ((Formula.mem n w).conj (hasLength w n r)).conj (aligned w f k r n)

def existsCode {m} (w f k r : Fin m) : Formula m := .ex (coded w.castSucc f.castSucc k.castSucc r.castSucc (Fin.last m))

def property {m} (w f l r : Fin m) : Formula m := .all
  ((Formula.mem (Fin.last m) w.castSucc).imp ((sum w.castSucc r.castSucc (Fin.last m) l.castSucc).imp
    (existsCode w.castSucc f.castSucc (Fin.last m) r.castSucc)))

def matrix : Formula 4 := property 0 1 2 3

theorem aligned_rename {m k} (w f i r n : Fin m) (s : Fin m → Fin k) :
    (aligned w f i r n).rename s = aligned (s w) (s f) (s i) (s r) (s n) := by
  simp only [aligned, Formula.rename, Formula.iff, sum_rename, field_rename, edge_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem coded_rename {m k} (w f i r n : Fin m) (s : Fin m → Fin k) :
    (coded w f i r n).rename s = coded (s w) (s f) (s i) (s r) (s n) := by
  simp only [coded, Formula.rename, hasLength_rename, aligned_rename]

theorem existsCode_rename {m k} (w f i r : Fin m) (s : Fin m → Fin k) :
    (existsCode w f i r).rename s = existsCode (s w) (s f) (s i) (s r) := by
  simp only [existsCode, Formula.rename, coded_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem property_rename {m k} (w f l r : Fin m) (s : Fin m → Fin k) :
    (property w f l r).rename s = property (s w) (s f) (s l) (s r) := by
  simp only [property, Formula.rename, sum_rename, existsCode_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem matrix_pred {m} (ρ : Fin 3 → Fin m) (x : Fin m) : MinimalPredicates.pred matrix ρ x = property (ρ 0) (ρ 1) (ρ 2) x := by
  have h0 : Fin.lastCases x ρ (0 : Fin 4) = ρ 0 := by
    change Fin.lastCases x ρ (0 : Fin 3).castSucc = ρ 0
    exact Fin.lastCases_castSucc _
  have h1 : Fin.lastCases x ρ (1 : Fin 4) = ρ 1 := by
    change Fin.lastCases x ρ (1 : Fin 3).castSucc = ρ 1
    exact Fin.lastCases_castSucc _
  have h2 : Fin.lastCases x ρ (2 : Fin 4) = ρ 2 := by
    change Fin.lastCases x ρ (2 : Fin 3).castSucc = ρ 2
    exact Fin.lastCases_castSucc _
  have h3 : Fin.lastCases x ρ (3 : Fin 4) = x := by
    change Fin.lastCases x ρ (Fin.last 3) = x
    exact Fin.lastCases_last
  simp only [MinimalPredicates.pred, matrix, property_rename, h0, h1, h2, h3]

theorem aligned_at {m} {Γ : Context m} (w f k r n i j y : Fin m) (hm : Derives Γ (aligned w f k r n))
    (hi : Derives Γ (.mem i r)) (hs : Derives Γ (sum w k i j)) : Derives Γ ((field w n i y).iff (edge f j y)) := by
  have h : Derives Γ (((Formula.mem i r).conj (sum w k i j)).imp ((field w n i y).iff (edge f j y))) := by
    simpa only [aligned, Formula.instantiate, Formula.rename, Formula.iff, sum_rename, field_rename, edge_rename,
      Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using Derives.allE y (Derives.allE j (Derives.allE i hm))
  exact .impE h (.conjI hi hs)

theorem code_at {m} {Γ : Context m} (w f l r k : Fin m) (hp : Derives Γ (property w f l r))
    (hk : Derives Γ (.mem k w)) (hs : Derives Γ (sum w r k l)) : Derives Γ (existsCode w f k r) := by
  have h : Derives Γ ((Formula.mem k w).imp ((sum w r k l).imp (existsCode w f k r))) := by
    simpa only [property, Formula.instantiate, Formula.rename, sum_rename, existsCode_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using Derives.allE k hp
  exact .impE (.impE h hk) hs

theorem intro_code {m} {Γ : Context m} (w f k r n : Fin m) (hn : Derives Γ (.mem n w))
    (hl : Derives Γ (hasLength w n r)) (hm : Derives Γ (aligned w f k r n)) : Derives Γ (existsCode w f k r) := by
  apply Derives.exI n
  simp only [Formula.instantiate, coded_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  exact .conjI (.conjI hn hl) hm
end PPAC.Migration.Internal.StructuralListSuffixSyntax
