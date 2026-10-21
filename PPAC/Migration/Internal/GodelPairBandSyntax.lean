import PPAC.Migration.Internal.GodelPairIntervals

/-! 平方区间是纯成员公式；平方及后继值均受对象全称量词约束。 -/
namespace PPAC.Migration.Internal.GodelPairBandSyntax
open Source SourceAlgebra SourceLogic OmegaSyntax
open NaturalMultiplicationSyntax (product product_rename)
open NaturalAdditionBounds (below below_rename)

def floor {m} (w x p : Fin m) : Formula m := .all
  ((product w.castSucc x.castSucc x.castSucc (Fin.last m)).imp (below (Fin.last m) p.castSucc))
def ceiling {m} (w x p : Fin m) : Formula m := .all (.all
  ((successor (Fin.last m).castSucc x.castSucc.castSucc).imp
    ((product w.castSucc.castSucc (Fin.last m).castSucc (Fin.last m).castSucc (Fin.last (m+1))).imp
      (.mem p.castSucc.castSucc (Fin.last (m+1))))))
def band {m} (w x p : Fin m) : Formula m := (floor w x p).conj (ceiling w x p)

theorem floor_rename {m k} (w x p : Fin m) (r : Fin m → Fin k) :
    (floor w x p).rename r = floor (r w) (r x) (r p) := by
  simp only [floor, Formula.rename, product_rename, below_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]
theorem ceiling_rename {m k} (w x p : Fin m) (r : Fin m → Fin k) :
    (ceiling w x p).rename r = ceiling (r w) (r x) (r p) := by
  simp only [ceiling, Formula.rename, successor_rename, product_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]
theorem band_rename {m k} (w x p : Fin m) (r : Fin m → Fin k) :
    (band w x p).rename r = band (r w) (r x) (r p) := by
  simp only [band, Formula.rename, floor_rename, ceiling_rename]

theorem floor_at {m} {Γ : Context m} (w x p q : Fin m) (hb : Derives Γ (band w x p))
    (hq : Derives Γ (product w x x q)) : Derives Γ (below q p) := by
  have hf := Derives.allE q (Derives.conjL hb)
  have hi : Derives Γ ((product w x x q).imp (below q p)) := by
    simpa only [floor, Formula.instantiate, Formula.rename, product_rename, below_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hf
  exact .impE hi hq

theorem ceiling_at {m} {Γ : Context m} (w x p s v : Fin m) (hb : Derives Γ (band w x p))
    (hs : Derives Γ (successor s x)) (hv : Derives Γ (product w s s v)) : Derives Γ (.mem p v) := by
  have h1 : Derives Γ (.all ((successor s.castSucc x.castSucc).imp
      ((product w.castSucc s.castSucc s.castSucc (Fin.last m)).imp (.mem p.castSucc (Fin.last m))))) := by
    simpa only [ceiling, Formula.instantiate, Formula.rename, successor_rename, product_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using Derives.allE s (Derives.conjR hb)
  have h2 : Derives Γ ((successor s x).imp ((product w s s v).imp (.mem p v))) := by
    simpa only [Formula.instantiate, Formula.rename, successor_rename, product_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using Derives.allE v h1
  exact .impE (.impE h2 hs) hv
end PPAC.Migration.Internal.GodelPairBandSyntax
