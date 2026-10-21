import PPAC.Migration.ObjectOmegaStructure
import PPAC.Migration.GraphPointwiseEntries
import PPAC.Migration.GraphInsertElimination

/-! 内部有限序列的实际集合图，值域限制是纯公式，保留完整原functionOn。 -/
namespace PPAC.Migration.Internal.SequenceSyntax
open Source SourceAlgebra SourceLogic GraphSyntax OmegaSyntax

def bounded {m} (f b : Fin m) : Formula m := .all (.all
  ((edge f.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))).imp
    (.mem (Fin.last (m+1)) b.castSucc.castSucc)))
def sequence {m} (f n b : Fin m) : Formula m := (functionOn f n).conj (bounded f b)
def existsSequence {m} (n b : Fin m) : Formula m := .ex (sequence (Fin.last m) n.castSucc b.castSucc)
def value {m} (f i b : Fin m) : Formula m := .ex
  ((Formula.mem (Fin.last m) b.castSucc).conj (valueAt f.castSucc i.castSucc (Fin.last m)))
def append {m} (g k f n y b : Fin m) : Formula m := (sequence g k b).conj
  ((GraphInsertSyntax.edgeLaw g f n y).conj (RestrictionSyntax.restrict f g n))
def appendExists {m} (k f n y b : Fin m) : Formula m := .ex
  (append (Fin.last m) k.castSucc f.castSucc n.castSucc y.castSucc b.castSucc)
def appendUnique {m} (k f n y b : Fin m) : Formula m := .ex
  ((append (Fin.last m) k.castSucc f.castSucc n.castSucc y.castSucc b.castSucc).conj (.all
    ((append (Fin.last (m+1)) k.castSucc.castSucc f.castSucc.castSucc n.castSucc.castSucc y.castSucc.castSucc b.castSucc.castSucc).imp
      (.equal (Fin.last (m+1)) (Fin.last m).castSucc))))
def existenceMatrix : Formula 2 := existsSequence 1 0

theorem bounded_rename {m k} (f b : Fin m) (r : Fin m → Fin k) :
    (bounded f b).rename r = bounded (r f) (r b) := by
  simp only [bounded, Formula.rename, edge_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]
theorem sequence_rename {m k} (f n b : Fin m) (r : Fin m → Fin k) :
    (sequence f n b).rename r = sequence (r f) (r n) (r b) := by
  simp only [sequence, Formula.rename, functionOn_rename, bounded_rename]
theorem existsSequence_rename {m k} (n b : Fin m) (r : Fin m → Fin k) :
    (existsSequence n b).rename r = existsSequence (r n) (r b) := by
  simp only [existsSequence, Formula.rename, sequence_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]
theorem value_rename {m k} (f i b : Fin m) (r : Fin m → Fin k) :
    (value f i b).rename r = value (r f) (r i) (r b) := by
  simp only [value, Formula.rename, valueAt_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]
theorem append_rename {m k} (g d f n y b : Fin m) (r : Fin m → Fin k) :
    (append g d f n y b).rename r = append (r g) (r d) (r f) (r n) (r y) (r b) := by
  simp only [append, Formula.rename, sequence_rename, GraphInsertSyntax.edgeLaw_rename, RestrictionSyntax.restrict_rename]
theorem appendExists_rename {m k} (d f n y b : Fin m) (r : Fin m → Fin k) :
    (appendExists d f n y b).rename r = appendExists (r d) (r f) (r n) (r y) (r b) := by
  simp only [appendExists, Formula.rename, append_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]
theorem appendUnique_rename {m k} (d f n y b : Fin m) (r : Fin m → Fin k) :
    (appendUnique d f n y b).rename r = appendUnique (r d) (r f) (r n) (r y) (r b) := by
  simp only [appendUnique, Formula.rename, append_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]
theorem existence_pred {m} (ρ : Fin 1 → Fin m) (n : Fin m) :
    MinimalPredicates.pred existenceMatrix ρ n = existsSequence n (ρ 0) := by
  have h0 : Fin.lastCases n ρ (0 : Fin 2) = ρ 0 := by
    change Fin.lastCases n ρ (0 : Fin 1).castSucc = ρ 0
    exact Fin.lastCases_castSucc _
  have h1 : Fin.lastCases n ρ (1 : Fin 2) = n := by
    change Fin.lastCases n ρ (Fin.last 1) = n
    exact Fin.lastCases_last
  simp only [MinimalPredicates.pred, existenceMatrix, existsSequence_rename, h0, h1]

theorem bounded_at {m} {Γ : Context m} (f b i y : Fin m) (hb : Derives Γ (bounded f b)) :
    Derives Γ ((edge f i y).imp (.mem y b)) := by
  have hi := Derives.allE y (Derives.allE i hb)
  simpa only [Formula.instantiate, Formula.rename, edge_rename, Formula.liftRen,
    Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hi

theorem law_at {m} {Γ : Context m} (g f n y i v : Fin m) (hl : Derives Γ (GraphInsertSyntax.edgeLaw g f n y)) :
    Derives Γ ((edge g i v).iff ((edge f i v).disj ((Formula.equal i n).conj (.equal v y)))) := by
  have hi := Derives.allE v (Derives.allE i hl)
  simpa only [Formula.instantiate, Formula.iff, Formula.rename, edge_rename, Formula.liftRen,
    Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hi

theorem intro_exists {m} {Γ : Context m} (f n b : Fin m) (hf : Derives Γ (sequence f n b)) :
    Derives Γ (existsSequence n b) := by
  apply Derives.exI f
  simpa only [Formula.instantiate, sequence_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hf

theorem subst_domain {m} {Γ : Context m} (f n k b : Fin m) (he : Derives Γ (.equal n k))
    (hf : Derives Γ (sequence f n b)) : Derives Γ (sequence f k b) := by
  have hi : Derives Γ ((sequence f.castSucc (Fin.last m) b.castSucc).instantiate n) := by
    simpa only [Formula.instantiate, sequence_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hf
  have hout := Derives.eqSubst (sequence f.castSucc (Fin.last m) b.castSucc) he hi
  simpa only [Formula.instantiate, sequence_rename, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq] using hout
end PPAC.Migration.Internal.SequenceSyntax
