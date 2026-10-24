import PPAC.Migration.Internal.ProjectSourceLocal

/-! 完整局部判据在实际上下文载体上的Separation；不含统一真值谓词或宿主选择。 -/
namespace PPAC.Migration.Internal.ProjectSourceTypeStateSyntax
open Source SourceAlgebra SourceLogic PairSyntax SyntaxAtomSyntax ProjectSourceLocalSyntax

def rowBody {m} (w n h p : Fin m) : Formula (m+2) :=
  (ordered p.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1))).conj
    (localType w.castSucc.castSucc (Fin.last m).castSucc (Fin.last (m+1)) h.castSucc.castSucc n.castSucc.castSucc)
def row {m} (w n h p : Fin m) : Formula m := .ex (.ex (rowBody w n h p))

def selectionMatrix : Formula (3+1) :=
  row (0 : Fin 3).castSucc (1 : Fin 3).castSucc (2 : Fin 3).castSucc (Fin.last 3)

def state {m} (w c n h v : Fin m) : Formula m :=
  MinimalPredicates.separated selectionMatrix (three w n h) c v
def existsState {m} (w c n h : Fin m) : Formula m := .ex
  (state w.castSucc c.castSucc n.castSucc h.castSucc (Fin.last m))
def uniqueState {m} (w c n h v : Fin m) : Formula m := .all
  ((state w.castSucc c.castSucc n.castSucc h.castSucc (Fin.last m)).imp (.equal (Fin.last m) v.castSucc))
def fiber {m} (w c n h : Fin m) : Formula m := .ex
  ((state w.castSucc c.castSucc n.castSucc h.castSucc (Fin.last m)).conj
    (uniqueState w.castSucc c.castSucc n.castSucc h.castSucc (Fin.last m)))

theorem row_rename {m k} (w n h p : Fin m) (r : Fin m → Fin k) :
    (row w n h p).rename r = row (r w) (r n) (r h) (r p) := by
  simp only [row, rowBody, Formula.rename, ordered_rename, localType_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem selection_at {m} (ρ : Fin 3 → Fin m) (p : Fin m) :
    MinimalPredicates.pred selectionMatrix ρ p = row (ρ 0) (ρ 1) (ρ 2) p := by
  simp only [MinimalPredicates.pred, selectionMatrix, row_rename, Fin.lastCases_castSucc, Fin.lastCases_last]

theorem state_rename {m k} (w c n h v : Fin m) (r : Fin m → Fin k) :
    (state w c n h v).rename r = state (r w) (r c) (r n) (r h) (r v) := by
  simp only [state, MinimalPredicates.separated_rename, three_map]

theorem existsState_rename {m k} (w c n h : Fin m) (r : Fin m → Fin k) :
    (existsState w c n h).rename r = existsState (r w) (r c) (r n) (r h) := by
  simp only [existsState, Formula.rename, state_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem uniqueState_rename {m k} (w c n h v : Fin m) (r : Fin m → Fin k) :
    (uniqueState w c n h v).rename r = uniqueState (r w) (r c) (r n) (r h) (r v) := by
  simp only [uniqueState, Formula.rename, state_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem fiber_rename {m k} (w c n h : Fin m) (r : Fin m → Fin k) :
    (fiber w c n h).rename r = fiber (r w) (r c) (r n) (r h) := by
  simp only [fiber, Formula.rename, state_rename, uniqueState_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc]

theorem state_at {m} {Γ : Context m} (w c n h v p : Fin m) (hs : Derives Γ (state w c n h v)) :
    Derives Γ ((Formula.mem p v).iff ((Formula.mem p c).conj (row w n h p))) := by
  have hi := MinimalPredicates.specialize_separated selectionMatrix (three w n h) c v p hs
  simp only [MinimalPredicates.satisfying, selection_at] at hi
  exact hi

theorem intro_row {m} {Γ : Context m} (w n h p b f : Fin m) (hp : Derives Γ (ordered p b f))
    (hl : Derives Γ (localType w b f h n)) : Derives Γ (row w n h p) := by
  apply Derives.exI b
  apply Derives.exI f
  simp only [rowBody, Formula.instantiate, Formula.rename, ordered_rename, localType_rename, Formula.liftRen, Fin.lastCases_last, Fin.lastCases_castSucc, id_eq]
  exact .conjI hp hl

theorem eliminate_row {m} {Γ : Context m} (w n h p : Fin m) (q : Formula m) (hr : Derives Γ (row w n h p))
    (hc : Derives (Context.add (rowBody w n h p) (Context.image Formula.raise (Context.image Formula.raise Γ))) q.raise.raise) : Derives Γ q := by
  apply Derives.exE hr
  apply Derives.exE (.hyp (Or.inl rfl))
  refine Derives.weaken ?_ hc
  rintro q (hq | ⟨s, hs, he⟩)
  · exact Or.inl hq
  · exact Or.inr ⟨s, Or.inr hs, he⟩
end PPAC.Migration.Internal.ProjectSourceTypeStateSyntax
