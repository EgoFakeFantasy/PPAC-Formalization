import PPAC.Migration.Internal.PacketStructureRuleData

/-! Exact numeric structural matrices; no runtime expression evaluation or host data recursion. -/
namespace PPAC.Migration.Internal.PacketStructureSyntax
open Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax
open SyntaxRenameQuerySyntax (of_eq)

def four {m} (a b c d : Fin m) : Fin 4 → Fin m := Fin.cases a (SyntaxAtomSyntax.three b c d)

theorem four_map {m j} (a b c d : Fin m) (ρ : Fin m → Fin j) :
    (fun i => ρ (four a b c d i)) = four (ρ a) (ρ b) (ρ c) (ρ d) := by
  funext i
  refine Fin.cases rfl (fun j => ?_) i
  exact congrFun (SyntaxAtomSyntax.three_map b c d ρ) j

def row {m} (k tag : Nat) (w : Fin m) (xs : Fin k → Fin m) (r : Fin m) : Formula m := SyntaxNodeSyntax.constructor k tag w xs r

def entry {m} (k tag : Nat) (w V : Fin m) (xs : Fin k → Fin m) : Formula m := .ex
  ((row k tag w.castSucc (fun i => (xs i).castSucc) (Fin.last m)).conj (.mem (Fin.last m) V.castSucc))

def treeRow {m} (w n t a r : Fin m) : Formula m := row 3 3 w (SyntaxAtomSyntax.three n t a) r

def forestRow {m} (w n l t a r : Fin m) : Formula m := row 4 4 w (four n l t a) r

def packetRow {m} (w a n r : Fin m) : Formula m := row 2 5 w (SyntaxAtomSyntax.two a n) r

def treeEntry {m} (w V n t a : Fin m) : Formula m := entry 3 3 w V (SyntaxAtomSyntax.three n t a)

def forestEntry {m} (w V n l t a : Fin m) : Formula m := entry 4 4 w V (four n l t a)

def treeAt {m} (w V r n : Fin m) (env : Fin 7 → Fin m) : Formula m :=
  (treeRow w n (env 2) (env 3) r).conj
    ((forestEntry w V (env 1) (env 4) (env 2) (env 5)).conj
      ((PacketTokenSyntax.entry w V (env 4) (env 5) (env 6)).conj (PacketTokenSyntax.entry w V (env 0) (env 6) (env 3))))

def nilAt {m} (w r z e : Fin m) (env : Fin 1 → Fin m) : Formula m := forestRow w e z (env 0) (env 0) r

def consAt {m} (w V r n s : Fin m) (env : Fin 6 → Fin m) : Formula m :=
  (forestRow w n s (env 3) (env 4) r).conj
    ((forestEntry w V (env 1) (env 2) (env 3) (env 5)).conj (treeEntry w V (env 0) (env 5) (env 4)))

def packetAt {m} (w V r e : Fin m) (env : Fin 3 → Fin m) : Formula m :=
  (packetRow w (env 1) (env 0) r).conj
    ((PacketTokenSyntax.tagEntry 1 w V e (env 2) (env 1)).conj (treeEntry w V (env 0) e (env 2)))

theorem row_rename {m j} (k tag : Nat) (w r : Fin m) (xs : Fin k → Fin m) (ρ : Fin m → Fin j) :
    (row k tag w xs r).rename ρ = row k tag (ρ w) (fun i => ρ (xs i)) (ρ r) := by
  simp only [row,SyntaxNodeSyntax.constructor_rename]

theorem entry_rename {m j} (k tag : Nat) (w V : Fin m) (xs : Fin k → Fin m) (ρ : Fin m → Fin j) :
    (entry k tag w V xs).rename ρ = entry k tag (ρ w) (ρ V) (fun i => ρ (xs i)) := by
  simp only [entry,Formula.rename,row_rename,Formula.liftRen,Fin.lastCases_last,Fin.lastCases_castSucc]

theorem treeRow_rename {m j} (w n t a r : Fin m) (ρ : Fin m → Fin j) :
    (treeRow w n t a r).rename ρ = treeRow (ρ w) (ρ n) (ρ t) (ρ a) (ρ r) := by
  simp only [treeRow,row_rename,SyntaxAtomSyntax.three_map]

theorem forestRow_rename {m j} (w n l t a r : Fin m) (ρ : Fin m → Fin j) :
    (forestRow w n l t a r).rename ρ = forestRow (ρ w) (ρ n) (ρ l) (ρ t) (ρ a) (ρ r) := by
  simp only [forestRow,row_rename,four_map]

theorem packetRow_rename {m j} (w a n r : Fin m) (ρ : Fin m → Fin j) :
    (packetRow w a n r).rename ρ = packetRow (ρ w) (ρ a) (ρ n) (ρ r) := by
  simp only [packetRow,row_rename,SyntaxAtomSyntax.two_map]

theorem treeEntry_rename {m j} (w V n t a : Fin m) (ρ : Fin m → Fin j) :
    (treeEntry w V n t a).rename ρ = treeEntry (ρ w) (ρ V) (ρ n) (ρ t) (ρ a) := by
  simp only [treeEntry,entry_rename,SyntaxAtomSyntax.three_map]

theorem forestEntry_rename {m j} (w V n l t a : Fin m) (ρ : Fin m → Fin j) :
    (forestEntry w V n l t a).rename ρ = forestEntry (ρ w) (ρ V) (ρ n) (ρ l) (ρ t) (ρ a) := by
  simp only [forestEntry,entry_rename,four_map]

theorem treeAt_rename {m j} (w V r n : Fin m) (env : Fin 7 → Fin m) (ρ : Fin m → Fin j) :
    (treeAt w V r n env).rename ρ = treeAt (ρ w) (ρ V) (ρ r) (ρ n) (fun i => ρ (env i)) := by
  simp only [treeAt,Formula.rename,treeRow_rename,forestEntry_rename,PacketTokenSyntax.entry_rename]

theorem nilAt_rename {m j} (w r z e : Fin m) (env : Fin 1 → Fin m) (ρ : Fin m → Fin j) :
    (nilAt w r z e env).rename ρ = nilAt (ρ w) (ρ r) (ρ z) (ρ e) (fun i => ρ (env i)) := by
  simp only [nilAt,forestRow_rename]

theorem consAt_rename {m j} (w V r n s : Fin m) (env : Fin 6 → Fin m) (ρ : Fin m → Fin j) :
    (consAt w V r n s env).rename ρ = consAt (ρ w) (ρ V) (ρ r) (ρ n) (ρ s) (fun i => ρ (env i)) := by
  simp only [consAt,Formula.rename,forestRow_rename,forestEntry_rename,treeEntry_rename]

theorem packetAt_rename {m j} (w V r e : Fin m) (env : Fin 3 → Fin m) (ρ : Fin m → Fin j) :
    (packetAt w V r e env).rename ρ = packetAt (ρ w) (ρ V) (ρ r) (ρ e) (fun i => ρ (env i)) := by
  simp only [packetAt,Formula.rename,packetRow_rename,PacketTokenSyntax.tagEntry_rename,treeEntry_rename]

end PPAC.Migration.Internal.PacketStructureSyntax
