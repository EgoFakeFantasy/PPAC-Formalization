import PPAC.Migration.Internal.ObjectPacketReaderReturn

/-! Actual readTokens initial state has fields input, zero, one, original Nil (whose actual code is one). Constants remain object witnesses. -/
namespace PPAC.Migration.Internal.PacketReaderInitSyntax
open Source SourceAlgebra SourceLogic OmegaSyntax HornBinderSyntax
open SyntaxRenameQuerySyntax (of_eq)

def seed {m} (w z o L n : Fin m) : Formula m := PacketReaderStateSyntax.code w L z o o n

def existsSeed {m} (w z o L : Fin m) : Formula m := .ex
  ((Formula.mem (Fin.last m) w.castSucc).conj (seed w.castSucc z.castSucc o.castSucc L.castSucc (Fin.last m)))

def seeded {m} (w B z o L q : Fin m) : Formula m := .ex
  ((seed w.castSucc z.castSucc o.castSucc L.castSucc (Fin.last m)).conj
    (PacketReaderReturnCodedSyntax.run w.castSucc B.castSucc z.castSucc o.castSucc (Fin.last m) q.castSucc))

def existsSeeded {m} (w B z o L : Fin m) : Formula m := .ex
  ((Formula.mem (Fin.last m) w.castSucc).conj (seeded w.castSucc B.castSucc z.castSucc o.castSucc L.castSucc (Fin.last m)))

def seededFiber {m} (w B z o L : Fin m) : Formula m := .ex
  (((Formula.mem (Fin.last m) w.castSucc).conj (seeded w.castSucc B.castSucc z.castSucc o.castSucc L.castSucc (Fin.last m))).conj (.all
    ((seeded w.castSucc.castSucc B.castSucc.castSucc z.castSucc.castSucc o.castSucc.castSucc L.castSucc.castSucc (Fin.last (m+1))).imp (.equal (Fin.last (m+1)) (Fin.last m).castSucc))))

def parseBody {m} (w L q : Fin m) : Formula (m+3) :=
  (SyntaxNumeralSyntax.numeral 128 (slot 3 0)).conj ((empty (slot 3 1)).conj
    ((successor (slot 3 2) (slot 3 1)).conj (seeded (old 3 w) (slot 3 0) (slot 3 1) (slot 3 2) (old 3 L) (old 3 q))))

def parse {m} (w L q : Fin m) : Formula m := existsMany 3 (parseBody w L q)

def existsParse {m} (w L : Fin m) : Formula m := .ex
  ((Formula.mem (Fin.last m) w.castSucc).conj (parse w.castSucc L.castSucc (Fin.last m)))

def parseFiber {m} (w L : Fin m) : Formula m := .ex
  (((Formula.mem (Fin.last m) w.castSucc).conj (parse w.castSucc L.castSucc (Fin.last m))).conj (.all
    ((parse w.castSucc.castSucc L.castSucc.castSucc (Fin.last (m+1))).imp (.equal (Fin.last (m+1)) (Fin.last m).castSucc))))

theorem seed_rename {m k} (w z o L n : Fin m) (ρ : Fin m → Fin k) :
    (seed w z o L n).rename ρ = seed (ρ w) (ρ z) (ρ o) (ρ L) (ρ n) := PacketReaderStateSyntax.code_rename _ _ _ _ _ _ _

theorem existsSeed_rename {m k} (w z o L : Fin m) (ρ : Fin m → Fin k) :
    (existsSeed w z o L).rename ρ = existsSeed (ρ w) (ρ z) (ρ o) (ρ L) := by
  simp only [existsSeed,Formula.rename,seed_rename,Formula.liftRen,Fin.lastCases_last,Fin.lastCases_castSucc]

theorem seeded_rename {m k} (w B z o L q : Fin m) (ρ : Fin m → Fin k) :
    (seeded w B z o L q).rename ρ = seeded (ρ w) (ρ B) (ρ z) (ρ o) (ρ L) (ρ q) := by
  simp only [seeded,Formula.rename,seed_rename,PacketReaderReturnCodedSyntax.run_rename,Formula.liftRen,Fin.lastCases_last,Fin.lastCases_castSucc]

theorem existsSeeded_rename {m k} (w B z o L : Fin m) (ρ : Fin m → Fin k) :
    (existsSeeded w B z o L).rename ρ = existsSeeded (ρ w) (ρ B) (ρ z) (ρ o) (ρ L) := by
  simp only [existsSeeded,Formula.rename,seeded_rename,Formula.liftRen,Fin.lastCases_last,Fin.lastCases_castSucc]

theorem seededFiber_rename {m k} (w B z o L : Fin m) (ρ : Fin m → Fin k) :
    (seededFiber w B z o L).rename ρ = seededFiber (ρ w) (ρ B) (ρ z) (ρ o) (ρ L) := by
  simp only [seededFiber,Formula.rename,seeded_rename,Formula.liftRen,Fin.lastCases_last,Fin.lastCases_castSucc]

theorem parseBody_lift {m k} (w L q : Fin m) (ρ : Fin m → Fin k) :
    (parseBody w L q).rename (lift 3 ρ) = parseBody (ρ w) (ρ L) (ρ q) := by
  simp only [parseBody,Formula.rename,SyntaxNumeralSyntax.numeral_rename,empty_rename,successor_rename,seeded_rename,lift_old,lift_slot]

theorem parse_rename {m k} (w L q : Fin m) (ρ : Fin m → Fin k) :
    (parse w L q).rename ρ = parse (ρ w) (ρ L) (ρ q) := by
  simp only [parse,existsMany_rename,parseBody_lift]

theorem existsParse_rename {m k} (w L : Fin m) (ρ : Fin m → Fin k) :
    (existsParse w L).rename ρ = existsParse (ρ w) (ρ L) := by
  simp only [existsParse,Formula.rename,parse_rename,Formula.liftRen,Fin.lastCases_last,Fin.lastCases_castSucc]

theorem parseFiber_rename {m k} (w L : Fin m) (ρ : Fin m → Fin k) :
    (parseFiber w L).rename ρ = parseFiber (ρ w) (ρ L) := by
  simp only [parseFiber,Formula.rename,parse_rename,Formula.liftRen,Fin.lastCases_last,Fin.lastCases_castSucc]

theorem intro_seeded {m} {Γ : Context m} (w B z o L q n : Fin m)
    (hs : Derives Γ (seed w z o L n)) (hr : Derives Γ (PacketReaderReturnCodedSyntax.run w B z o n q)) : Derives Γ (seeded w B z o L q) := by
  apply Derives.exI n
  exact of_eq (by simp only [Formula.instantiate,Formula.rename,seed_rename,PacketReaderReturnCodedSyntax.run_rename,Fin.lastCases_last,Fin.lastCases_castSucc,id_eq]) (.conjI hs hr)

theorem intro_parse {m} {Γ : Context m} (w L q B z o : Fin m)
    (hB : Derives Γ (SyntaxNumeralSyntax.numeral 128 B)) (hz : Derives Γ (empty z)) (ho : Derives Γ (successor o z))
    (hr : Derives Γ (seeded w B z o L q)) : Derives Γ (parse w L q) := by
  apply HornBinderRules.intro_many 3 _ (SyntaxAtomSyntax.three B z o)
  exact of_eq (by simp only [parseBody,Formula.rename,SyntaxNumeralSyntax.numeral_rename,empty_rename,successor_rename,seeded_rename,assign_old,assign_slot]; rfl) (.conjI hB (.conjI hz (.conjI ho hr)))

end PPAC.Migration.Internal.PacketReaderInitSyntax
