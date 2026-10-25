import PPAC.Migration.Internal.PacketReaderContinuation

/-! Terminal emission is actual Cons of the unbounded arithmetic result onto the reversed accumulator. -/
namespace PPAC.Migration.Internal.PacketReaderEmission
open Source SourceAlgebra SourceLogic OmegaSyntax PacketReaderStepSyntax
open PacketAffineSyntax (equation equation_rename)
open StructuralListSyntax (consCode consCode_rename)
open StructuralListTraceSyntax (valid valid_rename)
open SyntaxRenameQuerySyntax (of_eq)

def existsResult {m} (w b v s a : Fin m) : Formula m := .ex
  ((valid w.castSucc (Fin.last m)).conj (emission w.castSucc b.castSucc v.castSucc s.castSucc a.castSucc (Fin.last m)))
theorem existsResult_rename {m k} (w b v s a : Fin m) (ρ : Fin m → Fin k) :
    (existsResult w b v s a).rename ρ = existsResult (ρ w) (ρ b) (ρ v) (ρ s) (ρ a) := by
  simp only [existsResult,Formula.rename,valid_rename,emission_rename,Formula.liftRen,Fin.lastCases_last,Fin.lastCases_castSucc]

theorem intro_emission {m} {Γ : Context m} (w b v s a c n : Fin m)
    (hn : Derives Γ (equation w b v s n)) (hc : Derives Γ (consCode w n a c)) : Derives Γ (emission w b v s a c) := by
  apply Derives.exI n
  exact of_eq (by simp only [Formula.instantiate,Formula.rename,equation_rename,consCode_rename,Fin.lastCases_last,Fin.lastCases_castSucc,id_eq]) (.conjI hn hc)

theorem domain {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w b v s a c : Fin m)
    (hw : Derives Γ (omega w)) (hv : Derives Γ (.mem v w)) (ha : Derives Γ (valid w a))
    (hc : Derives Γ (emission w b v s a c)) : Derives Γ (valid w c) := by
  let N := (equation w.castSucc b.castSucc v.castSucc s.castSucc (Fin.last m)).conj (consCode w.castSucc (Fin.last m) a.castSucc c.castSucc)
  let Δ := Context.add N (Context.image Formula.raise Γ)
  apply Derives.exE (p := N) hc
  have hN : Derives Δ N := .hyp (Or.inl rfl)
  have hZ1 := ZFContext.under hZ N
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw N)
  have ha1 := of_eq (valid_rename w a Fin.castSucc) (under ha N)
  have hn := PacketReaderArithmetic.equation_range hZ1 _ _ _ _ _ hw1 (under hv N) (.conjL hN)
  simpa only [Formula.raise,valid_rename] using StructuralListValidity.cons_valid hZ1 _ _ _ _ hw1 hn ha1 (.conjR hN)

theorem unique {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w b v s a c d : Fin m)
    (hw : Derives Γ (omega w)) (hb : Derives Γ (.mem b w)) (hv : Derives Γ (.mem v w))
    (hs : Derives Γ (.mem s w)) (ha : Derives Γ (.mem a w))
    (hc : Derives Γ (emission w b v s a c)) (hd : Derives Γ (emission w b v s a d)) : Derives Γ (.equal c d) := by
  let N := (equation w.castSucc b.castSucc v.castSucc s.castSucc (Fin.last m)).conj (consCode w.castSucc (Fin.last m) a.castSucc c.castSucc)
  let Δ := Context.add N (Context.image Formula.raise Γ)
  apply Derives.exE (p := N) hc
  have hN : Derives Δ N := .hyp (Or.inl rfl)
  have hZ1 := ZFContext.under hZ N
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw N)
  have hd1 := of_eq (emission_rename w b v s a d Fin.castSucc) (under hd N)
  let M := (equation w.castSucc.castSucc b.castSucc.castSucc v.castSucc.castSucc s.castSucc.castSucc (Fin.last (m+1))).conj
    (consCode w.castSucc.castSucc (Fin.last (m+1)) a.castSucc.castSucc d.castSucc.castSucc)
  let Ξ := Context.add M (Context.image Formula.raise Δ)
  apply Derives.exE (p := M) hd1
  have hM : Derives Ξ M := .hyp (Or.inl rfl)
  have hZ2 := ZFContext.under hZ1 M
  have hw2 := of_eq (omega_rename w.castSucc Fin.castSucc) (under hw1 M)
  have hb2 : Derives Ξ (.mem b.castSucc.castSucc w.castSucc.castSucc) := under (under hb N) M
  have hv2 : Derives Ξ (.mem v.castSucc.castSucc w.castSucc.castSucc) := under (under hv N) M
  have hs2 : Derives Ξ (.mem s.castSucc.castSucc w.castSucc.castSucc) := under (under hs N) M
  have ha2 : Derives Ξ (.mem a.castSucc.castSucc w.castSucc.castSucc) := under (under ha N) M
  have hn2 := of_eq (equation_rename w.castSucc b.castSucc v.castSucc s.castSucc (Fin.last m) Fin.castSucc) (under (.conjL hN) M)
  have hc2 := of_eq (consCode_rename w.castSucc (Fin.last m) a.castSucc c.castSucc Fin.castSucc) (under (.conjR hN) M)
  have he := PacketAffineCore.equation_unique hZ2 _ _ _ _ _ _ hw2 hb2 hs2 hn2 (.conjL hM)
  have hdc := PacketVarintCanonicalPieces.cons_head _ _ _ _ _ (eq_symm he) (.conjR hM)
  have hnN := PacketReaderArithmetic.equation_range hZ2 _ _ _ _ _ hw2 hv2 hn2
  exact StructuralConsUnique.unique hZ2 _ _ _ _ _ hw2 hnN ha2 hc2 hdc

theorem exists_emission {m} {Γ : Context m} (hZ : ZFContext.Evidence Γ) (w b v s a : Fin m)
    (hw : Derives Γ (omega w)) (hb : Derives Γ (.mem b w)) (hv : Derives Γ (.mem v w))
    (hs : Derives Γ (.mem s w)) (ha : Derives Γ (valid w a)) : Derives Γ (existsResult w b v s a) := by
  let N := (Formula.mem (Fin.last m) w.castSucc).conj (equation w.castSucc b.castSucc v.castSucc s.castSucc (Fin.last m))
  let Δ := Context.add N (Context.image Formula.raise Γ)
  apply Derives.exE (p := N) (PacketReaderArithmetic.exists_equation hZ w b v s hw hb hv hs)
  have hN : Derives Δ N := .hyp (Or.inl rfl)
  have hZ1 := ZFContext.under hZ N
  have hw1 := of_eq (omega_rename w Fin.castSucc) (under hw N)
  have ha1 := of_eq (valid_rename w a Fin.castSucc) (under ha N)
  let C := (Formula.mem (Fin.last (m+1)) w.castSucc.castSucc).conj (consCode w.castSucc.castSucc (Fin.last m).castSucc a.castSucc.castSucc (Fin.last (m+1)))
  let Ξ := Context.add C (Context.image Formula.raise Δ)
  apply Derives.exE (p := C) (StructuralConsCore.exists_cons hZ1 _ _ _ hw1 (.conjL hN) (StructuralListValidity.range _ _ ha1))
  have hC : Derives Ξ C := .hyp (Or.inl rfl)
  have hZ2 := ZFContext.under hZ1 C
  have hw2 := of_eq (omega_rename w.castSucc Fin.castSucc) (under hw1 C)
  have ha2 := of_eq (valid_rename w.castSucc a.castSucc Fin.castSucc) (under ha1 C)
  have hnN : Derives Ξ (.mem (Fin.last m).castSucc w.castSucc.castSucc) := under (.conjL hN) C
  have hn2 := of_eq (equation_rename w.castSucc b.castSucc v.castSucc s.castSucc (Fin.last m) Fin.castSucc) (under (.conjR hN) C)
  have hvld := StructuralListValidity.cons_valid hZ2 _ _ _ _ hw2 hnN ha2 (.conjR hC)
  have hem := intro_emission _ _ _ _ _ _ _ hn2 (.conjR hC)
  have hout : Derives Ξ (existsResult w.castSucc.castSucc b.castSucc.castSucc v.castSucc.castSucc s.castSucc.castSucc a.castSucc.castSucc) := by
    apply Derives.exI (Fin.last (m+1))
    exact of_eq (by simp only [Formula.instantiate,Formula.rename,valid_rename,emission_rename,Fin.lastCases_last,Fin.lastCases_castSucc,id_eq]) (.conjI hvld hem)
  simpa only [Formula.raise,existsResult_rename] using hout

end PPAC.Migration.Internal.PacketReaderEmission
