import PPAC.Migration.Internal.PacketReaderCodedSyntax

/-! Object equality aligns source state fields and their actual codes. -/
namespace PPAC.Migration.Internal.PacketReaderCodedTransport
open Source SourceAlgebra SourceLogic PacketReaderStateSyntax
open SyntaxRenameQuerySyntax (of_eq)

theorem advance_l {m} {Γ : Context m} (w B z o l v s a x y q c L : Fin m) (he : Derives Γ (.equal l L))
    (hh : Derives Γ (PacketReaderInputSyntax.advance w B z o l v s a x y q c)) : Derives Γ (PacketReaderInputSyntax.advance w B z o L v s a x y q c) := by
  let P := PacketReaderInputSyntax.advance w.castSucc B.castSucc z.castSucc o.castSucc (Fin.last m) v.castSucc s.castSucc a.castSucc x.castSucc y.castSucc q.castSucc c.castSucc
  have h0 : P.instantiate l = PacketReaderInputSyntax.advance w B z o l v s a x y q c := by simp only [P,Formula.instantiate,PacketReaderInputSyntax.advance_rename,Fin.lastCases_last,Fin.lastCases_castSucc,id_eq]
  have h1 : P.instantiate L = PacketReaderInputSyntax.advance w B z o L v s a x y q c := by simp only [P,Formula.instantiate,PacketReaderInputSyntax.advance_rename,Fin.lastCases_last,Fin.lastCases_castSucc,id_eq]
  exact of_eq h1 (Derives.eqSubst P he (of_eq h0.symm hh))

theorem advance_v {m} {Γ : Context m} (w B z o l v s a x y q c V : Fin m) (he : Derives Γ (.equal v V))
    (hh : Derives Γ (PacketReaderInputSyntax.advance w B z o l v s a x y q c)) : Derives Γ (PacketReaderInputSyntax.advance w B z o l V s a x y q c) := by
  let P := PacketReaderInputSyntax.advance w.castSucc B.castSucc z.castSucc o.castSucc l.castSucc (Fin.last m) s.castSucc a.castSucc x.castSucc y.castSucc q.castSucc c.castSucc
  have h0 : P.instantiate v = PacketReaderInputSyntax.advance w B z o l v s a x y q c := by simp only [P,Formula.instantiate,PacketReaderInputSyntax.advance_rename,Fin.lastCases_last,Fin.lastCases_castSucc,id_eq]
  have h1 : P.instantiate V = PacketReaderInputSyntax.advance w B z o l V s a x y q c := by simp only [P,Formula.instantiate,PacketReaderInputSyntax.advance_rename,Fin.lastCases_last,Fin.lastCases_castSucc,id_eq]
  exact of_eq h1 (Derives.eqSubst P he (of_eq h0.symm hh))

theorem advance_s {m} {Γ : Context m} (w B z o l v s a x y q c S : Fin m) (he : Derives Γ (.equal s S))
    (hh : Derives Γ (PacketReaderInputSyntax.advance w B z o l v s a x y q c)) : Derives Γ (PacketReaderInputSyntax.advance w B z o l v S a x y q c) := by
  let P := PacketReaderInputSyntax.advance w.castSucc B.castSucc z.castSucc o.castSucc l.castSucc v.castSucc (Fin.last m) a.castSucc x.castSucc y.castSucc q.castSucc c.castSucc
  have h0 : P.instantiate s = PacketReaderInputSyntax.advance w B z o l v s a x y q c := by simp only [P,Formula.instantiate,PacketReaderInputSyntax.advance_rename,Fin.lastCases_last,Fin.lastCases_castSucc,id_eq]
  have h1 : P.instantiate S = PacketReaderInputSyntax.advance w B z o l v S a x y q c := by simp only [P,Formula.instantiate,PacketReaderInputSyntax.advance_rename,Fin.lastCases_last,Fin.lastCases_castSucc,id_eq]
  exact of_eq h1 (Derives.eqSubst P he (of_eq h0.symm hh))

theorem advance_a {m} {Γ : Context m} (w B z o l v s a x y q c A : Fin m) (he : Derives Γ (.equal a A))
    (hh : Derives Γ (PacketReaderInputSyntax.advance w B z o l v s a x y q c)) : Derives Γ (PacketReaderInputSyntax.advance w B z o l v s A x y q c) := by
  let P := PacketReaderInputSyntax.advance w.castSucc B.castSucc z.castSucc o.castSucc l.castSucc v.castSucc s.castSucc (Fin.last m) x.castSucc y.castSucc q.castSucc c.castSucc
  have h0 : P.instantiate a = PacketReaderInputSyntax.advance w B z o l v s a x y q c := by simp only [P,Formula.instantiate,PacketReaderInputSyntax.advance_rename,Fin.lastCases_last,Fin.lastCases_castSucc,id_eq]
  have h1 : P.instantiate A = PacketReaderInputSyntax.advance w B z o l v s A x y q c := by simp only [P,Formula.instantiate,PacketReaderInputSyntax.advance_rename,Fin.lastCases_last,Fin.lastCases_castSucc,id_eq]
  exact of_eq h1 (Derives.eqSubst P he (of_eq h0.symm hh))

theorem code_l {m} {Γ : Context m} (w l v s a n L : Fin m) (he : Derives Γ (.equal l L))
    (hh : Derives Γ (code w l v s a n)) : Derives Γ (code w L v s a n) := by
  let P := code w.castSucc (Fin.last m) v.castSucc s.castSucc a.castSucc n.castSucc
  have h0 : P.instantiate l = code w l v s a n := by simp only [P,Formula.instantiate,code_rename,Fin.lastCases_last,Fin.lastCases_castSucc,id_eq]
  have h1 : P.instantiate L = code w L v s a n := by simp only [P,Formula.instantiate,code_rename,Fin.lastCases_last,Fin.lastCases_castSucc,id_eq]
  exact of_eq h1 (Derives.eqSubst P he (of_eq h0.symm hh))

theorem code_v {m} {Γ : Context m} (w l v s a n V : Fin m) (he : Derives Γ (.equal v V))
    (hh : Derives Γ (code w l v s a n)) : Derives Γ (code w l V s a n) := by
  let P := code w.castSucc l.castSucc (Fin.last m) s.castSucc a.castSucc n.castSucc
  have h0 : P.instantiate v = code w l v s a n := by simp only [P,Formula.instantiate,code_rename,Fin.lastCases_last,Fin.lastCases_castSucc,id_eq]
  have h1 : P.instantiate V = code w l V s a n := by simp only [P,Formula.instantiate,code_rename,Fin.lastCases_last,Fin.lastCases_castSucc,id_eq]
  exact of_eq h1 (Derives.eqSubst P he (of_eq h0.symm hh))

theorem code_s {m} {Γ : Context m} (w l v s a n S : Fin m) (he : Derives Γ (.equal s S))
    (hh : Derives Γ (code w l v s a n)) : Derives Γ (code w l v S a n) := by
  let P := code w.castSucc l.castSucc v.castSucc (Fin.last m) a.castSucc n.castSucc
  have h0 : P.instantiate s = code w l v s a n := by simp only [P,Formula.instantiate,code_rename,Fin.lastCases_last,Fin.lastCases_castSucc,id_eq]
  have h1 : P.instantiate S = code w l v S a n := by simp only [P,Formula.instantiate,code_rename,Fin.lastCases_last,Fin.lastCases_castSucc,id_eq]
  exact of_eq h1 (Derives.eqSubst P he (of_eq h0.symm hh))

theorem code_a {m} {Γ : Context m} (w l v s a n A : Fin m) (he : Derives Γ (.equal a A))
    (hh : Derives Γ (code w l v s a n)) : Derives Γ (code w l v s A n) := by
  let P := code w.castSucc l.castSucc v.castSucc s.castSucc (Fin.last m) n.castSucc
  have h0 : P.instantiate a = code w l v s a n := by simp only [P,Formula.instantiate,code_rename,Fin.lastCases_last,Fin.lastCases_castSucc,id_eq]
  have h1 : P.instantiate A = code w l v s A n := by simp only [P,Formula.instantiate,code_rename,Fin.lastCases_last,Fin.lastCases_castSucc,id_eq]
  exact of_eq h1 (Derives.eqSubst P he (of_eq h0.symm hh))

theorem align_source {m} {Γ : Context m} (w B z o l v s a x y q c L V S A : Fin m)
    (he : Derives Γ (PacketReaderStep.same l v s a L V S A))
    (ha : Derives Γ (PacketReaderInputSyntax.advance w B z o l v s a x y q c)) :
    Derives Γ (PacketReaderInputSyntax.advance w B z o L V S A x y q c) := by
  have h0 := advance_l _ _ _ _ _ _ _ _ _ _ _ _ _ (.conjL he) ha
  have h1 := advance_v _ _ _ _ _ _ _ _ _ _ _ _ _ (.conjL (.conjR he)) h0
  have h2 := advance_s _ _ _ _ _ _ _ _ _ _ _ _ _ (.conjL (.conjR (.conjR he))) h1
  exact advance_a _ _ _ _ _ _ _ _ _ _ _ _ _ (.conjR (.conjR (.conjR he))) h2

theorem align_code {m} {Γ : Context m} (w l v s a n L V S A : Fin m)
    (he : Derives Γ (PacketReaderStep.same l v s a L V S A)) (hc : Derives Γ (code w l v s a n)) : Derives Γ (code w L V S A n) := by
  have h0 := code_l _ _ _ _ _ _ _ (.conjL he) hc
  have h1 := code_v _ _ _ _ _ _ _ (.conjL (.conjR he)) h0
  have h2 := code_s _ _ _ _ _ _ _ (.conjL (.conjR (.conjR he))) h1
  exact code_a _ _ _ _ _ _ _ (.conjR (.conjR (.conjR he))) h2

end PPAC.Migration.Internal.PacketReaderCodedTransport
