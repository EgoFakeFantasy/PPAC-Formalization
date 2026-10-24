import PPAC.Migration.Internal.PacketVarintPrefixSyntax

/-! Actual independent prefixCode witnesses give the numeric input, remaining tail and output domains. -/
namespace PPAC.Migration.Internal.PacketVarintPrefixDomain
open Source SourceAlgebra SourceLogic PacketVarintPrefixSyntax
open SyntaxRenameQuerySyntax (of_eq)

theorem domain {m} {Γ : Context m} (w n t a : Fin m) (hp : Derives Γ (prefixCode w n t a)) :
    Derives Γ ((Formula.mem n w).conj ((Formula.mem t w).conj (.mem a w))) := by
  let R := body w n t a
  let Δ := Context.add R (Context.image Formula.raise Γ)
  apply Derives.exE (p := R) hp
  have hR : Derives Δ R := .hyp (Or.inl rfl)
  have hn := Derives.conjL (PacketVarintDomain.domain w.castSucc n.castSucc (Fin.last m) (.conjL hR))
  have hb := PacketBytesLaws.domain w.castSucc (Fin.last m) t.castSucc a.castSucc (.conjR hR)
  exact .conjI hn (.conjR hb)

end PPAC.Migration.Internal.PacketVarintPrefixDomain
