UM = 'src/CategoricalCrypto/UC/Machine.agda'
EDITS = [
(UM, """  where
  relay : Dₚ (MC.St f × (Neg A ⊎ Pos B))
        → Dₚ (MC.St f × ((Neg Y ⊎ Neg A) ⊎ (Pos Y ⊎ Pos B)))
  relay = mapₚ λ p → proj₁ p , outT (proj₂ p)

  stepT""", """  where
  stepT"""),
(UM, """  stepT (s , inj₁ (inj₂ a)) = relay (MC.step f (s , inj₁ a))
""", """  stepT (s , inj₁ (inj₂ a)) = mapₚ (map₂ outT) (MC.step f (s , inj₁ a))
"""),
(UM, """  stepT (s , inj₂ (inj₂ b)) = relay (MC.step f (s , inj₂ b))
""", """  stepT (s , inj₂ (inj₂ b)) = mapₚ (map₂ outT) (MC.step f (s , inj₂ b))
"""),
(UM, """  relay : Dₚ (MC.St s × (Neg X ⊎ Pos Y))
        → Dₚ (MC.St s × ((Neg X ⊎ Neg A) ⊎ (Pos Y ⊎ Pos A)))
  relay = mapₚ λ p → proj₁ p , outS (proj₂ p)

""", ""),
(UM, """  stepS (t , inj₁ (inj₁ x)) = relay (MC.step s (t , inj₁ x))
""", """  stepS (t , inj₁ (inj₁ x)) = mapₚ (map₂ outS) (MC.step s (t , inj₁ x))
"""),
(UM, """  stepS (t , inj₂ (inj₁ y)) = relay (MC.step s (t , inj₂ y))
""", """  stepS (t , inj₂ (inj₁ y)) = mapₚ (map₂ outS) (MC.step s (t , inj₂ y))
"""),
]
