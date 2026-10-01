EDITS = [
  ('src/CategoricalCrypto/Examples/CoinToss/Ideal/Receiver/Hybrid.agda',
   '  hearᴴʰ sg t m q eq =\n        Hᵁ.step-R sg (t , m) (inj₁ q)\n    ⟨≈⟩ >>=ₚ-identityˡ (sg , inj₁ (inj₁ q)) (Hᶜ.resumeG (t , m))\n    ⟨≈⟩ Hᵁ.solve-B⁻ sg (t , m) (inj₁ q)\n    ⟨≈⟩ bindˣ (bindˣ eq)\n    ⟨≈⟩ >>=ₚ-assoc _ _ _\n    ⟨≈⟩ bindᶠ (λ _ → >>=ₚ-identityˡ _ _)\n',
   '  hearᴴʰ sg t m q eq =\n        Hᵁ.step-R sg (t , m) (inj₁ q)\n    ⟨≈⟩ >>=ₚ-identityˡ (sg , inj₁ (inj₁ q)) (Hᶜ.resumeG (t , m))\n    ⟨≈⟩ cellᴴʰ sg t m (inj₁ q) eq\n'),
  ('src/CategoricalCrypto/Examples/CoinToss/Ideal/Receiver/Hybrid.agda',
   '  cellᴴʰ : (sg : QSt) (t : Tbl) (m : Maybe Bool) (e : HonQʰ)\n           {D : Dₚ (RState × (Neg unitᴵ ⊎ Pos Resᴵ))}\n         → step resource ((t , m) , inj₂ (downᶠʰ (inj₂ e))) ≈ₚ D\n         → Hᶜ.resumeG (t , m) (sg , inj₁ (inj₂ e))\n         ≈ₚ (D >>=ₚ λ w → Hᶜ.resumeF sg (proj₁ w , Sum.map₂ upᶠʰ (proj₂ w)))\n  cellᴴʰ sg t m e eq =\n        Hᵁ.solve-B⁻ sg (t , m) (inj₂ e)\n    ⟨≈⟩ bindˣ (bindˣ eq)\n    ⟨≈⟩ >>=ₚ-assoc _ _ _\n    ⟨≈⟩ bindᶠ (λ _ → >>=ₚ-identityˡ _ _)\n',
   '  cellᴴʰ : (sg : QSt) (t : Tbl) (m : Maybe Bool) (b : Neg (Lkᴵʰ ⊗ᴵ Honᴵʰ))\n           {D : Dₚ (RState × (Neg unitᴵ ⊎ Pos Resᴵ))}\n         → step resource ((t , m) , inj₂ (downᶠʰ b)) ≈ₚ D\n         → Hᶜ.resumeG (t , m) (sg , inj₁ b)\n         ≈ₚ (D >>=ₚ λ w → Hᶜ.resumeF sg (proj₁ w , Sum.map₂ upᶠʰ (proj₂ w)))\n  cellᴴʰ sg t m b eq =\n        Hᵁ.solve-B⁻ sg (t , m) b\n    ⟨≈⟩ bindˣ (bindˣ eq)\n    ⟨≈⟩ >>=ₚ-assoc _ _ _\n    ⟨≈⟩ bindᶠ (λ _ → >>=ₚ-identityˡ _ _)\n'),
  ('src/CategoricalCrypto/Examples/CoinToss/Ideal/Receiver/Hybrid.agda',
   'cellᴴʰ (openᵗ b₁ b₂) t (just b₁) openᴱ (cell-get t b₁)',
   'cellᴴʰ (openᵗ b₁ b₂) t (just b₁) (inj₂ openᴱ) (cell-get t b₁)'),
  ('src/CategoricalCrypto/Examples/CoinToss/Ideal/Receiver/Hybrid.agda',
   'cellᴴʰ (comᵗ b₁) t nothing (commitᴱ b₁) (cell-put t b₁)',
   'cellᴴʰ (comᵗ b₁) t nothing (inj₂ (commitᴱ b₁)) (cell-put t b₁)'),
]
