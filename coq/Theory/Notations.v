(*------------------------------------------------------------------------------
  -- ＮＯＴＡＴＩＯＮＳ
  ----------------------------------------------------------------------------*)


(* -- Ｃｏｒｅ  ｎｏｔａｔｉｏｎｓ                                         -- *)
Notation "⊤" := True.
Notation "⊥" := False.
Notation "_⟨⊎⟩_" := sum (only parsing).
Infix "⟨⊎⟩" := sum (at level 25, left associativity).
Infix "⟨×⟩" := prod (at level 20, left associativity).
Notation "_⟨×⟩_" := prod (only parsing).
(*----------------------------------------------------------------------------*)


(* -- Ｃａｔｅｇｏｒｙ ｎｏｔａｔｉｏｎｓ                                 - --*)
Reserved Notation "A ⇒ B" (at level 30, right associativity).
Reserved Notation "f ∘ g" (at level 40, left associativity).
Reserved Notation "⟨ f , g ⟩" (at level 0, no associativity).
(*----------------------------------------------------------------------------*)
