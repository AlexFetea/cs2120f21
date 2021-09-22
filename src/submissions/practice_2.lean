/-
Prove the following simple logical conjectures.
Give a formal and an English proof of each one.
Your English language proofs should be complete
in the sense that they identify all the axioms
and/or theorems that you use.
-/

example : true := true.intro

example : false := _    -- trick question? why?

example : ∀ (P : Prop), P ∨ P ↔ P := 
begin
    assume P, 
  apply iff.intro _ _,
  -- forward
    assume prop,
    apply or.elim prop,
    -- left disjunct is true
      assume p,
      exact p,
    -- right disjunct is true
      assume p,
      exact p,
  -- backwards
    assume p,
    exact or.intro_left P p,
end

example : ∀ (P : Prop), P ∧ P ↔ P := 
begin
  assume P,
  apply iff.intro _ _,
   assume prop,
    apply and.elim prop,
    assume p,
    assume p,
    exact p,
    assume prop,
    apply and.intro _ _,
    apply prop,
    apply prop,
 

end

example : ∀ (P Q : Prop), P ∨ Q ↔ Q ∨ P := 
begin
assume P Q,
apply iff.intro _ _,

assume prop,
apply or.elim prop,
assume p,
apply or.intro_right,
exact p,
assume q,
apply or.intro_left,
exact q,

assume prop,
apply or.elim prop,
assume p,
apply or.intro_right,
exact p,
assume q,
apply or.intro_left,
exact q,

end


example : ∀ (P Q : Prop), P ∧ Q ↔ Q ∧ P := 
begin
  assume P Q,
  apply iff.intro _ _,

  assume prop,
  apply and.elim prop,
  assume p,
  assume q,
  apply and.intro _ _,
  exact q,
  exact p,

  assume prop,
  apply and.elim prop,
  assume q,
  assume p,
  apply and.intro _ _,
  exact p,
  exact q,

end

example : ∀ (P Q R : Prop), P ∧ (Q ∨ R) ↔ (P ∧ Q) ∨ (P ∧ R) := 
begin
assume P Q R,
apply iff.intro _ _,

assume prop,
apply and.elim prop,
assume p,
assume prop2,
apply or.elim prop2,
assume q,
apply or.intro_left,
apply and.intro _ _,
exact p,
exact q,
assume r,
apply or.intro_right,
apply and.intro _ _,
exact p,
exact r,

assume prop,
apply or.elim prop,
assume prop2,
apply and.elim prop2,
assume p,
assume q,
apply and.intro _ _,
exact p,
apply or.intro_left,
exact q,

assume prop3,
apply and.elim prop3,
assume p,
assume r,
apply and.intro _ _,
exact p,
apply or.intro_right,
exact r,
end

example : ∀ (P Q R : Prop), P ∨ (Q ∧ R) ↔ (P ∨ Q) ∧ (P ∨ R) := 
begin
  assume P Q R,
  apply iff.intro _ _,

  assume prop,
  apply or.elim prop,
  assume p,
  apply and.intro,
  apply or.intro_left,
  exact p,
  apply or.intro_left,
  exact p,
  assume prop2,
  apply and.elim prop2,
  assume q,
  assume r,
  apply and.intro,
  apply or.intro_right,
  exact q,
  apply or.intro_right,
  exact r,

  assume prop,
  apply and.elim prop,
  assume prop2,
  assume prop3,

  have r: R  := or.elim_right prop2,
  apply or.elim prop2,
  assume p,
  apply or.intro_left,
  exact p,

  assume q,
  apply or.intro_right,
  apply and.intro,
  exact q,
  
  apply or.elim,
  assume p,


end

example : ∀ (P Q : Prop), P ∧ (P ∨ Q) ↔ P := 
begin
  assume P Q,
  apply iff.intro _ _,
  assume prop,
  apply and.elim prop,
  assume p,
  assume prop2,
  exact p,
  assume p,
  apply and.intro _ _,
  exact p,
  apply or.intro_left,
  exact p,
end

example : ∀ (P Q : Prop), P ∨ (P ∧ Q) ↔ P := 
begin
  assume P Q,
  apply iff.intro _ _,
  assume prop,
  apply or.elim prop,
  assume p,
  exact p,
  assume prop2,
  apply and.elim prop2,
  assume p,
  assume q,
  exact p,
  assume p,
  apply or.intro_left,
  exact p,
end

example : ∀ (P : Prop), P ∨ true ↔ true := 
begin
  assume P,
  apply iff.intro,
  assume prop,
  exact true.intro,
  assume t,
  apply or.intro_right,
  exact t,
end

example : ∀ (P : Prop), P ∨ false ↔ P := 
begin
  assume P,
  apply iff.intro,
  assume prop,
  apply or.elim prop,
  assume p,
  exact p,
  apply false.elim,
  assume p,
  apply or.intro_left,
  exact p, 

end

example : ∀ (P : Prop), P ∧ true ↔ P := 
begin
  assume P,
  apply iff.intro,
  assume prop,
  apply and.elim prop,
  assume p,
  assume t,
  exact p,
  
  assume p,
  apply and.intro,
  exact p,
  exact true.intro,
end

example : ∀ (P : Prop), P ∧ false ↔ false := 
begin
  assume P,
  apply iff.intro,
  assume prop,
  apply and.elim prop,
  assume p,
  assume f,
  exact f,
  apply false.elim,
end


