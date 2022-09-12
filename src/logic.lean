
section propositional

variables P Q R : Prop


------------------------------------------------
-- Proposições de dupla negaço:
------------------------------------------------

theorem doubleneg_intro :
  P → ¬¬P  :=
begin
  intro p,
  intro no_p,
  contradiction,
end

theorem doubleneg_elim :
  ¬¬P → P  :=
begin
  intro p,
  by_cases new_p : P,
  exact new_p,
  contradiction,
end

theorem doubleneg_law :
  ¬¬P ↔ P  :=
begin
  split,
  intro p,
  by_cases new_p : P,
  exact new_p,
  contradiction,
  intro p,
  intro no_p,
  contradiction,
end

------------------------------------------------
-- Comutatividade dos ∨,∧:
------------------------------------------------

theorem disj_comm :
  (P ∨ Q) → (Q ∨ P)  :=
begin
  intro p_or_q,
  cases p_or_q with p q,
  right,
  exact p,
  left,
  exact q,
end

theorem conj_comm :
  (P ∧ Q) → (Q ∧ P)  :=
begin
  intro p_and_q,
  split,
  cases p_and_q,
  exact p_and_q_right,
  cases p_and_q,
  exact p_and_q_left,
end


------------------------------------------------
-- Proposições de interdefinabilidade dos →,∨:
------------------------------------------------

theorem impl_as_disj_converse :
  (¬P ∨ Q) → (P → Q)  :=
begin
  intro p,
  intro h,
  cases p with no_p q,
  contradiction,
  exact q,
end

theorem disj_as_impl :
  (P ∨ Q) → (¬P → Q)  :=
begin
  intro p_or_q,
  intro no_p,
  cases p_or_q with p q,
  contradiction,
  exact q,
end


------------------------------------------------
-- Proposições de contraposição:
------------------------------------------------

theorem impl_as_contrapositive :
  (P → Q) → (¬Q → ¬P)  :=
begin
  intro p_q,
  intro no_q,
  intro p_boom,
  have q : Q := p_q p_boom,
  contradiction,
end

theorem impl_as_contrapositive_converse :
  (¬Q → ¬P) → (P → Q)  :=
begin
  intro nq_np,
  intro p,
  by_contradiction qboom,
  have np : ¬P := nq_np qboom,
  contradiction,
end

theorem contrapositive_law :
  (P → Q) ↔ (¬Q → ¬P)  :=
begin
  split,
  intro p_q,
  intro no_q,
  intro p_boom,
  have q: Q := p_q p_boom,
  contradiction,
  intro nq_np,
  intro p,
  by_contradiction qboom,
  have np: ¬P := nq_np qboom,
  contradiction,
end


------------------------------------------------
-- A irrefutabilidade do LEM:
------------------------------------------------

theorem lem_irrefutable :
  ¬¬(P∨¬P)  :=
begin
  intro p_np,
  have h : (P∨¬P),
  right,
  intro p,
  have p_or_np : (P∨¬P),
  left, 
  exact p,
  contradiction,
  contradiction,
  
end


------------------------------------------------
-- A lei de Peirce
------------------------------------------------

theorem peirce_law_weak :
  ((P → Q) → P) → ¬¬P  :=
begin
  intro p_q_p,
  intro np,
  have p_q : (P → Q),
  intro p,
  contradiction,
  have p : P := p_q_p p_q,
  contradiction,

end


------------------------------------------------
-- Proposições de interdefinabilidade dos ∨,∧:
------------------------------------------------

theorem disj_as_negconj :
  P∨Q → ¬(¬P∧¬Q)  :=
begin
  intro p_or_q,
  intro np_nq,
  cases np_nq,
  cases p_or_q,
  contradiction,
  contradiction,
end

theorem conj_as_negdisj :
  P∧Q → ¬(¬P∨¬Q)  :=
begin
  intro p_q,
  intro np_or_nq,
  cases np_or_nq,
  cases p_q,
  contradiction,
  cases p_q,
  contradiction,
end


------------------------------------------------
-- As leis de De Morgan para ∨,∧:
------------------------------------------------

theorem demorgan_disj :
  ¬(P∨Q) → (¬P ∧ ¬Q)  :=
begin
  intro n_p_or_q,
  split,
  intro p,
  have p_or_q :(P∨Q),
  left,
  exact p,
  contradiction,
  intro q,
  have p_or_q :(P∨Q),
  right,
  exact q,
  contradiction,
end

theorem demorgan_disj_converse :
  (¬P ∧ ¬Q) → ¬(P∨Q)  :=
begin
  intro np_nq,
  intro p_or_q,
  cases np_nq,
  cases p_or_q,
  contradiction,
  contradiction,
end

theorem demorgan_conj :
  ¬(P∧Q) → (¬Q ∨ ¬P)  :=
begin
  intro n_p_q,
  by_cases p: P,
  left,
  intro q,
  have p_q: (P∧Q),
  split,
  exact p,
  exact q,
  contradiction,
  right,
  exact p,
end

theorem demorgan_conj_converse :
  (¬Q ∨ ¬P) → ¬(P∧Q)  :=
begin
  intro n_q_or_n_p,
  intro p_q,
  cases p_q,
  cases n_q_or_n_p,
  contradiction,
  contradiction,
end

theorem demorgan_conj_law :
  ¬(P∧Q) ↔ (¬Q ∨ ¬P)  :=
begin
  split,
  intro n_p_q,
  by_cases p: P,
  left,
  intro q,
  have p_q: (P∧Q),
  split,
  exact p,
  exact q,
  contradiction,
  right,
  exact p,
  intro n_q_or_n_p,
  intro p_q,
  cases p_q,
  cases n_q_or_n_p,
  contradiction,
  contradiction,

end

theorem demorgan_disj_law :
  ¬(P∨Q) ↔ (¬P ∧ ¬Q)  :=
begin
  split,
  intro n_p_or_q,
  split,
  intro p,
  have p_or_q :(P∨Q),
  left,
  exact p,
  contradiction,
  intro q,
  have p_or_q :(P∨Q),
  right,
  exact q,
  contradiction,
  intro np_nq,
  intro p_or_q,
  cases np_nq,
  cases p_or_q,
  contradiction,
  contradiction,

end

------------------------------------------------
-- Proposições de distributividade dos ∨,∧:
------------------------------------------------

theorem distr_conj_disj :
  P∧(Q∨R) → (P∧Q)∨(P∧R)  :=
begin
  intro p_q_or_r,
  cases p_q_or_r,
  cases p_q_or_r_right,
  left,
  split,
  exact p_q_or_r_left,
  exact p_q_or_r_right,
  right,
  split,
  exact p_q_or_r_left,
  exact p_q_or_r_right,

end

theorem distr_conj_disj_converse :
  (P∧Q)∨(P∧R) → P∧(Q∨R)  :=
begin
  intro pq_or_pr,
  cases pq_or_pr,
  cases pq_or_pr,
  split,
  exact pq_or_pr_left,
  left,
  exact pq_or_pr_right,
  cases pq_or_pr,
  split,
  exact pq_or_pr_left,
  right,
  exact pq_or_pr_right,
end

theorem distr_disj_conj :
  P∨(Q∧R) → (P∨Q)∧(P∨R)  :=
begin
  intro p_or_qr,
  cases p_or_qr,
  split,
  left,
  exact p_or_qr,
  left,
  exact p_or_qr,
  cases p_or_qr,
  split,
  right,
  exact p_or_qr_left,
  right,
  exact p_or_qr_right,
end

theorem distr_disj_conj_converse :
  (P∨Q)∧(P∨R) → P∨(Q∧R)  :=
begin
  intro p_or_q_p_or_r,
  cases p_or_q_p_or_r,
  cases p_or_q_p_or_r_left,
  left, 
  exact p_or_q_p_or_r_left,
  cases p_or_q_p_or_r_right,
  left,
  exact p_or_q_p_or_r_right,
  right,
  split,
  exact p_or_q_p_or_r_left,
  exact p_or_q_p_or_r_right,
end


------------------------------------------------
-- Currificação
------------------------------------------------

theorem curry_prop :
  ((P∧Q)→R) → (P→(Q→R))  :=
begin
  intro pqr,
  intro p,
  intro q,
  have pq : (P∧Q),
  split,
  exact p,
  exact q,
  have r := pqr pq,
  exact r,
end

theorem uncurry_prop :
  (P→(Q→R)) → ((P∧Q)→R)  :=
begin
  intro p_q_r,
  intro pq,
  cases pq,
  have q_r := p_q_r pq_left,
  have r := q_r pq_right,
  exact r;
end


------------------------------------------------
-- Reflexividade da →:
------------------------------------------------

theorem impl_refl :
  P → P  :=
begin
  intro p,
  exact p,
end

------------------------------------------------
-- Weakening and contraction:
------------------------------------------------

theorem weaken_disj_right :
  P → (P∨Q)  :=
begin
  intro p,
  left,
  exact p,
end

theorem weaken_disj_left :
  Q → (P∨Q)  :=
begin
  intro q,
  right,
  exact q,
end

theorem weaken_conj_right :
  (P∧Q) → P  :=
begin
  intro pq,
  cases pq,
  exact pq_left,
end

theorem weaken_conj_left :
  (P∧Q) → Q  :=
begin
  intro pq,
  cases pq,
  exact pq_right,
end

theorem conj_idempot :
  (P∧P) ↔ P :=
begin
  split,
  intro pp,
  cases pp,
  exact pp_left,
  intro p,
  split,
  exact p,
  exact p,
end

theorem disj_idempot :
  (P∨P) ↔ P  :=
begin
  split,
  intro p_or_p,
  cases p_or_p,
  exact p_or_p,
  exact p_or_p,
  intro p,
  left,
  exact p,
end

end propositional


----------------------------------------------------------------


section predicate

variable U : Type
variables P Q : U -> Prop


------------------------------------------------
-- As leis de De Morgan para ∃,∀:
------------------------------------------------

theorem demorgan_exists :
  ¬(∃x, P x) → (∀x, ¬P x)  :=
begin
  sorry,
end

theorem demorgan_exists_converse :
  (∀x, ¬P x) → ¬(∃x, P x)  :=
begin
  sorry,
end

theorem demorgan_forall :
  ¬(∀x, P x) → (∃x, ¬P x)  :=
begin
  sorry,
end

theorem demorgan_forall_converse :
  (∃x, ¬P x) → ¬(∀x, P x)  :=
begin
  sorry,
end

theorem demorgan_forall_law :
  ¬(∀x, P x) ↔ (∃x, ¬P x)  :=
begin
  sorry,
end

theorem demorgan_exists_law :
  ¬(∃x, P x) ↔ (∀x, ¬P x)  :=
begin
  sorry,
end


------------------------------------------------
-- Proposições de interdefinabilidade dos ∃,∀:
------------------------------------------------

theorem exists_as_neg_forall :
  (∃x, P x) → ¬(∀x, ¬P x)  :=
begin
  sorry,
end

theorem forall_as_neg_exists :
  (∀x, P x) → ¬(∃x, ¬P x)  :=
begin
  sorry,
end

theorem forall_as_neg_exists_converse :
  ¬(∃x, ¬P x) → (∀x, P x)  :=
begin
  sorry,
end

theorem exists_as_neg_forall_converse :
  ¬(∀x, ¬P x) → (∃x, P x)  :=
begin
  sorry,
end

theorem forall_as_neg_exists_law :
  (∀x, P x) ↔ ¬(∃x, ¬P x)  :=
begin
  sorry,
end

theorem exists_as_neg_forall_law :
  (∃x, P x) ↔ ¬(∀x, ¬P x)  :=
begin
  sorry,
end


------------------------------------------------
--  Proposições de distributividade de quantificadores:
------------------------------------------------

theorem exists_conj_as_conj_exists :
  (∃x, P x ∧ Q x) → (∃x, P x) ∧ (∃x, Q x)  :=
begin
  sorry,
end

theorem exists_disj_as_disj_exists :
  (∃x, P x ∨ Q x) → (∃x, P x) ∨ (∃x, Q x)  :=
begin
  sorry,
end

theorem exists_disj_as_disj_exists_converse :
  (∃x, P x) ∨ (∃x, Q x) → (∃x, P x ∨ Q x)  :=
begin
  sorry,
end

theorem forall_conj_as_conj_forall :
  (∀x, P x ∧ Q x) → (∀x, P x) ∧ (∀x, Q x)  :=
begin
  sorry,
end

theorem forall_conj_as_conj_forall_converse :
  (∀x, P x) ∧ (∀x, Q x) → (∀x, P x ∧ Q x)  :=
begin
  sorry,
end


theorem forall_disj_as_disj_forall_converse :
  (∀x, P x) ∨ (∀x, Q x) → (∀x, P x ∨ Q x)  :=
begin
  sorry,
end


/- NOT THEOREMS --------------------------------

theorem forall_disj_as_disj_forall :
  (∀x, P x ∨ Q x) → (∀x, P x) ∨ (∀x, Q x)  :=
begin
end

theorem exists_conj_as_conj_exists_converse :
  (∃x, P x) ∧ (∃x, Q x) → (∃x, P x ∧ Q x)  :=
begin
end

---------------------------------------------- -/

end predicate
