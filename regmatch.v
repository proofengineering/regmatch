Require Import List.
Require Import Arith.
Require Import Wellfounded.
Require Import Relation_Definitions.
Require Import Relation_Operators.
Require Import Lia.

From mathcomp Require Import ssreflect.
From RegMatch Require Import regexp.

Import ListNotations.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section PListDec.

Variables A B : Type.

Variable ABlt : A * B -> A * B -> Prop.

Variable P : A * B -> Prop.

Variable ab : A * B.

Variable P_dec : forall ab', ABlt ab' ab -> { P ab' }+{ ~ P ab' }.

Variable f : A -> A * B.
Hypothesis f_ABlt : forall a' : A, ABlt (f a') ab.

Definition list_t (l : list A) := { a0 | In a0 l /\ P (f a0) }+{ (forall a', In a' l -> ~ P (f a')) }.

Fixpoint P_list_dec (l : list A) : list_t l.
refine
  (match l as l0 return _ = l0 -> _ with
   | [] => fun H_eq_l => inright _
   | a :: l' =>
     fun H_eq_l => 
       match @P_dec (f a) _ with
       | left H_dec => inleft (exist _ a _)
       | right H_dec =>
         match P_list_dec l' with
         | inleft (exist a' H_l') => inleft (exist _ a' _)
         | inright H_l' => inright _
         end
       end
   end (refl_equal _)).
- move => a' H_in H_p; subst.
  by inversion H_in.
- subst.
  exact: f_ABlt.
- subst.
  by split; first by left.
- subst.
  simpl in *.
  move: H_l' => [H_l' H_p].
  by split; first by right.
- move => a' H_in H_p.
  subst.
  case: H_in => H_in; first by subst.
  by apply H_l' in H_in.
Defined.

End PListDec.

Section lexprod'.

Variable A : Type.

Variable ltA : A -> A -> Prop.

Inductive lexprod' : A * A -> A * A -> Prop :=
| left_lex' : forall (x1 x2 y1 y2 : A), ltA x1 x2 -> lexprod' (x1, y1) (x2, y2)
| right_lex' : forall (x y1 y2 : A), ltA y1 y2 -> lexprod' (x, y1) (x, y2).

Lemma lexprod'_Acc : well_founded ltA -> forall x, Acc ltA x -> forall y, Acc ltA y -> Acc lexprod' (x, y).
Proof.
intros H x Hx.
induction Hx as [x _ IHacc].
intros y Hy.
induction Hy as [y _ IHacc0].
apply Acc_intro.
intros (x1, y1) HA.
inversion HA; subst.
- apply IHacc; auto.
- apply IHacc0; auto.
Defined.

Theorem wf_lexprod' : well_founded ltA -> well_founded lexprod'.
Proof.
intros H_wf (x, y).
by auto using lexprod'_Acc.
Defined.

End lexprod'.

Section lexprod''.

Variable A : Type.

Variable ltA : A -> A -> Prop.

Inductive lexprod'' : A * A * A -> A * A * A -> Prop :=
| left_lex'' : forall (x1 x2 y1 y2 z1 z2 : A), ltA x1 x2 -> lexprod'' (x1, y1, z1) (x2, y2, z2)
| mid_lex'' : forall (x y1 y2 z1 z2 : A), ltA y1 y2 -> lexprod'' (x, y1, z1) (x, y2, z2)
| right_lex'' : forall (x y z1 z2 : A), ltA z1 z2 -> lexprod'' (x, y, z1) (x, y, z2).

Lemma lexprod''_Acc : well_founded ltA -> forall x, Acc ltA x -> forall y, Acc ltA y -> forall z, Acc ltA z -> Acc lexprod'' (x, y, z).
Proof.
intros H x Hx.
induction Hx as [x _ IHacc].
intros y Hy.
induction Hy as [y _ IHacc0].
intros z Hz.
induction Hz as [z _ IHacc1].
apply Acc_intro.
intros ((x1, y1), z1) HA.
inversion HA; subst; auto.
Defined.

Theorem wf_lexprod'' : well_founded ltA -> well_founded lexprod''.
Proof.
intros H_wf ((x, y), z).
by auto using lexprod''_Acc.
Defined.

End lexprod''.

Section Accept.

Variable char : Type.

Variable char_eq_dec : forall c0 c1 : char, {c0 = c1}+{c0 <> c1}.

Fixpoint regexp_size (r : r char) : nat :=
match r with
| r_zero => 1
| r_unit => 1
| r_char _ => 1
| r_plus r1 r2 => regexp_size r1 + regexp_size r2 + 1
| r_times r1 r2 => regexp_size r1 + regexp_size r2 + 1
| r_star r => regexp_size r + 1
end.

Definition regexp_size_lt (r r' : r char) := regexp_size r < regexp_size r'.

Lemma regexp_size_wf : well_founded regexp_size_lt.
Proof.
exact: (well_founded_lt_compat _ (fun r => regexp_size r)).
Defined.

Fixpoint regexp_subsize (r : r char) : nat :=
match r with
| r_times r1 r2 => regexp_size r1
| _ => 0
end.

Definition regexp_subsize_lt (r r' : r char) := regexp_subsize r < regexp_subsize r'.

Lemma regexp_subsize_wf : well_founded regexp_subsize_lt.
Proof.
exact: (well_founded_lt_compat _ (fun r => regexp_subsize r)).
Defined.

Definition regexp_lt_size_subsize_lexprod' (r r' : r char) :=
lexprod' lt (regexp_size r, regexp_subsize r) (regexp_size r', regexp_subsize r').

Lemma regexp_lt_size_subsize_lexprod'_wf : well_founded regexp_lt_size_subsize_lexprod'.
Proof.
intro.
apply (wf_inverse_image _ _ _ (fun r => (regexp_size r, regexp_subsize r))).
by apply wf_lexprod'; apply lt_wf.
Defined.

Inductive regexp_lt : r char -> r char -> Prop :=
| regexp_lt_lt : forall r r' : r char, 
    regexp_size r < regexp_size r' -> 
    regexp_lt r r'
| regexp_lt_times_lt : forall r11 r12 r21 r22 : r char,
    regexp_size (r_times r11 r12) = regexp_size (r_times r21 r22) ->
    regexp_size r11 < regexp_size r21 ->
    regexp_lt (r_times r11 r12) (r_times r21 r22).

Lemma regexp_lt_size_subsize_symprod_incl_impl : 
  forall r r' : r char, 
    regexp_lt r r' -> regexp_lt_size_subsize_lexprod' r r'.
Proof.
move => r r'.
elim => {r r'}.
- move => r r' H_lt.
  rewrite /regexp_lt_size_subsize_lexprod'.
  exact: left_lex'.
- move => r11 r12 r21 r22 H_eq H_lt.
  rewrite /regexp_lt_size_subsize_lexprod' H_eq /=.
  exact: right_lex'.
Defined.

Lemma regexp_lt_size_subsize_symprod_incl : inclusion _ regexp_lt regexp_lt_size_subsize_lexprod'.
Proof.
move => x y.
exact: regexp_lt_size_subsize_symprod_incl_impl.
Defined.

Lemma regexp_lt_well_founded : well_founded regexp_lt.
Proof.
apply (wf_incl _ _ _ regexp_lt_size_subsize_symprod_incl).
exact: regexp_lt_size_subsize_lexprod'_wf.
Defined.

Definition regexps_no_c_lt (rc rc' : r char * char) := regexp_lt (fst rc) (fst rc').

Lemma regexps_no_c_lt_well_founded : well_founded regexps_no_c_lt.
Proof.
apply (wf_inverse_image _ _ _ (fun rs => fst rs)).
apply regexp_lt_well_founded.
Defined.

Definition regexps_no_c_t (rc : r char * char) : Type :=
{ l : list (r char) | (forall r : r char, In r l -> (forall s, s_in_regexp_lang char s r -> s_in_regexp_c_lang char s (fst rc) (snd rc))) /\ (forall s, s_in_regexp_c_lang char s (fst rc) (snd rc) -> exists r, In r l /\ s_in_regexp_lang char s r) }.

Lemma star_times : 
  forall (s' : list char) c r',
  s_in_regexp_lang _ (c :: s') (r_star r') ->
  s_in_regexp_lang _ (c :: s') (r_times r' (r_star r')).
Proof.
case => //=.
- move => c r' H_s.
  inversion H_s; subst.
  destruct s5.
    simpl in *.
    have ->: s' = [] ++ s' by [].
    by apply s_in_regexp_lang_times.
  injection H => H_eq H_eq_c; subst.
  destruct s5 => //=.
  have ->: c :: s' = [c] ++ s' by [].
  by apply s_in_regexp_lang_times.
- move => c s' c' r' H_r'.
  inversion H_r'; subst.
  destruct s5.
  * simpl in *.
    have ->: s'0 = [] ++ s'0 by [].
    by apply s_in_regexp_lang_times.
  * injection H => H_eq H_eq_c.
    subst.
    by apply s_in_regexp_lang_times.
Qed.

Lemma regexp_star_split : forall r' s' c,
  s_in_regexp_lang char (c :: s') (r_star r') ->
  exists s1 s2, s' = s1 ++ s2 /\ s_in_regexp_lang char (c :: s1) r' /\ s_in_regexp_lang char s2 (r_star r').
Proof.
  intros.
  remember (c :: s') as s0.
  remember (r_star r') as r0.
  revert r' s' c Heqs0 Heqr0.
  induction H; intros; try congruence.
  inversion Heqr0; subst; clear Heqr0.
  destruct s5.
  - apply IHs_in_regexp_lang2; auto.
  - simpl in *. inversion Heqs0; subst; clear Heqs0.
    eauto.
Qed.

Inductive accept_lt : r char * list char -> r char * list char -> Prop :=
| accept_lt_string : forall rs rs' : r char * list char,
  length (snd rs) < length (snd rs') ->
  accept_lt rs rs'
| accept_lt_regexp : forall rs rs' : r char * list char,
  length (snd rs) = length (snd rs') ->
  regexp_lt (fst rs) (fst rs') ->
  accept_lt rs rs'.

Definition accept_lt_lexprod'' (rs rs' : r char * list char) :=
lexprod'' lt 
          (length (snd rs), regexp_size (fst rs), regexp_subsize (fst rs))
          (length (snd rs'), regexp_size (fst rs'), regexp_subsize (fst rs')).

Lemma accept_lt_lexprod''_wf : well_founded accept_lt_lexprod''.
Proof.
intro.
apply (wf_inverse_image _ _ _ (fun rs => (length (snd rs), regexp_size (fst rs), regexp_subsize (fst rs)))).
by apply wf_lexprod''; apply lt_wf.
Defined.

Lemma accept_lt_lexprod''_impl : forall rs rs', accept_lt rs rs' -> accept_lt_lexprod'' rs rs'.
Proof.
move => rs rs'.
elim => {rs rs'}.
- move => rs rs' H_lt.
  rewrite /accept_lt_lexprod''.
  exact: left_lex''.
- move => rs rs' H_eq H_lt.
  rewrite /accept_lt_lexprod'' H_eq /=.
  inversion H_lt; subst.
  * exact: mid_lex''.
  * rewrite H1.
    exact: right_lex''.
Defined.

Lemma accept_lt_lexprod''_incl : inclusion _ accept_lt accept_lt_lexprod''.
Proof.
move => x y.
exact: accept_lt_lexprod''_impl.
Defined.

Lemma accept_lt_well_founded : well_founded accept_lt.
Proof.
apply (wf_incl _ _ _ accept_lt_lexprod''_incl).
exact: accept_lt_lexprod''_wf.
Defined.

Definition accept_p (rs : r char * list char) :=
  s_in_regexp_lang _ (snd rs) (fst rs).

Definition accept_t (rs : r char * list char) : Type :=
{ accept_p rs }+{ ~ accept_p rs }.

Definition accept_list_dec := @P_list_dec (r char) (list char) accept_lt accept_p.

End Accept.

Require Import Equations.Equations.
Open Scope equations_scope.

Section AcceptEquations.

Variable char : Type.

Variable char_eq_dec : forall c0 c1 : char, {c0 = c1}+{c0 <> c1}.

Instance wf_regexps_no_c_lt : WellFounded (@regexps_no_c_lt char).
apply regexps_no_c_lt_well_founded.
Defined.

Equations regexps_no_c (rc : r char * char) : regexps_no_c_t rc by wf rc (@regexps_no_c_lt char) :=
  regexps_no_c (r_zero, _) := exist _ [] _;
  regexps_no_c (r_unit, _) := exist _ [] _;
  regexps_no_c (r_char c, c') :=
    match char_eq_dec c c' with
    | left H_a => exist _ [r_unit] _
    | right H_a => exist _ [] _
    end;
  regexps_no_c (r_plus r1 r2, c) :=
    match regexps_no_c (r1, c), regexps_no_c (r2, c) with
    | exist l1 H_ex1, exist l2 H_ex2 => exist _ (l1 ++ l2) _
    end;
  regexps_no_c (r_star r, c) :=      
    match regexps_no_c (r, c) with
    | exist l H_ex =>
      exist _ (map (fun r' => r_times r' (r_star r)) l) _
    end;
  regexps_no_c (r_times r_zero _, _) := exist _ [] _;
  regexps_no_c (r_times r_unit r2, c) :=
    match regexps_no_c (r2, c) with
    | exist l H_ex => exist _ l _
    end;
  regexps_no_c (r_times (r_char c) r2, c') :=
    match char_eq_dec c c' with
    | left H_a => exist _ [r2] _
    | right H_a => exist _ [] _
    end;
  regexps_no_c (r_times (r_plus r11 r12) r2, c) :=
    match regexps_no_c (r_times r11 r2, c), regexps_no_c (r_times r12 r2, c) with
    | exist l11 H_ex11, exist l12 H_ex12 => exist _ (l11 ++ l12) _
    end;
  regexps_no_c (r_times (r_times r11 r12) r2, c) :=
    match regexps_no_c (r_times r11 (r_times r12 r2), c) with
    | exist l H_ex => exist _ l _
    end;
  regexps_no_c (r_times (r_star r1) r2, c) :=
    match regexps_no_c (r2, c), regexps_no_c (r1, c) with
    | exist l2 H_ex2, exist l1 H_ex1 =>
      exist _ (l2 ++ (map (fun r' => r_times r' (r_times (r_star r1) r2)) l1)) _
    end.
Next Obligation.
split => //.
move => s H_s.
inversion H_s; subst.
by inversion H.
Qed.
Next Obligation.
split => //.
move => s H_s.
inversion H_s; subst.
simpl in *.
by inversion H.
Qed.
Next Obligation.
split.
* move => r; case => //.
  move => H_eq; subst.
  move => s H_in.
  inversion H_in; subst.
  apply: s_in_regexp_c_lang_cs.
  rewrite /=.
  exact: s_in_regexp_lang_char.
* move => s' H_s.
  inversion H_s; subst.
  simpl in *.
  inversion H; subst.
  exists r_unit.
  split; first by left.
  exact: s_in_regexp_lang_unit.
Qed.
Next Obligation.
split => //=.
move => s' H_s.
inversion H_s; subst.
simpl in *.
by inversion H; subst.
Qed.
Next Obligation.
rewrite /regexps_no_c_lt /=.
by apply regexp_lt_lt => /=; lia.
Qed.
Next Obligation.
rewrite /regexps_no_c_lt /=.
by apply regexp_lt_lt => /=; lia.
Qed.
Next Obligation.
split.
* move => r H_in s H_s.
  apply: s_in_regexp_c_lang_cs => /=.
  apply in_app_or in H_in.
  case: H_in => H_in.
  + have H_s' := H1 _ H_in _ H_s.
    inversion H_s'; subst.
    simpl in *.
    exact: s_in_regexp_lang_plus_1.
  + have H_s' := H _ H_in _ H_s.
    inversion H_s'; subst.
    simpl in *.
    exact: s_in_regexp_lang_plus_2.    
* move => s' H_s'.
  inversion H_s'; subst.
  simpl in *.
  inversion H3; subst.
  * apply s_in_regexp_c_lang_cs in H6.
    have [r [H_in H_ex1'']] := H2 _ H6.
    exists r. split => //.
    by apply in_or_app; left.
  * apply s_in_regexp_c_lang_cs in H6.
    have [r [H_in H_ex2'']] := H0 _ H6.
    exists r. split => //.
    by apply in_or_app; right.
Qed.
Next Obligation.
split => //.
move => s H_s.
inversion H_s; subst.
simpl in *.
inversion H; subst.
by inversion H3.
Qed.  
Next Obligation.
rewrite /regexps_no_c_lt /=.
by apply regexp_lt_lt => /=; lia.
Qed.
Next Obligation.
split.
* move => r' H_in s H_s.
  apply: s_in_regexp_c_lang_cs => /=.
  have H_s' := H _ H_in _ H_s.
  inversion H_s'; subst.
  simpl in *.
  have ->: c :: s = [] ++ c :: s by [].
  apply s_in_regexp_lang_times => //.
  exact: s_in_regexp_lang_unit.
* move => s' H_s'.
  inversion H_s'; subst.
  simpl in *.
  inversion H1; subst.
  inversion H5; subst.
  simpl in *.
  subst.
  apply s_in_regexp_c_lang_cs in H6.
  apply H0 in H6.
  move: H6 => [r0 [H_in H_s0]].
  by exists r0.
Qed.
Next Obligation.
split.
* move => r'; case => // H_eq; subst.
  move => s H_s.
  apply: s_in_regexp_c_lang_cs => /=.
  have ->: c' :: s = [c'] ++ s by [].
  apply s_in_regexp_lang_times => //.
  exact: s_in_regexp_lang_char.
* move => s H_s.
  inversion H_s; subst.
  simpl in *.
  inversion H; subst.
  inversion H3; subst.
  simpl in *.
  injection H0 => H_eq.
  subst.
  exists r2.
  by split; first by left.
Qed.
Next Obligation.
split => //.
move => s H_s.
inversion H_s; subst.
simpl in *.
inversion H; subst.
inversion H3; subst.
simpl in *.
by injection H0.
Qed.
Next Obligation.
rewrite /regexps_no_c_lt /=.
by apply regexp_lt_lt => /=; lia.
Qed.
Next Obligation.
rewrite /regexps_no_c_lt /=.
by apply regexp_lt_lt => /=; lia.
Qed.
Next Obligation.
split.
* move => r' H_in s H_s.
  apply: s_in_regexp_c_lang_cs => /=.
  apply in_app_or in H_in.
  case: H_in => H_in.
  + have H_s' := H1 _ H_in _ H_s.
    inversion H_s'; subst.
    simpl in *.
    inversion H3; subst.
    apply s_in_regexp_lang_times => //.
    exact: s_in_regexp_lang_plus_1.
  + have H_s' := H _ H_in _ H_s.
    inversion H_s'; subst.
    simpl in *.
    inversion H3; subst.
    apply s_in_regexp_lang_times => //.
    exact: s_in_regexp_lang_plus_2.
* move => s' H_s'.
  inversion H_s'; subst.
  simpl in *.
  inversion H3; subst.
  inversion H7; subst.
  + destruct s5.
    -- simpl in *.
       subst.
       have H_sc: s_in_regexp_c_lang _ s' (r_times r11 r2) c.
         apply s_in_regexp_c_lang_cs.
         simpl.
         have ->: c :: s' = [] ++ c :: s' by [].
         by apply s_in_regexp_lang_times.                      
       apply H2 in H_sc.
       move: H_sc => [r0 [H_in H_s0]].
       exists r0.
       split => //.
       by apply in_or_app; left.
    -- simpl in *.
       injection H4 => H_eq H_eq_c.
       subst.
       have H_sc: s_in_regexp_c_lang _ (s5 ++ s'0) (r_times r11 r2) c.
         apply s_in_regexp_c_lang_cs.
         simpl.
         have ->: c :: (s5 ++ s'0) = (c :: s5) ++ s'0 by [].
         by apply s_in_regexp_lang_times.
       apply H2 in H_sc.
       move: H_sc => [r0 [H_in H_s0]].
       exists r0.
       split => //.
       by apply in_or_app; left.
  + destruct s5.
    -- simpl in *.
       subst.
       have H_sc: s_in_regexp_c_lang _ s' (r_times r12 r2) c.
         apply s_in_regexp_c_lang_cs.
         simpl.
         have ->: c :: s' = [] ++ c :: s' by [].
         by apply s_in_regexp_lang_times.               
       apply H0 in H_sc.
       move: H_sc => [r0 [H_in H_s0]].
       exists r0.
       split => //.
       by apply in_or_app; right.
    -- simpl in *.
       injection H4 => H_eq H_eq_c.
       subst.
       have H_sc: s_in_regexp_c_lang _ (s5 ++ s'0) (r_times r12 r2) c.
         apply s_in_regexp_c_lang_cs.
         simpl.
         have ->: c :: (s5 ++ s'0) = (c :: s5) ++ s'0 by [].
         by apply s_in_regexp_lang_times.
       apply H0 in H_sc.
       move: H_sc => [r0 [H_in H_s0]].
       exists r0.
       split => //.
       by apply in_or_app; right.
Qed.
Next Obligation.
rewrite /regexps_no_c_lt /=.
by apply regexp_lt_times_lt => /=; lia.
Qed.
Next Obligation.
split.
* move => r' H_in s' H_s.
  apply: s_in_regexp_c_lang_cs => /=.
  have H_s' := H _ H_in _ H_s.
  inversion H_s'; subst.
  simpl in *.
  inversion H1; subst.
  inversion H6; subst.
  rewrite app_assoc.
  apply s_in_regexp_lang_times => //.
  exact: s_in_regexp_lang_times.
* move => s' H_s'.
  inversion H_s'; subst.
  simpl in *.
  inversion H1; subst.
  inversion H5; subst.
  destruct s0.
  + simpl in *.
    destruct s'1.
    -- simpl in *.
       subst.
       have H_sc: s_in_regexp_c_lang _ s' (r_times r11 (r_times r12 r2)) c.
         apply s_in_regexp_c_lang_cs.
         simpl.
         have ->: c :: s' = [] ++ c :: s' by [].
         apply s_in_regexp_lang_times => //.
         have ->: c :: s' = [] ++ c :: s' by [].
         by apply s_in_regexp_lang_times => //.
       by apply H0 in H_sc.
    -- injection H2 => H_eq H_eq_c; subst.
       have H_sc: s_in_regexp_c_lang _ (s'1 ++ s'0) (r_times r11 (r_times r12 r2)) c.
         apply s_in_regexp_c_lang_cs.
         simpl.
         have ->: c :: (s'1 ++ s'0) = [] ++ c :: (s'1 ++ s'0) by [].
         apply s_in_regexp_lang_times => //.
         have ->: c :: (s'1 ++ s'0) = (c :: s'1) ++ s'0 by [].
         by apply s_in_regexp_lang_times.
       by apply H0 in H_sc.
  + simpl in *.
    injection H2 => H_eq H_eq_c.
    subst.
    have H_sc: s_in_regexp_c_lang _ (s0 ++ (s'1 ++ s'0)) (r_times r11 (r_times r12 r2)) c.
      apply s_in_regexp_c_lang_cs.
      simpl.
      have ->: c :: (s0 ++ s'1 ++ s'0) = (c :: s0) ++ s'1 ++ s'0 by [].
      apply s_in_regexp_lang_times => //.
      by apply s_in_regexp_lang_times.
    apply H0 in H_sc.
    move: H_sc => [r0 [H_in H_r0]].
    exists r0.
    split => //.
    by rewrite -app_assoc.
Qed.
Next Obligation.
rewrite /regexps_no_c_lt /=.
by apply regexp_lt_lt => /=; lia.
Qed.
Next Obligation.
rewrite /regexps_no_c_lt /=.
by apply regexp_lt_lt => /=; lia.
Qed.
Next Obligation.
split.
* move => r' H_in s' H_s'.
  apply: s_in_regexp_c_lang_cs => /=.
  apply in_app_or in H_in.
  case: H_in => H_in.
  + have H_s0 := H1 _ H_in _ H_s'.
    inversion H_s0; subst.
    simpl in *.
    have ->: c :: s' = [] ++ c :: s' by [].
    apply s_in_regexp_lang_times => //.
    exact: s_in_regexp_lang_star_1.
  + apply in_map_iff in H_in.
    move: H_in => [r0 [H_eq_r0 H_in']].
    subst.
    inversion H_s'; subst.
    have H_s0 := H _ H_in' _ H6.
    inversion_clear H7; subst.
    inversion_clear H_s0; subst.
    simpl in *.
    have ->: c :: (s5 ++ s0 ++ s') = (c :: s5 ++ s0) ++ s' by rewrite app_assoc.
    apply s_in_regexp_lang_times => //.
    have ->: c :: s5 ++ s0 = (c :: s5) ++ s0 by [].
    exact: s_in_regexp_lang_star_2.
* move => s' H_s'.
  inversion H_s'; subst.
  simpl in *.
  inversion H3; subst.
  destruct s5.
  + simpl in *.
    subst.    
    apply s_in_regexp_c_lang_cs in H8.
    apply H2 in H8.
    move: H8 => [r0 [H_in H_r0]].
    exists r0.
    split => //.
    apply in_or_app.
    by left.
  + injection H4 => H_eq H_eq_c.
    subst.
    apply regexp_star_split in H7.
    move: H7 => [s1 [s2 [H_eq [H_s12 H_s12']]]].
    subst.
    apply s_in_regexp_c_lang_cs in H_s12.
    apply H0 in H_s12.
    move: H_s12 => [r0 [H_in H_r0]].
    exists (r_times r0 (r_times (r_star r1) r2)).
    split.
    -- apply in_or_app.
       right.
       apply in_split in H_in.
       move: H_in => [l'2 [l'3 H_eq]].
       subst.
       move {H1 H2 H0 H}.
       elim: l'2 => //=; first by left.
       move => r'0 l'.
       rewrite map_app /= => H_in.
       right.
       apply in_or_app.
       by right; left.
    -- rewrite -app_assoc.
       apply s_in_regexp_lang_times => //.
       exact: s_in_regexp_lang_times.
Qed.
Next Obligation.
rewrite /regexps_no_c_lt /=.
by apply regexp_lt_lt => /=; lia.
Qed.
Next Obligation.    
split.
* move => r' H_in s' H_s'.
  apply: s_in_regexp_c_lang_cs => /=.
  apply in_map_iff in H_in.
  move: H_in => [r0 [H_eq_r0 H_in']].
  subst.
  inversion_clear H_s'; subst.
  have H_ex0 := H _ H_in' _ H1.
  inversion_clear H_ex0; subst.
  simpl in *.
  have ->: c :: (s5 ++ s'0) = (c :: s5) ++ s'0 by [].
  exact: s_in_regexp_lang_star_2.
* move => s' H_s'.
  inversion H_s'; subst.
  simpl in *.
  apply regexp_star_split in H1.
  move: H1 => [s1 [s2 [H_eq [H_s1 H_s2]]]].
  subst.
  apply s_in_regexp_c_lang_cs in H_s1.
  apply H0 in H_s1.
  move: H_s1 => [r0 [H_in H_r0]].
  exists (r_times r0 (r_star r)).
  split.
  + apply in_split in H_in.
    move: H_in => [l1 [l2 H_eq]].
    subst.
    elim: l1 {H H0} => /=; first by left.
    move => r1 l.
    rewrite map_app /= => H_in.
    by right.
  + exact: s_in_regexp_lang_times.
Qed.

Instance wf_accept_lt : WellFounded (@accept_lt char).
apply accept_lt_well_founded.
Defined.

Equations acc (rs : r char * list char) : accept_t rs by wf rs (@accept_lt char) :=
  acc (r_zero, _) := right _;
  acc (r_unit, []) := left _; acc (r_unit, _ :: _) := right _;
  acc (r_char c, [c']) := match char_eq_dec c c' with left _ => left _ | right _ => right _ end;
  acc (r_char _, []) := right _; acc (r_char _, _ :: _) := right _;
  acc (r_plus r1 r2, s) := match acc (r1, s) with left _=> left _ | right _ => match acc (r2, s) with left _ => left _ | right _ => right _ end end;
  acc (r_times r1 r2, []) := match acc (r1, []) with left _ => (match acc (r2, []) with left _ => left _ | right _ => right _ end) | right _ => right _ end;
  acc (r_times r_zero _, _) := right _;
  acc (r_times r_unit r2, c :: s) := match acc (r2, c :: s) with left _ => left _ | right _ => right _ end;
  acc (r_times (r_char c) r2, c' :: s) := match char_eq_dec c c' with left _ => (match acc (r2, s) with left _ => left _ | right _ => right _ end) | right _ => right _ end;
  acc (r_times (r_times r'1 r'2) r2, c :: s) := match acc (r_times r'1 (r_times r'2 r2), c :: s) with left _ => left _ | right _ => right _ end;
  acc (r_times (r_plus r'1 r'2) r2, c :: s) :=
    match acc (r_times r'1 r2, c :: s) with left _ => left _  | right _ => match acc (r_times r'2 r2, c :: s) with left _ => left _ | right _ => right _ end end;
  acc (r_times (r_star r1) r2, c :: s) :=
      match acc (r2, c :: s) with
      | left _ => left _ 
      | right _ => (match regexps_no_c (r1, c) with
                   | exist l H_l =>
                     match @accept_list_dec char (r_times (r_star r1) r2, c :: s) acc (fun r0 => (r_times r0 (r_times (r_star r1) r2), s)) _ l with
                     | inleft (exist _ H_ex) => left _ 
                     | inright H_l' => right _
                     end
                   end)
      end;
  acc (r_star r, []) := left _;
  acc (r_star r, c :: s) :=
    (match regexps_no_c (r, c) with
     | exist l H_l => 
       match @accept_list_dec char (r_star r, c :: s) acc (fun r0 => (r_times r0 (r_star r), s)) _ l with
       | inleft (exist _ H_ex) => left _
       | inright H_l' => right _ 
       end
     end).
Next Obligation.
by inversion H.
Qed.
Next Obligation.
exact: s_in_regexp_lang_unit.
Qed.
Next Obligation.
by inversion H.
Qed.
Next Obligation.
by inversion H.
Qed.
Next Obligation.
exact: s_in_regexp_lang_char.
Qed.
Next Obligation.
by inversion H; subst.
Qed.
Next Obligation.
by inversion H.
Qed.
Next Obligation.
apply accept_lt_regexp => //=.
apply regexp_lt_lt.
rewrite /=.
by lia.
Qed.
Next Obligation.
exact: s_in_regexp_lang_plus_1.
Qed.
Next Obligation.
apply accept_lt_regexp => //.
apply regexp_lt_lt.
rewrite /=.
by lia.
Qed.
Next Obligation.
exact: s_in_regexp_lang_plus_2.
Qed.
Next Obligation.
by inversion H.
Qed.
Next Obligation.
apply accept_lt_regexp => //.
apply regexp_lt_lt.
rewrite /=.
by lia.
Qed.
Next Obligation.
apply accept_lt_regexp => //.
apply regexp_lt_lt.
rewrite /=.
by lia.
Qed.
Next Obligation.
exact: s_in_regexp_lang_times _ _ _ _ a a0.
Qed.
Next Obligation.
inversion H; subst.
case: n.
by destruct s5, s'.
Qed.
Next Obligation.
case: n.
inversion H; subst.
by destruct s5, s'.
Qed.
Next Obligation.
inversion H; subst.
by inversion H3.
Qed.
Next Obligation.
apply accept_lt_regexp => //.
apply regexp_lt_lt.
rewrite /=.
by lia.
Qed.
Next Obligation.
have H_eq: [] ++ c :: s = c :: s by [].
rewrite -H_eq.
apply s_in_regexp_lang_times => //.
exact: s_in_regexp_lang_unit.
Qed.
Next Obligation.
inversion H; subst.
inversion H3; subst.
case: n.
by rewrite -H0 /=.
Qed.
Next Obligation.
exact: accept_lt_string.
Qed.
Next Obligation.
have H_eq: [c'] ++ s = c' :: s by [].
rewrite -H_eq.
apply s_in_regexp_lang_times => //.
exact: s_in_regexp_lang_char.
Qed.
Next Obligation.
inversion H; subst.
inversion H3; subst.
move: H0.
rewrite /=; case => Hs.
subst.
by case: n.
Qed.
Next Obligation.
inversion H; subst.
inversion H3; subst.
by inversion H0.
Qed.
Next Obligation.
apply accept_lt_regexp => //.
apply regexp_lt_lt.
rewrite /=.
by lia.
Qed.
Next Obligation.
inversion a; subst.
apply s_in_regexp_lang_times => //.
exact: s_in_regexp_lang_plus_1.
Qed.
Next Obligation.
apply accept_lt_regexp => //=.
apply regexp_lt_lt => /=.
by lia.
Qed.
Next Obligation.
inversion a; subst.
apply s_in_regexp_lang_times => //.
exact: s_in_regexp_lang_plus_2.
Qed.
Next Obligation.
inversion H; subst.
inversion H3; subst.
- case: n.
  rewrite -H0.
  exact: s_in_regexp_lang_times.
- case: n0.
  rewrite -H0.
  exact: s_in_regexp_lang_times.
Qed.
Next Obligation.
apply accept_lt_regexp => //.
by apply regexp_lt_times_lt => /=; lia.
Qed.
Next Obligation.
inversion a; subst.
inversion H3; subst.
rewrite app_assoc.
apply s_in_regexp_lang_times => //.
exact: s_in_regexp_lang_times.
Qed.
Next Obligation.
inversion H; subst.
inversion H3; subst.
contradict n.
rewrite -app_assoc in H0.
rewrite -H0.
apply s_in_regexp_lang_times => //.
exact: s_in_regexp_lang_times.
Qed.
Next Obligation.
apply accept_lt_regexp => //=.
by apply regexp_lt_lt => /=; lia.
Qed.
Next Obligation.
rewrite /accept_p /= in a.
rewrite /accept_p /=.
have ->: c :: s = [] ++ c :: s by [].
apply s_in_regexp_lang_times => //.
exact: s_in_regexp_lang_star_1.
Qed.
Next Obligation.
exact: accept_lt_string.
Qed.
Next Obligation.
inversion H0; subst.
simpl in *.
subst.
have H_l0 := H1 _ H _ H8.
inversion H_l0; subst.
simpl in *.
inversion H9; subst.
have ->: c :: s5 ++ s1 ++ s'0 = ((c :: s5) ++ s1) ++ s'0 by rewrite app_assoc.
apply s_in_regexp_lang_times => //.
by apply s_in_regexp_lang_star_2.
Qed.
Next Obligation.
inversion H1; subst.
destruct s5.
- simpl in *.
  by subst.
- injection H2 => H_eq H_eq_c.
  subst.
  clear H2.
  apply regexp_star_split in H5.
  move: H5 => [s1 [s2 [H_s1 [H_s2 H_eq]]]].
  subst.
  have H_sc: s_in_regexp_c_lang _ s1 r1 c by apply s_in_regexp_c_lang_cs.
  apply H0 in H_sc.
  move: H_sc => [r0 [H_in H_r0]].
  have H_l'' := H_l' _ H_in.
  case: H_l''.
  rewrite /accept_p /=.
  rewrite -app_assoc.
  apply s_in_regexp_lang_times => //.
  by apply s_in_regexp_lang_times.
Qed.
Next Obligation.
exact: s_in_regexp_lang_star_1.
Qed.
Next Obligation.
exact: accept_lt_string.
Qed.
Next Obligation.
inversion H0; subst.
simpl in *.
subst.
have H_l' := H1 _ H _ H8.
inversion H_l'; subst.
simpl in *.
rewrite /accept_p /=.
have ->: c :: (s5 ++ s') = (c :: s5) ++ s' by [].
by apply s_in_regexp_lang_star_2.
Qed.
Next Obligation.
have H_s' := star_times H1.
have [s1 [s2 [H_eq [H_s1 H_s2]]]] := regexp_star_split H1.
subst.
have H_c_l: s_in_regexp_c_lang _ (s1 ++ s2) (r_times r (r_star r)) c by apply s_in_regexp_c_lang_cs.
have H_s0: forall r', (forall s, s_in_regexp_c_lang _ s r c -> s_in_regexp_lang _ s r') -> s_in_regexp_lang _ (c :: (s1 ++ s2)) (r_times (r_char c) (r_times r' (r_star r))).
  move => r' H_sc.
  have ->: c :: (s1 ++ s2) = [c] ++ (s1 ++ s2) by [].
  apply s_in_regexp_lang_times; first by apply s_in_regexp_lang_char.
  apply s_in_regexp_lang_times => //.
  apply H_sc.
  by apply s_in_regexp_c_lang_cs.
have H_s1' := H0 s1.
have H_cs: s_in_regexp_c_lang _ s1 r c by apply s_in_regexp_c_lang_cs.
apply H_s1' in H_cs.
move: H_cs => [r' [H_in H_ss]].
apply H_l' in H_in.
case: H_in.
rewrite /accept_p /=.
by apply s_in_regexp_lang_times.
Qed.

End AcceptEquations.
