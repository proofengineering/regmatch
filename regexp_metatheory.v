Require Import regexp.

Require Import mathcomp.ssreflect.ssreflect.

Require Import List.
Require Import Relation_Definitions.
Require Import Relation_Operators.
Require Import Wf_nat.
Require Import Wellfounded.
Require Import Wellfounded.Lexicographic_Product.
Require Import Omega.

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

Fixpoint regexp_size (r : re char) : nat :=
match r with
| re_zero => 1
| re_unit => 1
| re_char _ => 1
| re_plus r1 r2 => regexp_size r1 + regexp_size r2 + 1
| re_times r1 r2 => regexp_size r1 + regexp_size r2 + 1
| re_star r => regexp_size r + 1
end.

Definition regexp_size_lt (r r' : re char) := regexp_size r < regexp_size r'.

Lemma regexp_size_wf : well_founded regexp_size_lt.
Proof.
exact: (well_founded_lt_compat _ (fun r => regexp_size r)).
Defined.

Fixpoint regexp_subsize (r : re char) : nat :=
match r with
| re_times r1 r2 => regexp_size r1
| _ => 0
end.

Definition regexp_subsize_lt (r r' : re char) := regexp_subsize r < regexp_subsize r'.

Lemma regexp_subsize_wf : well_founded regexp_subsize_lt.
Proof.
exact: (well_founded_lt_compat _ (fun r => regexp_subsize r)).
Defined.

Definition regexp_lt_size_subsize_lexprod' (r r' : re char) :=
lexprod' lt (regexp_size r, regexp_subsize r) (regexp_size r', regexp_subsize r').

Lemma regexp_lt_size_subsize_lexprod'_wf : well_founded regexp_lt_size_subsize_lexprod'.
Proof.
intro.
apply (wf_inverse_image _ _ _ (fun r => (regexp_size r, regexp_subsize r))).
by apply wf_lexprod'; apply lt_wf.
Defined.

Inductive regexp_lt : re char -> re char -> Prop :=
| regexp_lt_lt : forall r r' : re char, 
    regexp_size r < regexp_size r' -> 
    regexp_lt r r'
| regexp_lt_times_lt : forall r11 r12 r21 r22 : re char,
    regexp_size (re_times r11 r12) = regexp_size (re_times r21 r22) ->
    regexp_size r11 < regexp_size r21 ->
    regexp_lt (re_times r11 r12) (re_times r21 r22).

Lemma regexp_lt_size_subsize_symprod_incl_impl : 
  forall r r' : re char, 
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

Definition regexps_no_c_lt (rc rc' : re char * char) := regexp_lt (fst rc) (fst rc').

Lemma regexps_no_c_lt_well_founded : well_founded regexps_no_c_lt.
Proof.
apply (wf_inverse_image _ _ _ (fun rs => fst rs)).
apply regexp_lt_well_founded.
Defined.

Definition regexps_no_c_t (rc : re char * char) :=
{ l : list (re char) | (forall r : re char, In r l -> (forall s, s_in_regexp_lang char s r -> s_in_regexp_c_lang char s (fst rc) (snd rc))) /\ (forall s, s_in_regexp_c_lang char s (fst rc) (snd rc) -> exists r, In r l /\ s_in_regexp_lang char s r) }.

Lemma star_times : 
  forall (s' : list char) c r',
  s_in_regexp_lang _ (c :: s') (re_star r') ->
  s_in_regexp_lang _ (c :: s') (re_times r' (re_star r')).
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
  s_in_regexp_lang char (c :: s') (re_star r') ->
  exists s1 s2, s' = s1 ++ s2 /\ s_in_regexp_lang char (c :: s1) r' /\ s_in_regexp_lang char s2 (re_star r').
Proof.
  intros.
  remember (c :: s') as s0.
  remember (re_star r') as r0.
  revert r' s' c Heqs0 Heqr0.
  induction H; intros; try congruence.
  inversion Heqr0; subst; clear Heqr0.
  destruct s5.
  - apply IHs_in_regexp_lang2; auto.
  - simpl in *. inversion Heqs0; subst; clear Heqs0.
    eauto.
Qed.

Definition regexps_no_c_F : forall (rc : re char * char),
  (forall rc' : re char * char, regexps_no_c_lt rc' rc -> regexps_no_c_t rc') -> regexps_no_c_t rc.
refine
  (fun rc regexps_no_c_rec =>
     match fst rc as r0 return _ = r0 -> _ with
     | re_zero => fun H_eq => exist _ [] _
     | re_unit => fun H_eq => exist _ [] _
     | re_char c =>
       fun H_eq =>
         match char_eq_dec c (snd rc) with
         | left H_a => exist _ [re_unit] _
         | right H_a => exist _ [] _
         end
     | re_plus r1 r2 => 
       fun H_eq =>
         match regexps_no_c_rec (r1, snd rc) _, regexps_no_c_rec (r2, snd rc) _ with
         | exist l1 H_ex1, exist l2 H_ex2 => exist _ (l1 ++ l2) _
         end
     | re_star r =>
       fun H_eq =>
         match regexps_no_c_rec (r, snd rc) _ with
         | exist l H_ex =>
           exist _ (map (fun r' => re_times r' (re_star r)) l) _
         end
     | re_times re_zero _ => fun H_eq => exist _ [] _
     | re_times re_unit r2 =>
       fun H_eq =>
         match regexps_no_c_rec (r2, snd rc) _ with
         | exist l H_ex => exist _ l _
         end
     | re_times (re_char c) r2 =>
       fun H_eq =>
         match char_eq_dec c (snd rc) with
         | left H_a => exist _ [r2] _
         | right H_a => exist _ [] _
         end
     | re_times (re_plus r11 r12) r2 =>
       fun H_eq =>
         match regexps_no_c_rec (re_times r11 r2, snd rc) _, regexps_no_c_rec (re_times r12 r2, snd rc) _ with
         | exist l11 H_ex11, exist l12 H_ex12 => exist _ (app l11 l12) _
         end
     | re_times (re_times r11 r12) r2 =>
       fun H_eq =>
         match regexps_no_c_rec (re_times r11 (re_times r12 r2), snd rc) _ with
         | exist l H_ex => exist _ l _
         end
     | re_times (re_star r1) r2 =>
       fun H_eq =>
         match regexps_no_c_rec (r2, snd rc) _, regexps_no_c_rec (r1, snd rc) _ with
         | exist l2 H_ex2, exist l1 H_ex1 =>
           exist _ (app l2 (map (fun r' => re_times r' (re_times (re_star r1) r2)) l1)) _
         end
     end (refl_equal _)); destruct rc; simpl in *; subst => //=.
- split => //.
  move => s H_s.
  inversion H_s; subst.
  by inversion H.
- split => //.
  move => s H_s.
  inversion H_s; subst.
  simpl in *.
  by inversion H.
- split.
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
    exists re_unit.
    split; first by left.
    exact: s_in_regexp_lang_unit.
- split => //=.
  move => s' H_s.
  inversion H_s; subst.
  simpl in *.
  by inversion H; subst.
- rewrite /regexps_no_c_lt /=.
  by apply regexp_lt_lt => /=; omega.
- rewrite /regexps_no_c_lt /=.
  by apply regexp_lt_lt => /=; omega.
- move: H_ex1 => [H_ex1 H_ex1'].
  move: H_ex2 => [H_ex2 H_ex2'].
  split.
  * move => r H_in s H_s.
    apply: s_in_regexp_c_lang_cs => /=.
    apply in_app_or in H_in.
    case: H_in => H_in.
    + have H_s' := H_ex1 _ H_in _ H_s.
      inversion H_s'; subst.
      simpl in *.
      exact: s_in_regexp_lang_plus_1.
    + have H_s' := H_ex2 _ H_in _ H_s.
      inversion H_s'; subst.
      simpl in *.
      exact: s_in_regexp_lang_plus_2.
  * move => s' H_s'.
    inversion H_s'; subst.
    simpl in *.
    inversion H; subst.
    * apply s_in_regexp_c_lang_cs in H2.
      have [r [H_in H_ex1'']] := H_ex1' _ H2.
      exists r. split => //.
      by apply in_or_app; left.
    * apply s_in_regexp_c_lang_cs in H2.
      have [r [H_in H_ex2'']] := H_ex2' _ H2.
      exists r. split => //.
      by apply in_or_app; right.
- split => //.
  move => s H_s.
  inversion H_s; subst.
  simpl in *.
  inversion H; subst.
  by inversion H3.
- rewrite /regexps_no_c_lt /=.
  by apply regexp_lt_lt => /=; omega.
- move: H_ex => [H_ex H_ex'].
  split.
  * move => r' H_in s H_s.
    apply: s_in_regexp_c_lang_cs => /=.
    have H_s' := H_ex _ H_in _ H_s.
    inversion H_s'; subst.
    simpl in *.
    have ->: c :: s = [] ++ c :: s by [].
    apply s_in_regexp_lang_times => //.
    exact: s_in_regexp_lang_unit.
  * move => s' H_s'.
    inversion H_s'; subst.
    simpl in *.
    inversion H; subst.
    inversion H3; subst.
    simpl in *.
    subst.
    apply s_in_regexp_c_lang_cs in H4.
    apply H_ex' in H4.
    move: H4 => [r0 [H_in H_s0]].
    by exists r0.
- split.
  * move => r'; case => // H_eq; subst.
    move => s H_s.
    apply: s_in_regexp_c_lang_cs => /=.
    have ->: c0 :: s = [c0] ++ s by [].
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
- split => //.
  move => s H_s.
  inversion H_s; subst.
  simpl in *.
  inversion H; subst.
  inversion H3; subst.
  simpl in *.
  by injection H0.
- rewrite /regexps_no_c_lt /=.
  by apply regexp_lt_lt => /=; omega.
- rewrite /regexps_no_c_lt /=.
  by apply regexp_lt_lt => /=; omega.
- move: H_ex11 => [H_ex11 H_ex11'].
  move: H_ex12 => [H_ex12 H_ex12'].
  split.  
  * move => r' H_in s H_s.
    apply: s_in_regexp_c_lang_cs => /=.
    apply in_app_or in H_in.
    case: H_in => H_in.
    + have H_s' := H_ex11 _ H_in _ H_s.
      inversion H_s'; subst.
      simpl in *.
      inversion H; subst.
      apply s_in_regexp_lang_times => //.
      exact: s_in_regexp_lang_plus_1.
    + have H_s' := H_ex12 _ H_in _ H_s.
      inversion H_s'; subst.
      simpl in *.
      inversion H; subst.
      apply s_in_regexp_lang_times => //.
      exact: s_in_regexp_lang_plus_2.
  * move => s' H_s'.
    inversion H_s'; subst.
    simpl in *.
    inversion H; subst.
    inversion H3; subst.
    + destruct s5.
      -- simpl in *.
         subst.
         have H_sc: s_in_regexp_c_lang _ s' (re_times r11 r2) c.           
           apply s_in_regexp_c_lang_cs.
           simpl.
           have ->: c :: s' = [] ++ c :: s' by [].
           by apply s_in_regexp_lang_times.                      
         apply H_ex11' in H_sc.
         move: H_sc => [r0 [H_in H_s0]].
         exists r0.
         split => //.
         by apply in_or_app; left.
      -- simpl in *.
         injection H0 => H_eq H_eq_c.
         subst.
         have H_sc: s_in_regexp_c_lang _ (s5 ++ s'0) (re_times r11 r2) c.
           apply s_in_regexp_c_lang_cs.
           simpl.
           have ->: c :: (s5 ++ s'0) = (c :: s5) ++ s'0 by [].
           by apply s_in_regexp_lang_times.
         apply H_ex11' in H_sc.
         move: H_sc => [r0 [H_in H_s0]].
         exists r0.
         split => //.
         by apply in_or_app; left.
    + destruct s5.
      -- simpl in *.
         subst.
         have H_sc: s_in_regexp_c_lang _ s' (re_times r12 r2) c.
           apply s_in_regexp_c_lang_cs.
           simpl.
           have ->: c :: s' = [] ++ c :: s' by [].
           by apply s_in_regexp_lang_times.                      
         apply H_ex12' in H_sc.
         move: H_sc => [r0 [H_in H_s0]].
         exists r0.
         split => //.
         by apply in_or_app; right.
      -- simpl in *.
         injection H0 => H_eq H_eq_c.
         subst.
         have H_sc: s_in_regexp_c_lang _ (s5 ++ s'0) (re_times r12 r2) c.
           apply s_in_regexp_c_lang_cs.
           simpl.
           have ->: c :: (s5 ++ s'0) = (c :: s5) ++ s'0 by [].
           by apply s_in_regexp_lang_times.
         apply H_ex12' in H_sc.
         move: H_sc => [r0 [H_in H_s0]].
         exists r0.
         split => //.
         by apply in_or_app; right.        
- rewrite /regexps_no_c_lt /=.
  by apply regexp_lt_times_lt => /=; omega.
- move: H_ex => [H_ex H_ex'].
  split.
  * move => r' H_in s' H_s.
    apply: s_in_regexp_c_lang_cs => /=.
    have H_s' := H_ex _ H_in _ H_s.
    inversion H_s'; subst.
    simpl in *.
    inversion H; subst.
    inversion H4; subst.
    rewrite app_assoc.
    apply s_in_regexp_lang_times => //.
    exact: s_in_regexp_lang_times.
  * move => s' H_s'.
    inversion H_s'; subst.
    simpl in *.
    inversion H; subst.
    inversion H3; subst.
    destruct s0.
    + simpl in *.
      destruct s'1.
      -- simpl in *.
         subst.
         have H_sc: s_in_regexp_c_lang _ s' (re_times r11 (re_times r12 r2)) c.
           apply s_in_regexp_c_lang_cs.
           simpl.
           have ->: c :: s' = [] ++ c :: s' by [].
           apply s_in_regexp_lang_times => //.
           have ->: c :: s' = [] ++ c :: s' by [].
           by apply s_in_regexp_lang_times => //.
         by apply H_ex' in H_sc.
      -- injection H0 => H_eq H_eq_c; subst.
         have H_sc: s_in_regexp_c_lang _ (s'1 ++ s'0) (re_times r11 (re_times r12 r2)) c.
           apply s_in_regexp_c_lang_cs.
           simpl.
           have ->: c :: (s'1 ++ s'0) = [] ++ c :: (s'1 ++ s'0) by [].
           apply s_in_regexp_lang_times => //.
           have ->: c :: (s'1 ++ s'0) = (c :: s'1) ++ s'0 by [].
           by apply s_in_regexp_lang_times.
         by apply H_ex' in H_sc.
    + simpl in *.
      injection H0 => H_eq H_eq_c.
      subst.
      have H_sc: s_in_regexp_c_lang _ (s0 ++ (s'1 ++ s'0)) (re_times r11 (re_times r12 r2)) c.
        apply s_in_regexp_c_lang_cs.
        simpl.
        have ->: c :: (s0 ++ s'1 ++ s'0) = (c :: s0) ++ s'1 ++ s'0 by [].
        apply s_in_regexp_lang_times => //.
        by apply s_in_regexp_lang_times.
      apply H_ex' in H_sc.
      move: H_sc => [r0 [H_in H_r0]].
      exists r0.
      split => //.
      by rewrite -app_assoc.
- rewrite /regexps_no_c_lt /=.
  by apply regexp_lt_lt => /=; omega.
- rewrite /regexps_no_c_lt /=.
  by apply regexp_lt_lt => /=; omega.
- move: H_ex1 => [H_ex1 H_ex1'].
  move: H_ex2 => [H_ex2 H_ex2'].
  split.
  * move => r' H_in s' H_s'.
    apply: s_in_regexp_c_lang_cs => /=.
    apply in_app_or in H_in.
    case: H_in => H_in.
    + have H_s0 := H_ex2 _ H_in _ H_s'.
      inversion H_s0; subst.
      simpl in *.
      have ->: c :: s' = [] ++ c :: s' by [].
      apply s_in_regexp_lang_times => //.
      exact: s_in_regexp_lang_star_1.
    + apply in_map_iff in H_in.
      move: H_in => [r0 [H_eq_r0 H_in']].
      subst.
      inversion H_s'; subst.
      have H_s0 := H_ex1 _ H_in' _ H2.
      inversion_clear H3; subst.
      inversion_clear H_s0; subst.
      simpl in *.
      have ->: c :: (s5 ++ s0 ++ s') = (c :: s5 ++ s0) ++ s' by rewrite app_assoc.
      apply s_in_regexp_lang_times => //.
      have ->: c :: s5 ++ s0 = (c :: s5) ++ s0 by [].
      exact: s_in_regexp_lang_star_2.
  * move => s' H_s'.
    inversion H_s'; subst.
    simpl in *.
    inversion H; subst.
    destruct s5.
    + simpl in *.
      subst.
      apply s_in_regexp_c_lang_cs in H4.
      apply H_ex2' in H4.
      move: H4 => [r0 [H_in H_r0]].
      exists r0.
      split => //.
      apply in_or_app.
      by left.
    + injection H0 => H_eq H_eq_c.
      subst.
      apply regexp_star_split in H3.
      move: H3 => [s1 [s2 [H_eq [H_s12 H_s12']]]].
      subst.
      apply s_in_regexp_c_lang_cs in H_s12.
      apply H_ex1' in H_s12.
      move: H_s12 => [r0 [H_in H_r0]].
      exists (re_times r0 (re_times (re_star r1) r2)).
      split.
      -- apply in_or_app.
         right.
         apply in_split in H_in.
         move: H_in => [l'2 [l'3 H_eq]].
         subst.
         move {H_ex1 H_ex1'}.
         elim: l'2 => //=; first by left.
         move => r'0 l'.
         rewrite map_app /= => H_in.
         right.
         apply in_or_app.
         by right; left.
      -- rewrite -app_assoc.
         apply s_in_regexp_lang_times => //.
         exact: s_in_regexp_lang_times.
- rewrite /regexps_no_c_lt /=.
  by apply regexp_lt_lt => /=; omega.
- move: H_ex => [H_ex H_ex'].
  split.
  * move => r' H_in s' H_s'.
    apply: s_in_regexp_c_lang_cs => /=.
    apply in_map_iff in H_in.
    move: H_in => [r0 [H_eq_r0 H_in']].
    subst.
    inversion_clear H_s'; subst.
    have H_ex0 := H_ex _ H_in' _ H.
    inversion_clear H_ex0; subst.
    simpl in *.
    have ->: c :: (s5 ++ s'0) = (c :: s5) ++ s'0 by [].
    exact: s_in_regexp_lang_star_2.
  * move => s' H_s'.
    inversion H_s'; subst.
    simpl in *.
    apply regexp_star_split in H.
    move: H => [s1 [s2 [H_eq [H_s1 H_s2]]]].
    subst.
    apply s_in_regexp_c_lang_cs in H_s1.
    apply H_ex' in H_s1.
    move: H_s1 => [r0 [H_in H_r0]].
    exists (re_times r0 (re_star r)).
    split.
    + apply in_split in H_in.
      move: H_in => [l1 [l2 H_eq]].
      subst.
      elim: l1 {H_ex' H_ex} => /=; first by left.
      move => r1 l.
      rewrite map_app /= => H_in.
      by right.
    + exact: s_in_regexp_lang_times.
Defined.

Definition regexps_no_c : forall (rs : re char * char), regexps_no_c_t rs :=
@well_founded_induction_type _ _ regexps_no_c_lt_well_founded regexps_no_c_t regexps_no_c_F.

Definition string_lt (s s' : list char) := length s < length s'.

Lemma string_lt_well_founded : well_founded string_lt.
Proof.
exact: (well_founded_lt_compat _ (fun s => length s)).
Defined.

Inductive accept_lt : re char * list char -> re char * list char -> Prop :=
| accept_lt_string : forall rs rs' : re char * list char,
  length (snd rs) < length (snd rs') ->
  accept_lt rs rs'
| accept_lt_regexp : forall rs rs' : re char * list char,
  length (snd rs) = length (snd rs') ->
  regexp_lt (fst rs) (fst rs') ->
  accept_lt rs rs'.

Definition accept_lt_lexprod'' (rs rs' : re char * list char) :=
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

Definition accept_p (rs : re char * list char) :=
  s_in_regexp_lang _ (snd rs) (fst rs).

Definition accept_t (rs : re char * list char) :=
{ accept_p rs }+{ ~ accept_p rs }.

Definition accept_list_dec := @P_list_dec (re char) (list char) accept_lt accept_p.

Definition accept_F : forall rs : re char * list char,
  (forall rs', accept_lt rs' rs -> accept_t rs') -> accept_t rs.
  refine
    (fun rs accept_rec =>
       match snd rs as s0 return _ = s0 -> _ with
       | [] =>
         fun H_eq_s =>
           match fst rs as r0 return _ = r0 -> _ with
           | re_zero => fun H_eq_r => right _
           | re_unit => fun H_eq_r => left _
           | re_char _ => fun H_eq_r => right _
           | re_plus r1 r2 =>
             fun H_eq_r =>
               match accept_rec (r1, []) _ with
               | left H_r1 => left _
               | right H_r1 =>
                 match accept_rec (r2, []) _ with
                 | left H_r2 => left _
                 | right H_r2 => right _
                 end
               end
           | re_times r1 r2 =>
             fun H_eq_r =>
               match accept_rec (r1, []) _ with
               | left H_r1 =>
                 match accept_rec (r2, []) _ with
                 | left H_r2 => left _
                 | right H_r2 => right _
                 end
               | right H_r1 => right _
               end
           | re_star r' => fun H_eq_r => left _
           end (refl_equal _)
       | c :: s' =>
         fun H_eq_s =>
           match fst rs as r0 return _ = r0 -> _ with
           | re_zero => fun H_eq_r => right _
           | re_unit => fun H_eq_r => right _
           | re_char c' =>
             fun H_eq_r =>
               match s' as s1 return _ = s1 -> _ with
               | [] =>
                 fun H_eq_s' =>
                   match char_eq_dec c c' with
                   | left H_c => left _
                   | right H_c => right _
                   end
               | _ => fun H_eq_s' => right _ 
               end (refl_equal _)
           | re_plus r1 r2 =>
             fun H_eq_r =>
               match accept_rec (r1, c :: s') _ with
               | left H_r1 => left _
               | right H_r1 =>
                 match accept_rec (r2, c :: s') _ with
                 | left H_r2 => left _
                 | right H_r2 => right _
                 end
               end
           | re_times re_unit r2 =>
             fun H_eq_r =>
               match accept_rec (r2, c :: s') _ with
               | left H_r2 => left _
               | right H_r2 => right _
               end
           | re_times (re_char c') r2 =>
             fun H_eq_r =>
               match char_eq_dec c c' with
               | left H_c =>
                 match accept_rec (r2, s') _ with
                 | left H_r2 => left _
                 | right H_r2 => right _
                 end
               | right H_c => right _
               end
           | re_times (re_times r11 r12) r2 =>
             fun H_eq_r =>
               match accept_rec (re_times r11 (re_times r12 r2), c :: s') _ with
               | left H_r => left _
               | right H_r => right _
               end
           | re_times (re_plus r11 r12) r2 =>
             fun H_eq_r =>
               match accept_rec (re_times r11 r2, c :: s') _ with
               | left H_r11 => left _
               | right H_r11 =>
                 match accept_rec (re_times r12 r2, c :: s') _ with
                 | left H_r12 => left _
                 | right H_r12 => right _
                 end
               end
           | re_times (re_star r1) r2 =>
             fun H_eq_r =>
              match accept_rec (r2, c :: s') _ with
              | left H_r2 => left _
              | right H_r2 =>
                match regexps_no_c (r1, c) with
                | exist l H_l =>
                  match @accept_list_dec rs accept_rec (fun r0 => (re_times r0 (re_times (re_star r1) r2), s')) _ l with
                  | inleft (exist _ H_ex) => left _ 
                  | inright H_l' => right _
                  end
                end 
              end
           | re_star r' =>
             fun H_eq_r =>
               match regexps_no_c (r', c) with
               | exist l H_l => 
                 match @accept_list_dec rs accept_rec (fun r0 => (re_times r0 (re_star r'), s')) _ l with
                 | inleft (exist _ H_ex) => left _
                 | inright H_l' => right _ 
                 end
               end                       
           | re_times re_zero _ => 
             fun H_eq_r => right _
           end (refl_equal _)
       end (refl_equal _)); destruct rs; simpl in *; subst.
- by move => H_m; inversion H_m.
- exact: s_in_regexp_lang_unit.
- by move => H_m; inversion H_m.
- apply accept_lt_regexp => //.
  apply regexp_lt_lt.
  rewrite /=.
  by omega.
- exact: s_in_regexp_lang_plus_1.
- apply accept_lt_regexp => //.
  apply regexp_lt_lt.
  rewrite /=.
  by omega.
- exact: s_in_regexp_lang_plus_2.
- by move => H_m; inversion H_m; subst.
- apply accept_lt_regexp => //.
  apply regexp_lt_lt.
  rewrite /=.
  by omega.
- apply accept_lt_regexp => //.
  apply regexp_lt_lt.
  rewrite /=.
  by omega.
- exact: s_in_regexp_lang_times _ _ _ _ H_r1 H_r2.
- move => H_m; inversion H_m; subst.
  case: H_r2.
  by destruct s5, s'.
- move => H_m; inversion H_m; subst.
  by destruct s5.
- by apply s_in_regexp_lang_star_1.
- by move => H_m; inversion H_m.
- by move => H_m; inversion H_m.
- exact: s_in_regexp_lang_char.
- by move => H_m; inversion H_m; subst.
- by move => H_m; inversion H_m; subst.
- apply accept_lt_regexp => //.
  apply regexp_lt_lt.
  rewrite /=.
  by omega.
- exact: s_in_regexp_lang_plus_1.
- apply accept_lt_regexp => //.
  apply regexp_lt_lt.
  rewrite /=.
  by omega.
- exact: s_in_regexp_lang_plus_2.
- by move => H_m; inversion H_m.
- move => H_m; inversion H_m; subst.
  by inversion H2.
- apply accept_lt_regexp => //.
  apply regexp_lt_lt.
  rewrite /=.
  by omega.
- have H_eq: [] ++ c :: s' = c :: s' by [].
  rewrite -H_eq.
  apply s_in_regexp_lang_times => //.
  exact: s_in_regexp_lang_unit.
- move => H_s.
  inversion H_s; subst.
  inversion H2; subst.
  simpl in *.
  subst.
  by contradict H_r2.
- exact: accept_lt_string.
- have H_eq: [c'] ++ s' = c' :: s' by [].
  rewrite -H_eq.
  apply s_in_regexp_lang_times => //.
  exact: s_in_regexp_lang_char.
- move => H_m; inversion H_m; subst.
  inversion H2; subst.
  injection H => H_eq.
  by subst.
- move => H_m; inversion H_m; subst.
  inversion H2; subst.
  injection H => H_eq H_eq'.
  by subst.
- apply accept_lt_regexp => //.
  apply regexp_lt_lt.
  rewrite /=.
  by omega.
- inversion H_r11; subst.
  apply s_in_regexp_lang_times => //.
  exact: s_in_regexp_lang_plus_1.
- apply accept_lt_regexp => //.
  apply regexp_lt_lt.
  rewrite /=.
  by omega.
- inversion H_r12; subst.
  apply s_in_regexp_lang_times => //.
  exact: s_in_regexp_lang_plus_2.
- move => H_m; inversion H_m; subst.
  inversion H2; subst.
  * contradict H_r11.
    rewrite -H.
    exact: s_in_regexp_lang_times.
  * contradict H_r12.
    rewrite -H.
    exact: s_in_regexp_lang_times.
- apply accept_lt_regexp => //.
  by apply regexp_lt_times_lt => /=; omega.
- inversion H_r; subst.
  inversion H3; subst.
  rewrite app_assoc.
  apply s_in_regexp_lang_times => //.
  exact: s_in_regexp_lang_times.
- move => H_s; inversion H_s; subst.
  inversion H2; subst.
  contradict H_r.
  rewrite -app_assoc in H.
  rewrite -H.
  apply s_in_regexp_lang_times => //.
  exact: s_in_regexp_lang_times.
- apply accept_lt_regexp => //=.
  by apply regexp_lt_lt => /=; omega.
- rewrite /accept_p /= in H_r2.
  rewrite /accept_p /=.
  have ->: c :: s' = [] ++ c :: s' by [].
  apply s_in_regexp_lang_times => //.
  exact: s_in_regexp_lang_star_1.
- move => r0.
  exact: accept_lt_string.
- move: H_ex => [H_in H_acc].
  rewrite /accept_p /= in H_acc,H_r2.
  rewrite /accept_p /=.
  move {s}.
  move: H_l => [H_l H_l'].
  have H_l0 := H_l _ H_in.
  inversion H_acc; subst.
  inversion H3; subst.
  clear H_l'.
  apply H_l0 in H2.
  inversion H2; subst.
  simpl in *.
  have ->: c :: s5 ++ s0 ++ s' = ((c :: s5) ++ s0) ++ s' by rewrite app_assoc.
  apply s_in_regexp_lang_times => //.
  by apply s_in_regexp_lang_star_2.
- rewrite /accept_p /=.
  rewrite /accept_p /= in H_r2.
  move: H_l => [H_l H_l0].
  move => H_s.
  inversion H_s; subst.
  destruct s5.
  * simpl in *.
    by subst.
  * injection H => H_eq H_eq_c.
    subst.
    clear H.
    apply regexp_star_split in H2.
    move: H2 => [s1 [s2 [H_s1 [H_s2 H_eq]]]].
    subst.
    have H_sc: s_in_regexp_c_lang _ s1 r1 c by apply s_in_regexp_c_lang_cs.
    apply H_l0 in H_sc.
    move: H_sc => [r0 [H_in H_r0]].
    have H_l'' := H_l' _ H_in.
    case: H_l''.
    rewrite /accept_p /=.
    rewrite -app_assoc.
    apply s_in_regexp_lang_times => //.
    by apply s_in_regexp_lang_times.
- move => r0.
  exact: accept_lt_string.
- move: H_ex => [H_in H_acc].
  inversion H_acc; subst.
  move: H_l => [H_l H_l0].
  have H_l' := H_l _ H_in _ H2.
  inversion H_l'; subst.
  simpl in *.
  rewrite /accept_p /=.
  rewrite -H1 /=.
  have ->: c :: (s5 ++ s'0) = (c :: s5) ++ s'0 by [].
  by apply s_in_regexp_lang_star_2.
- rewrite /accept_p /=. 
  move => H_s.
  have H_s' := star_times H_s.
  have [s1 [s2 [H_eq [H_s1 H_s2]]]] := regexp_star_split H_s.
  subst.
  have H_c_l: s_in_regexp_c_lang _ (s1 ++ s2) (re_times r' (re_star r')) c by apply s_in_regexp_c_lang_cs.
  have H_s0: forall r, (forall s, s_in_regexp_c_lang _ s r' c -> s_in_regexp_lang _ s r) -> s_in_regexp_lang _ (c :: (s1 ++ s2)) (re_times (re_char c) (re_times r (re_star r'))).
    move => r H_sc.
    have ->: c :: (s1 ++ s2) = [c] ++ (s1 ++ s2) by [].
    apply s_in_regexp_lang_times; first by apply s_in_regexp_lang_char.
    apply s_in_regexp_lang_times => //.
    apply H_sc.
    by apply s_in_regexp_c_lang_cs.
  move: H_l => [H_l H_ex].
  have H_s1' := H_ex s1.
  have H_cs: s_in_regexp_c_lang _ s1 r' c by apply s_in_regexp_c_lang_cs.
  apply H_s1' in H_cs.
  move: H_cs => [r [H_in H_ss]].
  apply H_l' in H_in.
  case: H_in.
  rewrite /accept_p /=.
  by apply s_in_regexp_lang_times.
Defined.

Definition accept : forall (rs : re char * list char), accept_t rs :=
@well_founded_induction_type _ _ accept_lt_well_founded accept_t accept_F.

End Accept.
