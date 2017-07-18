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
Open Scope string_scope.

Fixpoint regexp_size (r : regexp) : nat :=
match r with
| regexp_zero => 1
| regexp_unit => 1
| regexp_char _ => 1
| regexp_plus r1 r2 => regexp_size r1 + regexp_size r2 + 1
| regexp_times r1 r2 => regexp_size r1 + regexp_size r2 + 1
end.

Definition regexp_size_lt (r r' : regexp) := regexp_size r < regexp_size r'.

Lemma regexp_size_wf : well_founded regexp_size_lt.
Proof.
exact: (well_founded_lt_compat _ (fun r => regexp_size r)).
Defined.

Fixpoint regexp_subsize (r : regexp) : nat :=
match r with
| regexp_zero => 0
| regexp_unit => 0
| regexp_char _ => 0
| regexp_plus r1 r2 => 0
| regexp_times r1 r2 => regexp_size r1
end.

Definition regexp_subsize_lt (r r' : regexp) := regexp_subsize r < regexp_subsize r'.

Lemma regexp_subsize_wf : well_founded regexp_subsize_lt.
Proof.
exact: (well_founded_lt_compat _ (fun r => regexp_subsize r)).
Defined.

Section lexprod'.

Variable A : Type.

Variable ltA : A -> A -> Prop.

Inductive lexprod' : A * A -> A * A -> Prop :=
| left_lex : forall (x1 x2 y1 y2 : A), ltA x1 x2 -> lexprod' (x1, y1) (x2, y2)
| right_lex : forall (x y1 y2 : A), ltA y1 y2 -> lexprod' (x, y1) (x, y2).

Lemma lexprod'_Acc : well_founded ltA -> forall x, Acc ltA x -> forall y, Acc ltA y -> Acc lexprod' (x, y).
Proof.
intros H x Hx.
induction Hx as [x _ IHacc].
intros y Hy.
induction Hy as [y _ IHacc0].
apply Acc_intro.
intros (x1, y1) HA.
by inversion HA; subst; auto.
Defined.

Theorem wf_lexprod' : well_founded ltA -> well_founded lexprod'.
Proof.
intros H_wf (x, y).
by auto using lexprod'_Acc.
Defined.

End lexprod'.

Definition regexp_lt_size_subsize_lexprod' (r r' : regexp) :=
lexprod' _ lt (regexp_size r, regexp_subsize r) (regexp_size r', regexp_subsize r').

Lemma regexp_lt_size_subsize_lexprod'_wf : well_founded regexp_lt_size_subsize_lexprod'.
Proof.
intro.
apply (wf_inverse_image _ _ _ (fun r => (regexp_size r, regexp_subsize r))).
by apply wf_lexprod'; apply lt_wf.
Defined.

Inductive regexp_lt : regexp -> regexp -> Prop :=
| regexp_lt_lt : forall r r' : regexp, 
    regexp_size r < regexp_size r' -> 
    regexp_lt r r'
| regexp_lt_times_lt : forall r11 r12 r21 r22,
    regexp_size (regexp_times r11 r12) = regexp_size (regexp_times r21 r22) ->
    regexp_size r11 < regexp_size r21 ->
    regexp_lt (regexp_times r11 r12) (regexp_times r21 r22).

Lemma regexp_lt_size_subsize_symprod_incl_impl : forall r r', regexp_lt r r' -> regexp_lt_size_subsize_lexprod' r r'.
Proof.
move => r r'.
elim => {r r'}.
- move => r r' H_lt.
  rewrite /regexp_lt_size_subsize_lexprod'.
  exact: left_lex.
- move => r11 r12 r21 r22 H_eq H_lt.
  rewrite /regexp_lt_size_subsize_lexprod' H_eq /=.
  exact: right_lex.
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

Definition accept_lt (rs rs' : regexp * string) := regexp_lt (fst rs) (fst rs').

Lemma accept_lt_well_founded : well_founded accept_lt.
Proof.
apply (wf_inverse_image _ _ _ (fun rs => fst rs)).
apply regexp_lt_well_founded.
Defined.

Definition accept_t (rs : regexp * string) :=
{ s_matches_r (fst rs) (snd rs)}+{ ~ s_matches_r (fst rs) (snd rs) }.

Lemma string_append_assoc : forall s0 s1 s2, s0 ++ s1 ++ s2 = (s0 ++ s1) ++ s2.
elim => //.
move => a s0 IH s1 s2.
by rewrite /= IH.
Qed.

Definition accept_F : forall rs : regexp * string,
  (forall rs', accept_lt rs' rs -> accept_t rs') -> accept_t rs.
  refine
    (fun rs accept_rec =>
       match snd rs as s0 return _ = s0 -> _ with
       | "" =>
         fun H_eq_s =>
           match fst rs as r0 return _ = r0 -> _ with
           | regexp_zero => fun H_eq_r => right _
           | regexp_unit => fun H_eq_r => left _
           | regexp_char _ => fun H_eq_r => right _
           | regexp_plus r1 r2 =>
             fun H_eq_r =>
               match accept_rec (r1, "") _ with
               | left H_r1 => left _
               | right H_r1 =>
                 match accept_rec (r2, "") _ with
                 | left H_r2 => left _
                 | right H_r2 => right _
                 end
               end
           | regexp_times r1 r2 =>
             fun H_eq_r =>
               match accept_rec (r1, "") _ with
               | left H_r1 =>
                 match accept_rec (r2, "") _ with
                 | left H_r2 => left _
                 | right H_r2 => right _
                 end
               | right H_r1 => right _
               end
           end (refl_equal _)
       | String c s' =>
         fun H_eq_s =>
           match fst rs as r0 return _ = r0 -> _ with
           | regexp_zero => fun H_eq_r => right _
           | regexp_unit => fun H_eq_r => right _
           | regexp_char c' =>
             fun H_eq_r =>
               match s' as s1 return _ = s1 -> _ with
               | "" =>
                 fun H_eq_s' =>
                   match ascii_dec c c' with
                   | left H_c => left _
                   | right H_c => right _
                   end
               | _ => fun H_eq_s' => right _ 
               end (refl_equal _)
           | regexp_plus r1 r2 =>
             fun H_eq_r =>
               match accept_rec (r1, String c s') _ with
               | left H_r1 => left _
               | right H_r1 =>
                 match accept_rec (r2, String c s') _ with
                 | left H_r2 => left _
                 | right H_r2 => right _
                 end
               end
           | regexp_times regexp_unit r2 =>
             fun H_eq_r =>
               match accept_rec (r2, String c s') _ with
               | left H_r2 => left _
               | right H_r2 => right _
               end
           | regexp_times (regexp_char c') r2 =>
             fun H_eq_r =>
               match ascii_dec c c' with
               | left H_c =>
                 match accept_rec (r2, s') _ with
                 | left H_r2 => left _
                 | right H_r2 => right _
                 end
               | right H_c => right _
               end
           | regexp_times (regexp_times r11 r12) r2 =>
             fun H_eq_r =>
               match accept_rec (regexp_times r11 (regexp_times r12 r2), String c s') _ with
               | left H_r => left _
               | right H_r => right _
               end
           | regexp_times (regexp_plus r11 r12) r2 =>
             fun H_eq_r =>
               match accept_rec (regexp_times r11 r2, String c s') _ with
               | left H_r11 => left _
               | right H_r11 =>
                 match accept_rec (regexp_times r12 r2, String c s') _ with
                 | left H_r12 => left _
                 | right H_r12 => right _
                 end
               end
           | _ => fun H_eq_r => right _
           end (refl_equal _)
       end (refl_equal _)); destruct rs; simpl in *; subst.
- by move => H_m; inversion H_m.
- exact: s_matches_r_unit.
- by move => H_m; inversion H_m.
- rewrite /accept_lt /=.
  apply regexp_lt_lt.
  rewrite /=.
  by omega.
- exact: s_matches_r_plus_1.
- rewrite /accept_lt /=.
  apply regexp_lt_lt.
  rewrite /=.
  by omega.
- exact: s_matches_r_plus_2.
- by move => H_m; inversion H_m; subst.
- rewrite /accept_lt /=.
  apply regexp_lt_lt.
  rewrite /=.
  by omega.
- rewrite /accept_lt /=.
  apply regexp_lt_lt.
  rewrite /=.
  by omega.
- exact: s_matches_r_times _ _ _ _ H_r1 H_r2.
- move => H_m; inversion H_m; subst.
  by destruct s1, s2.
- move => H_m; inversion H_m; subst.
  by destruct s1.
- by move => H_m; inversion H_m.
- by move => H_m; inversion H_m.
- exact: s_matches_r_char.
- by move => H_m; inversion H_m; subst.
- by move => H_m; inversion H_m; subst.
- rewrite /accept_lt /=.
  apply regexp_lt_lt.
  rewrite /=.
  by omega.
- exact: s_matches_r_plus_1.
- rewrite /accept_lt /=.
  apply regexp_lt_lt.
  rewrite /=.
  by omega.
- exact: s_matches_r_plus_2.
- by move => H_m; inversion H_m.
- move => H_m; inversion H_m; subst.
  by inversion H2.
- rewrite /accept_lt /=.
  apply regexp_lt_lt.
  rewrite /=.
  by omega.
- have H_eq: append "" (String c s') = String c s' by [].
  rewrite -H_eq.
  apply s_matches_r_times => //.
  exact: s_matches_r_unit.
- move => H_s.
  inversion H_s; subst.
  inversion H2; subst.
  simpl in *.
  subst.
  by contradict H_r2.
- rewrite /accept_lt /=.
  apply regexp_lt_lt.
  rewrite /=.
  by omega.
- have H_eq: append (String c' "") s' = String c' s' by [].
  rewrite -H_eq.
  apply s_matches_r_times => //.
  exact: s_matches_r_char.
- move => H_m; inversion H_m; subst.
  inversion H2; subst.
  injection H1 => H_eq.
  by subst.
- move => H_m; inversion H_m; subst.
  inversion H2; subst.
  injection H1 => H_eq H_eq'.
  by subst.
- rewrite /accept_lt /=.
  apply regexp_lt_lt.
  rewrite /=.
  by omega.
- inversion H_r11; subst.
  apply s_matches_r_times => //.
  exact: s_matches_r_plus_1.
- rewrite /accept_lt /=.
  apply regexp_lt_lt.
  rewrite /=.
  by omega.
- inversion H_r12; subst.
  apply s_matches_r_times => //.
  exact: s_matches_r_plus_2.
- move => H_m; inversion H_m; subst.
  inversion H2; subst.
  * contradict H_r11.
    rewrite -H1.
    exact: s_matches_r_times.
  * contradict H_r12.
    rewrite -H1.
    exact: s_matches_r_times.
- rewrite /accept_lt /=.
  by apply regexp_lt_times_lt => /=; omega.
- inversion H_r; subst.
  inversion H3; subst.
  rewrite string_append_assoc.
  apply s_matches_r_times => //.
  exact: s_matches_r_times.
- move => H_s; inversion H_s; subst.
  inversion H2; subst.
  contradict H_r.
  rewrite -string_append_assoc in H1.
  rewrite -H1.
  apply s_matches_r_times => //.
  exact: s_matches_r_times.
Defined.

Definition accept : forall (rs : regexp * string), accept_t rs :=
@well_founded_induction _ _ accept_lt_well_founded accept_t accept_F.
