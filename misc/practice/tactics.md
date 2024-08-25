intros n
intros n m
revert m
revert n m
induction n
destruct n
simpl
simpl in H
simpl in *
reflexivity
rewrite plus_comm
rewrite IHn
rewrite plus_comm in H
constructor (on goal True)
destruct H (on H : False)
discriminate
injection in H as H'
apply plus_comm
apply plus_comm in H
apply H
apply H in H'
split (on goal P /\ Q)
destruct H (on H : P /\ Q)
destruct H (on H : P \/ Q)
left
right
