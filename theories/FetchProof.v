From Coq Require Import List ZArith.
From compcert Require Import Integers Values Memory.
From bpf.semantics Require Import ebpfSyntax ebpfState ebpfBinSem.

(** The fetch premises select exactly the program named by [code_id]. *)
Lemma selected_code_spec : forall p code_id c,
    (code_id = None -> c = main_code p) ->
    (forall idx, code_id = Some idx -> jump_table p idx = Some c) ->
    find_code code_id p = Some c.
Proof.
  intros p [idx|] c Hmain Hjump; simpl.
  - apply Hjump. reflexivity.
  - rewrite (Hmain eq_refl). reflexivity.
Qed.

(** This covers both ordinary instructions and external calls. *)
Theorem step_fetches_active_program :
  forall fetch helper addr_map p rs stk code_id cnt m et s',
    step fetch helper addr_map p (TLS_State rs stk code_id cnt m) et s' ->
    exists c b ofs i,
      find_code code_id p = Some c /\
      rs PC = Vptr b ofs /\
      fetch (Ptrofs.unsigned ofs) c = Some i.
Proof.
  intros fetch helper addr_map p rs stk code_id cnt m et s' Hstep.
  inversion Hstep; subst.
  all: do 4 eexists; split; [eapply selected_code_spec; eassumption|].
  all: split; eassumption.
Qed.

Theorem atomic_step_fetches_active_program :
  forall fetch p rs stk code_id cnt m et s',
    atomic_step fetch p (TLS_State rs stk code_id cnt m) et s' ->
    exists c b ofs i,
      find_code code_id p = Some c /\
      rs PC = Vptr b ofs /\
      fetch (Ptrofs.unsigned ofs) c = Some i.
Proof.
  intros fetch p rs stk code_id cnt m et s' Hstep.
  inversion Hstep; subst.
  do 4 eexists; split; [eapply selected_code_spec; eassumption|].
  split; eassumption.
Qed.

(** A missing jump-table entry cannot be bypassed by choosing another index. *)
Corollary missing_active_program_no_step :
  forall fetch helper addr_map p rs stk code_id cnt m et s',
    find_code code_id p = None ->
    ~ step fetch helper addr_map p (TLS_State rs stk code_id cnt m) et s'.
Proof.
  intros fetch helper addr_map p rs stk code_id cnt m et s' Hmissing Hstep.
  destruct (step_fetches_active_program _ _ _ _ _ _ _ _ _ _ _ Hstep)
    as (c & b & ofs & i & Hcode & _).
  congruence.
Qed.

Corollary missing_active_program_no_atomic_step :
  forall fetch p rs stk code_id cnt m et s',
    find_code code_id p = None ->
    ~ atomic_step fetch p (TLS_State rs stk code_id cnt m) et s'.
Proof.
  intros fetch p rs stk code_id cnt m et s' Hmissing Hstep.
  destruct (atomic_step_fetches_active_program _ _ _ _ _ _ _ _ _ Hstep)
    as (c & b & ofs & i & Hcode & _).
  congruence.
Qed.
