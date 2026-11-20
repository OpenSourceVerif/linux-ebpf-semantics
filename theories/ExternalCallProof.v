From Coq Require Import List.
From compcert Require Import Integers Values.
From bpf.semantics Require Import ebpfSyntax ebpfState ebpfBinSem.

Import ListNotations.

(** Returning external calls advance by one instruction slot, including when
    execution is in a program selected by an earlier tail call. *)
Lemma external_call_next_pc:
  forall fetch helper addr_map p rs stk code_id tail_call_cnt m
         rs' stk' code_id' tail_call_cnt' m',
    step fetch helper addr_map p
      (TLS_State rs stk code_id tail_call_cnt m) [eBPF_ext_call]
      (TLS_State rs' stk' code_id' tail_call_cnt' m') ->
    rs' PC = Val.offset_ptr (rs PC) Ptrofs.one.
Proof.
  intros fetch helper addr_map p rs stk code_id tail_call_cnt m
         rs' stk' code_id' tail_call_cnt' m' Hstep.
  inversion Hstep; subst.
  - match goal with
    | H : exec_instr_event ?i = [eBPF_ext_call] |- _ =>
        destruct i; discriminate H
    end.
  - reflexivity.
Qed.

(** The complete control-state contract for a returning external call. *)
Theorem external_call_return_control:
  forall fetch helper addr_map p rs stk code_id tail_call_cnt m
         rs' stk' code_id' tail_call_cnt' m',
    step fetch helper addr_map p
      (TLS_State rs stk code_id tail_call_cnt m) [eBPF_ext_call]
      (TLS_State rs' stk' code_id' tail_call_cnt' m') ->
    rs' PC = Val.offset_ptr (rs PC) Ptrofs.one /\
    stk' = stk /\ code_id' = code_id /\ tail_call_cnt' = tail_call_cnt.
Proof.
  intros fetch helper addr_map p rs stk code_id tail_call_cnt m
         rs' stk' code_id' tail_call_cnt' m' Hstep.
  split.
  - eapply external_call_next_pc; exact Hstep.
  - eapply external_call_preserves_control_state; exact Hstep.
Qed.
