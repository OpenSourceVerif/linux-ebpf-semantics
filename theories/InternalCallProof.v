From Coq Require Import ZArith List Lia.
From compcert Require Import Integers Values Memory.
From bpf.semantics Require Import ebpfSyntax ebpfState ebpfBinSem.

Import ListNotations.
Open Scope Z_scope.

(** Internal calls use a signed displacement relative to the next instruction.
    [Ptrofs.repr] makes the pointer-width wrapping explicit. *)
Lemma exec_call_internal_target:
  forall i rs stk code_id tail_call_cnt m rs' stk' code_id' tail_call_cnt' m'
         b ofs,
    rs PC = Vptr b ofs ->
    exec_call_internal i rs stk code_id tail_call_cnt m =
      Next rs' stk' code_id' tail_call_cnt' m' ->
    rs' PC = Vptr b (Ptrofs.repr (Ptrofs.unsigned ofs + 1 + Int.signed i)).
Proof.
  intros i rs stk code_id tail_call_cnt m rs' stk' code_id' tail_call_cnt' m'
         b ofs Hpc Hcall.
  unfold exec_call_internal in Hcall.
  destruct (Mem.alloc m 0 bpf_stack_size) as [allocated frame].
  inversion Hcall; subst; clear Hcall.
  rewrite Pregmap.gso by discriminate.
  rewrite Pregmap.gss, Hpc.
  cbn [Val.offset_ptr].
  f_equal.
  unfold Ptrofs.add, Ptrofs.of_ints.
  rewrite Ptrofs.unsigned_one.
  apply Ptrofs.eqm_samerepr.
  replace (Ptrofs.unsigned ofs + 1 + Int.signed i)
    with ((Ptrofs.unsigned ofs + Int.signed i) + 1) by lia.
  apply Ptrofs.eqm_add; [|apply Ptrofs.eqm_refl].
  apply Ptrofs.eqm_unsigned_repr_l.
  apply Ptrofs.eqm_add; [apply Ptrofs.eqm_refl|].
  apply Ptrofs.eqm_sym, Ptrofs.eqm_unsigned_repr.
Qed.

(** Execute the actual call implementation from PC 10, including frame
    allocation. The zero and forward cases preserve the existing next-instruction
    increment; the backward case detects unsigned interpretation of a negative
    call displacement. *)
Local Definition call_pc_from_ten (displacement: Z): val :=
  let rs := Pregmap.set PC (Vptr 1%positive (Ptrofs.repr 10))
                       (Pregmap.init Vundef) in
  match exec_call_internal (Int.repr displacement) rs [] None 0 Mem.empty with
  | Next rs' _ _ _ _ => rs' PC
  | Stuck => Vundef
  end.

Example internal_call_zero_offset:
  call_pc_from_ten 0 = Vptr 1%positive (Ptrofs.repr 11).
Proof. vm_compute. reflexivity. Qed.

Example internal_call_forward_offset:
  call_pc_from_ten 3 = Vptr 1%positive (Ptrofs.repr 14).
Proof. vm_compute. reflexivity. Qed.

Example internal_call_backward_offset:
  call_pc_from_ten (-5) = Vptr 1%positive (Ptrofs.repr 6).
Proof. vm_compute. reflexivity. Qed.
