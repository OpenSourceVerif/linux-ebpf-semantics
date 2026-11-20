From Coq Require Import ZArith.
From compcert Require Import Integers.
From bpf.semantics Require Import ebpfSyntax ebpfDecoder.

(** Native tail calls may carry a JIT poke descriptor index in the immediate.
    Decoding does not depend on that metadata. *)
Lemma decode_native_tail_call_metadata : forall metadata,
  decode_insn (Byte.repr 0xf5) R0 R0 Ptrofs.zero metadata =
  Some Ptail_call.
Proof. intros. reflexivity. Qed.

(** Accepting metadata must not relax the reserved register fields. *)
Lemma decode_native_tail_call_rejects_dst : forall dst src off metadata,
  dst <> R0 ->
  decode_insn (Byte.repr 0xf5) dst src off metadata = None.
Proof.
  intros dst src off metadata Hdst.
  destruct dst; try contradiction; reflexivity.
Qed.

Lemma decode_native_tail_call_rejects_src : forall dst src off metadata,
  src <> R0 ->
  decode_insn (Byte.repr 0xf5) dst src off metadata = None.
Proof.
  intros dst src off metadata Hsrc.
  destruct dst, src; try contradiction; reflexivity.
Qed.

(** The offset remains a reserved zero field. *)
Lemma decode_native_tail_call_rejects_offset : forall dst src off metadata,
  Ptrofs.signed off <> 0%Z ->
  decode_insn (Byte.repr 0xf5) dst src off metadata = None.
Proof.
  intros dst src off metadata Hoff.
  destruct dst, src; try reflexivity.
  change ((if Z.eqb (Ptrofs.signed off) 0 then Some Ptail_call else None) = None).
  apply Z.eqb_neq in Hoff.
  rewrite Hoff. reflexivity.
Qed.
