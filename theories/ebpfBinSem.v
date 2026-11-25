From Coq Require Import List.

(** Abstract syntax and semantics for RISC-V assembly language. *)

From compcert Require Import Coqlib Ctypes AST Integers.
From compcert Require Import Maps Values Memory.  (*
From compcert.common Require Import Globalenvs. *) (*
From compcert Require Import Locations. *)

From compcert Require Import Conventions Events Smallstep.
From compcert Require Stacklayout.
From compcert Require Import Op.

From bpf.semantics Require Import GlobalSem ebpfSyntax ebpfState ebpfHelper.

Import ListNotations.


(** Regions are nonempty, representable, nonwrapping half-open intervals. *)
Definition address_region_valid (r: addr_region): bool :=
  (0 <? size_blk r) && (size_blk r <=? Ptrofs.modulus) &&
  (Int64.unsigned (base_addr r) + size_blk r <=? Int64.modulus).

Fixpoint find_address_region (b: block) (regions: list addr_region): option addr_region :=
  match regions with
  | [] => None
  | r :: rest => if Pos.eqb (base_blk r) b then Some r
                 else find_address_region b rest
  end.

Definition region_pointer (word: int64) (r: addr_region): option val :=
  let offset := Int64.unsigned word - Int64.unsigned (base_addr r) in
  if address_region_valid r && (0 <=? offset) && (offset <? size_blk r)
  then Some (Vptr (base_blk r) (Ptrofs.repr offset)) else None.

(** Reverse conversion rejects one-past and out-of-region offsets. *)
Definition cast_address_abs_to_concrete (ptr: val) (regions: list addr_region): option int64 :=
  match ptr with
  | Vptr b ofs =>
      match find_address_region b regions with
      | None => None
      | Some r =>
          let offset := Ptrofs.unsigned ofs in
          if address_region_valid r && (offset <? size_blk r)
          then Some (Int64.repr (Int64.unsigned (base_addr r) + offset))
          else None
      end
  | _ => None
  end.

(** A stack top is an address boundary, not a dereferenceable pointer.
    Construct it explicitly; do not weaken reverse conversion to admit it. *)
Definition stack_top_word (b: block) (size: Z) (regions: list addr_region): option int64 :=
  match find_address_region b regions with
  | Some r =>
      let top := Int64.unsigned (base_addr r) + size in
      if address_region_valid r && (size_blk r =? size) && (top <? Int64.modulus)
      then Some (Int64.repr top) else None
  | None => None
  end.

(** Ignore unallocated or freed regions, including reserved future stack frames.
    Mem.load/store still check the full access width, alignment and permissions. *)
Fixpoint word_pointer_candidates (m: mem) (word: int64)
    (regions: list addr_region): list val :=
  match regions with
  | [] => []
  | r :: rest =>
      let candidates := word_pointer_candidates m word rest in
      match region_pointer word r with
      | Some (Vptr b ofs) =>
          if Mem.valid_pointer m b (Ptrofs.unsigned ofs)
          then Vptr b ofs :: candidates else candidates
      | _ => candidates
      end
  end.

(** Ambiguous live mappings are rejected, never resolved by list order. *)
Definition cast_i2p (m: mem) (word: int64) (regions: list addr_region): option val :=
  match word_pointer_candidates m word regions with
  | [ptr] => Some ptr
  | _ => None
  end.

Definition add_word_offset (v: val) (ofs: ptrofs): val :=
  Val.addl v (Vlong (Int64.repr (Ptrofs.signed ofs))).

Definition resolve_address (m: mem) (v: val) (ofs: ptrofs)
    (regions: list addr_region): option val :=
  match add_word_offset v ofs with
  | Vlong word => cast_i2p m word regions
  | _ => None
  end.

(** Normalize complete values at memory and external-call boundaries.
    Undefined values remain undefined; no pointer enters the register file. *)
Definition register_word (v: val) (regions: list addr_region): option val :=
  match v with
  | Vlong _ | Vundef => Some v
  | Vint i => Some (Vlong (Int64.repr (Int.unsigned i)))
  | Vptr _ _ =>
      match cast_address_abs_to_concrete v regions with
      | Some word => Some (Vlong word) | None => None
      end
  | _ => None
  end.

Section RELSEM.

(** Looking up instructions in a code sequence by position. *)
Variable find_instr: Z -> code -> option instruction.

(*
Variable ge: genv.
Fixpoint find_instr (pos: Z) (c: code) {struct c} : option instruction :=
  match c with
  | nil => None
  | i :: il => if zeq pos 0 then Some i else find_instr (pos - 1) il
  end. *)

  (*
(** Position corresponding to a label *)

Definition is_label (lbl: label) (instr: instruction) : bool :=
  match instr with
  | Plabel lbl' => if peq lbl lbl' then true else false
  | _ => false
  end.

Lemma is_label_correct:
  forall lbl instr,
  if is_label lbl instr then instr = Plabel lbl else instr <> Plabel lbl.
Proof.
  intros.  destruct instr; simpl; try discriminate.
  case (peq lbl lbl0); intro; congruence.
Qed.

Fixpoint label_pos (lbl: label) (pos: Z) (c: code) {struct c} : option Z :=
  match c with
  | nil => None
  | instr :: c' =>
      if is_label lbl instr then Some (pos + 1) else label_pos lbl (pos + 1) c'
  end.
*)


(**r give an immediate number for function ID, plus R1-R5 values as well as the current memory,
  returns a value for R0 and a new global mem *)
Variable ebpf_call_function:
  imm -> val -> val -> val -> val -> val -> outcome -> option (val * mem).

(** Resolve original static helper IDs using program/code identity and the
    final instruction offset.  CALL immediates may already be relocated.
    A validator must supply this mapping from checked capture metadata. *)
Variable helper_id_at: ebpf_prog -> option nat -> Z -> option Z.


(** Advance the numeric slot PC by one. *)
Definition nextinstr (rs: regset) :=
  rs#PC <- (Val.addl rs#PC (Vlong Int64.one)).



Definition int64_of_int (i:int) := Int64.repr (Int.signed i).
Definition int_of_int64 (i:int64) := Int.repr (Int64.signed i).

Definition map_sum_left {A B A': Type} (F: A -> A')  (x: A+B) : A'+B :=
  match x with
  | inl i => inl (F i)
  | inr i => inr i
  end.

(**
   https://docs.cilium.io/en/latest/bpf/architecture/#instruction-set
 imm(ediate) is of signed type *)

Definition eval_reg_immw (w:width) (rs : regset) (ri: ireg+int) : val :=
  match ri with
  | inl i =>
    match w with
    | W32 => match rs i with | Vlong i => Vint (Int.repr (Int64.unsigned i)) | _ => Vundef end
    | W64 => rs i
    end
  | inr i =>
    match w with
    | W32 => Vint i
    | W64 => Vlong (int64_of_int i)
    end
  end.

Definition eval_val_int (w:width)  (ri: val+int) : val :=
  match ri with
  | inl i => i (** we assume each eBPF register is 64-bit: i.e. Vlong or Vundef *)
  | inr i => match w with
             | W32 => Vint i
             | W64 => Vlong (int64_of_int i)
                            (* constant are given a signed interpretation *)
             end
  end.

(** RFC9669: 4.1. Arithmetic Instructions 
      DIV 0x3 0 dst = (src != 0) ? (dst / src) : 0
      SDIV 0x3 1 dst = (src != 0) ? (dst s/ src) : 0

    fix: linux-doc-bpf
      DIV    0x3    0        dst = (src != 0) ? (dst / src) : 0
      SDIV   0x3    1        dst = (src == 0) ? 0 : ((src == -1 && dst == LLONG_MIN) ? LLONG_MIN : (dst s/ src))
  *)
  
Definition LLONG_MIN := Vlong (Int64.repr Int64.min_signed).
Definition INT_MIN := Vint (Int.repr Int.min_signed).

Definition eval_div_u32 (v1 v2:val) : val :=
  match Val.divu v1 v2 with
  | Some res => res
  | None => if Val.eq v2 Vzero then Vzero else Vundef
  end.

Definition eval_div_s32 (v1 v2:val) : val :=
  match Val.divs v1 v2 with
  | Some res => res
  | None =>
    if Val.eq v2 Vzero then Vzero
    else if (Val.eq v2 (Vint Int.mone)) && (Val.eq v1 INT_MIN) then INT_MIN
    else Vundef
  end.

Definition eval_div_u64 (v1 v2:val) : val :=
  match Val.divlu v1 v2 with
  | Some res => res
  | None => if Val.eq v2 (Vlong Int64.zero) then Vlong Int64.zero else Vundef
  end.

Definition eval_div_s64 (v1 v2:val) : val :=
  match Val.divls v1 v2 with
  | Some res => res
  | None =>
    if Val.eq v2 (Vlong Int64.zero) then  Vlong Int64.zero
    else if (Val.eq v2 (Vlong Int64.mone)) && (Val.eq v1 LLONG_MIN) then LLONG_MIN 
    else Vundef 
  end.

(** RFC9669: 4.1. Arithmetic Instructions 
      MOD 0x9 0 dst = (src != 0) ? (dst % src) : dst
      SMOD 0x9 1 dst = (src != 0) ? (dst s% src) : dst

    fix: linux-doc-bpf
      MOD    0x9    0        dst = (src != 0) ? (dst % src) : dst
      SMOD   0x9    1        dst = (src == 0) ? dst : ((src == -1 && dst == LLONG_MIN) ? 0: (dst s% src))
  *)
Definition eval_mod_u32 (v1 v2:val) : val :=
  match Val.modu v1 v2 with
  | Some res => res
  | None => if Val.eq v2 Vzero then v1 else (** unreachable *) Vundef
  end.

Definition eval_mod_s32 (v1 v2:val) : val :=
  match Val.mods v1 v2 with
  | Some res => res
  | None =>
    if Val.eq v2 Vzero then v1 
    else if (Val.eq v2 (Vint Int.mone)) && (Val.eq v1 INT_MIN) then Vzero
    else (** unreachable *) Vundef
  end.

Definition eval_mod_u64 (v1 v2:val) : val :=
  match Val.modlu v1 v2 with
  | Some res => res
  | None => if Val.eq v2 (Vlong Int64.zero) then v1 else (** unreachable *) Vundef
  end.

Definition eval_mod_s64 (v1 v2:val) : val :=
  match Val.modls v1 v2 with
  | Some res => res
  | None =>
    if Val.eq v2 (Vlong Int64.zero) then v1
    else if (Val.eq v2 (Vlong Int64.mone)) && (Val.eq v1 LLONG_MIN) then Vlong Int64.zero
    else (** unreachable *) Vundef
  end.

  (** RFC9669: 4.1. Arithmetic Instructions
      LSH 0x6 0 dst <<= (src & mask)
      RSH 0x7 0 dst >>= (src & mask)
      ARSH 0xc 0 sign extending (Section 2.3) dst >>= (src & mask)

    Note that: In the Coq formalization, we select to do mask for all ebPF shift instruction because the eBPF verifier guarantee the imm-based eBPF shift range checking.
    
    - In the core.c, it doesn't require the mask operations for the imm-based eBPF shift
    ```c
    // https://elixir.bootlin.com/linux/v6.17-rc4/source/kernel/bpf/core.c#L1790
    #define SHT(OPCODE, OP)					\
      ALU64_##OPCODE##_X:				\
        DST = DST OP (SRC & 63);		\
        CONT;					\
      ALU_##OPCODE##_X:				\
        DST = (u32) DST OP ((u32) SRC & 31);	\
        CONT;					\
      ALU64_##OPCODE##_K:				\
        DST = DST OP IMM;			\
        CONT;					\
      ALU_##OPCODE##_K:				\
        DST = (u32) DST OP (u32) IMM;		\
        CONT;
    ``` 
    - But the verifier.c statically checks the range of imm-based shift value.
    ```c
    //https://elixir.bootlin.com/linux/v6.17-rc4/source/kernel/bpf/verifier.c#L15770
    		if ((opcode == BPF_LSH || opcode == BPF_RSH ||
		     opcode == BPF_ARSH) && BPF_SRC(insn->code) == BPF_K) {
			int size = BPF_CLASS(insn->code) == BPF_ALU64 ? 64 : 32;

			if (insn->imm < 0 || insn->imm >= size) {
				verbose(env, "invalid shift %d\n", insn->imm);
				return -EINVAL;
			}
		}
    ```
  *)
Definition eval_shift_mask (w:width) (v1:val) : val :=
  match w with
  | W32 => Val.and v1 (Vint (Int.repr 31%Z))
  | W64 => match v1 with
           | Vlong vl => Val.and (Vint (int_of_int64 vl)) (Vint (Int.repr 63%Z))
           | _ => Vundef
           end
  end.

(** RFC9669: 4.1. Arithmetic Instructions 
      MOV 0xb 0 dst = src
      MOVSX 0xb 8/16/32 dst = (s8,s16,s32)src
  *)
Definition eval_movsx (w:width) (c: signExtOp) (v2 :val) : val :=
  match w with
  | W32 => Val.longofintu (Val.sign_ext (signExtOp2Z c) v2)
  | W64 => Val.sign_ext_l (signExtOp2Z c) v2
  end.

(** RFC9669: 4.1. Arithmetic Instructions
      END 0xd 0 byte swap operations (see Section 4.2)
  *)
Definition swab16 (i: int64): int64 :=
  let i0 := Int64.unsigned_bitfield_extract 0 8 i in
  let i1 := Int64.unsigned_bitfield_extract 8 8 i in
    Int64.bitfield_insert 8 8 i1 i0.

(*
Compute (swab16 (Int64.repr 0x3412)). (**r 4660 *)
Compute 0x1234. (**r 4660 *)
Compute 0x3412. (**r 13330 *) *)

Definition swab32 (i: int64): int64 :=
  let i0 := Int64.unsigned_bitfield_extract 0 8 i in
  let i1 := Int64.unsigned_bitfield_extract 8 8 i in
  let i2 := Int64.unsigned_bitfield_extract 16 8 i in
  let i3 := Int64.unsigned_bitfield_extract 24 8 i in
    Int64.bitfield_insert 24 8
      (Int64.bitfield_insert 16 8
        (Int64.bitfield_insert 8 8 i3 i2) i1) i0.

(*
Compute (swab32 (Int64.repr 0x12345678)). (**r 2018915346 *)
Compute 0x12345678. (**r 305419896 *)
Compute 0x78563412. (**r 2018915346 *) *)

Definition swab64 (i: int64): int64 :=
  let i0 := Int64.unsigned_bitfield_extract 0 8 i in
  let i1 := Int64.unsigned_bitfield_extract 8 8 i in
  let i2 := Int64.unsigned_bitfield_extract 16 8 i in
  let i3 := Int64.unsigned_bitfield_extract 24 8 i in
  let i4 := Int64.unsigned_bitfield_extract 32 8 i in
  let i5 := Int64.unsigned_bitfield_extract 40 8 i in
  let i6 := Int64.unsigned_bitfield_extract 48 8 i in
  let i7 := Int64.unsigned_bitfield_extract 56 8 i in
    Int64.bitfield_insert 56 8
      (Int64.bitfield_insert 48 8
        (Int64.bitfield_insert 40 8
          (Int64.bitfield_insert 32 8
            (Int64.bitfield_insert 24 8
              (Int64.bitfield_insert 16 8
                (Int64.bitfield_insert 8 8 i7 i6) i5) i4) i3) i2) i1) i0.

(*
Compute (swab64 (Int64.repr 0x1234567890abcdef)). (**r 17279655982273016850 *)
Compute 0x1234567890abcdef. (**r 1311768467294899695 *)
Compute 0xefcdab9078563412. (**r 17279655982273016850 *) *)

Definition swapn (s: endSize) :=
  match s with
  | S16 => swab16
  | S32 => swab32
  | S64 => swab64
  end.

Definition eval_end_trunction (s: endSize) (v: int64) : int64 :=
  match s with
  | S16 => Int64.zero_ext 16 v
  | S32 => Int64.zero_ext 32 v
  | S64 => v
  end.

Definition eval_end (e:endOp) (s: endSize) (v: val) : val :=
  let eval (vl: int64) :=
    match e with
    | LE32 => if Archi.big_endian then (swapn s) vl else eval_end_trunction s vl
    | BE32 => if Archi.big_endian then eval_end_trunction s vl else (swapn s) vl
    | LE64 => (swapn s) vl
    end in
  match v with
  | Vlong vl => Vlong (eval vl)
  | Vint vi => Vlong (eval (Int64.repr (Int.unsigned vi)))
  | _ => Vundef
  end.

(** Evaluation of [Palu] operands *)
Definition eval_alu32 (op: aluOp) (v1: val) (v2: val+int) : val :=
  let dst := Val.loword v1 in
  let src := match v2 with | inl r => Val.loword r | inr i => Vint i end in
    match op with
    | ADD   => Val.longofintu (Val.add dst src)
    | SUB   => Val.longofintu (Val.sub dst src)
    | MUL   => Val.longofintu (Val.mul dst src)
    | DIV   => Val.longofintu (eval_div_u32 dst src)
    | SDIV  => Val.longofintu (eval_div_s32 dst src)
    | OR    => Val.longofintu (Val.or dst src)
    | AND   => Val.longofintu (Val.and dst src)
    | LSH   => Val.longofintu (Val.shl dst (eval_shift_mask W32 src))
    | RSH   => Val.longofintu (Val.shru dst (eval_shift_mask W32 src))
    | NEG   => Val.longofintu (Val.neg dst)
    | MOD   => Val.longofintu (eval_mod_u32 dst src)
    | SMOD  => Val.longofintu (eval_mod_s32 dst src)
    | XOR   => Val.longofintu (Val.xor  dst src)
    | MOV   => Val.longofintu src
    | MOVSX c => eval_movsx W32 c src
    | ARSH  => Val.longofintu (Val.shr dst (eval_shift_mask W32 src))
    | END e s => eval_end e s dst
    end.

Definition eval_alu64 (op: aluOp) (dst: val) (v2: val+int) : val :=
  let src := eval_val_int W64 v2 in
  match op with
  | ADD   => Val.addl dst src
  | SUB   => Val.subl dst src
  | MUL   => Val.mull dst src
  | DIV   => eval_div_u64 dst src
  | SDIV  => eval_div_s64 dst src
  | OR    => Val.orl dst src
  | AND   => Val.andl dst src
  | LSH   => Val.shll dst (eval_shift_mask W64 src)
  | RSH   => Val.shrlu dst (eval_shift_mask W64 src)
  | NEG   => Val.negl dst
  | MOD   => eval_mod_u64 dst src
  | SMOD  => eval_mod_s64 dst src
  | XOR   => Val.xorl dst src
  | MOV   => src
  | MOVSX c => eval_movsx W64 c src
  | ARSH  => Val.shrl dst (eval_shift_mask W64 src)
  | END e s => eval_end e s dst
  end.

Definition exec_alu (op: aluOp) (w:width) (r: ireg) (ri: ireg+int) (rs: regset) (c_stk: cstk) (code_id: option nat) (tail_call_cnt: nat) (m: mem) :=
  let alu_f := match w with | W32 => eval_alu32 | W64 => eval_alu64 end in
  let v :=
    match ri with
    | inl src =>
      if ireg_eqb r src then
        match op with
        | SUB | XOR => Vlong Int64.zero
        | _ => alu_f op (rs#r) (inl (rs#src))
        end
      else alu_f op (rs#r) (inl (rs#src))
    | inr i => alu_f op (rs#r) (inr i)
    end in
    Next (nextinstr (rs#r <- v)) c_stk code_id tail_call_cnt m.

(** RFC9669: 4.3. Jump Instructions

  ========  =====  =======  =================================  ===================================================
  code      value  src_reg  description                        notes
  ========  =====  =======  =================================  ===================================================
  JA        0x0    0x0      PC += offset                       {JA, K, JMP} only
  JA        0x0    0x0      PC += imm                          {JA, K, JMP32} only
  JEQ       0x1    any      PC += offset if dst == src
  JGT       0x2    any      PC += offset if dst > src          unsigned
  JGE       0x3    any      PC += offset if dst >= src         unsigned
  JSET      0x4    any      PC += offset if dst & src
  JNE       0x5    any      PC += offset if dst != src
  JSGT      0x6    any      PC += offset if dst > src          signed
  JSGE      0x7    any      PC += offset if dst >= src         signed
  JLT       0xa    any      PC += offset if dst < src          unsigned
  JLE       0xb    any      PC += offset if dst <= src         unsigned
  JSLT      0xc    any      PC += offset if dst < src          signed
  JSLE      0xd    any      PC += offset if dst <= src         signed
  ========  =====  =======  =================================  ===================================================
*)
Definition eval_cmp32 (op: cmpOp) (rs: regset) (m: mem) (r: ireg) (ri: ireg+imm) : option bool :=
  let dst := Val.loword (rs#r) in
  let src := match ri with | inl r => Val.loword (rs#r) | inr i => Vint i end in
    match op with
    | EQ          => Val.cmpu_bool (Mem.valid_pointer m) Ceq dst src
    | GT Signed   => Val.cmp_bool Cgt dst src
    | GT Unsigned => Val.cmpu_bool (Mem.valid_pointer m) Cgt dst src
    | GE Signed   => Val.cmp_bool Cge dst src
    | GE Unsigned => Val.cmpu_bool (Mem.valid_pointer m) Cge dst src
    | LT Signed   => Val.cmp_bool Clt dst src
    | LT Unsigned => Val.cmpu_bool (Mem.valid_pointer m) Clt dst src
    | LE Signed   => Val.cmp_bool Cle dst src
    | LE Unsigned => Val.cmpu_bool (Mem.valid_pointer m) Cle dst src
    | SET         => Val.cmpu_bool (Mem.valid_pointer m) Cne (Val.and dst src) (Vint Int.zero)
    | NE          => Val.cmpu_bool (Mem.valid_pointer m) Cne dst src
    end.

Definition eval_cmp64 (op: cmpOp) (rs: regset) (m: mem) (r: ireg) (ri: ireg+imm) : option bool :=
  let dst := rs#r in
  let src := match ri with | inl r => rs#r | inr i => Vlong (int64_of_int i) end in
    match op with
    | EQ          => Val.cmplu_bool (Mem.valid_pointer m) Ceq dst src
    | GT Signed   => Val.cmpl_bool Cgt dst src
    | GT Unsigned => Val.cmplu_bool (Mem.valid_pointer m) Cgt dst src
    | GE Signed   => Val.cmpl_bool Cge dst src
    | GE Unsigned => Val.cmplu_bool (Mem.valid_pointer m) Cge dst src
    | LT Signed   => Val.cmpl_bool Clt dst src
    | LT Unsigned => Val.cmplu_bool (Mem.valid_pointer m) Clt dst src
    | LE Signed   => Val.cmpl_bool Cle dst src
    | LE Unsigned => Val.cmplu_bool (Mem.valid_pointer m) Cle dst src
    | SET         => Val.cmplu_bool (Mem.valid_pointer m) Cne (Val.andl dst src) (Vlong Int64.zero)
    | NE          => Val.cmplu_bool (Mem.valid_pointer m) Cne dst src
    end.

Definition exec_jmp32 (i: imm) (rs: regset) (c_stk: cstk) (code_id: option nat) (tail_call_cnt: nat) (m: mem) :=
  Next (nextinstr (rs#PC <- (Val.addl (rs PC) (Vlong (Int64.repr (Int.signed i)))))) c_stk code_id tail_call_cnt m.

Definition exec_jmp64 (o: off) (rs: regset) (c_stk: cstk) (code_id: option nat) (tail_call_cnt: nat) (m: mem) :=
  Next (nextinstr (rs#PC <- (add_word_offset (rs PC) o))) c_stk code_id tail_call_cnt m.

Definition eval_cmp_static (op: cmpOp) (w: width) (r: ireg) (ri: ireg+imm) : option bool :=
  match ri with
  | inl src =>
    if ireg_eqb r src then
      match op with
      | EQ | GE _ | LE _ => Some true
      | NE | GT _ | LT _ => Some false
      | SET => None
      end
    else None
  | inr i =>
    match w, op with
    | W32, GT Signed =>
      if Int.eq i (Int.repr Int.max_signed) then Some false else None
    | W32, GE Signed =>
      if Int.eq i (Int.repr Int.min_signed) then Some true else None
    | W32, LT Signed =>
      if Int.eq i (Int.repr Int.min_signed) then Some false else None
    | W32, LE Signed =>
      if Int.eq i (Int.repr Int.max_signed) then Some true else None
    | W32, GT Unsigned => if Int.eq i Int.mone then Some false else None
    | W32, GE Unsigned => if Int.eq i Int.zero then Some true else None
    | W32, LT Unsigned => if Int.eq i Int.zero then Some false else None
    | W32, LE Unsigned => if Int.eq i Int.mone then Some true else None
    | W64, GT Unsigned => if Int.eq i Int.mone then Some false else None
    | W64, GE Unsigned => if Int.eq i Int.zero then Some true else None
    | W64, LT Unsigned => if Int.eq i Int.zero then Some false else None
    | W64, LE Unsigned => if Int.eq i Int.mone then Some true else None
    | _, _ => None
    end
  end.

Definition exec_jmpcmp (op: cmpOp) (w: width) (r: ireg) (ri: ireg+imm) (o: off) (rs: regset) (c_stk: cstk) (code_id: option nat) (tail_call_cnt: nat) (m: mem) :=
  match
    match eval_cmp_static op w r ri with
    | Some cond => Some cond
    | None =>
      match w with
      | W32 => eval_cmp32 op rs m r ri
      | W64 => eval_cmp64 op rs m r ri
      end
    end with
  | None => Stuck
  | Some cond => 
    let rs' := if cond then rs#PC <- (add_word_offset (rs PC) o) else rs in
      Next (nextinstr rs') c_stk code_id tail_call_cnt m
  end.

(** Auxiliaries for memory accesses *)

(*Definition size_to_memory_chunk (size: sizeOp) : memory_chunk :=
  match size with
  | Byte => Mint8unsigned
  | HalfWord => Mint16unsigned
  | Word => Many32
  | SignedWord => Mint32
  end.
 *)

 
Definition loadv_unaligned (chunk: memory_chunk) (m: mem) (addr: val) : option val :=
  match addr with
  | Vptr b ofs =>
    match Mem.loadbytes m b (Ptrofs.unsigned ofs) (size_chunk chunk) with
    | Some bytes => Some (decode_val chunk bytes)
    | None => None
    end
  | _ => None
  end.

Definition storev_unaligned (chunk: memory_chunk) (m: mem) (addr v: val) : option mem :=
  match addr with
  | Vptr b ofs => Mem.storebytes m b (Ptrofs.unsigned ofs) (encode_val chunk v)
  | _ => None
  end.

Definition load (k: sizeOp) (addr:val) (m: mem) :=
  match k with
  | Byte      => loadv_unaligned Mint8unsigned m addr
  | HalfWord  => loadv_unaligned Mint16unsigned m addr
  | Word      => loadv_unaligned Mint32 m addr
  | DBWord    => loadv_unaligned Mint64 m addr
  (* if Archi.ptr64 then Mem.loadv Mint64 m addr else None *)
  end.

Definition load_value_casting (v: val): val :=
  match v with
  | Vint i => Vlong (Int64.repr (Int.unsigned i))
  | _ => v
  end.

Definition load_value_sx_casting (v: val): val :=
  match v with
  | Vint i => Vlong (Int64.repr (Int.signed i))
  | _ => v
  end.

Definition load_result (signed: bool) (v: val) (addr_map: list addr_region): option val :=
  register_word
    (if signed then load_value_sx_casting v else load_value_casting v)
    addr_map.

Definition exec_memory_load (read: sizeOp -> val -> mem -> option val)
    (signed probe: bool) (k: sizeOp) (r r': ireg) (o: off)
    (rs: regset) (c_stk: cstk) (code_id: option nat) (tail_call_cnt: nat)
    (m: mem) (addr_map: list addr_region): outcome :=
  let loaded := match resolve_address m (rs r') o addr_map with
                | Some addr => read k addr m | None => None end in
  match loaded with
  | None => if probe then
      Next (nextinstr (rs#r <- (Vlong Int64.zero))) c_stk code_id tail_call_cnt m
      else Stuck
  | Some v => match load_result signed v addr_map with
      | Some word => Next (nextinstr (rs#r <- word)) c_stk code_id tail_call_cnt m
      | None => Stuck
      end
  end.

Definition exec_load := exec_memory_load load false false.
Definition exec_load_probe := exec_memory_load load false true.

Definition loadsx (k: sizeOp) (addr:val) (m: mem) :=
  match k with
  | Byte      => loadv_unaligned Mint8signed m addr
  | HalfWord  => loadv_unaligned Mint16signed m addr
  | Word      => loadv_unaligned Mint32 m addr
  | DBWord    => None
  (* if Archi.ptr64 then Mem.loadv Mint64 m addr else None *)
  end.

Definition exec_loadsx := exec_memory_load loadsx true false.
Definition exec_loadsx_probe (k: sizeOp) :=
  match k with
  | DBWord => exec_memory_load loadsx true false k
  | _ => exec_memory_load loadsx true true k
  end.

Definition store (k: sizeOp) (addr:val) (v:val) (m: mem) :=
  match k with
  | Byte      => storev_unaligned Mint8unsigned m addr v
  | HalfWord  => storev_unaligned Mint16unsigned m addr v
  | Word      => storev_unaligned Mint32 m addr v
  | DBWord    => storev_unaligned Mint64 m addr v
  (*if Archi.ptr64 then Mem.storev Mint64 m addr v else None *)
  end.

Definition exec_store (k: sizeOp) (r:ireg) (ri:ireg+int) (o:off)
    (rs: regset) (c_stk: cstk) (code_id: option nat) (tail_call_cnt: nat)
    (m: mem) (addr_map: list addr_region): outcome :=
  match resolve_address m (rs r) o addr_map with
  | None => Stuck
  | Some addr =>
      match store k addr (eval_reg_immw (sizew k) rs ri) m with
      | None => Stuck
      | Some m' => Next (nextinstr rs) c_stk code_id tail_call_cnt m'
      end
  end.

(** Immediates, including already resolved pseudo addresses, remain words.
    Resolving a map FD or index is a separate loader/environment obligation. *)
Definition exec_lddw (r:ireg) (lo hi: imm) (rs: regset) (c_stk: cstk)
    (code_id: option nat) (tail_call_cnt: nat) (m: mem) : outcome :=
  Next (nextinstr (nextinstr (rs#r <- (Vlong (Int64.ofwords hi lo)))))
    c_stk code_id tail_call_cnt m.

(** Undefine all ebpf caller-saved registers: i.e. R1 to R5 *)
Definition undef_caller_save_regs (rs: regset) : regset :=
  fun r =>
    match r with
    | R1 | R2 | R3 | R4 | R5 => Vundef
    | _ => rs r
    end.

(** Check a helper transition against its precondition and postcondition.
    For trace validation, the caller supplies both memories in a shared
    block layout, using the observed bytes of a single call. *)
Inductive exec_helper (addr_map: list addr_region) (id: Z) (result: val) (rs: regset) (stk: cstk)
    (code_id: option nat) (tail_call_cnt: nat) (m m': mem): outcome -> Prop :=
  | exec_helper_intro: forall spec word,
      find_helper id = Some spec ->
      helper_pre_holds spec rs m = true ->
      helper_post_holds spec rs m result m' ->
      register_word result addr_map = Some word ->
      exec_helper addr_map id result rs stk code_id tail_call_cnt m m'
        (Next (nextinstr ((undef_caller_save_regs rs)#R0 <- word))
          stk code_id tail_call_cnt m').

(** Undefine all ebpf registers except caller-saved registers (i.e. R1 to R5) and R10 *)
Definition def_caller_save_regs (rs: regset) : regset :=
  fun r =>
    match r with
    | R1 | R2 | R3 | R4 | R5 (* | R10 | BP *) => rs r
    | _ => Vundef
    end.

(** Each frame has 512 bytes of data. Return PC and saved register words
    live in cstk, not in the program-visible memory. *)
Definition bpf_stack_size: Z := 512%Z.



(** The address environment reserves a region for each allocated frame.
    Missing layout information causes Stuck rather than inventing an address. *)
Definition exec_call_internal (i: imm) (rs: regset) (c_stk: cstk)
    (code_id: option nat) (tail_call_cnt: nat) (m: mem)
    (addr_map: list addr_region): outcome :=
  let (m', frame) := Mem.alloc m 0 bpf_stack_size in
  match stack_top_word frame bpf_stack_size addr_map with
  | None => Stuck
  | Some top =>
      let saved := {| stk_ra := Val.addl (rs PC) (Vlong Int64.one);
        stk_r6 := rs R6; stk_r7 := rs R7; stk_r8 := rs R8;
        stk_r9 := rs R9; stk_r10 := rs R10 |} in
      Next ((def_caller_save_regs rs)
        #PC <- (Val.addl (Val.addl (rs PC) (Vlong (Int64.repr (Int.signed i)))) (Vlong Int64.one))
        #R10 <- (Vlong top)) (saved :: c_stk) code_id tail_call_cnt m'
  end.

(** A halted PC is distinct from every numeric slot, including wrapped jumps.
    From a numeric PC, arithmetic cannot manufacture this terminal marker. *)
Definition exec_ret (rs: regset) (c_stk: cstk) (code_id: option nat)
    (tail_call_cnt: nat) (m: mem) (addr_map: list addr_region): outcome :=
  match c_stk with
  | [] => Next (rs#PC <- Vundef) [] code_id tail_call_cnt m
  | saved :: rest =>
      (* R10 is one-past the current frame; resolve its base instead. *)
      let freed :=
        match resolve_address m (rs R10) (Ptrofs.repr (-bpf_stack_size)) addr_map with
        | Some (Vptr frame ofs) =>
            match find_address_region frame addr_map with
            | Some region =>
                if Ptrofs.eq ofs Ptrofs.zero && Z.eqb (size_blk region) bpf_stack_size
                then Mem.free m frame 0 bpf_stack_size else None
            | None => None
            end
        | _ => None
        end in
      match freed with
      | None => Stuck
      | Some m' => Next ((undef_caller_save_regs rs)
          #PC <- (stk_ra saved) #R6 <- (stk_r6 saved) #R7 <- (stk_r7 saved)
          #R8 <- (stk_r8 saved) #R9 <- (stk_r9 saved) #R10 <- (stk_r10 saved))
          rest code_id tail_call_cnt m'
      end
  end.

Definition MAX_TAIL_CALL_CNT: nat := 33.

Definition exec_tail_call (p: ebpf_prog) (rs: regset) (c_stk: cstk) (code_id: option nat) (tail_call_cnt: nat) (m: mem) (addr_map: list addr_region) :=
  match rs R3 with
  | Vlong i =>
    (* The Linux interpreter converts R3 to u32 before the bounds check and lookup. *)
    let index := Int64.zero_ext 32 i in
    match resolve_address m (rs R2) Ptrofs.zero addr_map with
    | None => Stuck
    | Some r2_ptr =>
      match r2_ptr with
      | Vptr b ofs =>
        if (Z.leb (max_entries p) (Int64.unsigned index)) ||
            (Nat.leb MAX_TAIL_CALL_CNT tail_call_cnt)
        then
          Next (nextinstr rs) c_stk code_id tail_call_cnt m
        else
          let next_tail_call_cnt := (tail_call_cnt + 1)%nat in
          match Mem.loadv Mint64 m (Val.offset_ptr r2_ptr (Ptrofs.of_int64u (Int64.mul index (Int64.repr 8%Z)))) with
          | None => Next (nextinstr rs) c_stk code_id next_tail_call_cnt m
          | Some res =>
            match register_word res addr_map with
            | Some (Vlong target) =>
                if Int64.eq target Int64.zero then
                  Next (nextinstr rs) c_stk code_id next_tail_call_cnt m
                else match jump_table p (Z.to_nat (Int64.unsigned index)) with
                | Some _ => Next (rs#PC <- (Vlong Int64.zero)) c_stk
                    (Some (Z.to_nat (Int64.unsigned index))) next_tail_call_cnt m
                | None => Stuck
                end
            | _ => Next (nextinstr rs) c_stk code_id next_tail_call_cnt m
            end
          end
      | _ => Stuck
      end
    end
  | _ => Stuck
  end.

(** Execution of a single instruction [i] in initial state
    [rs] and [m].  Return updated state.  For instructions
    that correspond to actual eBPF instructions, the cases are
    straightforward transliterations of the informal descriptions
    given in the eBPF reference manuals.  For pseudo-instructions,
    refer to the informal descriptions given above. *)

Definition exec_instr (p: ebpf_prog) (i: instruction) (rs:regset) (c_stk: cstk) (code_id: option nat) (tail_call_cnt: nat) (m: mem) (addr_map: list addr_region) : outcome :=
  match i with
  | Plddw ty r lo hi         => exec_lddw r lo hi rs c_stk code_id tail_call_cnt m
  | Ploadsx k r r' o         => exec_loadsx k r r' o rs c_stk code_id tail_call_cnt m addr_map
  | Pload_probe k r r' o     => exec_load_probe k r r' o rs c_stk code_id tail_call_cnt m addr_map
  | Ploadsx_probe k r r' o   => exec_loadsx_probe k r r' o rs c_stk code_id tail_call_cnt m addr_map
  | Pno_spec              => Next (nextinstr rs) c_stk code_id tail_call_cnt m
  | Ptail_call            => exec_tail_call p rs c_stk code_id tail_call_cnt m addr_map
  | Pload k r r' o        => exec_load k r r' o rs c_stk code_id tail_call_cnt m addr_map
  | Pstore k r ri o       => exec_store k r ri o rs c_stk code_id tail_call_cnt m addr_map
  | Palu op w r ri        => exec_alu op w r ri rs c_stk code_id tail_call_cnt m
  | Pjmp32 i              => exec_jmp32 i rs c_stk code_id tail_call_cnt m
  | Pjmp64 o              => exec_jmp64 o rs c_stk code_id tail_call_cnt m
  | Pjmpcmp op w r ri o   => exec_jmpcmp op w r ri o rs c_stk code_id tail_call_cnt m
  | Pcall CallInternal i  => exec_call_internal i rs c_stk code_id tail_call_cnt m addr_map
  | Pret                  => exec_ret rs c_stk code_id tail_call_cnt m addr_map
  | _                     => Stuck
  end.


(** Undefine all registers except SP, BP and callee-save registers *)
(*
Definition undef_caller_save_regs (rs: regset) : regset :=
  fun r =>
    if preg_eq r BP || preg_eq r R10
    || In_dec preg_eq r (List.map preg_of (List.filter is_callee_save all_mregs))
    then rs r
    else Vundef.

(** Extract the values of the arguments of an external call.
    We exploit the calling conventions from module [Conventions], except that
    we use eBPF registers instead of locations. *)

Inductive extcall_arg (rs: regset) (c_stk: cstk) (code_id: option nat) (tail_call_cnt: nat) (m: mem): loc -> val -> Prop :=
  | extcall_arg_reg: forall r,
      extcall_arg rs m (R r) (rs (preg_of r))
  | extcall_arg_stack: forall ofs ty bofs v,
      bofs = Stacklayout.fe_ofs_arg + 4 * ofs ->
      Mem.loadv (chunk_of_type ty) m
                (Val.offset_ptr rs#BP (Ptrofs.repr bofs)) = Some v ->
      extcall_arg rs m (S Outgoing ofs ty) v.

Inductive extcall_arg_pair (rs: regset) (c_stk: cstk) (code_id: option nat) (tail_call_cnt: nat) (m: mem): rpair loc -> val -> Prop :=
  | extcall_arg_one: forall l v,
      extcall_arg rs m l v ->
      extcall_arg_pair rs m (One l) v
  | extcall_arg_twolong: forall hi lo vhi vlo,
      extcall_arg rs m hi vhi ->
      extcall_arg rs m lo vlo ->
      extcall_arg_pair rs m (Twolong hi lo) (Val.longofwords vhi vlo).

Definition extcall_arguments
    (rs: regset) (c_stk: cstk) (code_id: option nat) (tail_call_cnt: nat) (m: mem) (sg: signature) (args: list val) : Prop :=
  list_forall2 (extcall_arg_pair rs m) (loc_arguments sg) args.

Definition loc_external_result (sg: signature) : rpair preg :=
  map_rpair preg_of (loc_result sg).
*)

(** Execution of the instruction at [rs PC]. *)

Inductive tls_state: Type :=
  | TLS_State: regset -> cstk -> option nat -> nat -> mem -> tls_state.

Inductive eBPF_event : Set :=
  | eBPF_vload
  | eBPF_vstore
  | eBPF_ext_call
  | eBPF_atomic
  | eBPF_switch.

Definition etrace := list eBPF_event.
Definition eE0: list eBPF_event := nil.

Definition exec_instr_event (i: instruction) : etrace :=
  match i with
  | Pload k r r' o        => [eBPF_vload]
  | Pstore k r ri o       => [eBPF_vstore]
  | _                     => eE0
  end.

(** Quantify the selected index universally: choosing an unrelated index in a
    rule constructor would leave the active program's code unconstrained. *)
Inductive step (addr_map: list addr_region) (p: ebpf_prog): tls_state -> etrace -> tls_state -> Prop :=
  | exec_step_internal:
      forall c ofs i rs stk code_id tail_call_cnt m rs' stk' code_id' tail_call_cnt' m' et,
      rs PC = Vlong ofs ->
      (code_id = None -> c = (main_code p)) ->
      (forall idx, code_id = Some idx -> (jump_table p) idx = Some c) ->
      find_instr (Int64.unsigned ofs) c = Some i ->
      exec_instr p i rs stk code_id tail_call_cnt m addr_map = Next rs' stk' code_id' tail_call_cnt' m' ->
      exec_instr_event i = et ->
      step addr_map p (TLS_State rs stk code_id tail_call_cnt m) et (TLS_State rs' stk' code_id' tail_call_cnt' m')
  | exec_step_helper:
      forall c ofs i id res rs stk code_id tail_call_cnt m rs' m',
      rs PC = Vlong ofs ->
      (match code_id with
       | None => Some (main_code p)
       | Some idx => (jump_table p) idx
       end) = Some c ->
      find_instr (Int64.unsigned ofs) c = Some (Pcall CallByStaticID i) ->
      helper_id_at p code_id (Int64.unsigned ofs) = Some id ->
      exec_helper addr_map id res rs stk code_id tail_call_cnt m m'
        (Next rs' stk code_id tail_call_cnt m') ->
      step addr_map p (TLS_State rs stk code_id tail_call_cnt m) [eBPF_ext_call]
        (TLS_State rs' stk code_id tail_call_cnt m')
  | exec_step_external:
      forall c ofs cty i res word rs stk code_id tail_call_cnt m rs' m',
      rs PC = Vlong ofs ->
      (code_id = None -> c = (main_code p)) ->
      (forall idx, code_id = Some idx -> (jump_table p) idx = Some c) ->
      find_instr (Int64.unsigned ofs) c = Some (Pcall cty i) ->
      cty = CallByBTF ->
      ebpf_call_function i rs#R1 rs#R2 rs#R3 rs#R4 rs#R5 (Next rs stk code_id tail_call_cnt m) = Some (res, m') -> (**r an ebpf call may invoke another ebpf program that modifies the global memory *)
      register_word res addr_map = Some word ->
      rs' = (nextinstr (undef_caller_save_regs rs)) #R0 <- word ->
      step addr_map p (TLS_State rs stk code_id tail_call_cnt m) [eBPF_ext_call] (TLS_State rs' stk code_id tail_call_cnt m')
      .

Inductive initial_lst_state (addr_map: list addr_region) (ctx stk: block): tls_state -> Prop :=
  | initial_lst_state_intro: forall m rs ctx_word top,
      cast_address_abs_to_concrete (Vptr ctx Ptrofs.zero) addr_map = Some ctx_word ->
      stack_top_word stk bpf_stack_size addr_map = Some top ->
      rs = (Pregmap.init Vundef)#PC <- (Vlong Int64.zero)
             #R10 <- (Vlong top) #R1 <- (Vlong ctx_word) ->
      (forall i, 0 <= i -> i < bpf_stack_size -> Mem.valid_access m Mint8unsigned stk i Freeable) ->
      initial_lst_state addr_map ctx stk (TLS_State rs [] None 0 m).

Inductive final_lst_state (addr_map: list addr_region) (stk: block): tls_state -> val -> Prop :=
  | final_lst_state_intro: forall rs m t k word top,
      rs PC = Vundef ->
      rs R0 = Vlong word ->
      stack_top_word stk bpf_stack_size addr_map = Some top ->
      rs R10 = Vlong top ->
      (forall i, 0 <= i -> i < bpf_stack_size -> Mem.valid_access m Mint8unsigned stk i Freeable) ->
      final_lst_state addr_map stk (TLS_State rs [] t k m) (Vlong word).

Definition is_final_state (addr_map: list addr_region) (stk_blk: block)
    (rs: regset) (m: mem) (stk: cstk): bool :=
  match rs PC, rs R0, rs R10, stack_top_word stk_blk bpf_stack_size addr_map, stk with
  | Vundef, Vlong _, Vlong sp, Some top, [] => Int64.eq sp top
  | _, _, _, _, _ => false
  end.

Definition find_code (code_id:option nat) (bpf_prog: ebpf_prog): option code :=
  match code_id with
  | None => Some (main_code bpf_prog)
  | Some idx => (jump_table bpf_prog) idx
  end.

Fixpoint bpf_interpreter_old (fuel: nat) (bpf_prog: ebpf_prog) (st: outcome) (addr_map: list addr_region) (stk_blk: block): option val :=
  match fuel with
  | O => None (* assume we have enough fuel *)
  | S k =>
    match st with
    | Stuck => None
    | Next rs stk code_id tail_call_cnt m =>
      if is_final_state addr_map stk_blk rs m stk then Some (rs R0)
      else
        match rs PC with
        | Vlong ofs =>
          match find_code code_id bpf_prog with
          | None => None
          | Some c =>
            match find_instr (Int64.unsigned ofs) c with
            | None => None
            | Some i => bpf_interpreter_old k bpf_prog (exec_instr bpf_prog i rs stk code_id tail_call_cnt m addr_map) addr_map stk_blk
            end
          end
        | _ => None
        end
    end
  end.

 (** The global memory model for all eBPF programs, it splits into:
 - local memory, like eBPF stack or program-local array, only accessed by eBPF load/store instructions
 - shared memory, like map, hashmap, only accessed by eBPF atomic instructions
 *)
Definition tid := nat.

Record ThreadPool := {
  tp_map: tid -> option (regset * block);
  next_tid : tid;
}.

Record state := mkBuild_state {
  thread_pool : ThreadPool;
  env : block -> ebpf_prog * (option nat);
  gm          : mem;
  atom_bit    : bool; (*r true -> In atomic zone; false -> NOT-IN atomic zone *)
}.

Definition update_core (tp: ThreadPool) (t: tid) (r: regset): ThreadPool :=
{|
  tp_map :=
    fun i =>
      if Nat.eqb i t then
        match (tp_map tp) t with
        | None => None
        | Some (_, b) => Some (r, b)
        end
      else
        (tp_map tp) i;
  next_tid := next_tid tp
|}.


Definition atomic_fun (w: width) (aty: atomic_type) :=
  match aty with
  | AtomicADD w => if w then Val.addl else Val.add
  | AtomicOR  w => if w then Val.orl else Val.or
  | AtomicXOR w => if w then Val.xorl else Val.xorl
  | AtomicAND w => if w then Val.andl else Val.andl
  | _ => Val.andl (** TODO *)
  end.

Definition chunk_of_width (w: width) :=
  match w with
  | W32 => Mint32
  | W64 => Mint64
  end.

Definition exec_atomic_store (w: width) (aty: atomic_type) (dst src: ireg) (o : off) (rs:regset) (stk: cstk) (code_id: option nat) (tail_call_cnt: nat) (m: mem) (addr_map: list addr_region): outcome :=
  let sv := match w with W32 => Val.loword (rs src) | W64 => rs src end in
  match resolve_address m (rs dst) o addr_map with
  | None => Stuck
  | Some addr =>
    match Mem.loadv (chunk_of_width w) m addr with
    | None => Stuck
    | Some raw =>
      match register_word raw addr_map with
      | None => Stuck
      | Some word =>
      let v := match w with W32 => Val.loword word | W64 => word end in
      let res := (atomic_fun w aty v sv) in
        match Mem.storev (chunk_of_width w) m addr res with
        | None => Stuck
        | Some m' => Next (nextinstr rs) stk code_id tail_call_cnt m'
        end
      end
    end
  end.

Definition exec_atomic (w: width) (aty: atomic_type) (dst: ireg) (src: ireg+imm) (o : off) (rs:regset) (stk: cstk) (code_id: option nat) (tail_call_cnt: nat) (m: mem) (addr_map: list addr_region): outcome :=
  match src with
  | inl r => exec_atomic_store w aty dst r o rs stk code_id tail_call_cnt m addr_map
  | _ => Stuck
  end. 

Definition exec_atomic_instr_event (aty: atomic_type): etrace :=
  [eBPF_vload].

Inductive atomic_step (addr_map: list addr_region) (p: ebpf_prog): tls_state -> etrace -> tls_state -> Prop :=
  | exec_atomic_step:
      forall c ofs rs stk code_id tail_call_cnt m rs' stk' code_id' tail_call_cnt' m' et aty w dst src o,
      rs PC = Vlong ofs ->
      (code_id = None -> c = (main_code p)) ->
      (forall idx, code_id = Some idx -> (jump_table p) idx = Some c) ->
      find_instr (Int64.unsigned ofs) c = Some (Patomic aty dst src o) ->
      exec_atomic w aty dst src o rs stk code_id tail_call_cnt m addr_map = Next rs' stk' code_id' tail_call_cnt' m' ->
      exec_atomic_instr_event aty = et ->
        atomic_step addr_map p (TLS_State rs stk code_id tail_call_cnt m) et (TLS_State rs' stk' code_id' tail_call_cnt' m').
  (*
  | Switch_step: forall tp cid gm d cid' s s',
    (tp_map tp) cid = Some s -> (* valid eBPF thread id *)
    (tp_map tp) cid' = Some s' -> (* valid eBPF thread id *)
      gstep (mkBuild_state tp ge gm d) [eBPF_switch]
            (mkBuild_state tp cid' gm d)
.
  | Callstep: 
            
.*)

Section eBPF_GlobalSem.

(** One address environment is shared by every step in an execution. *)
Variable global_addr_map: list addr_region.

Inductive nstep: tid -> state -> etrace -> state -> Prop :=
  | Core_step: forall tp cid ge gm d et rs stk code_id tail_call_cnt tp' rs' stk' code_id' tail_call_cnt' gm' blk,
    (tp_map tp) cid = Some (rs, blk) ->
    update_core tp cid rs' = tp' ->
    step global_addr_map (fst (ge blk)) (TLS_State rs stk code_id tail_call_cnt gm) et (TLS_State rs' stk' code_id' tail_call_cnt' gm') ->
      nstep cid (mkBuild_state tp ge gm d) et 
                (mkBuild_state tp' ge gm' d).

Inductive astep: tid -> state -> etrace -> state -> Prop :=
  | At_step: forall tp cid ge gm d et rs stk code_id tail_call_cnt tp' rs' stk' code_id' tail_call_cnt' gm' blk,
    (tp_map tp) cid = Some (rs, blk) ->
    atomic_step global_addr_map (fst (ge blk)) (TLS_State rs stk code_id tail_call_cnt gm) et (TLS_State rs' stk' code_id' tail_call_cnt' gm') ->
      astep cid (mkBuild_state tp ge gm d) et 
                (mkBuild_state tp' ge gm' d).

Definition is_atomic (cid: tid) (st: state): bool :=
  match (tp_map (thread_pool st)) cid with
  | None => false 
  | Some (rs, blk) =>
    let (bpf_prog, code_id) := (env st) blk in
      match rs PC with
      | Vlong ofs =>
        match find_code code_id bpf_prog with
        | None => false
        | Some c =>
          match find_instr (Int64.unsigned ofs) c with
          | Some ins =>
            match ins with 
            | Patomic aty dst src offset => true
            | _ => false
            end
          | None => false
          end
        end
      | _ => false
      end
  end.

Definition read_address (cid: tid) (st: state): val -> Prop :=
  fun addr =>
    match (tp_map (thread_pool st)) cid with
    | None => False 
    | Some (rs, blk) =>
      let (bpf_prog, code_id) := (env st) blk in
        match rs PC with
        | Vlong ofs =>
          match find_code code_id bpf_prog with
          | None => False
          | Some c =>
            match find_instr (Int64.unsigned ofs) c with
            | Some ins =>
              match ins with
              | Pload sz dst src offset =>
                (add_word_offset rs#src offset) = addr (*
              | Pstore sz dst src offset =>
                (add_word_offset rs#dst offset) = addr
              | Patomic aty dst src offset =>
                (* TODO: refine atomic instruction? *)
                (add_word_offset rs#dst offset) = addr *)
              | _ => True
              end
            | None => False
            end
          end
        | _ => False
        end
      end.

Definition write_address (cid: tid) (st: state): val -> Prop :=
  fun addr =>
    match (tp_map (thread_pool st)) cid with
    | None => False 
    | Some (rs, blk) =>
      let (bpf_prog, code_id) := (env st) blk in
        match rs PC with
        | Vlong ofs =>
          match find_code code_id bpf_prog with
          | None => False
          | Some c =>
            match find_instr (Int64.unsigned ofs) c with
            | Some ins =>
              match ins with
              | Pstore sz dst src offset =>
                (add_word_offset rs#dst offset) = addr
              | Patomic aty dst src offset =>
                (* TODO: refine atomic instruction? *)
                (add_word_offset rs#dst offset) = addr
              | _ => True
              end
            | None => False
            end
          end
        | _ => False
        end
      end.

Definition has_race (s:state) (tid1:tid) (tid2:tid) :=
 (is_atomic tid1 s && is_atomic tid2 s = false) /\ (* not both are atomic *)
    (
      (exists a, write_address tid1 s a /\ write_address tid2 s a) (* concurrent write *)
      \/
        (exists a, write_address tid1 s a /\ read_address tid2 s a) (* concurrent read/write *)
      \/
        (exists a, read_address tid1 s a /\ write_address tid2 s a)) (* concurrent read/write *)
      .

Inductive GState :=
| GNormal (s:state)
| GStuck  (tid:tid) (s:state) (* thread [tid] is racy for state [s] *).

Inductive gstep : GState -> etrace -> GState -> Prop :=
| Atomic_step : forall tid s e s',
    is_atomic tid s = true -> (* the thread performs an atomic access (if there is a race, the other thread will generate an error) *)
    astep tid s e s' ->
      gstep (GNormal s) e (GNormal s')
| NAtomic_step : forall tid s e s',
    is_atomic tid s = false -> (* the thread do NOT perform an atomic access *)
    (forall tid', tid <> tid' -> not (has_race s tid' tid)) -> (* but there is no race. *)
    nstep tid s e s' ->
      gstep (GNormal s) e (GNormal s')
| Error_step : forall tid s,
    is_atomic tid s = false -> (* theres is a non-atomic racy access *)
    (exists tid', tid' <> tid /\ has_race s tid tid') ->
      gstep (GNormal s) eE0 (GStuck tid s).  
End eBPF_GlobalSem.

End RELSEM.
