; NOTE: Assertions have been autogenerated by utils/update_llc_test_checks.py
; RUN: llc < %s -mtriple=x86_64-apple-darwin | FileCheck %s

@.str2 = private unnamed_addr constant [7 x i8] c"memchr\00", align 1
@.str3 = private unnamed_addr constant [11 x i8] c"bsd_memchr\00", align 1
@str4 = private unnamed_addr constant [5 x i8] c"Bug!\00"

; Make sure at end of do.cond.i, we jump to do.body.i first to have a tighter
; inner loop.
define i32 @test_branches_order() uwtable ssp {
; CHECK-LABEL: test_branches_order:
; CHECK:       ## %bb.0: ## %entry
; CHECK-NEXT:    pushq %rbp
; CHECK-NEXT:    .cfi_def_cfa_offset 16
; CHECK-NEXT:    pushq %r15
; CHECK-NEXT:    .cfi_def_cfa_offset 24
; CHECK-NEXT:    pushq %r14
; CHECK-NEXT:    .cfi_def_cfa_offset 32
; CHECK-NEXT:    pushq %r13
; CHECK-NEXT:    .cfi_def_cfa_offset 40
; CHECK-NEXT:    pushq %r12
; CHECK-NEXT:    .cfi_def_cfa_offset 48
; CHECK-NEXT:    pushq %rbx
; CHECK-NEXT:    .cfi_def_cfa_offset 56
; CHECK-NEXT:    subq $1001016, %rsp ## imm = 0xF4638
; CHECK-NEXT:    .cfi_def_cfa_offset 1001072
; CHECK-NEXT:    .cfi_offset %rbx, -56
; CHECK-NEXT:    .cfi_offset %r12, -48
; CHECK-NEXT:    .cfi_offset %r13, -40
; CHECK-NEXT:    .cfi_offset %r14, -32
; CHECK-NEXT:    .cfi_offset %r15, -24
; CHECK-NEXT:    .cfi_offset %rbp, -16
; CHECK-NEXT:    movq ___stack_chk_guard@{{.*}}(%rip), %rax
; CHECK-NEXT:    movq (%rax), %rax
; CHECK-NEXT:    movq %rax, {{[0-9]+}}(%rsp)
; CHECK-NEXT:    xorl %r12d, %r12d
; CHECK-NEXT:    leaq -{{[0-9]+}}(%rsp), %r14
; CHECK-NEXT:    movq %rsp, %r15
; CHECK-NEXT:    jmp LBB0_1
; CHECK-NEXT:    .p2align 4, 0x90
; CHECK-NEXT:  LBB0_6: ## %for.inc9
; CHECK-NEXT:    ## in Loop: Header=BB0_1 Depth=1
; CHECK-NEXT:    incl %r12d
; CHECK-NEXT:  LBB0_1: ## %for.cond
; CHECK-NEXT:    ## =>This Loop Header: Depth=1
; CHECK-NEXT:    ## Child Loop BB0_3 Depth 2
; CHECK-NEXT:    cmpl $999, %r12d ## imm = 0x3E7
; CHECK-NEXT:    jg LBB0_7
; CHECK-NEXT:  ## %bb.2: ## %for.cond1.preheader
; CHECK-NEXT:    ## in Loop: Header=BB0_1 Depth=1
; CHECK-NEXT:    movl $-1, %ebp
; CHECK-NEXT:    movq %r15, %rdi
; CHECK-NEXT:    movq %r14, %rbx
; CHECK-NEXT:    .p2align 4, 0x90
; CHECK-NEXT:  LBB0_3: ## %for.cond1
; CHECK-NEXT:    ## Parent Loop BB0_1 Depth=1
; CHECK-NEXT:    ## => This Inner Loop Header: Depth=2
; CHECK-NEXT:    incl %ebp
; CHECK-NEXT:    cmpl $999, %ebp ## imm = 0x3E7
; CHECK-NEXT:    jg LBB0_6
; CHECK-NEXT:  ## %bb.4: ## %for.body3
; CHECK-NEXT:    ## in Loop: Header=BB0_3 Depth=2
; CHECK-NEXT:    addq $1002, %rbx ## imm = 0x3EA
; CHECK-NEXT:    leaq 1001(%rdi), %r13
; CHECK-NEXT:    movl $1000, %edx ## imm = 0x3E8
; CHECK-NEXT:    movl $120, %esi
; CHECK-NEXT:    callq _memchr
; CHECK-NEXT:    cmpq %rax, %rbx
; CHECK-NEXT:    movq %r13, %rdi
; CHECK-NEXT:    je LBB0_3
; CHECK-NEXT:    jmp LBB0_5
; CHECK-NEXT:  LBB0_7: ## %for.end11
; CHECK-NEXT:    leaq {{.*}}(%rip), %rdi
; CHECK-NEXT:    callq _puts
; CHECK-NEXT:    xorl %eax, %eax
; CHECK-NEXT:    movq %rsp, %rcx
; CHECK-NEXT:    jmp LBB0_8
; CHECK-NEXT:    .p2align 4, 0x90
; CHECK-NEXT:  LBB0_15: ## %for.inc38
; CHECK-NEXT:    ## in Loop: Header=BB0_8 Depth=1
; CHECK-NEXT:    incl %eax
; CHECK-NEXT:  LBB0_8: ## %for.cond14
; CHECK-NEXT:    ## =>This Loop Header: Depth=1
; CHECK-NEXT:    ## Child Loop BB0_10 Depth 2
; CHECK-NEXT:    ## Child Loop BB0_12 Depth 3
; CHECK-NEXT:    cmpl $999, %eax ## imm = 0x3E7
; CHECK-NEXT:    jg LBB0_16
; CHECK-NEXT:  ## %bb.9: ## %for.cond18.preheader
; CHECK-NEXT:    ## in Loop: Header=BB0_8 Depth=1
; CHECK-NEXT:    movq %rcx, %rdx
; CHECK-NEXT:    xorl %esi, %esi
; CHECK-NEXT:    xorl %edi, %edi
; CHECK-NEXT:    jmp LBB0_10
; CHECK-NEXT:    .p2align 4, 0x90
; CHECK-NEXT:  LBB0_14: ## %exit
; CHECK-NEXT:    ## in Loop: Header=BB0_10 Depth=2
; CHECK-NEXT:    addq %rsi, %rbp
; CHECK-NEXT:    incq %rdi
; CHECK-NEXT:    decq %rsi
; CHECK-NEXT:    addq $1001, %rdx ## imm = 0x3E9
; CHECK-NEXT:    cmpq $-1000, %rbp ## imm = 0xFC18
; CHECK-NEXT:    jne LBB0_5
; CHECK-NEXT:  LBB0_10: ## %for.cond18
; CHECK-NEXT:    ## Parent Loop BB0_8 Depth=1
; CHECK-NEXT:    ## => This Loop Header: Depth=2
; CHECK-NEXT:    ## Child Loop BB0_12 Depth 3
; CHECK-NEXT:    cmpl $999, %edi ## imm = 0x3E7
; CHECK-NEXT:    jg LBB0_15
; CHECK-NEXT:  ## %bb.11: ## %for.body20
; CHECK-NEXT:    ## in Loop: Header=BB0_10 Depth=2
; CHECK-NEXT:    movq $-1000, %rbp ## imm = 0xFC18
; CHECK-NEXT:    .p2align 4, 0x90
; CHECK-NEXT:  LBB0_12: ## %do.body.i
; CHECK-NEXT:    ## Parent Loop BB0_8 Depth=1
; CHECK-NEXT:    ## Parent Loop BB0_10 Depth=2
; CHECK-NEXT:    ## => This Inner Loop Header: Depth=3
; CHECK-NEXT:    cmpb $120, 1000(%rdx,%rbp)
; CHECK-NEXT:    je LBB0_14
; CHECK-NEXT:  ## %bb.13: ## %do.cond.i
; CHECK-NEXT:    ## in Loop: Header=BB0_12 Depth=3
; CHECK-NEXT:    incq %rbp
; CHECK-NEXT:    jne LBB0_12
; CHECK-NEXT:  LBB0_5: ## %if.then
; CHECK-NEXT:    leaq {{.*}}(%rip), %rdi
; CHECK-NEXT:    callq _puts
; CHECK-NEXT:    movl $1, %edi
; CHECK-NEXT:    callq _exit
; CHECK-NEXT:  LBB0_16: ## %for.end40
; CHECK-NEXT:    leaq {{.*}}(%rip), %rdi
; CHECK-NEXT:    callq _puts
; CHECK-NEXT:    movq ___stack_chk_guard@{{.*}}(%rip), %rax
; CHECK-NEXT:    movq (%rax), %rax
; CHECK-NEXT:    cmpq {{[0-9]+}}(%rsp), %rax
; CHECK-NEXT:    jne LBB0_18
; CHECK-NEXT:  ## %bb.17: ## %for.end40
; CHECK-NEXT:    xorl %eax, %eax
; CHECK-NEXT:    addq $1001016, %rsp ## imm = 0xF4638
; CHECK-NEXT:    popq %rbx
; CHECK-NEXT:    popq %r12
; CHECK-NEXT:    popq %r13
; CHECK-NEXT:    popq %r14
; CHECK-NEXT:    popq %r15
; CHECK-NEXT:    popq %rbp
; CHECK-NEXT:    retq
; CHECK-NEXT:  LBB0_18: ## %for.end40
; CHECK-NEXT:    callq ___stack_chk_fail
entry:
  %strs = alloca [1000 x [1001 x i8]], align 16
  br label %for.cond

for.cond:
  %j.0 = phi i32 [ 0, %entry ], [ %inc10, %for.inc9 ]
  %cmp = icmp slt i32 %j.0, 1000
  br i1 %cmp, label %for.cond1, label %for.end11

for.cond1:
  %indvars.iv50 = phi i64 [ %indvars.iv.next51, %for.body3 ], [ 0, %for.cond ]
  %0 = trunc i64 %indvars.iv50 to i32
  %cmp2 = icmp slt i32 %0, 1000
  br i1 %cmp2, label %for.body3, label %for.inc9

for.body3:
  %arraydecay = getelementptr inbounds [1000 x [1001 x i8]], [1000 x [1001 x i8]]* %strs, i64 0, i64 %indvars.iv50, i64 0
  %call = call i8* @memchr(i8* %arraydecay, i32 120, i64 1000)
  %add.ptr = getelementptr inbounds [1000 x [1001 x i8]], [1000 x [1001 x i8]]* %strs, i64 0, i64 %indvars.iv50, i64 %indvars.iv50
  %cmp7 = icmp eq i8* %call, %add.ptr
  %indvars.iv.next51 = add i64 %indvars.iv50, 1
  br i1 %cmp7, label %for.cond1, label %if.then

if.then:
  %puts = call i32 @puts(i8* getelementptr inbounds ([5 x i8], [5 x i8]* @str4, i64 0, i64 0))
  call void @exit(i32 1) noreturn
  unreachable

for.inc9:
  %inc10 = add nsw i32 %j.0, 1
  br label %for.cond

for.end11:
  %puts42 = call i32 @puts(i8* getelementptr inbounds ([7 x i8], [7 x i8]* @.str2, i64 0, i64 0))
  br label %for.cond14

for.cond14:
  %j13.0 = phi i32 [ 0, %for.end11 ], [ %inc39, %for.inc38 ]
  %cmp15 = icmp slt i32 %j13.0, 1000
  br i1 %cmp15, label %for.cond18, label %for.end40

for.cond18:
  %indvars.iv = phi i64 [ %indvars.iv.next, %exit ], [ 0, %for.cond14 ]
  %1 = trunc i64 %indvars.iv to i32
  %cmp19 = icmp slt i32 %1, 1000
  br i1 %cmp19, label %for.body20, label %for.inc38

for.body20:
  %arraydecay24 = getelementptr inbounds [1000 x [1001 x i8]], [1000 x [1001 x i8]]* %strs, i64 0, i64 %indvars.iv, i64 0
  br label %do.body.i

do.body.i:
  %n.addr.0.i = phi i64 [ %dec.i, %do.cond.i ], [ 1000, %for.body20 ]
  %p.0.i = phi i8* [ %incdec.ptr.i, %do.cond.i ], [ %arraydecay24, %for.body20 ]
  %2 = load i8, i8* %p.0.i, align 1
  %cmp3.i = icmp eq i8 %2, 120
  br i1 %cmp3.i, label %exit, label %do.cond.i

do.cond.i:
  %incdec.ptr.i = getelementptr inbounds i8, i8* %p.0.i, i64 1
  %dec.i = add i64 %n.addr.0.i, -1
  %cmp5.i = icmp eq i64 %dec.i, 0
  br i1 %cmp5.i, label %if.then32, label %do.body.i

exit:
  %add.ptr30 = getelementptr inbounds [1000 x [1001 x i8]], [1000 x [1001 x i8]]* %strs, i64 0, i64 %indvars.iv, i64 %indvars.iv
  %cmp31 = icmp eq i8* %p.0.i, %add.ptr30
  %indvars.iv.next = add i64 %indvars.iv, 1
  br i1 %cmp31, label %for.cond18, label %if.then32

if.then32:
  %puts43 = call i32 @puts(i8* getelementptr inbounds ([5 x i8], [5 x i8]* @str4, i64 0, i64 0))
  call void @exit(i32 1) noreturn
  unreachable

for.inc38:
  %inc39 = add nsw i32 %j13.0, 1
  br label %for.cond14

for.end40:
  %puts44 = call i32 @puts(i8* getelementptr inbounds ([11 x i8], [11 x i8]* @.str3, i64 0, i64 0))
  ret i32 0
}

declare i8* @memchr(i8*, i32, i64) nounwind readonly
declare void @exit(i32) noreturn
declare i32 @puts(i8* nocapture) nounwind

