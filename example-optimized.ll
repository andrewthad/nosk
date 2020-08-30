; ModuleID = '<stdin>'
source_filename = "<stdin>"

%list-w32-cons = type { i32, i32, %list-w32-cons addrspace(1)* }

declare i64 addrspace(1)* @allocateHeapBlock(i64 addrspace(1)*) local_unnamed_addr

declare i64 addrspace(1)* @llvm.ptrmask.p1i64.i64(i64 addrspace(1)*, i64)

define i32 @exampleFunction(i64 addrspace(1)* %hp.0, i32 returned %x, i32 %y) local_unnamed_addr {
beginning:
  %hp.upper = getelementptr inbounds i64, i64 addrspace(1)* %hp.0, i64 24
  %hp.low = tail call i64 addrspace(1)* @llvm.ptrmask.p1i64.i64(i64 addrspace(1)* %hp.0, i64 -4096)
  %hp.high = getelementptr inbounds i64, i64 addrspace(1)* %hp.low, i64 4095
  %has-sufficient-space = icmp ult i64 addrspace(1)* %hp.upper, %hp.high
  br i1 %has-sufficient-space, label %beginning.post-heap-check, label %beginning.allocate-heap-block

beginning.allocate-heap-block:                    ; preds = %beginning
  %hp.updated = tail call i64 addrspace(1)* @allocateHeapBlock(i64 addrspace(1)* %hp.0)
  br label %beginning.post-heap-check

beginning.post-heap-check:                        ; preds = %beginning.allocate-heap-block, %beginning
  %hp.01 = phi i64 addrspace(1)* [ %hp.0, %beginning ], [ %hp.updated, %beginning.allocate-heap-block ]
  %hp.b.list.base = bitcast i64 addrspace(1)* %hp.01 to %list-w32-cons addrspace(1)*
  %hp.b.list.tag = bitcast i64 addrspace(1)* %hp.01 to i32 addrspace(1)*
  store i32 1, i32 addrspace(1)* %hp.b.list.tag, align 4
  %hp.b.list.elem = getelementptr inbounds %list-w32-cons, %list-w32-cons addrspace(1)* %hp.b.list.base, i64 0, i32 1
  store i32 507, i32 addrspace(1)* %hp.b.list.elem, align 4
  ret i32 %x
}
