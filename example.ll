; ModuleID = 'exampleModule'


 


%list-w32-cons = type {i32, i32, %list-w32-cons addrspace(1)*}


declare external ccc  i64 addrspace(1)* @allocateHeapBlock(i64 addrspace(1)*)    


declare i64 addrspace(1)* @llvm.ptrmask.p1i64.i64(i64 addrspace(1)*, i64) readnone speculatable   


define external ccc  i32 @exampleFunction(i64 addrspace(1)*  %hp.0, i32  %x, i32  %y)    {
beginning:
  %hp = alloca i64 addrspace(1)*, align 8 
  store  i64 addrspace(1)* %hp.0, i64 addrspace(1)** %hp, align 8 
  %z = add   i32 %x, %y 
  %hp.check = load  i64 addrspace(1)*, i64 addrspace(1)** %hp, align 8 
  %hp.upper = getelementptr inbounds i64, i64 addrspace(1)* %hp.check, i64 24 
  %hp.low =  call ccc  i64 addrspace(1)*  @llvm.ptrmask.p1i64.i64(i64 addrspace(1)*  %hp.check, i64  18446744073709547520)  
  %hp.high = getelementptr inbounds i64, i64 addrspace(1)* %hp.low, i64 4095 
  %has-sufficient-space = icmp ult i64 addrspace(1)* %hp.upper, %hp.high 
  br i1 %has-sufficient-space, label %beginning.post-heap-check, label %beginning.allocate-heap-block 
beginning.allocate-heap-block:
  %hp.updated =  call ccc  i64 addrspace(1)*  @allocateHeapBlock(i64 addrspace(1)*  %hp.check)  
  store  i64 addrspace(1)* %hp.updated, i64 addrspace(1)** %hp, align 8 
  br label %beginning.post-heap-check 
beginning.post-heap-check:
  %hp.b = load  i64 addrspace(1)*, i64 addrspace(1)** %hp, align 8 
  %hp.b.list.base = bitcast i64 addrspace(1)* %hp.b to %list-w32-cons addrspace(1)* 
  %hp.b.list.tag = getelementptr inbounds %list-w32-cons, %list-w32-cons addrspace(1)* %hp.b.list.base, i64 0, i32 0 
  store  i32 1, i32 addrspace(1)* %hp.b.list.tag, align 4 
  %hp.b.list.elem = getelementptr inbounds %list-w32-cons, %list-w32-cons addrspace(1)* %hp.b.list.base, i64 0, i32 1 
  store  i32 507, i32 addrspace(1)* %hp.b.list.elem, align 4 
  %hp.b.next = getelementptr inbounds i64, i64 addrspace(1)* %hp.b, i64 3 
  store  i64 addrspace(1)* %hp.b.next, i64 addrspace(1)** %hp, align 8 
  ret i32 %x 
}
