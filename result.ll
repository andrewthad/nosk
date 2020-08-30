define external ccc  i32 @exampleFunction(i32  %x, i32  %y)    {
beginning:
  br label %later
def.1:
  br label %return.0 
pattern.12.2:
  switch i32 %w, label %def.3 [i32 109, label %pattern.109.5 i32 258, label %pattern.258.4] 
def.3:
  br label %return.0 
pattern.258.4:
  br label %return.0 
pattern.109.5:
  %b = mul   i32 %z, 653 
  br label %return.0 
pattern.36.6:
  %t = mul   i32 %z, %z 
  br label %return.0 
return.0:
  %p = phi i32 [%t, %pattern.36.6], [%b, %pattern.109.5], [998, %pattern.258.4], [630, %def.3], [500, %def.1] 
  %q = mul   i32 %p, 55 
  ret i32 %q 
later:
  %z = add   i32 %x, %y 
  %w = mul   i32 %y, %z 
  switch i32 %w, label %def.1 [i32 36, label %pattern.36.6 i32 12, label %pattern.12.2] 
}
