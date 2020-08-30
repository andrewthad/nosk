define external ccc  i32 @example(i32  %x, i32  %y)    {
beginning:
  %z = mul   i32 %x, %y 
join-true:
  %b = mul   i32 %z, 653 
  ret i32 %b
join-false:
  ret
}

